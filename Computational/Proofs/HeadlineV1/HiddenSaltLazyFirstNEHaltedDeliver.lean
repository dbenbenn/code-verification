/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Honest
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Inject.HelpersC
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple4
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple5
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple6
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple8
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliver
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliverProbe
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import ProofLib.SepLogic.WP.StateNorm

/-!
# Online-Halted `deliver` Coupling

**Checked by Lean.** Proves the halted per-query `deliver` coupling step
`firstNECoupledInvD_deliver_halted_query_step` between `firstNEHalted'` and
`cellSimRunTrackHalted`.-/

public section

set_option autoImplicit false

open scoped MeasureTheory
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHalted (evalDist_firstNEHalted'_dead_eq_zero firstNEHalted')
open Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliverAux (bucketSimRunTrackHalted bucketSimRunTrackHalted_bind cellSimRunTrackHalted deliver_halted_cell_win deliver_halted_pure_lockstep firstNEHalted'_deliver_of_not_lazy simImplCTrackHalted_deliver_run simImplCTrackHalted_inject_run simulateQ_firstNEHalted'_deliver_query_bind stage2CellBucketSumRunTrackHalted updDeliverTr)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.LibsignalSM.Proofs.Refinement (KemFailTrackState deliverForgeHook sameWireFig8 simImplCTrackHalted simRecvStepC)
open CryptoGames.LibsignalSession (GhostState IdentityKey Params PublicKey)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart X25519RealizesDh lFS lFig8)
open CryptoGames.Ratchet.LibsignalSim (Fig8C Fig8St SimState fwd liftQ onAnswer)
open CryptoGames.Ratchet.LibsignalSimC (Hook LibsignalToModularSchemeSimState probeHook)
open CryptoGames.SM (RecvResult)
open CryptoGames.SM.Construction.DeliverForge (bucketAuthCfg deliverForgeBaseImpl deliverForgeQuery dfQueryTargetEpoch fullImplBaseDFPaper fullImplBaseDFPaperBucket inStage2Bucket injectQueryDF oracleImplBaseDFPaper oracleImplPaper sameHdrScheme simDeliverForgeDF simImplDF'Paper simInjectDF withWinEpDF)
open CryptoGames.SM.Thm1 (Mirror)
open CryptoGames.SM.Thm1L17 (StateT_run_lift)
open CryptoVerification.LibsignalSession.HeadlineV1 (EvictedSpurHistSimInvLazy FirstNECellFamilyInvT_body FirstNECoupledInvD FirstNEInTransOriginInv PPrimePaperRelShifted SyncInv bucketWinPred cellDelta cellDelta_le_three cellTrivialT cellTrivialT_of_not_B1 cellWinPred deliverForgeHook_probe_run deliver_accept_sync_and_family_step evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy exists_winning_cell_of_deliverHcasesAtExt fig8ToDFImpl_inject_run firstNEInTransOriginInv_accept_step firstNEInTransOriginInv_inject_step firstNEProbeAt_imp_deliverHcasesAtExt_of_inv_lazy fwdAnswerC_deliver_lockstep fwdAnswerC_run fwdC_true_cases guardC_simRecvC_true_lazy_cases hc'_cases_of_sameWireFig8 inTransit_sync_of_evictedSpurHistSimInvLazy injectImplCell injectImplCell_run injectImpl_h1_run inject_step_branch_cases lFig8_receive_spec onAccept_true_of_inTransit_some onAnswer_rejected_run onAnswer_run_pure onAnswer_true_accepted_of_inTransit_some pos_epoch_lt_min_of_trivial probeHook_fwdAnswerC_inject_run_of_eq probeStep_of_guardC_probe_rejected probeStep_of_guardC_pure probe_c'_facts_of_sameWire_ne resyncC_none_lockstep resyncC_some_of_accept resyncC_some_of_receive_none runCellStep runCellStep_congr_run runCellStep_fwdAnswerC_inject_of_eq runCellStep_guardC_probe_rejected_of_receive_none runCellStep_guardC_pure runCellStep_probe_rejected_win s_win_of_cellWinPred simRecvStepC_of_probeHook_run syncInv_inject_accept_step syncInv_updAmbSimStateC updAmbSimStateC updAmbSimStateC_fields updKeptOnRes updKeptOnRes_base_sent_snaps_eq updKeptOnRes_rejected updMirOnRes zoomB_deliverForgeHook_run)

namespace Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliver

open scoped ENNReal BigOperators
open OracleComp OracleSpec

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)

/-! ## 1. Halted Stage-2 Bucket Win Evaluation (`fwdAnswerC` and `probe`) -/

theorem bucketSimRunTrackHalted_fwdAnswerC_win
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (par isDel : Bool) (Q : Party) (w : List (BitVec 8))
    (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (st' : Fig8St Pt) (t₀ i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ)
    (sC sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s₀ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (ans : Option (RecvResult (Plain ℓ))) (b' : SimState (List (BitVec 8)) Pt ℓ)
    (hfwd : (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000)
        (deliverForgeHook Pt ℓ) Q w isDel)).run sC =
      (CryptoGames.Ratchet.LibsignalSimC.fwdAnswerC qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w isDel ci? T pq' c').run sC₀)
    (hInT : (sC₀.base.honest.any fun wc => decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false)
    (hwin₀ : s₀.win = false) (hinT₀ : (s₀.inTransit Q.other c').isSome = false) (hsafe₀ : s₀.safeInj (2 + 1) = true)
    (hrcv₀ : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s₀.st Q) c' = some (st', t₀, i', m_out))
    (hq : ¬((qep + 1) + 1 < t₀)) (htriv₀ : s₀.trivial (2 + 1) ⟨Q.other, t₀, i'⟩ = false)
    (hinB : inStage2Bucket 1 tL par t₀ = true) (hep_c' : c'.1.1 = t₀)
    (hrun : (onAnswer (PQ := List (BitVec 8)) (Pt := Pt) (ℓ := ℓ) (qep := qep) Q w isDel ci? T pq' (some .rejected)).run
        (updKeptOnRes (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (lFS P.C P.codec ℓ encT idOf 25000)
          Q c' (some .rejected) sC₀).base = pure (ans, b')) :
    bucketSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep tL par
      (cond isDel
        (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8)))
          (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w)))))))
        (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8)))
          (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))))))
      sC tr sent m' (s₀, none) =
      pure ((((ans, ({ updKeptOnRes (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) Q c' (some .rejected) sC₀ with base := b' },
        cond isDel (updDeliverTr K sC tr Q w ans) tr)), sent), m'), ({ s₀ with win := true }, some t₀)) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  have hbase_step : (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par
      (.inr (.inl (.inl (.inr (Q, c')))))).run (s₀, none) = pure (some .rejected, ({ s₀ with win := true }, some t₀)) := by
    change fig.receive (s₀.st Q) c' = some (st', t₀, i', m_out) at hrcv₀
    simp only [fullImplBaseDFPaperBucket, withWinEpDF, StateT.run_mk, fullImplBaseDFPaper,
      oracleImplBaseDFPaper, oracleImplPaper, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
    unfold CryptoGames.SM.injectImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, hinT₀, hsafe₀,
      Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hrcv₀, hq, htriv₀,
      bucketAuthCfg, hinB, StateT.run_set, StateT.run_pure, dfQueryTargetEpoch, hep_c']; rfl
  have hcore : (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
        (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC
          P encT decT qep fig fs (deliverForgeHook Pt ℓ) Q w isDel)).run sC).run sent)).run m')).run (s₀, none) =
      pure ((((ans, { updKeptOnRes fig fs Q c' (some .rejected) sC₀ with base := b' }), sent), m'),
        ({ s₀ with win := true }, some t₀)) := by
    rw [hfwd, fwdAnswerC_run]; simp only [StateT.run_bind, simulateQ_bind]
    rw [zoomB_deliverForgeHook_run]; unfold fwd
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hInT, Bool.false_eq_true, ↓reduceIte]
    unfold liftQ CryptoGames.SM.injectQuery
    simp only [StateT_run_lift, deliverForgeHook, StateT.run_bind, StateT.run_pure,
      simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, bind_assoc, pure_bind]
    rw [fig8ToDFImpl_inject_run]; unfold injectQueryDF
    simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
      StateT.run_bind, StateT.run_pure]
    change ((simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simInjectDF (Q, c')).run m')).run (s₀, none) >>= _) = _
    unfold simInjectDF injectQueryDF
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
    change ((fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par
      (.inr (.inl (.inl (.inr (Q, c')))))).run (s₀, none) >>= _) = _
    rw [hbase_step, pure_bind]; simp only [StateT.run_pure, simulateQ_pure, pure_bind]
    change (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
        (((CryptoGames.Ratchet.LibsignalSimC.runOnBaseState (deliverForgeHook Pt ℓ)
            (onAnswer (qep := qep) Q w isDel ci? T pq' (some .rejected))).run
          (updKeptOnRes fig fs Q c' (some .rejected) sC₀)).run sent)).run m')).run
      ({ s₀ with win := true }, some t₀) = _
    rw [zoomB_deliverForgeHook_run, hrun]
    simp only [deliverForgeHook, simulateQ_pure, StateT.run_pure, pure_bind]
  cases isDel
  · unfold bucketSimRunTrackHalted; dsimp only [cond]; simp only [simulateQ_query]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd, PFunctor.Obj.mk, id]
    simp only [id_map]
    change (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
        (((simImplCTrackHalted P K encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh
            (.inr (.inl (.inr (Q, w))))).run (sC, tr)).run sent)).run m')).run (s₀, none) = _
    rw [simImplCTrackHalted_inject_run]
    simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]; rw [hcore, pure_bind]
  · unfold bucketSimRunTrackHalted; dsimp only [cond]; simp only [simulateQ_query]
    dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
      OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd, PFunctor.Obj.mk, id]
    simp only [id_map]
    change (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
        (((simImplCTrackHalted P K encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh
            (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr)).run sent)).run m')).run (s₀, none) = _
    rw [simImplCTrackHalted_deliver_run]
    simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]; rw [hcore, pure_bind]

theorem bucketSimRunTrackHalted_deliver_probe_win
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (par : Bool) (Q : Party) (w : List (BitVec 8))
    (c c' : Fig8C Pt) (r : CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (st' : Fig8St Pt) (t' i' : ℕ) (m_out : LibsignalMsgPublicPart × Plain ℓ)
    (sC sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s₀ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hprobe : (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC
        P encT decT qep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) (deliverForgeHook Pt ℓ) Q w true)).run sC =
      ((StateT.lift ((deliverForgeHook Pt ℓ).probe Q c') >>= fun _ => pure (some RecvResult.rejected)) :
        StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) _ _).run sC₀)
    (hfind : sent.find? (fun c₀ => sameWireFig8 c₀ c') = some c) (hwin₀ : s₀.win = false)
    (hin₀ : s₀.inTransit Q.other c = some r)
    (hbad₀ : ((s₀.inTransit Q.other c').isSome || s₀.comp.contains r.pos || !sameHdrScheme c c') = false)
    (hrcv₀ : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (s₀.st Q) c' = some (st', t', i', m_out))
    (ht'_cond : (decide ((qep + 1) + 1 < t') || t' != r.pos.epoch) = false)
    (htriv₀ : s₀.trivial (2 + 1) ⟨Q.other, t', i'⟩ = false)
    (hinB : inStage2Bucket 1 tL par t' = true) (hep_c' : c'.1.1 = t') :
    bucketSimRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep tL par
      (liftM (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8)))
        (Plain ℓ) (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w)))))))
      sC tr sent m' (s₀, none) =
      pure ((((some RecvResult.rejected, (sC₀, updDeliverTr K sC tr Q w (some RecvResult.rejected))), sent), m'),
        ({ s₀ with win := true }, some t')) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  have hbase_step : (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par (.inr (.inr (Q, c, c')))).run
      (s₀, none) = pure (some .rejected, ({ s₀ with win := true }, some t')) := by
    change fig.receive (s₀.st Q) c' = some (st', t', i', m_out) at hrcv₀
    simp only [fullImplBaseDFPaperBucket, withWinEpDF, StateT.run_mk, fullImplBaseDFPaper,
      oracleImplBaseDFPaper, QueryImpl.add_apply_inr]
    unfold deliverForgeBaseImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hwin₀, Bool.false_eq_true, ↓reduceIte,
      hin₀, hbad₀, hrcv₀, ht'_cond, htriv₀, bucketAuthCfg, hinB, StateT.run_set, StateT.run_pure,
      dfQueryTargetEpoch, hep_c']; rfl
  have hcore : (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
        (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC
          P encT decT qep fig fs (deliverForgeHook Pt ℓ) Q w true)).run sC).run sent)).run m')).run (s₀, none) =
      pure ((((some RecvResult.rejected, sC₀), sent), m'), ({ s₀ with win := true }, some t')) := by
    rw [hprobe]
    simp only [StateT_run_lift, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, bind_assoc]
    rw [deliverForgeHook_probe_run, hfind]; dsimp only
    unfold deliverForgeQuery
    simp only [simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind]
    change ((simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
      ((simDeliverForgeDF (Q, c, c')).run m')).run (s₀, none) >>= _) = _
    unfold simDeliverForgeDF deliverForgeQuery
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT_run_lift,
      simulateQ_bind, simulateQ_HasQuery_query, bind_assoc]
    change ((fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par (.inr (.inr (Q, c, c')))).run
      (s₀, none) >>= _) = _
    rw [hbase_step, pure_bind]; simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  unfold bucketSimRunTrackHalted; dsimp only; simp only [simulateQ_query]
  dsimp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, OracleSpec.query,
    OracleQuery.input, OracleQuery.cont, OracleQuery.mk, PFunctor.Obj.fst, PFunctor.Obj.snd, PFunctor.Obj.mk, id]
  simp only [id_map]
  change (simulateQ (fullImplBaseDFPaperBucket fig 1 (qep + 1) sameHdrScheme tL par)
    ((simulateQ (simImplDF'Paper (2 + 1) (qep + 1))
      (((simImplCTrackHalted P K encT decT qep fig fs (deliverForgeHook Pt ℓ) Dh
          (.inr (.inl (.inl (.inr (Q, w)))))).run (sC, tr)).run sent)).run m')).run (s₀, none) = _
  rw [simImplCTrackHalted_deliver_run]
  simp only [StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]; rw [hcore, pure_bind]

/-! ## 4. Halted `deliver` Sub-Branch Lemmas and `firstNECoupledInvD_deliver_halted_query_step` -/

private theorem firstNECoupledInvD_deliver_halted_probe_none_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8)) (b : Bool) (c' : Fig8C Pt)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hrcv : (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c' = none)
    (hprobe : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        ((StateT.lift (H.probe Q c') >>= fun _ => pure (some CryptoGames.SM.RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) M _).run
          (updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep (u u₁)
        sC₁ tr₁ sent₁ m₁' s_cell₁) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₁ := updAmbSimStateC Pt b sC
  have hprobe_run := probeStep_of_guardC_probe_rejected Pt P encT decT qep fig fs Q w c'
    sC sC₁ g (hprobe (probeHook fig (qep + 1)))
  rw [hrcv, Option.isSome_none] at hprobe_run
  have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, hbody, (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
      syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g
        (s_cell 0 none) hsync⟩)
  refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
    sC sC₁ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
    hbody hlazy hprobe_run hinv₁ (fun t ht tL htL => ?_) hih
  rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
  · exact Or.inl hdoomed
  · exact Or.inr (runCellStep_guardC_probe_rejected_of_receive_none Pt P encT decT qep t tL
      fig fs Q w c' sC sC₁ sent m' hrel_sh hrcv (hprobe (deliverForgeHook Pt ℓ)))

private theorem firstNECoupledInvD_deliver_halted_probe_lazy_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8)) (b : Bool) (c' : Fig8C Pt)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = true)
    (hrcv : ((lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam).receive (g.st Q) c').isSome = true)
    (hc'_probe :
      ∀ (c_hon : Fig8C Pt),
        (sC.base.honest.find? fun wc =>
          wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c_hon →
        sameWireFig8 c_hon c' = true ∧ c_hon ≠ c')
    (hprobe : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        ((StateT.lift (H.probe Q c') >>= fun _ => pure (some CryptoGames.SM.RecvResult.rejected)) :
          StateT (LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) M _).run
          (updAmbSimStateC Pt b sC)) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₀ := updAmbSimStateC Pt b sC
  obtain ⟨⟨st', t', i', m_out⟩, hrcv_eq⟩ := Option.isSome_iff_exists.mp hrcv
  have hprobe_run := probeStep_of_guardC_probe_rejected Pt P encT decT qep fig fs Q w c'
    sC sC₀ g (hprobe (probeHook fig (qep + 1)))
  rw [hrcv] at hprobe_run
  have hstep_probe :
      (simRecvStepC P ℓ Dh encPt encT decT idOf lam qep Q w true (sC, (g, false))).2.2.2 =
        true := by
    rw [simRecvStepC_of_probeHook_run P ℓ Dh encPt encT decT idOf lam qep Q w true
      sC sC₀ g g false true (some CryptoGames.SM.RecvResult.rejected) hprobe_run]
  obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
  obtain ⟨c, r, hhonC, hc_mem, hc_sender, hin_g, _, _, _, hpos_qep, _⟩ :=
    inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
      hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
  obtain ⟨hsame, hne⟩ := hc'_probe c hhonC
  rcases hlazy with ⟨r_idx, w_rem, hInv⟩
  obtain ⟨hw, hfind, hhdr, hnone_g, hr_pos⟩ :=
    probe_c'_facts_of_sameWire_ne Pt P K InvPQ Dh encPt encT hinj idOf lam qep q r_idx w_rem
      Q w c c' r st' t' i' m_out hInv hsync.2.2.2.2.2.2.2.2.2.2.2 hhonC hc_mem hc_sender
      hin_g hrcv_eq hsame hne
  have ht'_le : t' ≤ (qep + 1) + 1 := by
    have ht'_ep : t' = r.pos.epoch := by rw [hr_pos]
    omega
  have ht'_mem : t' ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  obtain ⟨x₀, s_R, ec, winBefore, epExp, hinv_sim, _⟩ := hInv.2
  have hno_ev := evictedOnlyNoForgeAt_of_evictedSpurHistSimInvLazy P K hspqr_eq hInv_top ℓ Dh
    encPt encT decT idOf hid hdec lam sC g Q hInv
  have hcases := firstNEProbeAt_imp_deliverHcasesAtExt_of_inv_lazy
    P InvPQ ℓ Dh hDh encPt encT decT idOf hX hinj lam qep q r_idx Q w c r t' i' x₀ s_R sC g
    ec winBefore epExp hinv_sim hsync.2.2.2.2.2.2.2.2.1 hsync.2.2.2.2.2.2.1 hno_ev
    hstep_probe hw hbody.2 horig ht'_le hin_g hr_pos
  obtain ⟨tLStar, htLStar, hrel_star, hcomp_star, htriv_star, hwin_star⟩ :=
    exists_winning_cell_of_deliverHcasesAtExt qep Q c r t' i' hbody ht'_le hin_g hr_pos hcases
  refine deliver_halted_cell_win P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
    sC sC₀ g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell
    t' ht'_mem tLStar htLStar { s_cell t' tLStar with win := true } ?_ hwin_star
    fun hnotB1 hnotB2 par hinB => ?_
  · rw [runCellStep_congr_run fig qep t' tLStar _ _ sC sC₀ sent m' (s_cell t' tLStar)
        (hprobe (deliverForgeHook Pt ℓ)),
      runCellStep_probe_rejected_win Pt fig qep t' tLStar Q c c' r st' i' m_out sC₀ sent m'
        hrel_star hfind ht'_le hin_g hnone_g hcomp_star hhdr hrcv_eq hr_pos htriv_star]
  · have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hrel0 : PPrimePaperRelShifted (s_cell 0 none) m' g := (hbody.2 0 ht0).1.toShifted
    have hwin0 : (s_cell 0 none).win = false := hrel0.win_df_false
    have hs0_eq : s_cell t' tLStar = s_cell 0 none := by
      rcases (hbody.2 t' ht'_mem).2.2 tLStar htLStar with hdoomed | ⟨_, _, _, hcomp₀⟩
      · exfalso
        exact Bool.false_ne_true (hrel_star.win_df_false.symm.trans hdoomed.2.2.2)
      · exact (hcomp₀.eq_of_not_B1_not_B2 hnotB1 hnotB2).trans (hbody.1 t' ht'_mem 0 ht0)
    have hin₀ : (s_cell 0 none).inTransit Q.other c = some r := by
      rw [hrel0.inTransit_eq]; exact hin_g
    have hbad₀ : (((s_cell 0 none).inTransit Q.other c').isSome ||
        (s_cell 0 none).comp.contains r.pos || !CryptoGames.SM.Construction.DeliverForge.sameHdrScheme c c') = false := by
      rw [hrel0.inTransit_eq Q.other c', hnone_g, ← hs0_eq, hcomp_star, hhdr]; rfl
    have hrcv₀ : fig.receive ((s_cell 0 none).st Q) c' = some (st', t', i', m_out) := by
      rw [congrFun hrel0.st_eq Q]; exact hrcv_eq
    have ht'_cond : (decide ((qep + 1) + 1 < t') || t' != r.pos.epoch) = false := by
      have h1 : decide ((qep + 1) + 1 < t') = false := decide_eq_false (by omega)
      have h2 : (t' != r.pos.epoch) = false := by rw [hr_pos]; simp
      rw [h1, h2]; rfl
    have htriv₀ : (s_cell 0 none).trivial (2 + 1) ⟨Q.other, t', i'⟩ = false := by
      have h := htriv_star
      simp only [cellDelta, hnotB1, ↓reduceIte, hs0_eq] at h
      exact h
    have hep_c' : c'.1.1 = t' :=
      (lFig8_receive_spec Pt P Dh encPt encT idOf lam hrcv_eq).2.1.symm
    refine ⟨({ s_cell 0 none with win := true }, some t'), ?_, ?_⟩
    · rw [bucketSimRunTrackHalted_bind,
        bucketSimRunTrackHalted_deliver_probe_win P K Dh encPt encT decT idOf lam qep tLStar par
          Q w c c' r st' t' i' m_out sC sC₀ tr sent m' (s_cell 0 none)
          (hprobe (deliverForgeHook Pt ℓ)) hfind hwin0 hin₀ hbad₀ hrcv₀ ht'_cond htriv₀ hinB hep_c',
        pure_bind]
    · unfold bucketWinPred; dsimp only
      have hw_eq : cellWinPred tLStar t' { s_cell 0 none with win := true } = true :=
        hs0_eq ▸ hwin_star
      unfold cellWinPred at hw_eq
      simp only [hnotB1, ↓reduceIte] at hw_eq
      exact hw_eq

private theorem firstNECoupledInvD_deliver_halted_resync_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8))
    (c : Fig8C Pt) (v : Option (ℕ × ℕ × (LibsignalMsgPublicPart × Plain ℓ)))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hstop : sC.base.stopped = false)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = true)
    (hhonC : (sC.base.honest.find? fun wc =>
      wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c)
    (hres : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        (CryptoGames.Ratchet.LibsignalSimC.resyncC qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) H Q w ci? T pq' c v).run
          (updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep (u u₁)
        sC₁ tr₁ sent₁ m₁' s_cell₁) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₀ := updAmbSimStateC Pt b sC
  have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
    syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none) hsync
  have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
    (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
  have hstop₀ : sC₀.base.stopped = false :=
    (updAmbSimStateC_fields Pt b sC).2.2.2.2.2.trans hstop
  have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
  rcases v with _ | ⟨t_v, i_v, pm_v⟩
  · have hprobe_run :
        (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
            (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
          pure ((some CryptoGames.SM.RecvResult.rejected, sC₀), (g, false)) := by
      rw [hres (probeHook fig (qep + 1))]
      exact (resyncC_none_lockstep Pt qep 0 none fig fs Q w ci? T pq' c sC₀ sent m'
        g (s_cell 0 none) false).1
    refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
      sC sC₀ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
      hbody hlazy hprobe_run hinv₀ (fun t _ tL _ => Or.inr ?_) hih
    rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
        (hres (deliverForgeHook Pt ℓ)),
      (resyncC_none_lockstep Pt qep t tL fig fs Q w ci? T pq' c sC₀ sent m' g
        (s_cell t tL) false).2]
  · obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
    obtain ⟨c_hon, r, hhonC_eq, _, _, hr_g, hpos_eq, hpos_ep, hpos_le, hpos_qep, _⟩ :=
      inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
        hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
    have hc_eq : c_hon = c := Option.some.inj (hhonC_eq.symm.trans hhonC)
    subst c_hon
    have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
    have hrel0 : PPrimePaperRelShifted (s_cell 0 none) m' g := (hbody.2 0 ht0).1.toShifted
    cases hrcv : fig.receive (g.st Q) c with
    | none =>
      have hprobe_run :
          (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some CryptoGames.SM.RecvResult.rejected, sC₀), (g, false)) := by
        rw [hres (probeHook fig (qep + 1))]
        exact (resyncC_some_of_receive_none Pt fig fs qep 0 none Q w ci? T pq' c t_v i_v pm_v
          sC₀ sent false hrel0 hsync.2.1 hr_g hrcv).1
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₀ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
        hbody hlazy hprobe_run hinv₀ (fun t ht tL htL => ?_) hih
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hres (deliverForgeHook Pt ℓ)),
          (resyncC_some_of_receive_none Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v
            sC₀ sent false hrel_sh hsync.2.1 hr_g hrcv).2]
    | some v_out =>
      rcases v_out with ⟨st', t', i', m_out⟩
      have hr_m₀ : sC₀.base.mir.inTransit Q.other w = some r_m :=
        (updAmbSimStateC_fields Pt b sC).2.2.2.2.1.symm ▸ hr_m
      obtain ⟨ans, b', hrun_acc, hhon_b', hstop_b', hmir_b'⟩ :=
        onAccept_true_of_inTransit_some Pt qep Q w t_v i_v pm_v.2 ci? T pq' sC₀.base hr_m₀
      rw [← hpos_eq] at hmir_b'
      let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
        some (.accepted t' i' (some m_out))
      let sC₁ := { updKeptOnRes fig fs Q c res_acc sC₀ with base := b' }
      let g₁ := g.accept Q st' r.pos
      let m₁' := m'.accept Q () r.pos
      let s_cell₁ :
          ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
        fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' r.pos
      have hprobe_run :
          (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((ans, sC₁), (g₁, false)) := by
        rw [hres (probeHook fig (qep + 1))]
        exact (resyncC_some_of_accept Pt fig fs qep 0 none Q w ci? T pq' c t_v i_v pm_v
          sC₀ sent false hrel0 hsync.2.1 hr_g hrcv ans b' hrun_acc).1
      obtain ⟨hsync₁, hfam₁, hcells₁⟩ :=
        deliver_accept_sync_and_family_step Pt P Dh encPt encT idOf lam qep Q
          (s_cell := s_cell) (res := res_acc) hsync₀ hbody.1 hbody.2 hstop₀
          hpos_ep hpos_le hpos_qep hrcv ⟨some m_out, rfl⟩ hhon_b' hstop_b' hmir_b'
      have hbody₁ : FirstNECellFamilyInvT_body qep g₁ m₁' s_cell₁ := by
        rcases hfam₁ with ⟨t, ht, tL, htL, hwin_cell⟩ | ⟨_, hcol₁, hrel₁⟩
        · exfalso
          rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
          · rw [hdoomed.cellWinPred_eq_false] at hwin_cell; cases hwin_cell
          · have hw := s_win_of_cellWinPred hwin_cell
            rw [hacc] at hw
            exact Bool.false_ne_true (hrel_sh.win_df_false.symm.trans hw)
        · exact ⟨hcol₁, hrel₁⟩
      have horig₁ : FirstNEInTransOriginInv qep sC₁.snaps g₁ s_cell₁ := by
        have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
          (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c res_acc sC₀).2.2
        rw [hsnaps₁]
        exact firstNEInTransOriginInv_accept_step qep Q st' r.pos sC₀.snaps horig₀
      have h0_eq : s_cell₁ 0 none = (s_cell 0 none).accept Q st' r.pos := by
        dsimp only [s_cell₁]
        rw [(hbody.2 0 ht0).1.win_df_false]
        rfl
      have hsync₁' : SyncInv P Dh encPt encT idOf lam qep sC₁ sent m₁' g₁ (s_cell₁ 0 none) := by
        rw [h0_eq]; exact hsync₁
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
          sC₁ sent m₁' g₁ s_cell₁ :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody₁, horig₁, hsync₁'⟩)
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₁ g g₁ ans tr sent sent m' m₁' s_cell s_cell₁
        hbody hlazy hprobe_run hinv₁ (fun t ht tL htL => ?_) hih
      rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
      · exact Or.inl hdoomed
      · right
        rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hres (deliverForgeHook Pt ℓ)),
          (resyncC_some_of_accept Pt fig fs qep t tL Q w ci? T pq' c t_v i_v pm_v
            sC₀ sent false hrel_sh hsync.2.1 hr_g hrcv ans b' hrun_acc).2,
          ← hacc]

private theorem firstNECoupledInvD_deliver_halted_fwdAnswer_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt] {ℓ : ℕ}
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (hinj : Function.Injective encT)
    (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (b : Bool) (ci? : Option ℕ) (T : PublicKey) (pq' : List (BitVec 8)) (c' : Fig8C Pt)
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g)
    (hstop : sC.base.stopped = false)
    (hinT : (sC.base.mir.inTransit Q.other w).isSome = true)
    (hc'_cases :
      (sC.base.honest.find? fun wc =>
        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2) = some c' ∨
      (g.safeInj (2 + 1) = true ∧
        (∀ wc ∈ sC.base.honest, wc.2 ≠ c') ∧
        (g.inTransit Q.other c').isSome = false ∧
        (c'.1.1 = g.epoch Q + 1 ∨
          ∀ (c_hon : Fig8C Pt) (r : CryptoGames.SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
            (w, c_hon) ∈ sC.base.honest →
            g.inTransit Q.other c_hon = some r →
            r.pos = ⟨Q.other, c'.1.1, c'.2.1⟩)))
    (hfa : ∀ {M : Type → Type} [Monad M] [LawfulMonad M] (H : Hook Pt ℓ M),
      (CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep
        (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (lFS P.C P.codec ℓ encT idOf 25000) H Q w true)).run sC =
        (CryptoGames.Ratchet.LibsignalSimC.fwdAnswerC qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
          (lFS P.C P.codec ℓ encT idOf 25000) H Q w true ci? T pq' c').run
          (updAmbSimStateC Pt b sC))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep (u u₁)
        sC₁ tr₁ sent₁ m₁' s_cell₁) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  let sC₀ := updAmbSimStateC Pt b sC
  have hsync₀ : SyncInv P Dh encPt encT idOf lam qep sC₀ sent m' g (s_cell 0 none) :=
    syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g (s_cell 0 none) hsync
  have horig₀ : FirstNEInTransOriginInv qep sC₀.snaps g s_cell :=
    (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig
  have hstop₀ : sC₀.base.stopped = false :=
    (updAmbSimStateC_fields Pt b sC).2.2.2.2.2.trans hstop
  have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, hbody, horig₀, hsync₀⟩)
  obtain ⟨r_m, hr_m⟩ := Option.isSome_iff_exists.mp hinT
  obtain ⟨c_hon, r, hhonC, hmem_hon, _, hr_g, hpos_eq, hpos_ep, hpos_le, hpos_qep, hInT⟩ :=
    inTransit_sync_of_evictedSpurHistSimInvLazy Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w
      hlazy hsync.2.2.2.2.2.2.2.1.htcur hsync.2.2.2.2.1 hr_m
  have hr_m₀ : sC₀.base.mir.inTransit Q.other w = some r_m := by
    rw [(updAmbSimStateC_fields Pt b sC).2.2.2.2.1]; exact hr_m
  have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  have hnone0 : none ∈ CryptoGames.SM.admissibleLastLeakGuesses 2 0 := by simp [CryptoGames.SM.admissibleLastLeakGuesses]
  have hrel0 : PPrimePaperRelShifted (s_cell 0 none) m' g := by
    rcases (hbody.2 0 ht0).2.2 none hnone0 with hdoomed | ⟨hrel_sh, _, _, _⟩
    · exact False.elim (nomatch hdoomed.1)
    · exact hrel_sh
  rcases hc'_cases with hhonC' | ⟨hsafe_g, hc'_not_hon, hinT_g, hc'_ep⟩
  · have hc_eq : c_hon = c' := Option.some.inj (hhonC.symm.trans hhonC')
    subst hc_eq
    have hInT₀ : (sC₀.base.honest.any fun wc =>
        decide (wc.2 = c_hon) && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = true := by
      rw [(updAmbSimStateC_fields Pt b sC).2.2.2.1, (updAmbSimStateC_fields Pt b sC).2.2.2.2.1]
      exact hInT
    cases hrcv : fig.receive (g.st Q) c_hon with
    | none =>
      have hrej_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
      have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c_hon sC₀
      have hlock := fwdAnswerC_deliver_lockstep Pt fig fs qep 0 none Q w true ci? T pq' c_hon
        sC₀ sent false hrel0 hsync.2.1 hInT₀ (some CryptoGames.SM.RecvResult.rejected) sC₀.base
        (by simpa [hr_g, hrcv] using hrej_ans)
      simp only [hr_g, hrcv, hrej_kept] at hlock
      have hprobe_run :
          (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some CryptoGames.SM.RecvResult.rejected, sC₀), (g, false)) := by
        rw [hfa (probeHook fig (qep + 1))]; exact hlock.1
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₀ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
        hbody hlazy hprobe_run hinv₀ (fun t ht tL htL => ?_) hih
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        have hlock_t := fwdAnswerC_deliver_lockstep Pt fig fs qep t tL Q w true ci? T pq' c_hon
          sC₀ sent false hrel_sh hsync.2.1 hInT₀ (some CryptoGames.SM.RecvResult.rejected) sC₀.base
          (by simpa [hr_g, hrcv] using hrej_ans)
        simp only [hr_g, hrcv, hrej_kept] at hlock_t
        rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hlock_t.2]
    | some val =>
      rcases val with ⟨st', t', i', m_out⟩
      let pm : Option (LibsignalMsgPublicPart × Plain ℓ) :=
        if r.pos ∈ g.chall then none else some m_out
      let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
        some (.accepted t' i' pm)
      obtain ⟨ans, b', hrun_ans, hhon_b', hstop_b', hmir_b'⟩ :=
        onAnswer_true_accepted_of_inTransit_some Pt qep Q w ci? T pq' t' i' pm sC₀.base hr_m₀
      rw [← hpos_eq] at hmir_b'
      let sC₁ := { updKeptOnRes fig fs Q c_hon res_acc sC₀ with base := b' }
      let g₁ := g.accept Q st' r.pos
      let m₁' := m'.accept Q () r.pos
      let s_cell₁ :
          ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
        fun t tL => if (s_cell t tL).win then s_cell t tL else (s_cell t tL).accept Q st' r.pos
      have hlock := fwdAnswerC_deliver_lockstep Pt fig fs qep 0 none Q w true ci? T pq' c_hon
        sC₀ sent false hrel0 hsync.2.1 hInT₀ ans b'
        (by simpa [hr_g, hrcv, res_acc, pm] using hrun_ans)
      simp only [hr_g, hrcv] at hlock
      have hprobe_run :
          (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((ans, sC₁), (g₁, false)) := by
        rw [hfa (probeHook fig (qep + 1))]; exact hlock.1
      obtain ⟨hsync₁, hfam₁, hcells₁⟩ :=
        deliver_accept_sync_and_family_step Pt P Dh encPt encT idOf lam qep Q
          (s_cell := s_cell) (res := res_acc) hsync₀ hbody.1 hbody.2 hstop₀
          hpos_ep hpos_le hpos_qep hrcv ⟨pm, rfl⟩ hhon_b' hstop_b' hmir_b'
      have hbody₁ : FirstNECellFamilyInvT_body qep g₁ m₁' s_cell₁ := by
        rcases hfam₁ with ⟨t, ht, tL, htL, hwin_cell⟩ | ⟨_, hcol₁, hrel₁⟩
        · exfalso
          rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
          · rw [hdoomed.cellWinPred_eq_false] at hwin_cell; cases hwin_cell
          · have hw := s_win_of_cellWinPred hwin_cell
            rw [hacc] at hw
            exact Bool.false_ne_true (hrel_sh.win_df_false.symm.trans hw)
        · exact ⟨hcol₁, hrel₁⟩
      have horig₁ : FirstNEInTransOriginInv qep sC₁.snaps g₁ s_cell₁ := by
        have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
          (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c_hon res_acc sC₀).2.2
        rw [hsnaps₁]
        exact firstNEInTransOriginInv_accept_step qep Q st' r.pos sC₀.snaps horig₀
      have h0_eq : s_cell₁ 0 none = (s_cell 0 none).accept Q st' r.pos := by
        dsimp only [s_cell₁]
        rw [(hbody.2 0 ht0).1.win_df_false]
        rfl
      have hsync₁' : SyncInv P Dh encPt encT idOf lam qep sC₁ sent m₁' g₁ (s_cell₁ 0 none) := by
        rw [h0_eq]; exact hsync₁
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
          sC₁ sent m₁' g₁ s_cell₁ :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody₁, horig₁, hsync₁'⟩)
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₁ g g₁ ans tr sent sent m' m₁' s_cell s_cell₁
        hbody hlazy hprobe_run hinv₁ (fun t ht tL htL => ?_) hih
      rcases hcells₁ t ht tL htL with hdoomed | ⟨hrel_sh, hacc⟩
      · exact Or.inl hdoomed
      · right
        have hlock_t := fwdAnswerC_deliver_lockstep Pt fig fs qep t tL Q w true ci? T pq' c_hon
          sC₀ sent false hrel_sh hsync.2.1 hInT₀ ans b'
          (by simpa [hr_g, hrcv, res_acc, pm] using hrun_ans)
        simp only [hr_g, hrcv] at hlock_t
        rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hlock_t.2, ← hacc]
  · have hInT_sC₀ : (sC₀.base.honest.any fun wc =>
        decide (wc.2 = c') && (sC₀.base.mir.inTransit Q.other wc.1).isSome) = false := by
      rw [List.any_eq_false]
      intro wc hwc
      rw [(updAmbSimStateC_fields Pt b sC).2.2.2.1] at hwc
      simp [hc'_not_hon wc hwc]
    have hwin_g : g.win = false := (hbody.2 0 ht0).1.win_mir_false
    cases hrcv : fig.receive (g.st Q) c' with
    | none =>
      have hrun_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
      have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c' sC₀
      have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
          pure (some .rejected, g) := by
        rw [injectImpl_h1_run fig qep Q c' g hwin_g]
        simp [hinT_g, hsafe_g, hrcv]
      have hprobe_run :
          (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
              (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
            pure ((some CryptoGames.SM.RecvResult.rejected, sC₀), (g, false)) := by
        rw [hfa (probeHook fig (qep + 1))]
        simpa [hrej_kept] using
          probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g g false
            (some .rejected) (some .rejected) sC₀.base hInT_sC₀ hinj_g
            (by simpa [hrej_kept] using hrun_ans)
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₀ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
        hbody hlazy hprobe_run hinv₀ (fun t ht tL htL => ?_) hih
      rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
      · exact Or.inl hdoomed
      · right
        have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
            (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
          rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
          have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
            rw [hrel_sh.inTransit_eq]; exact hinT_g
          have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
            hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
          have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = none := by
            rw [congrFun hrel_sh.st_eq Q]; exact hrcv
          simp [hinT_c, hsafe_c, hrcv_c]
        have hcell_step :
            runCellStep fig qep t tL
              (CryptoGames.Ratchet.LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w true ci? T pq' c')
              sC₀ sent m' (s_cell t tL) =
            pure ((((some .rejected, sC₀), sent), m'), s_cell t tL) := by
          simpa [hrej_kept, updMirOnRes] using
            runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀ sent m'
              (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
              hInT_sC₀ hinj_c (by simpa [hrej_kept] using hrun_ans)
        rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
            (hfa (deliverForgeHook Pt ℓ)),
          hcell_step]
    | some v =>
      rcases v with ⟨st', t', i', m_out⟩
      by_cases hq : (qep + 1) + 1 < t'
      · have hrun_ans := onAnswer_rejected_run qep Q w true ci? T pq' sC₀.base
        have hrej_kept := updKeptOnRes_rejected Pt fig fs Q c' sC₀
        have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
            pure (some .rejected, g) := by
          rw [injectImpl_h1_run fig qep Q c' g hwin_g]
          simp [hinT_g, hsafe_g, hrcv, hq]
        have hprobe_run :
            (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
                (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
              pure ((some CryptoGames.SM.RecvResult.rejected, sC₀), (g, false)) := by
          rw [hfa (probeHook fig (qep + 1))]
          simpa [hrej_kept] using
            probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g g false
              (some .rejected) (some .rejected) sC₀.base hInT_sC₀ hinj_g
              (by simpa [hrej_kept] using hrun_ans)
        refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
          sC sC₀ g g (some CryptoGames.SM.RecvResult.rejected) tr sent sent m' m' s_cell s_cell
          hbody hlazy hprobe_run hinv₀ (fun t ht tL htL => ?_) hih
        rcases (hbody.2 t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
        · exact Or.inl hdoomed
        · right
          have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
              (s_cell t tL) = pure (some .rejected, s_cell t tL) := by
            rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
            have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
              rw [hrel_sh.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
              hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
            have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq]
          have hcell_step :
              runCellStep fig qep t tL
                (CryptoGames.Ratchet.LibsignalSimC.fwdAnswerC qep fig fs (deliverForgeHook Pt ℓ) Q w true ci? T pq' c')
                sC₀ sent m' (s_cell t tL) =
              pure ((((some .rejected, sC₀), sent), m'), s_cell t tL) := by
            simpa [hrej_kept, updMirOnRes] using
              runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀ sent m'
                (s_cell t tL) (s_cell t tL) (some .rejected) (some .rejected) sC₀.base
                hInT_sC₀ hinj_c (by simpa [hrej_kept] using hrun_ans)
          rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
              (hfa (deliverForgeHook Pt ℓ)),
            hcell_step]
      · have ht'_le : t' ≤ (qep + 1) + 1 := Nat.le_of_not_lt hq
        let res_acc : Option (RecvResult (LibsignalMsgPublicPart × Plain ℓ)) :=
          some (.accepted t' i' (some m_out))
        let s_cell' :
            ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
          fun t tL =>
            if (s_cell t tL).win then s_cell t tL
            else if cellTrivialT tL t (s_cell t tL) ⟨Q.other, t', i'⟩ then
              (s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩
            else if t' == t then { s_cell t tL with win := true }
            else s_cell t tL
        rcases inject_step_branch_cases fig qep Q c' st' t' i' m_out
            (m₁' := updMirOnRes Q res_acc m') hbody.1 hbody.2 ht'_le hinT_g hsafe_g hrcv with
          ⟨t₀, ht₀, tL₀, htL₀, hrel_sh₀, htriv₀, ht_eq₀, hwin₀⟩ |
          ⟨htriv_g, hg'_eq, hinv', hcells'⟩
        · obtain ⟨ans, b', hrun_ans, _, _⟩ :=
            onAnswer_run_pure qep Q w true ci? T pq' (some .rejected)
              (updKeptOnRes fig fs Q c' (some .rejected) sC₀).base
          have hinj_c₀ : (injectImplCell fig (qep + 1) tL₀ t₀ (CryptoGames.SM.Config.auth t₀) (Q, c')).run
              (s_cell t₀ tL₀) = pure (some .rejected, { s_cell t₀ tL₀ with win := true }) := by
            rw [injectImplCell_run fig qep tL₀ t₀ Q c' (s_cell t₀ tL₀) hrel_sh₀.win_df_false]
            have hinT_c : ((s_cell t₀ tL₀).inTransit Q.other c').isSome = false := by
              rw [hrel_sh₀.inTransit_eq]; exact hinT_g
            have hsafe_c : (s_cell t₀ tL₀).safeInj (cellDelta tL₀ t₀) = true :=
              hrel_sh₀.safeInj_df_of_safeInj_mir (cellDelta_le_three tL₀ t₀) hsafe_g
            have hrcv_c : fig.receive ((s_cell t₀ tL₀).st Q) c' = some (st', t', i', m_out) := by
              rw [congrFun hrel_sh₀.st_eq Q]; exact hrcv
            simp [hinT_c, hsafe_c, hrcv_c, hq, htriv₀, ht_eq₀]
          refine deliver_halted_cell_win P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
            sC { updKeptOnRes fig fs Q c' (some .rejected) sC₀ with base := b' } g ans tr
            sent sent m' m' s_cell t₀ ht₀ tL₀ htL₀ { s_cell t₀ tL₀ with win := true } ?_ hwin₀
            fun hnotB1 hnotB2 par hinB => ?_
          · rw [runCellStep_congr_run fig qep t₀ tL₀ _ _ sC sC₀ sent m' (s_cell t₀ tL₀)
                (hfa (deliverForgeHook Pt ℓ)),
              runCellStep_fwdAnswerC_inject_of_eq fig fs qep t₀ tL₀ Q w true ci? T pq' c' sC₀
                sent m' (s_cell t₀ tL₀) { s_cell t₀ tL₀ with win := true } (some .rejected) ans b'
                hInT_sC₀ hinj_c₀ hrun_ans]
            rfl
          · have ht'_eq : t' = t₀ := beq_iff_eq.mp ht_eq₀
            have hs0_eq : s_cell t₀ tL₀ = s_cell 0 none := by
              rcases (hbody.2 t₀ ht₀).2.2 tL₀ htL₀ with hdoomed | ⟨_, _, _, hcomp₀⟩
              · exfalso
                exact Bool.false_ne_true (hrel_sh₀.win_df_false.symm.trans hdoomed.2.2.2)
              · exact (hcomp₀.eq_of_not_B1_not_B2 hnotB1 hnotB2).trans (hbody.1 t₀ ht₀ 0 ht0)
            have hep_c' : c'.1.1 = t₀ :=
              (lFig8_receive_spec Pt P Dh encPt encT idOf lam hrcv).2.1.symm.trans ht'_eq
            have hinT₀ : ((s_cell 0 none).inTransit Q.other c').isSome = false := by
              rw [hrel0.inTransit_eq]; exact hinT_g
            have hsafe₀ : (s_cell 0 none).safeInj (2 + 1) = true :=
              hrel0.safeInj_df_of_safeInj_mir (by omega) hsafe_g
            have hrcv₀ : fig.receive ((s_cell 0 none).st Q) c' = some (st', t₀, i', m_out) := by
              rw [congrFun hrel0.st_eq Q, ← ht'_eq]; exact hrcv
            have htriv₀' : (s_cell 0 none).trivial (2 + 1) ⟨Q.other, t₀, i'⟩ = false := by
              have h := htriv₀
              rw [cellTrivialT_of_not_B1 hnotB1, hs0_eq, ht'_eq] at h
              exact h
            refine ⟨({ s_cell 0 none with win := true }, some t₀), ?_, ?_⟩
            · rw [bucketSimRunTrackHalted_bind]
              exact (congrArg (· >>= _)
                (bucketSimRunTrackHalted_fwdAnswerC_win P K Dh encPt encT decT idOf lam qep tL₀ par
                  true Q w ci? T pq' c' st' t₀ i' m_out sC sC₀ tr sent m' (s_cell 0 none) ans b'
                  (hfa (deliverForgeHook Pt ℓ)) hInT_sC₀ hrel0.win_df_false hinT₀ hsafe₀ hrcv₀
                  (ht'_eq ▸ hq) htriv₀' hinB hep_c' hrun_ans)).trans (pure_bind _ _)
            · unfold bucketWinPred; dsimp only
              have hw_eq : cellWinPred tL₀ t₀ { s_cell 0 none with win := true } = true :=
                hs0_eq ▸ hwin₀
              unfold cellWinPred at hw_eq
              simp only [hnotB1, ↓reduceIte] at hw_eq
              exact hw_eq
        · have hpos_lt : (⟨Q.other, t', i'⟩ : CryptoGames.SM.Pos).epoch < min (g.epoch .A) (g.epoch .B) :=
            pos_epoch_lt_min_of_trivial hsync.2.2.1 hsafe_g htriv_g
          have hlt_Q : t' < g.epoch Q := by
            change (⟨Q.other, t', i'⟩ : CryptoGames.SM.Pos).epoch < g.epoch Q
            cases Q <;> omega
          have hrcv_spec :=
            lFig8_receive_spec Pt P Dh encPt encT idOf lam hrcv
          have ht'_eq_c' : t' = c'.1.1 := hrcv_spec.2.1
          have hi'_eq_c' : i' = c'.2.1 := by
            have htcur_Q := hsync.2.2.2.2.2.2.2.1.htcur Q
            rcases hrcv_spec.2.2.2 with ⟨hnew, _⟩ | ⟨_, _, _, _, v₀, v', _, hfs⟩
            · omega
            · dsimp only [lFS, CryptoGames.FSAEAD.fromAEADPRG] at hfs
              cases hlk : v₀.skippedKeys.lookup c'.2.1 with
              | some key =>
                rw [hlk] at hfs
                simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hfs
                rcases hfs with ⟨_, _, _, rfl, _⟩
                rfl
              | none =>
                rw [hlk] at hfs
                dsimp only at hfs
                split_ifs at hfs
                simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hfs
                rcases hfs with ⟨_, _, _, rfl, _⟩
                rfl
          have hpos_c' : (⟨Q.other, t', i'⟩ : CryptoGames.SM.Pos) = r.pos := by
            rcases hc'_ep with hep_succ | hfn
            · omega
            · rw [ht'_eq_c', hi'_eq_c', (hfn c_hon r hmem_hon hr_g).symm]
          have hr_m_kept :
              (updKeptOnRes fig fs Q c' res_acc sC₀).base.mir.inTransit Q.other w = some r_m :=
            hr_m₀
          obtain ⟨ans, b', hrun_ans, hhon_b', hstop_b', hmir_b'⟩ :=
            onAnswer_true_accepted_of_inTransit_some Pt qep Q w ci? T pq' t' i' (some m_out)
              (updKeptOnRes fig fs Q c' res_acc sC₀).base hr_m_kept
          dsimp only [updKeptOnRes] at hhon_b' hstop_b' hmir_b'
          rw [← hpos_eq, ← hpos_c'] at hmir_b'
          have hinj_g : (CryptoGames.SM.injectImpl fig (2 + 1) (qep + 1) CryptoGames.SM.Config.h1 (Q, c')).run g =
              pure (res_acc, g.accept Q st' ⟨Q.other, t', i'⟩) := by
            rw [injectImpl_h1_run fig qep Q c' g hwin_g]
            simp [hinT_g, hsafe_g, hrcv, hq, htriv_g, res_acc]
          let sC₁ := { updKeptOnRes fig fs Q c' res_acc sC₀ with base := b' }
          have hprobe_run :
              (((CryptoGames.Ratchet.LibsignalSimC.guardC (CryptoGames.Ratchet.LibsignalSimC.simRecvC P encT decT qep fig fs
                  (probeHook fig (qep + 1)) Q w true)).run sC).run (g, false)) =
                pure ((ans, sC₁), (g.accept Q st' ⟨Q.other, t', i'⟩, false)) := by
            rw [hfa (probeHook fig (qep + 1))]
            exact probeHook_fwdAnswerC_inject_run_of_eq fig fs qep Q w true ci? T pq' c' sC₀ g
              (g.accept Q st' ⟨Q.other, t', i'⟩) false res_acc ans b' hInT_sC₀ hinj_g hrun_ans
          rw [hg'_eq] at hinv' hcells'
          have hinvD' : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
              sC₁ sent (updMirOnRes Q res_acc m') (g.accept Q st' ⟨Q.other, t', i'⟩) s_cell' := by
            rcases hinv' with ⟨t, ht, tL, htL, hwin_cell⟩ | ⟨_, hcol', hrel_all'⟩
            · exfalso
              rcases hcells' t ht tL htL with hdoomed' | ⟨hrel_sh, _, hs_eq⟩
              · rw [hdoomed'.cellWinPred_eq_false] at hwin_cell; cases hwin_cell
              · have hw := s_win_of_cellWinPred hwin_cell
                dsimp only [s_cell'] at hs_eq hw; rw [hs_eq] at hw
                simp only [CryptoGames.SM.GameState.accept, CryptoGames.SM.GameState.delete,
                  hrel_sh.win_df_false, Bool.false_eq_true] at hw
            · refine Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol', hrel_all'⟩, ?_, ?_⟩)
              · have hsnaps₁ : sC₁.snaps = sC₀.snaps :=
                  (updKeptOnRes_base_sent_snaps_eq Pt fig fs Q c' res_acc sC₀).2.2
                rw [hsnaps₁]
                exact hg'_eq ▸ firstNEInTransOriginInv_inject_step qep Q st' t' i' sC₀.snaps horig₀
              · have hsync' := syncInv_inject_accept_step P Dh encPt encT idOf lam qep Q hsync₀
                  hstop₀ hsafe_g htriv_g hrcv hhon_b' hstop_b' hmir_b'
                rcases hcells' 0 ht0 none (Finset.mem_insert_self none _) with
                  hdoomed0 | ⟨_, _, hs0_eq⟩
                · have hw0 := hdoomed0.2.2.2
                  rw [(hrel_all' 0 ht0).1.win_df_false] at hw0; nomatch hw0
                · dsimp only [updMirOnRes, res_acc, s_cell'] at hs0_eq ⊢
                  rwa [hs0_eq]
          refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
            sC sC₁ g (g.accept Q st' ⟨Q.other, t', i'⟩) ans tr sent sent m'
            (updMirOnRes Q res_acc m') s_cell s_cell'
            hbody hlazy hprobe_run hinvD' (fun t ht tL htL => ?_) hih
          rcases hcells' t ht tL htL with hdoomed' | ⟨hrel_sh, htriv_sh, hs_eq⟩
          · exact Or.inl hdoomed'
          · right
            dsimp only [s_cell'] at hs_eq ⊢
            rw [hs_eq]
            have hinj_c : (injectImplCell fig (qep + 1) tL t (CryptoGames.SM.Config.auth t) (Q, c')).run
                (s_cell t tL) = pure (res_acc, (s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) := by
              rw [injectImplCell_run fig qep tL t Q c' (s_cell t tL) hrel_sh.win_df_false]
              have hinT_c : ((s_cell t tL).inTransit Q.other c').isSome = false := by
                rw [hrel_sh.inTransit_eq]; exact hinT_g
              have hsafe_c : (s_cell t tL).safeInj (cellDelta tL t) = true :=
                hrel_sh.safeInj_df_of_safeInj_mir (cellDelta_le_three tL t) hsafe_g
              have hrcv_c : fig.receive ((s_cell t tL).st Q) c' = some (st', t', i', m_out) := by
                rw [congrFun hrel_sh.st_eq Q]; exact hrcv
              simp [hinT_c, hsafe_c, hrcv_c, hq, htriv_sh, res_acc]
            rw [runCellStep_congr_run fig qep t tL _ _ sC sC₀ sent m' (s_cell t tL)
                (hfa (deliverForgeHook Pt ℓ)),
              runCellStep_fwdAnswerC_inject_of_eq fig fs qep t tL Q w true ci? T pq' c' sC₀
                sent m' (s_cell t tL) ((s_cell t tL).accept Q st' ⟨Q.other, t', i'⟩) res_acc ans b'
                hInT_sC₀ hinj_c hrun_ans]

theorem firstNECoupledInvD_deliver_halted_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (hspqr_eq : P.spqr = spqrV1SessionUniformCoins P.C.F K)
    (InvPQ : ℕ → List (BitVec 8) → Prop)
    (hInv_top : ∀ n pq, InvPQ n pq → TopState P.C.F K pq)
    (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (hDh : Dh.Commutes)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (hid : idOf .A = P.idA ∧ idOf .B = P.idB)
    (hX : X25519RealizesDh P.C Dh encPt encT)
    (hinj : Function.Injective encT) (hdec : ∀ T, decT (encT T) = some T)
    (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
      OracleComp (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ :
        ℕ → Option ℕ → CryptoGames.SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure z.2.2.1.2.1] {true} ≤
      stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep (u u₁)
        sC₁ tr₁ sent₁ m₁' s_cell₁) :
    𝒟[(simulateQ (firstNEHalted' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure z.2.2.1.2.1] {true} ≤
    stage2CellBucketSumRunTrackHalted P K ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + CryptoGames.SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC tr sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let fs := lFS P.C P.codec ℓ encT idOf 25000
  by_cases hlazy : ∃ r_idx w_rem,
      EvictedSpurHistSimInvLazy P K InvPQ ℓ Dh encPt encT idOf lam qep q r_idx w_rem sC g
  · rcases guardC_simRecvC_true_lazy_cases Pt P K hspqr_eq InvPQ hInv_top Dh encPt encT decT idOf
        hid hinj hdec lam qep q Q w sC g hlazy with
      ⟨ans, b, hpure⟩ |
      ⟨b, c', hrcv_none, hprobe⟩ |
      ⟨hstop, hinT, b, T, pq', c', hsafe_g, hc'_not_hon, hinT_g, hc'_ep, hfa⟩ |
      ⟨hstop, hinT, b, ci?, T, pq', c, c', hhonC, hsame, hfwd⟩
    · let sC₁ := updAmbSimStateC Pt b sC
      have hpure_probe := probeStep_of_guardC_pure Pt P encT decT qep fig fs Q w true
        sC sC₁ g false ans (hpure (probeHook fig (qep + 1)))
      have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₁ sent m' g
          s_cell :=
        Or.inr (Or.inr ⟨rfl, rfl, hbody, (updAmbSimStateC_fields Pt b sC).2.2.1.symm ▸ horig,
          syncInv_updAmbSimStateC Pt P Dh encPt encT idOf lam qep b sC sent m' g
            (s_cell 0 none) hsync⟩)
      refine deliver_halted_pure_lockstep P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u
        sC sC₁ g g ans tr sent sent m' m' s_cell s_cell
        hbody hlazy hpure_probe hinv₁ (fun t _ tL _ => Or.inr ?_) hih
      exact runCellStep_guardC_pure Pt P encT decT qep t tL fig fs Q w true sC sC₁ sent m'
        (s_cell t tL) ans (hpure (deliverForgeHook Pt ℓ))
    · exact firstNECoupledInvD_deliver_halted_probe_none_step P K InvPQ Dh encPt encT decT idOf lam
        qep q Q w b c' u sC g tr sent m' s_cell hbody horig hsync hlazy hrcv_none hprobe hih
    · exact firstNECoupledInvD_deliver_halted_fwdAnswer_step P K InvPQ Dh encPt encT decT hinj idOf
        lam qep q Q w b none T pq' c' u sC g tr sent m' s_cell hbody horig hsync hlazy hstop hinT
        (Or.inr ⟨hsafe_g, hc'_not_hon, hinT_g, Or.inl hc'_ep⟩) hfa hih
    · let honestC := (sC.base.honest.find? fun wc =>
        wc.1 == w && CryptoGames.Party.senderOf wc.2.1.1 == Q.other).map (·.2)
      rcases fwdC_true_cases Pt P qep fig fs Q w ci? T pq' honestC c' (updAmbSimStateC Pt b sC) with
        ⟨c₀, hhonC₀, hne₀, _, _, hprobe⟩ |
        ⟨c₀, v, hhonC₀, _, _, _, hres⟩ |
        ⟨hfa_cond, hfa⟩
      · cases hrcv : fig.receive (g.st Q) c' with
        | none =>
          exact firstNECoupledInvD_deliver_halted_probe_none_step P K InvPQ Dh encPt encT decT idOf
            lam qep q Q w b c' u sC g tr sent m' s_cell hbody horig hsync hlazy hrcv
            (fun H => (hfwd H).trans (hprobe H)) hih
        | some _ =>
          have hrcv_some : (fig.receive (g.st Q) c').isSome = true := by rw [hrcv]; rfl
          have hc_eq : c = c₀ := Option.some.inj (hhonC.symm.trans hhonC₀)
          subst hc_eq
          exact firstNECoupledInvD_deliver_halted_probe_lazy_step P K hspqr_eq InvPQ hInv_top Dh
            hDh encPt encT decT idOf hid hX hinj hdec lam qep q Q w b c' u sC g tr sent m' s_cell
            hbody horig hsync hlazy hinT hrcv_some
            (fun c_hon hhon_eq => by
              have h := Option.some.inj (hhonC.symm.trans hhon_eq)
              subst h; exact ⟨hsame, hne₀⟩)
            (fun H => (hfwd H).trans (hprobe H))
      · exact firstNECoupledInvD_deliver_halted_resync_step P K InvPQ Dh encPt encT decT hinj idOf
          lam qep q Q w b ci? T pq' c₀ v u sC g tr sent m' s_cell hbody horig hsync hlazy hstop
          hinT hhonC₀ (fun H => (hfwd H).trans (hres H)) hih
      · exact firstNECoupledInvD_deliver_halted_fwdAnswer_step P K InvPQ Dh encPt encT decT hinj
          idOf lam qep q Q w b ci? T pq' c' u sC g tr sent m' s_cell hbody horig hsync hlazy hstop
          hinT
          (hc'_cases_of_sameWireFig8 Pt P K InvPQ Dh encPt encT hinj idOf lam qep q Q w b c c'
            hlazy hhonC hsame hfa_cond)
          (fun H => (hfwd H).trans (hfa H)) hih
  · obtain ⟨ans, sC₁, g₁, tr', hrun⟩ :=
      firstNEHalted'_deliver_of_not_lazy P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w sC g
        tr hlazy
    rw [simulateQ_firstNEHalted'_deliver_query_bind, hrun, pure_bind,
      evalDist_firstNEHalted'_dead_eq_zero]
    exact zero_le

end Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEHaltedDeliver
