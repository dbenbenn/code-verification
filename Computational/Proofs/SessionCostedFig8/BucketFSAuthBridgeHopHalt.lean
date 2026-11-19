/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect

/-!
# Halted/Doomed Exits & Per-Session `ActiveSessInv` Step Lemmas for `BucketFSAuthBridgeHop`

Section 4 of the `(tL, par)`-bucket FS-AEAD bridge (`N09b`):
1. Halted (`abort || win`), lookahead-win (`lfWin`), and receiver-corrupted zero-win exits.
2. Per-session active invariant `ActiveSessInv` coupling `mkRState`, `FSMultiBook`, `SyncRM`,
   and `SyncRML`, together with its step preservation lemmas for `transmit`, `corruptSender`,
   `deliver`, and `inject`.-/

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt

public section

open scoped ENNReal MeasureTheory
open OracleSpec OracleComp
open _root_.CryptoGames (PRFPRNG CKAScheme FSAEADScheme Party)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState fromAEADPRG ReceiveResult
  transmitImpl corruptSenderImpl deliverImpl injectImpl)
open _root_.CryptoGames.FSAEAD.Thm5 (HSt HState hInit hp DG transmitHWith corruptSenderH deliverH
  injectH SpecialOps)
open _root_.CryptoGames.FSAEAD.Thm5.Ends (WFSeed SyncRM SyncRML syncRML_init mkRState keyAt
  transmit_syncRM transmit_syncRML corruptSender_syncRM
  inject_syncRM_of_not_lookahead inject_syncRML_of_not_lookahead
  injectH_run_of_wfSeed_not_lookahead deliverH_run_of_wfSeed isCompromised_of_wfState_lt
  isCompromised_of_corr_lt_sent transmitH_run_of_wfSeed)
open _root_.CryptoGames.FSAEAD.Thm5On (InTransitOk inTransitOk_hInit inTransitOk_of_transmitH
  inTransitOk_of_corruptSenderH deliver_syncRM_on deliver_syncRML_on
  inTransitOk_of_injectH_not_lookahead inTransitOk_of_injectH_lookahead_none pure_eq_iff)
open _root_.CryptoGames.SM (GameState authLosingConditionsAvoided canon ltOpt)
open _root_.CryptoGames.SM.Construction (Header SchemeAdversary FSMultiSpec FSMultiBook)
open _root_.CryptoGames.SM.Engine (Hooks EState VP abortE commitE vSend deliverE injectE)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lAead lAeadR lChainPRG lIdeal lFS lPubOf)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey SignalMessageProtoCodec
  SignalRoundTripShort maxForwardJumps rustLenBound)
open _root_.CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open _root_.CryptoGames.LibsignalSM.Proofs.ProstMsgAeadCorrect (lAeadR_correctOn_short_proof
  lPubOf_enc_short_proof)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs (LocalBucketAuthState
  hooksLocalBucketAuth hooksLocalBucketAuthMain implLocalBucketAuthGen)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase (FSMultiBucketAuthState
  implFSMultiBucketAuth)
open Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopShallow (LeOne leOne_bind
  lFS_initSender_eq lFS_initReceiver_eq lFS_send_eq lFS_receive_eq
  injectL_lookahead_some_accepted)

/-! ### 1. Halted (`abort || win`), Lookahead-Win (`lfWin`), and Receiver-Corr Exits -/

theorem authLosingConditionsAvoided_congr {St₁ St₂ Msg C : Type} (Δ : ℕ) (tLStar : Option ℕ) (tStar : ℕ)
    (g₁ : GameState St₁ Msg C) (g₂ : GameState St₂ Msg C)
    (hleaks : g₁.leaks = g₂.leaks) (hcorrs : g₁.corrs = g₂.corrs) :
    authLosingConditionsAvoided Δ tLStar tStar g₁ = authLosingConditionsAvoided Δ tLStar tStar g₂ := by
  simp [authLosingConditionsAvoided, canon, hleaks, hcorrs]

@[expose] def mainParOut {St Msg C HS : Type} (Δ : ℕ) (tL : Option ℕ) (par : Bool)
    (es : EState St Msg C HS) (winEp : Option ℕ) : Bool :=
  match winEp with
  | none => false
  | some tWin => !es.abort && es.g.win && authLosingConditionsAvoided Δ tL tWin es.g &&
      (decide (Party.senderOf tWin == Party.A) == par)

theorem halted_leOne {Γ T Sig SS RS M E CCoins K I σM : Type} [DecidableEq T] [DecidableEq M]
    [DecidableEq E] [Inhabited E]
    (hkLoc : Hooks _root_.CryptoGames.SM.Construction.AuthL11.nilSpec
      (LocalBucketAuthState T Sig K I) Γ T Sig SS RS M E CCoins Γ Sig SS RS)
    (hkM : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T Sig K I E)
      Γ T Sig SS RS M E CCoins Γ Sig (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ) (par : Bool)
    (implM : QueryImpl (unifSpec + FSMultiSpec SS RS T M E) (StateT σM ProbComp))
    (hImplM_inl : ∀ (n : ℕ) (s : σM), (implM (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esLoc : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
    (esM : EState (VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T Sig K I E))
    (winEp : Option ℕ) (sM : σM)
    (hhalt : (esLoc.abort || esLoc.g.win) = true)
    (habort : esM.abort = esLoc.abort)
    (hwin : esM.g.win = esLoc.g.win)
    (hleaks : esM.g.leaks = esLoc.g.leaks)
    (hcorrs : esM.g.corrs = esLoc.g.corrs) :
    LeOne
      (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
        let (_, es, we) ← (simulateQ (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false) oa).run
          (esLoc, winEp)
        return mainParOut (2 + Δcka) tL par es we)
      (Prod.fst <$> (simulateQ implM do
        let (_, es, we) ← (simulateQ (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL) oa).run
          (esM, winEp)
        return mainParOut (2 + Δcka) tL par es we).run sM) := by
  have hhaltM : (esM.abort || esM.g.win) = true := by rw [habort, hwin]; exact hhalt
  induction oa using OracleComp.inductionOn generalizing sM with
  | pure _ =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, map_pure, LeOne]
    have hout : mainParOut (2 + Δcka) tL par esLoc winEp = mainParOut (2 + Δcka) tL par esM winEp := by
      cases winEp with
      | none => rfl
      | some tWin =>
        dsimp only [mainParOut]
        rw [habort, hwin, authLosingConditionsAvoided_congr (2 + Δcka) tL tWin esLoc.g esM.g
          hleaks.symm hcorrs.symm]
    rw [hout]
  | query_bind q k ih =>
    have hhalt' := (Bool.or_eq_true _ _).mp hhalt
    have hhaltM' := (Bool.or_eq_true _ _).mp hhaltM
    rw [simulateQ_query_bind, simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false (.inl n)).run (esLoc, winEp) =
          (liftM (OracleSpec.query (spec := unifSpec + _root_.CryptoGames.SM.Construction.AuthL11.nilSpec) (.inl n)) >>=
            fun u => pure (u, (esLoc, winEp))) := by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inl]
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL (.inl n)).run (esM, winEp) =
          (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)) >>=
            fun u => pure (u, (esM, winEp))) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
      rw [hL, hM, simulateQ_query_bind, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        _root_.CryptoGames.SM.Construction.AuthL11.lImpl, QueryImpl.add_apply_inl,
        QueryImpl.ofLift_apply,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, hImplM_inl, bind_assoc, pure_bind]
      exact leOne_bind (liftM (OracleSpec.query (spec := unifSpec) n)) fun u _ => ih u sM
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) := by
        simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hhalt']
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esM, winEp) = pure (none, (esM, winEp)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, hhaltM']
      rw [hL, hM]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false
          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) := by
        simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esM, winEp) = pure (none, (esM, winEp)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      rw [hL, hM]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false
          (.inr (.inl (.inl (.inr (P, c)))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) := by
        simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hhalt']
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inr (P, c)))))).run (esM, winEp) = pure (none, (esM, winEp)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, hhaltM']
      rw [hL, hM]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · have hnotNewLoc : (!esLoc.g.win && esLoc.g.win) = false := by cases esLoc.g.win <;> rfl
      have hnotNewM : (!esM.g.win && esM.g.win) = false := by cases esM.g.win <;> rfl
      have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false
          (.inr (.inl (.inr (P, c))))).run (esLoc, winEp) = pure (none, (esLoc, winEp)) := by
        simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hhalt']
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL
          (.inr (.inl (.inr (P, c))))).run (esM, winEp) = pure (none, (esM, winEp)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, hhaltM']
      rw [hL, hM]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM
    · have hL : (implLocalBucketAuthGen hkLoc Δcka qep maxSkip tL false (.inr (.inr P))).run (esLoc, winEp) =
          pure (none, (esLoc, winEp)) := by simp [implLocalBucketAuthGen, QueryImpl.add_apply_inr, hhalt']
      have hM : (implFSMultiBucketAuth hkM Δcka qep maxSkip true tL (.inr (.inr P))).run (esM, winEp) =
          pure (none, (esM, winEp)) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, hhaltM']
      rw [hL, hM]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none sM

theorem lfWin_aborted_eq_one
    {Γ T Sig SS RS M E CCoins K I σL : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hkL : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T Sig K I E)
      Γ T Sig SS RS M E CCoins Γ Sig (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (tL : Option ℕ)
    (implL : QueryImpl (unifSpec + FSMultiSpec SS RS T M E) (StateT σL ProbComp))
    (hImplL_inl : ∀ (n : ℕ) (s : σL), (implL (.inl n)).run s =
      ((liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>= fun u => pure (u, s)))
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esL : EState (VP Γ T Sig (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T Sig K I E))
    (winEpL : Option ℕ) (sL : σL) (habort : esL.abort = true) (hlf : esL.h.lfWin = true) :
    𝒟[Prod.fst <$> (simulateQ implL do
        let (_, es, _) ← (simulateQ (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL) oa).run
          (esL, winEpL)
        return es.h.lfWin).run sL] {true} = 1 := by
  induction oa using OracleComp.inductionOn generalizing winEpL sL with
  | pure _ => simp [simulateQ_pure, StateT.run_pure, hlf]
  | query_bind q k ih =>
    rw [simulateQ_query_bind]
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift]
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, StateT.run_bind, map_bind]
    rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL (.inl n)).run (esL, winEpL) =
          (liftM (OracleSpec.query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)) >>=
            fun u => pure (u, (esL, winEpL))) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inl]
      rw [hStep, simulateQ_query_bind]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, hImplL_inl, bind_assoc, pure_bind]
      rw [evalDist_bind_of_discrete, MeasureTheory.Measure.bind_apply MeasurableSet.of_discrete
        Measurable.of_discrete.aemeasurable]
      trans ∫⁻ (_ : Fin (n + 1)), (1 : ℝ≥0∞) ∂𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1)))]
      · exact MeasureTheory.lintegral_congr fun u => ih u winEpL sL
      · rw [MeasureTheory.lintegral_const, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inl (.inl (P, m, r))))))).run (esL, winEpL) = pure (none, (esL, winEpL)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, habort]
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inl (.inr (P, m₀, m₁, r))))))).run (esL, winEpL) = pure (none, (esL, winEpL)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL
          (.inr (.inl (.inl (.inr (P, c)))))).run (esL, winEpL) = pure (none, (esL, winEpL)) := by
        simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, deliverE, habort]
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL
    · have hStep : ∃ we', (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL
          (.inr (.inl (.inr (P, c))))).run (esL, winEpL) = pure (none, (esL, we')) :=
        ⟨if !esL.g.win && esL.g.win then some c.1.1 else winEpL, by
          simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, injectE, habort]⟩
      rcases hStep with ⟨we', hStep⟩
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none we' sL
    · have hStep : (implFSMultiBucketAuth hkL Δcka qep maxSkip true tL (.inr (.inr P))).run (esL, winEpL) =
          pure (none, (esL, winEpL)) := by simp [implFSMultiBucketAuth, QueryImpl.add_apply_inr, habort]
      rw [hStep]; simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact ih none winEpL sL

theorem corrs_sub_epMgmt {St Msg C : Type} (s s₁ : GameState St Msg C) (Δ qep : ℕ)
    (P : Party) (bad : Bool) (h : s.epMgmt Δ qep P bad = some s₁) :
    ∀ pe ∈ s.corrs, pe ∈ s₁.corrs := by
  intro pe hpe
  unfold GameState.epMgmt GameState.leak at h
  split at h
  · split at h
    · cases h
    · cases h; split <;> exact hpe
  · split at h
    · cases h
    · cases h; exact hpe

theorem cLoc_zero_of_receiver_corr
    {KC KR Γ T Sig SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (P_bad : Party) (ep_bad : ℕ)
    (oa : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (esLoc : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
    (hmem : (P_bad, ep_bad) ∈ esLoc.g.corrs)
    (hlt : ltOpt tL ep_bad = true)
    (hrecv : ∀ tWin : ℕ, (decide (Party.senderOf tWin == Party.A) == par) = true →
      P_bad = Party.receiverOf tWin)
    (winEp : Option ℕ)
    (hwe : winEp = none) :
    𝒟[simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
        let (_, es, we) ← (simulateQ (implLocalBucketAuthGen
          (hooksLocalBucketAuthMain cka prng fs Δcka qep tL) Δcka qep fs.maxSkip tL false) oa).run
          (esLoc, winEp)
        return mainParOut (2 + Δcka) tL par es we] {true} = 0 := by
  subst hwe
  suffices hgen : ∀ (oa' : SchemeAdversary Γ T Sig SS RS M CCoins E)
      (es0 : EState (VP Γ T Sig SS RS) M (Header T × E) (LocalBucketAuthState T Sig K I))
      (we0 : Option ℕ),
      (P_bad, ep_bad) ∈ es0.g.corrs →
      true ∉ support (simulateQ _root_.CryptoGames.SM.Construction.AuthL11.lImpl do
        let (_, es, we) ← (simulateQ (implLocalBucketAuthGen
          (hooksLocalBucketAuthMain cka prng fs Δcka qep tL) Δcka qep fs.maxSkip tL false) oa').run
          (es0, we0)
        return mainParOut (2 + Δcka) tL par es we) by
    have hnot := hgen oa esLoc none hmem
    rw [← bind_pure (simulateQ _ _)]
    exact _root_.CryptoGames.SM.Construction.AuthL11.evalDist_bind_eq_zero _ pure fun b hb => by
      cases b
      · simp
      · exact False.elim (hnot hb)
  intro oa'
  induction oa' using OracleComp.inductionOn with
  | pure _ =>
    intro es0 we0 hmem0 hsup
    simp only [simulateQ_pure, StateT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff] at hsup
    unfold mainParOut at hsup
    cases we0 with
    | none => exact Bool.false_ne_true hsup.symm
    | some tWin =>
      by_cases hpar : (decide (Party.senderOf tWin == Party.A) == par) = true
      · have hP := hrecv tWin hpar
        have hall_false :
            es0.g.corrs.all (fun pe => !(pe.1 == Party.receiverOf tWin && ltOpt tL pe.2)) = false := by
          rw [List.all_eq_false]
          exact ⟨(P_bad, ep_bad), hmem0, by simp [hP, hlt]⟩
        simp only [authLosingConditionsAvoided, hall_false, Bool.and_false, Bool.false_and] at hsup
        exact Bool.false_ne_true hsup.symm
      · simp only [Bool.eq_false_iff.mpr hpar, Bool.and_false] at hsup
        exact Bool.false_ne_true hsup.symm
  | query_bind q k ih =>
    intro es0 we0 hmem0 hsup
    rw [simulateQ_query_bind] at hsup
    dsimp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, liftM, monadLift] at hsup
    rw [StateT.run_bind, bind_assoc, simulateQ_bind, mem_support_bind_iff] at hsup
    rcases hsup with ⟨⟨out, es1, we1⟩, hstep, hu⟩
    have hmem1 : (P_bad, ep_bad) ∈ es1.g.corrs := by
      rcases q with n | ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P)
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inl] at hstep
        simp only [StateT.run_lift,
          simulateQ_bind, simulateQ_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hstep
        rcases hstep with ⟨_, _, hpair⟩
        rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, _⟩; exact hmem0
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hstep
        rw [StateT.run_bind, StateT.run_get, pure_bind] at hstep
        cases hg : es0.abort || es0.g.win
        · simp only [hg, Bool.false_eq_true, ↓reduceIte] at hstep
          cases hep : es0.g.epMgmt (2 + Δcka) qep P r.isSome with
          | none =>
            simp only [hep, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep
            rcases Prod.mk.inj (Prod.mk.inj hstep).2 with ⟨rfl, _⟩; exact hmem0
          | some s₁ =>
            simp only [hep, StateT.run_lift, StateT.run_bind,
              bind_assoc, pure_bind, simulateQ_bind, mem_support_bind_iff] at hstep
            rcases hstep with ⟨⟨res, h'⟩, _, hstep2⟩
            cases res <;>
              simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
                simulateQ_pure, support_pure, Set.mem_singleton_iff, GameState.record] at hstep2 <;>
              rcases Prod.mk.inj (Prod.mk.inj hstep2).2 with ⟨rfl, _⟩
            · exact hmem0
            · exact corrs_sub_epMgmt es0.g s₁ (2 + Δcka) qep P r.isSome hep _ hmem0
        · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep
          rcases Prod.mk.inj (Prod.mk.inj hstep).2 with ⟨rfl, _⟩; exact hmem0
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hstep
        simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep
        rcases Prod.mk.inj (Prod.mk.inj hstep).2 with ⟨rfl, _⟩; exact hmem0
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hstep
        simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hstep
        rcases hstep with ⟨⟨_, es'⟩, hstep1, hpair⟩
        rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, _⟩
        dsimp only [deliverE] at hstep1; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hstep1
        split at hstep1
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep1
          rcases Prod.mk.inj hstep1 with ⟨_, rfl⟩; exact hmem0
        · split at hstep1
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep1
            rcases Prod.mk.inj hstep1 with ⟨_, rfl⟩; exact hmem0
          · simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hstep1
            rcases hstep1 with ⟨⟨vout, es_mid⟩, hv, hstep2⟩
            have hg_mid : es_mid.g = es0.g := by
              dsimp only [CryptoGames.SM.Engine.liftH, StateT.run] at hv
              simp only [simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
                support_pure, Set.mem_singleton_iff] at hv
              rcases hv with ⟨⟨_, _⟩, _, hv_eq⟩; rcases Prod.mk.inj hv_eq with ⟨_, rfl⟩; rfl
            rcases vout with _ | (_ | ⟨st', t', i', m'⟩) <;> dsimp only at hstep2
            · simp [abortE, modify, modifyGet, MonadStateOf.modifyGet, StateT.run] at hstep2
              rcases hstep2 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
            · dsimp only [StateT.run] at hstep2
              split at hstep2
              · simp [modify, modifyGet, MonadStateOf.modifyGet] at hstep2
                rcases hstep2 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
              · simp at hstep2; rcases hstep2 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
            · simp [commitE, hooksLocalBucketAuthMain, hooksLocalBucketAuth, modify, modifyGet,
                MonadStateOf.modifyGet, StateT.run] at hstep2
              rcases hstep2 with ⟨_, rfl⟩
              split <;> { dsimp only [CryptoGames.SM.GameState.accept]; exact hmem0 }
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl] at hstep
        simp only [StateT.run_lift, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
          bind_assoc, pure_bind, simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at hstep
        rcases hstep with ⟨⟨_, es'⟩, hstep1, hpair⟩
        rcases Prod.mk.inj (Prod.mk.inj hpair).2 with ⟨rfl, _⟩
        dsimp only [injectE] at hstep1; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hstep1
        split at hstep1
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep1
          rcases Prod.mk.inj hstep1 with ⟨_, rfl⟩; exact hmem0
        · simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at hstep1
          rcases hstep1 with ⟨⟨rv, es_mid⟩, hv, hstep3⟩
          have hg_mid : es_mid.g = es0.g := by
            dsimp only [CryptoGames.SM.Engine.liftH, StateT.run] at hv
            simp only [simulateQ_bind, simulateQ_pure, mem_support_bind_iff,
              support_pure, Set.mem_singleton_iff] at hv
            rcases hv with ⟨⟨_, _⟩, _, hv_eq⟩; rcases Prod.mk.inj hv_eq with ⟨_, rfl⟩; rfl
          rcases rv with _ | (_ | ⟨st', t', i', m'⟩) <;> dsimp only at hstep3
          · simp [abortE, modify, modifyGet, MonadStateOf.modifyGet, StateT.run] at hstep3
            rcases hstep3 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
          · simp [StateT.run] at hstep3; rcases hstep3 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
          · by_cases hq : qep + 1 < t'
            · simp [hq, StateT.run] at hstep3; rcases hstep3 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
            · simp only [hq, ↓reduceIte] at hstep3
              by_cases htriv : es0.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
              · simp [htriv, commitE, hooksLocalBucketAuthMain, hooksLocalBucketAuth, modify,
                  modifyGet, MonadStateOf.modifyGet, StateT.run] at hstep3
                rcases hstep3 with ⟨_, rfl⟩
                dsimp only [CryptoGames.SM.GameState.accept]; exact hmem0
              · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hstep3
                dsimp only [StateT.run] at hstep3
                split at hstep3
                · simp [modify, modifyGet, MonadStateOf.modifyGet] at hstep3
                  rcases hstep3 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
                · simp at hstep3; rcases hstep3 with ⟨_, rfl⟩; simp [hg_mid, hmem0]
      · dsimp only [implLocalBucketAuthGen, QueryImpl.add_apply_inr] at hstep
        rw [StateT.run_bind, StateT.run_get, pure_bind] at hstep
        cases hg : es0.abort || es0.g.win || !(es0.g.corrAllowed P)
        · simp only [hg, Bool.false_eq_true, ↓reduceIte, hooksLocalBucketAuthMain,
            hooksLocalBucketAuth, StateT.run_lift, StateT.run_bind, StateT.run_set, StateT.run_pure,
            pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep
          rcases Prod.mk.inj (Prod.mk.inj hstep).2 with ⟨rfl, _⟩
          exact List.mem_cons_of_mem _ hmem0
        · simp only [hg, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hstep
          rcases Prod.mk.inj (Prod.mk.inj hstep).2 with ⟨rfl, _⟩; exact hmem0
    exact ih out es1 we1 hmem1 hu

/-! ### 2. Per-Session Active Invariant `ActiveSessInv` & Step Preservation -/

abbrev SessHSt (Pt : Type) (ℓ : ℕ) :=
  HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
    (Plain ℓ) LibsignalCiphertextWithSalt32

abbrev SessRState (Pt : Type) (ℓ : ℕ) :=
  _root_.CryptoGames.FSAEAD.State
    (RatchetSenderState (BitVec 256))
    (RatchetReceiverState (BitVec 256) (BitVec 256))
    (Header Pt × LibsignalMsgPublicPart)
    (Plain ℓ)
    (ℕ × LibsignalCiphertextWithSalt32)

structure ActiveSessInvAt {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (phase1 : Bool) (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32))
    (sM sL : SessHSt Pt ℓ) (stR : SessRState Pt ℓ) : Prop where
  syncRM : SyncRM (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) k stR sM
  syncRML : phase1 = true →
    SyncRML (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) k stR sM sL
  ss_eq : ssLoc = stR.senderState
  rs_eq : rsLoc = stR.receiverState
  not_ended : sM.1.ended = false
  chal_nil : sM.1.challengesInTransit = []
  ok_inTransit : InTransitOk (fun hp : Header Pt × LibsignalMsgPublicPart => hp.2.shortB) sM.1
  pub_inTransit : ∀ r ∈ sM.1.inTransit, lPubOf protoSignalCodec r.ct.2 = some r.ad.2
  bk_count : bk.fsCount = sM.1.lastSentIdx
  bk_corr : bk.sCorr = sM.1.senderCorruptedAt.isSome
  bk_trans : bk.fsTrans = sM.1.inTransit.map (fun r => (r.idx, r.ad.1, r.ct))

@[expose] def ActiveSessInv {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (phase1 : Bool) (k : BitVec 256) (ssLoc : RatchetSenderState (BitVec 256))
    (rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256))
    (bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32))
    (sM sL : SessHSt Pt ℓ) : Prop :=
  ∃ stR, ActiveSessInvAt C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL stR

theorem activeSessInv_init {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (phase1 : Bool) (k : BitVec 256) (b : Bool) :
    ActiveSessInv C ℓ encT idOf phase1 k
      ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initSender k)
      ((lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).initReceiver k)
      {} (hInit b (.seed k)) (hInit b (.seed k)) := by
  have hsync := syncRML_init (AD := Header Pt × LibsignalMsgPublicPart)
    (M := Plain ℓ) (C := LibsignalCiphertextWithSalt32)
    (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps k b
  refine ⟨_, hsync.syncRM, fun _ => hsync, ?_, ?_, rfl, rfl,
    inTransitOk_hInit _ b (.seed k), ?_, rfl, rfl, rfl⟩
  · rw [lFS_initSender_eq]; rfl
  · rw [lFS_initReceiver_eq]; rfl
  · intro r hr; simp [hInit] at hr

theorem activeSessInv_to_phase2 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL sL' : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc bk sM sL) :
    ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL' :=
  let ⟨stR, h⟩ := hinv
  ⟨stR, { h with syncRML := fun hp1 => Bool.noConfusion hp1 }⟩

private theorem ct_beq_iff : ∀ (c1 c2 : ℕ × LibsignalCiphertextWithSalt32), (c1 == c2) = true ↔ c1 = c2
  | ⟨n1, s1, b1⟩, ⟨n2, s2, b2⟩ => by
    change (n1 == n2 && (s1 == s2 && b1 == b2)) = true ↔ _
    simp [Bool.and_eq_true, beq_iff_eq]

private theorem hdr_beq_iff {Pt : Type} [DecidableEq Pt] :
    ∀ (h1 h2 : Header Pt), (h1 == h2) = true ↔ h1 = h2
  | ⟨t1, o1⟩, ⟨t2, o2⟩ => by
    cases o1 <;> cases o2 <;>
      (change (t1 == t2 && _) = true ↔ _; dsimp only [BEq.beq, Option.instBEq, Option.instBEq.beq];
       simp [Bool.and_eq_true])

private theorem ct_instBEq_eq (c1 c2 : ℕ × LibsignalCiphertextWithSalt32) :
    @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32
      instBEqOfDecidableEq instBEqOfDecidableEq) c1 c2 =
    @BEq.beq _ instBEqOfDecidableEq c1 c2 := by
  rcases c1 with ⟨n1, x1⟩; rcases c2 with ⟨n2, x2⟩; simp [BEq.beq, Prod.mk.injEq]

theorem activeSessInv_matched_iff {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32) :
    bk.fsTrans.find? (fun x => x.2 == (h, e)) =
      match lPubOf protoSignalCodec e.2 with
      | none => none
      | some p =>
        (sM.1.inTransit.find? (fun r =>
          @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
          @BEq.beq _ instBEqOfDecidableEq r.ct e)).map (fun r => (r.idx, r.ad.1, r.ct)) := by
  rcases hinv with ⟨_, hinv⟩
  rw [hinv.bk_trans]
  have hmem_pub := hinv.pub_inTransit
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none =>
    revert hmem_pub
    induction sM.1.inTransit with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro hmem_pub
      have hr_pub : lPubOf protoSignalCodec r.ct.2 = some r.ad.2 := hmem_pub r List.mem_cons_self
      have hrs_pub : ∀ r' ∈ rs, lPubOf protoSignalCodec r'.ct.2 = some r'.ad.2 :=
        fun r' hr' => hmem_pub r' (List.mem_cons_of_mem _ hr')
      have hct_false : (r.ct == e) = false := by
        cases hbeq : (r.ct == e) with
        | false => rfl
        | true => rw [(ct_beq_iff r.ct e).mp hbeq, hpub] at hr_pub; cases hr_pub
      have hfalse : ((r.ad.1, r.ct) == (h, e)) = false := by
        change (r.ad.1 == h && r.ct == e) = false; rw [hct_false, Bool.and_false]
      simp only [List.map_cons, List.find?_cons, hfalse]; exact ih hrs_pub
  | some p =>
    revert hmem_pub
    induction sM.1.inTransit with
    | nil => intro _; rfl
    | cons r rs ih =>
      intro hmem_pub
      have hr_pub : lPubOf protoSignalCodec r.ct.2 = some r.ad.2 := hmem_pub r List.mem_cons_self
      have hrs_pub : ∀ r' ∈ rs, lPubOf protoSignalCodec r'.ct.2 = some r'.ad.2 :=
        fun r' hr' => hmem_pub r' (List.mem_cons_of_mem _ hr')
      have hpred : ((r.ad.1, r.ct) == (h, e)) =
          (@BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
           @BEq.beq _ instBEqOfDecidableEq r.ct e) := by
        change (r.ad.1 == h && r.ct == e) = (decide (r.ad = (h, p)) && decide (r.ct = e))
        by_cases hce : r.ct = e
        · have had_p : r.ad.2 = p := by rw [hce, hpub] at hr_pub; injection hr_pub with hp_eq; exact hp_eq.symm
          have hct_t : (r.ct == e) = true := (ct_beq_iff r.ct e).mpr hce
          rcases hr_ad : r.ad with ⟨rh, rp⟩; rw [hr_ad] at had_p; change rp = p at had_p; subst had_p
          by_cases hhe : rh = h
          · subst hhe; simp [hce]
          · simp [hhe, Bool.eq_false_iff.mpr (mt (hdr_beq_iff rh h).mp hhe), hce]
        · simp [hce, Bool.eq_false_iff.mpr (mt (ct_beq_iff r.ct e).mp hce)]
      simp only [List.map_cons, List.find?_cons, hpred]
      cases (@BEq.beq _ instBEqOfDecidableEq r.ad (h, p) && @BEq.beq _ instBEqOfDecidableEq r.ct e)
      · exact ih hrs_pub
      · rfl

theorem activeSessInv_corruptSender {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL) :
    ∃ sM',
      ((corruptSenderH (lChainPRG C.F) (hp 0 0 false) () :
        StateT (SessHSt Pt ℓ) ProbComp _)).run sM = pure (some ssLoc, sM') ∧
      ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc { bk with sCorr := true } sM' sL := by
  rcases hinv with ⟨stR, hinv⟩
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  rcases corruptSender_syncRM ae G hinv.syncRM () with ⟨u, stR', sM', hR, hM, hsync', hce'⟩
  have hok' := inTransitOk_of_corruptSenderH ae G hinv.syncRM hinv.ok_inTransit hM
  have hend_false := hinv.not_ended; have hstR_eq := hinv.syncRM.stR_eq
  let stR_upd : SessRState Pt ℓ :=
    { stR with senderCorruptedAt := some (stR.senderCorruptedAt.getD stR.lastSentIdx) }
  have hR_eval : (corruptSenderImpl () : StateT (SessRState Pt ℓ) ProbComp _).run stR =
      pure (some ssLoc, stR_upd) := by
    have hend_stR : stR.ended = false := by rw [hstR_eq]; exact hend_false
    dsimp only [stR_upd]; simp [corruptSenderImpl, CryptoGames.FSAEAD.corruptSender, hend_stR, hinv.ss_eq]
  rw [hR_eval] at hR
  rcases Prod.mk.inj (pure_eq_iff.mp hR) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
  have hstR'_mk := hsync'.stR_eq
  have hend' : sM'.1.ended = false := by
    have : stR'.ended = sM'.1.ended := by rw [hstR'_mk]; rfl
    rw [← this, hstR']; dsimp only [stR_upd]; rw [hstR_eq]; exact hend_false
  have hcorr' : sM'.1.senderCorruptedAt.isSome = true := hce'.resolve_right (by simp [hend'])
  have hinT_eq : sM'.1.inTransit = sM.1.inTransit := by
    have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
    have h2 : stR.inTransit = sM.1.inTransit := by rw [hstR_eq]; rfl
    rw [← h1, hstR']; exact h2
  have hchal_eq : sM'.1.challengesInTransit = [] := by
    have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
    have h2 : stR.challengesInTransit = sM.1.challengesInTransit := by rw [hstR_eq]; rfl
    rw [← h1, hstR']; dsimp only [stR_upd]; rw [h2, hinv.chal_nil]
  have hsent_eq : sM'.1.lastSentIdx = sM.1.lastSentIdx := by
    have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
    have h2 : stR.lastSentIdx = sM.1.lastSentIdx := by rw [hstR_eq]; rfl
    rw [← h1, hstR']; exact h2
  refine ⟨sM', hM, ⟨stR', hsync', fun h => Bool.noConfusion h,
    by rw [hinv.ss_eq, hstR'], by rw [hinv.rs_eq, hstR'], hend', hchal_eq, hok',
    by rw [hinT_eq]; exact hinv.pub_inTransit, by dsimp only; rw [hinv.bk_count, hsent_eq],
    by dsimp only; rw [hcorr'], by dsimp only; rw [hinv.bk_trans, hinT_eq]⟩⟩

theorem activeSessInv_transmit {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (pm : LibsignalMsgPublicPart × Plain ℓ) (hshort : pm.1.shortB = true) :
    let o := (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).send ssLoc h pm
    let cnt' := bk.fsCount + 1
    let bk' : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32) :=
      { bk with fsCount := cnt', fsTrans := (cnt', h, o.2) :: bk.fsTrans }
    ∃ sM' sL',
      (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
        (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 false) (DG (lChainPRG C.F))
        (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run sM = pure (some o.2, sM') ∧
      (phase1 = true →
        (transmitHWith (lIdeal C protoSignalCodec ℓ encT)
          (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) (hp 0 0 true) (DG (lChainPRG C.F))
          (none : Option (SpecialOps _ _ _ ProbComp)) ((h, pm.1), pm.2)).run sL = pure (some o.2, sL')) ∧
      ActiveSessInv C ℓ encT idOf phase1 k o.1 rsLoc bk' sM' sL' := by
  rcases hinv with ⟨stR, hinv⟩
  let ideal := lIdeal C protoSignalCodec ℓ encT
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  intro o cnt' bk'
  have ho_eq : o = (fromAEADPRG ae G maxForwardJumps).send stR.senderState (h, pm.1) pm.2 := by
    rw [← hinv.ss_eq]; exact lFS_send_eq C protoSignalCodec ℓ encT idOf maxForwardJumps ssLoc h pm
  let stR_upd : SessRState Pt ℓ :=
    { stR with senderState := o.1, lastSentIdx := stR.lastSentIdx + 1
               inTransit := ⟨stR.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ :: stR.inTransit }
  have hR_eval : (transmitImpl (fromAEADPRG ae G maxForwardJumps) ((h, pm.1), pm.2)).run stR =
      pure (some o.2, stR_upd) := by
    have hend_stR : stR.ended = false := by rw [hinv.syncRM.stR_eq]; exact hinv.not_ended
    dsimp only [stR_upd]; simp [transmitImpl, CryptoGames.FSAEAD.transmit, hend_stR, ← ho_eq]
  cases phase1 with
  | false =>
    rcases transmit_syncRM ideal ae G maxForwardJumps hinv.syncRM ((h, pm.1), pm.2) with
      ⟨u, stR', sM', hR, hM, hsync', hca, hend⟩
    rw [hR_eval] at hR; rcases Prod.mk.inj (pure_eq_iff.mp hR) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
    have hok' := inTransitOk_of_transmitH ideal ae G hinv.syncRM.wf_seed hinv.ok_inTransit hshort hM
    have hstR'_mk := hsync'.stR_eq; have hstR_mk := hinv.syncRM.stR_eq
    have hinT' : sM'.1.inTransit = ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ :: sM.1.inTransit := by
      have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
      have h2 : stR.inTransit = sM.1.inTransit := by rw [hstR_mk]; rfl
      have h3 : stR.lastSentIdx = sM.1.lastSentIdx := by rw [hstR_mk]; rfl
      rw [← h1, hstR']; dsimp only [stR_upd]; rw [h2, h3]
    have hpub_o : lPubOf protoSignalCodec o.2.2 = some pm.1 := by
      rcases hsync'.wf_state.inTransit_valid ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩
        (by rw [hinT']; simp) with ⟨_, _, hct⟩
      rw [show o.2.2 = (lAead C protoSignalCodec ℓ encT idOf).enc
        (keyAt G k (sM.1.lastSentIdx + 1 - 1)) ((sM.1.lastSentIdx + 1, h), pm.1) pm.2 from
        congrArg Prod.snd hct]
      exact lPubOf_enc_short_proof C protoSignalCodec hrt ℓ hℓ encT idOf _ _ pm.1 pm.2 hshort
    refine ⟨sM', sL, hM, fun hp1 => Bool.noConfusion hp1,
      ⟨stR', hsync', fun hp1 => Bool.noConfusion hp1, by rw [hstR'], by rw [hinv.rs_eq, hstR'],
        by rw [hend]; exact hinv.not_ended, ?_, hok', ?_, ?_,
        by dsimp only [bk']; rw [hinv.bk_corr, hca],
        by dsimp only [bk', cnt']; rw [hinT', List.map_cons, hinv.bk_trans, hinv.bk_count]⟩⟩
    · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
      have h2 : stR.challengesInTransit = sM.1.challengesInTransit := by rw [hstR_mk]; rfl
      rw [← h1, hstR']; dsimp only [stR_upd]; rw [h2, hinv.chal_nil]
    · intro r hr; rw [hinT', List.mem_cons] at hr; rcases hr with rfl | hr
      · exact hpub_o
      · exact hinv.pub_inTransit r hr
    · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
      have h2 : stR.lastSentIdx = sM.1.lastSentIdx := by rw [hstR_mk]; rfl
      dsimp only [bk', cnt']; rw [hinv.bk_count, ← h1, hstR']; dsimp only [stR_upd]; rw [h2]
  | true =>
    rcases transmit_syncRML ideal ae G maxForwardJumps (hinv.syncRML rfl) ((h, pm.1), pm.2) with
      ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
    rw [hR_eval] at hR; rcases Prod.mk.inj (pure_eq_iff.mp hR) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
    have hok' := inTransitOk_of_transmitH ideal ae G hinv.syncRM.wf_seed hinv.ok_inTransit hshort hM
    have hstR'_mk := hsyncL'.syncRM.stR_eq; have hstR_mk := hinv.syncRM.stR_eq
    have hinT' : sM'.1.inTransit = ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩ :: sM.1.inTransit := by
      have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
      have h2 : stR.inTransit = sM.1.inTransit := by rw [hstR_mk]; rfl
      have h3 : stR.lastSentIdx = sM.1.lastSentIdx := by rw [hstR_mk]; rfl
      rw [← h1, hstR']; dsimp only [stR_upd]; rw [h2, h3]
    have hpub_o : lPubOf protoSignalCodec o.2.2 = some pm.1 := by
      rcases hsyncL'.syncRM.wf_state.inTransit_valid ⟨sM.1.lastSentIdx + 1, (h, pm.1), pm.2, o.2⟩
        (by rw [hinT']; simp) with ⟨_, _, hct⟩
      rw [show o.2.2 = (lAead C protoSignalCodec ℓ encT idOf).enc
        (keyAt G k (sM.1.lastSentIdx + 1 - 1)) ((sM.1.lastSentIdx + 1, h), pm.1) pm.2 from
        congrArg Prod.snd hct]
      exact lPubOf_enc_short_proof C protoSignalCodec hrt ℓ hℓ encT idOf _ _ pm.1 pm.2 hshort
    refine ⟨sM', sL', hM, fun _ => hL,
      ⟨stR', hsyncL'.syncRM, fun _ => hsyncL', by rw [hstR'], by rw [hinv.rs_eq, hstR'],
        hsyncL'.not_ended, ?_, hok', ?_, ?_,
        by dsimp only [bk']; rw [hinv.bk_corr, (hinv.syncRML rfl).uncorr, hsyncL'.uncorr],
        by dsimp only [bk', cnt']; rw [hinT', List.map_cons, hinv.bk_trans, hinv.bk_count]⟩⟩
    · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
      have h2 : stR.challengesInTransit = sM.1.challengesInTransit := by rw [hstR_mk]; rfl
      rw [← h1, hstR']; dsimp only [stR_upd]; rw [h2, hinv.chal_nil]
    · intro r hr; rw [hinT', List.mem_cons] at hr; rcases hr with rfl | hr
      · exact hpub_o
      · exact hinv.pub_inTransit r hr
    · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
      have h2 : stR.lastSentIdx = sM.1.lastSentIdx := by rw [hstR_mk]; rfl
      dsimp only [bk', cnt']; rw [hinv.bk_count, ← h1, hstR']; dsimp only [stR_upd]; rw [h2]

theorem activeSessInv_deliver {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x) (hrt : SignalRoundTripShort protoSignalCodec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {phase1 : Bool} {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    {mEntry : ℕ × Header Pt × (ℕ × LibsignalCiphertextWithSalt32)}
    (hmatch : bk.fsTrans.find? (fun x => x.2 == (h, e)) = some mEntry) :
    ∃ p : LibsignalMsgPublicPart,
      lPubOf protoSignalCodec e.2 = some p ∧
      match (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e with
      | none =>
        ∃ sM' sL',
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sM = pure (some .rejected, sM') ∧
          (phase1 = true →
            (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
              (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
              ((h, p), e)).run sL = pure (some .rejected, sL')) ∧
          ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc bk sM' sL'
      | some (rsLoc', idxOut, pmOut) =>
        mEntry.1 = idxOut ∧
        ∃ sM' sL',
          (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
            (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
            ((h, p), e)).run sM = pure (some (.accepted idxOut (some pmOut.2)), sM') ∧
          (phase1 = true →
            (deliverH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
              (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
              ((h, p), e)).run sL = pure (some (.accepted idxOut (some pmOut.2)), sL')) ∧
          pmOut.1 = p ∧
          ActiveSessInv C ℓ encT idOf phase1 k ssLoc rsLoc'
            { bk with fsTrans := bk.fsTrans.filter (·.1 != mEntry.1) } sM' sL' := by
  let ae := lAeadR C protoSignalCodec ℓ encT idOf
  let G := lChainPRG C.F
  have hae := lAeadR_correctOn_short_proof C hD protoSignalCodec hrt ℓ hℓ encT idOf
  have hiff := activeSessInv_matched_iff C ℓ encT idOf hinv h e
  rcases hinv with ⟨stR, hinv⟩
  rw [hmatch] at hiff
  cases hpub : lPubOf protoSignalCodec e.2 with
  | none => rw [hpub] at hiff; cases hiff
  | some p =>
    refine ⟨p, rfl, ?_⟩
    rw [hpub] at hiff; dsimp only at hiff
    cases hfind : sM.1.inTransit.find? (fun r =>
        @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
        @BEq.beq _ instBEqOfDecidableEq r.ct e) with
    | none => rw [hfind] at hiff; cases hiff
    | some r =>
      rw [hfind] at hiff; dsimp only [Option.map] at hiff; injection hiff with hmEntry
      have hr_mem : r ∈ sM.1.inTransit := List.mem_of_find?_eq_some hfind
      have hr_pred := List.find?_some hfind; simp only [Bool.and_eq_true] at hr_pred
      have hr_ct : r.ct = e := of_decide_eq_true hr_pred.2
      rcases hinv.syncRM.wf_state.inTransit_valid r hr_mem with ⟨_, _, hct_valid⟩
      have hr_idx : r.idx = e.1 := (congrArg Prod.fst (hr_ct.symm.trans hct_valid)).symm
      have hfind_eq : (sM.1.inTransit.find? fun x =>
          @BEq.beq _ instBEqOfDecidableEq x.ad (h, p) &&
          @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32
            instBEqOfDecidableEq instBEqOfDecidableEq) x.ct (e.1, e.2)) = some r := by
        simp only [ct_instBEq_eq]; exact hfind
      have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
          ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
            (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
      have hstR_mk := hinv.syncRM.stR_eq
      cases phase1 with
      | false =>
        rcases deliver_syncRM_on ae G maxForwardJumps hae hinv.syncRM hinv.ok_inTransit ((h, p), e)
          with ⟨u, stR', sM', hR, hM, hsync', hok', hca, hend⟩
        have hstR'_mk := hsync'.stR_eq
        have hR_unf := hR; rw [hstR_mk] at hR_unf
        simp only [deliverImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run,
          CryptoGames.FSAEAD.deliver, mkRState, hinv.not_ended, Bool.false_eq_true, ↓reduceIte,
          hfind, hinv.chal_nil, List.contains_nil] at hR_unf
        cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
            (mkRState G k sM.1).receiverState (h, p) e with
        | none =>
          have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
              none := by rw [hstR_mk]; exact hrec
          rw [hrecv_lFS, hrec', Option.map_none]
          have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
          rw [hrec_unf] at hR_unf; dsimp only at hR_unf
          rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
          have hinT' : sM'.1.inTransit = sM.1.inTransit := by
            have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          refine ⟨sM', sL, hM, fun hp1 => Bool.noConfusion hp1,
            ⟨stR', hsync', fun hp1 => Bool.noConfusion hp1,
              by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hinv.rs_eq, hstR', hstR_mk]; rfl,
              by rw [hend]; exact hinv.not_ended, ?_, hok',
              by rw [hinT']; exact hinv.pub_inTransit, ?_,
              by rw [hinv.bk_corr, hca], by rw [hinv.bk_trans, hinT']⟩⟩
          · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
            rw [hinv.bk_count, ← h1, hstR']
        | some rim =>
          rcases rim with ⟨rs', idxOut, msgOut⟩
          have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
              some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
          rw [hrecv_lFS, hrec', Option.map_some]
          have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
          rw [hrec_unf] at hR_unf; dsimp only at hR_unf
          rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
          dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
          have hM_check := hM
          rw [deliverH_run_of_wfSeed ae G maxForwardJumps (hp 0 0 false) (DG G)
            hinv.syncRM.wf_seed hinv.syncRM.wf_state.inTransit_valid
            hinv.syncRM.wf_state.sent_le_keys (h, p) e.1 e.2] at hM_check
          simp only [hinv.not_ended, Bool.false_eq_true, ↓reduceIte, hfind_eq, hinv.chal_nil,
            List.contains_nil] at hM_check
          have hidx : e.1 = idxOut := by
            split_ifs at hM_check
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _
          have hmEntry1 : mEntry.1 = idxOut := by rw [hmEntry]; dsimp only; rw [hr_idx, hidx]
          have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != r.idx) := by
            have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          refine ⟨hmEntry1, sM', sL, hM, fun hp1 => Bool.noConfusion hp1, rfl,
            ⟨stR', hsync', fun hp1 => Bool.noConfusion hp1,
              by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hstR'],
              by rw [hend]; exact hinv.not_ended, ?_, hok', ?_, ?_,
              by dsimp only; rw [hinv.bk_corr, hca],
              by dsimp only; rw [hmEntry1, ← hidx, ← hr_idx, hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
          · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']; rfl
          · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
          · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
            dsimp only; rw [hinv.bk_count, ← h1, hstR']
      | true =>
        rcases deliver_syncRML_on ae G maxForwardJumps hae (hinv.syncRML rfl) hinv.ok_inTransit
          ((h, p), e) with ⟨u, stR', sM', sL', hR, hM, hL, hsyncL', hok'⟩
        have hstR'_mk := hsyncL'.syncRM.stR_eq
        have hR_unf := hR; rw [hstR_mk] at hR_unf
        simp only [deliverImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run,
          CryptoGames.FSAEAD.deliver, mkRState, hinv.not_ended, Bool.false_eq_true, ↓reduceIte,
          hfind, hinv.chal_nil, List.contains_nil] at hR_unf
        cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
            (mkRState G k sM.1).receiverState (h, p) e with
        | none =>
          have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
              none := by rw [hstR_mk]; exact hrec
          rw [hrecv_lFS, hrec', Option.map_none]
          have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
          rw [hrec_unf] at hR_unf; dsimp only at hR_unf
          rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
          have hinT' : sM'.1.inTransit = sM.1.inTransit := by
            have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          refine ⟨sM', sL', hM, fun _ => hL,
            ⟨stR', hsyncL'.syncRM, fun _ => hsyncL',
              by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hinv.rs_eq, hstR', hstR_mk]; rfl,
              hsyncL'.not_ended, ?_, hok', by rw [hinT']; exact hinv.pub_inTransit, ?_,
              by rw [hinv.bk_corr, (hinv.syncRML rfl).uncorr, hsyncL'.uncorr],
              by rw [hinv.bk_trans, hinT']⟩⟩
          · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
            rw [hinv.bk_count, ← h1, hstR']
        | some rim =>
          rcases rim with ⟨rs', idxOut, msgOut⟩
          have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
              some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
          rw [hrecv_lFS, hrec', Option.map_some]
          have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
          rw [hrec_unf] at hR_unf; dsimp only at hR_unf
          rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
          dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
          have hM_check := hM
          rw [deliverH_run_of_wfSeed ae G maxForwardJumps (hp 0 0 false) (DG G)
            hinv.syncRM.wf_seed hinv.syncRM.wf_state.inTransit_valid
            hinv.syncRM.wf_state.sent_le_keys (h, p) e.1 e.2] at hM_check
          simp only [hinv.not_ended, Bool.false_eq_true, ↓reduceIte, hfind_eq, hinv.chal_nil,
            List.contains_nil] at hM_check
          have hidx : e.1 = idxOut := by
            split_ifs at hM_check
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _
          have hmEntry1 : mEntry.1 = idxOut := by rw [hmEntry]; dsimp only; rw [hr_idx, hidx]
          have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != r.idx) := by
            have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']
          refine ⟨hmEntry1, sM', sL', hM, fun _ => hL, rfl,
            ⟨stR', hsyncL'.syncRM, fun _ => hsyncL',
              by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hstR'], hsyncL'.not_ended, ?_, hok',
              ?_, ?_, by dsimp only; rw [hinv.bk_corr, (hinv.syncRML rfl).uncorr, hsyncL'.uncorr],
              by dsimp only; rw [hmEntry1, ← hidx, ← hr_idx, hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
          · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
            rw [← h1, hstR']; rfl
          · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
          · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
            dsimp only; rw [hinv.bk_count, ← h1, hstR']

theorem activeSessInv_inject_phase2 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM sL)
    (hscorr : bk.sCorr = true) (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (hmatch_none : bk.fsTrans.find? (fun x => x.2 == (h, e)) = none)
    (p : LibsignalMsgPublicPart) (hpub : lPubOf protoSignalCodec e.2 = some p) :
    match (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e with
    | none =>
      ∃ sM',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some .rejected, sM') ∧
        ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc bk sM' sL
    | some (rsLoc', idxOut, pmOut) =>
      ∃ sM',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some (.accepted idxOut (some pmOut.2)), sM') ∧
        pmOut.1 = p ∧
        ActiveSessInv C ℓ encT idOf false k ssLoc rsLoc'
          { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) } sM' sL := by
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  have hiff := activeSessInv_matched_iff C ℓ encT idOf hinv h e
  rcases hinv with ⟨stR, hinv⟩; rw [hmatch_none, hpub] at hiff; dsimp only at hiff
  have hfind_none : sM.1.inTransit.find? (fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ instBEqOfDecidableEq r.ct e) = none := by
    cases hf : sM.1.inTransit.find? _ with | none => rfl | some _ => rw [hf] at hiff; cases hiff
  have hany_impl : (sM.1.inTransit.any fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ instBEqOfDecidableEq r.ct e) = false :=
    List.any_eq_false.mpr (List.find?_eq_none.mp hfind_none)
  rcases inject_syncRM_of_not_lookahead ae G maxForwardJumps hinv.syncRM ((h, p), e)
    (by intro _ _ _ _ huncorr; have := hinv.bk_corr; rw [hscorr, huncorr] at this; cases this)
    with ⟨u, stR', sM', hR, hM, hsync', hca, hend, _, _⟩
  have hok' := inTransitOk_of_injectH_not_lookahead ae G maxForwardJumps hinv.syncRM
    hinv.ok_inTransit
    (by intro _ _ _ _ huncorr; have := hinv.bk_corr; rw [hscorr, huncorr] at this; cases this) hM
  have hstR_mk := hinv.syncRM.stR_eq; have hstR'_mk := hsync'.stR_eq
  have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
      ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
        (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
  have hR_unf := hR; rw [hstR_mk] at hR_unf
  simp only [injectImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run, CryptoGames.FSAEAD.inject,
    mkRState, hinv.not_ended, hany_impl, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hR_unf
  cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
      (mkRState G k sM.1).receiverState (h, p) e with
  | none =>
    have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e = none := by
      rw [hstR_mk]; exact hrec
    rw [hrecv_lFS, hrec', Option.map_none]
    have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
    rw [hrec_unf] at hR_unf; dsimp only at hR_unf
    rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
    have hinT' : sM'.1.inTransit = sM.1.inTransit := by
      have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
      rw [← h1, hstR']
    refine ⟨sM', hM, ⟨stR', hsync', fun hp1 => Bool.noConfusion hp1,
      by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hinv.rs_eq, hstR', hstR_mk]; rfl,
      by rw [hend]; exact hinv.not_ended, ?_, hok',
      by rw [hinT']; exact hinv.pub_inTransit, ?_, by rw [hinv.bk_corr, hca],
      by rw [hinv.bk_trans, hinT']⟩⟩
    · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
      rw [← h1, hstR']; exact hinv.chal_nil
    · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
      rw [hinv.bk_count, ← h1, hstR']
  | some rim =>
    rcases rim with ⟨rs', idxOut, msgOut⟩
    have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
        some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
    rw [hrecv_lFS, hrec', Option.map_some]
    have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
    rw [hrec_unf] at hR_unf; dsimp only at hR_unf
    rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
    dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
    have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != idxOut) := by
      have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
      rw [← h1, hstR']
    refine ⟨sM', hM, rfl, ⟨stR', hsync', fun hp1 => Bool.noConfusion hp1,
      by rw [hinv.ss_eq, hstR', hstR_mk]; rfl, by rw [hstR'], by rw [hend]; exact hinv.not_ended,
      ?_, hok', ?_, ?_, by dsimp only; rw [hinv.bk_corr, hca],
      by dsimp only; rw [hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
    · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
      rw [← h1, hstR']; simp [hinv.chal_nil]
    · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
    · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
      dsimp only; rw [hinv.bk_count, ← h1, hstR']

theorem activeSessInv_inject_phase1 {Pt : Type} [DecidableEq Pt]
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    {k : BitVec 256} {ssLoc : RatchetSenderState (BitVec 256)}
    {rsLoc : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {bk : FSMultiBook Pt (ℕ × LibsignalCiphertextWithSalt32)} {sM sL : SessHSt Pt ℓ}
    (hinv : ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc bk sM sL)
    (h : Header Pt) (e : ℕ × LibsignalCiphertextWithSalt32)
    (hmatch_none : bk.fsTrans.find? (fun x => x.2 == (h, e)) = none)
    (p : LibsignalMsgPublicPart) (hpub : lPubOf protoSignalCodec e.2 = some p) :
    (∃ msg sL', bk.sCorr = false ∧ bk.fsCount < e.1 ∧
      (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
        (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
        ((h, p), e)).run sL = pure (some (.accepted e.1 (some msg)), sL')) ∨
    match (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e with
    | none =>
      ∃ sM' sL',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some .rejected, sM') ∧
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sL = pure (some .rejected, sL') ∧
        ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc bk sM' sL'
    | some (rsLoc', idxOut, pmOut) =>
      ∃ sM' sL',
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 false) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sM = pure (some (.accepted idxOut (some pmOut.2)), sM') ∧
        (injectH (lAeadR C protoSignalCodec ℓ encT idOf) (lChainPRG C.F) maxForwardJumps
          (hp 0 0 true) (DG (lChainPRG C.F)) (none : Option (SpecialOps _ _ _ ProbComp))
          ((h, p), e)).run sL = pure (some (.accepted idxOut (some pmOut.2)), sL') ∧
        (bk.sCorr = false → idxOut ≤ bk.fsCount) ∧ pmOut.1 = p ∧
        ActiveSessInv C ℓ encT idOf true k ssLoc rsLoc'
          { bk with fsTrans := bk.fsTrans.filter (·.1 != idxOut) } sM' sL' := by
  let ae := lAeadR C protoSignalCodec ℓ encT idOf; let G := lChainPRG C.F
  have hiff := activeSessInv_matched_iff C ℓ encT idOf hinv h e
  rcases hinv with ⟨stR, hinv⟩; have hsyncL := hinv.syncRML rfl
  rw [hmatch_none, hpub] at hiff; dsimp only at hiff
  have hfind_none : sM.1.inTransit.find? (fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ instBEqOfDecidableEq r.ct e) = none := by
    cases hf : sM.1.inTransit.find? _ with | none => rfl | some _ => rw [hf] at hiff; cases hiff
  have hany_impl : (sM.1.inTransit.any fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ instBEqOfDecidableEq r.ct e) = false :=
    List.any_eq_false.mpr (List.find?_eq_none.mp hfind_none)
  have hany_false : (sM.1.inTransit.any fun r =>
      @BEq.beq _ instBEqOfDecidableEq r.ad (h, p) &&
      @BEq.beq _ (@instBEqProd ℕ LibsignalCiphertextWithSalt32 instBEqOfDecidableEq instBEqOfDecidableEq)
        r.ct (e.1, e.2)) = false := by simp only [ct_instBEq_eq]; exact hany_impl
  have hbk_uncorr : bk.sCorr = false := by rw [hinv.bk_corr, hsyncL.uncorr]; rfl
  by_cases hlook_case : e.1 ∉ sM.1.skipped ∧
      ¬ (e.1 ≤ sM.1.receiverIdx ∨ maxForwardJumps < e.1 - sM.1.receiverIdx - 1) ∧
      sM.1.lastSentIdx < e.1
  · rcases hlook_case with ⟨hcont, hout, hlt⟩
    cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 with
    | some msg =>
      left
      rcases injectL_lookahead_some_accepted ae G maxForwardJumps hsyncL (h, p) e.1 e.2 msg
        hinv.not_ended hany_false hcont hout hlt hdec with ⟨sL', hL⟩
      exact ⟨msg, sL', hbk_uncorr, by rw [hinv.bk_count]; exact hlt, hL⟩
    | none =>
      right
      rcases CryptoGames.FSAEAD.Thm5.Ends.inject_syncRML_of_lookahead_none ae G maxForwardJumps
        hsyncL (h, p) e.1 e.2 hinv.not_ended hany_false hcont hout hlt hdec with
        ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
      have hok' := inTransitOk_of_injectH_lookahead_none ae G maxForwardJumps (h, p) e.1 e.2
        hinv.ok_inTransit hinv.not_ended hany_false hcont hout hlt hsyncL.uncorr hM
      have hstR_mk : stR = mkRState G k sM.1 := hinv.syncRM.stR_eq
      have hstR'_mk := hsyncL'.syncRM.stR_eq
      have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
          ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
            (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
      have hrec_none : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e = none := by
        rw [hstR_mk]
        erw [CryptoGames.FSAEAD.Thm5.Ends.receive_real_of_in_window ae G maxForwardJumps k
          sM.1.receiverIdx sM.1.skipped (h, p) e.1 e.2 hcont hout]; simp [hdec]
      rw [hrecv_lFS, hrec_none, Option.map_none]
      have hR_unf := hR; rw [hstR_mk] at hR_unf
      simp only [injectImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run, CryptoGames.FSAEAD.inject,
        mkRState, hinv.not_ended, hany_impl, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hR_unf
      have hrec_mk : (fromAEADPRG ae G maxForwardJumps).receive
          (mkRState G k sM.1).receiverState (h, p) e = none := by rw [← hstR_mk]; exact hrec_none
      dsimp only [ae, G, mkRState] at hrec_mk hR_unf; rw [hrec_mk] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit := by
        have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']
      refine ⟨sM', sL', hM, hL,
        ⟨stR', hsyncL'.syncRM, fun _ => hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
          by rw [hinv.rs_eq, hstR', hstR_mk]; rfl, hsyncL'.not_ended, ?_, hok',
          by rw [hinT']; exact hinv.pub_inTransit, ?_, by rw [hbk_uncorr, hsyncL'.uncorr]; rfl,
          by rw [hinv.bk_trans, hinT']⟩⟩
      · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']; exact hinv.chal_nil
      · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
        rw [hinv.bk_count, ← h1, hstR']
  · right
    rcases inject_syncRML_of_not_lookahead ae G maxForwardJumps hsyncL ((h, p), e)
      (by intro _ _ hc ho _; by_contra hgt; exact hlook_case ⟨hc, ho, Nat.lt_of_not_ge hgt⟩)
      with ⟨u, stR', sM', sL', hR, hM, hL, hsyncL'⟩
    have hok' := inTransitOk_of_injectH_not_lookahead ae G maxForwardJumps hinv.syncRM
      hinv.ok_inTransit
      (by intro _ _ hc ho _; by_contra hgt; exact hlook_case ⟨hc, ho, Nat.lt_of_not_ge hgt⟩) hM
    have hstR_mk : stR = mkRState G k sM.1 := hinv.syncRM.stR_eq
    have hstR'_mk := hsyncL'.syncRM.stR_eq
    have hrecv_lFS : (lFS C protoSignalCodec ℓ encT idOf maxForwardJumps).receive rsLoc h e =
        ((fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e).map
          (fun o => (o.1, o.2.1, (p, o.2.2))) := by rw [hinv.rs_eq, lFS_receive_eq, hpub]
    have hR_unf := hR; rw [hstR_mk] at hR_unf
    simp only [injectImpl, CryptoGames.FSAEAD.Thm5.Ends.modifyGet_run, CryptoGames.FSAEAD.inject,
      mkRState, hinv.not_ended, hany_impl, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hR_unf
    cases hrec : (fromAEADPRG ae G maxForwardJumps).receive
        (mkRState G k sM.1).receiverState (h, p) e with
    | none =>
      have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e = none := by
        rw [hstR_mk]; exact hrec
      rw [hrecv_lFS, hrec', Option.map_none]
      have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
      rw [hrec_unf] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit := by
        have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']
      refine ⟨sM', sL', hM, hL,
        ⟨stR', hsyncL'.syncRM, fun _ => hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
          by rw [hinv.rs_eq, hstR', hstR_mk]; rfl, hsyncL'.not_ended, ?_, hok',
          by rw [hinT']; exact hinv.pub_inTransit, ?_, by rw [hbk_uncorr, hsyncL'.uncorr]; rfl,
          by rw [hinv.bk_trans, hinT']⟩⟩
      · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']; exact hinv.chal_nil
      · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
        rw [hinv.bk_count, ← h1, hstR']
    | some rim =>
      rcases rim with ⟨rs', idxOut, msgOut⟩
      have hrec' : (fromAEADPRG ae G maxForwardJumps).receive stR.receiverState (h, p) e =
          some (rs', idxOut, msgOut) := by rw [hstR_mk]; exact hrec
      rw [hrecv_lFS, hrec', Option.map_some]
      have hrec_unf := hrec; dsimp only [ae, G, mkRState] at hrec_unf hR_unf
      rw [hrec_unf] at hR_unf; dsimp only at hR_unf
      rcases Prod.mk.inj (pure_eq_iff.mp hR_unf) with ⟨hu, hstR'⟩; subst hu; symm at hstR'
      dsimp only [CryptoGames.FSAEAD.State.removeFromTransit] at hstR'
      have hinT' : sM'.1.inTransit = sM.1.inTransit.filter (fun r' => r'.idx != idxOut) := by
        have h1 : stR'.inTransit = sM'.1.inTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']
      have hidx_le : idxOut ≤ bk.fsCount := by
        rw [hinv.bk_count]; have hM_check := hM
        have hsk_comp : ∀ j ∈ sM.1.skipped, sM.1.lastSentIdx < j → sM.1.isCompromised j = true :=
          fun j hj hlt => isCompromised_of_wfState_lt ae G hinv.syncRM.wf_state
            (le_of_lt (hinv.syncRM.wf_state.skipped_bounds j hj).2) hlt
        rw [injectH_run_of_wfSeed_not_lookahead ae G maxForwardJumps false hinv.syncRM.wf_seed
          hinv.syncRM.wf_state.skipped_bounds hinv.syncRM.wf_state.rcv_le_keys hsk_comp
          (h, p) e.1 e.2 (by intro _ _ hc ho hlt; exact False.elim (hlook_case ⟨hc, ho, hlt⟩))]
          at hM_check
        simp only [hinv.not_ended, hany_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at hM_check
        by_cases hcont : e.1 ∈ sM.1.skipped
        · simp only [hcont, ↓reduceIte] at hM_check
          cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 <;> simp only [hdec] at hM_check
          · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
          · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
            injection hacc with hacc; injection hacc with hi _; subst hi
            have hb := (hinv.syncRM.wf_state.skipped_bounds e.1 hcont).2
            have hr_le := hinv.syncRM.wf_state.rcv_le_sent_of_uncorr hsyncL.uncorr; omega
        · simp only [hcont, ↓reduceIte] at hM_check
          by_cases hout : e.1 ≤ sM.1.receiverIdx ∨ maxForwardJumps < e.1 - sM.1.receiverIdx - 1
          · simp only [hout, ↓reduceIte] at hM_check
            obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
          · simp only [hout, ↓reduceIte] at hM_check
            cases hdec : ae.dec (keyAt G k (e.1 - 1)) (e.1, (h, p)) e.2 <;> simp only [hdec] at hM_check
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check); cases hacc
            · obtain ⟨hacc, _⟩ := Prod.ext_iff.mp (pure_eq_iff.mp hM_check)
              injection hacc with hacc; injection hacc with hi _; subst hi
              by_contra hgt; exact hlook_case ⟨hcont, hout, Nat.lt_of_not_ge hgt⟩
      refine ⟨sM', sL', hM, hL, fun _ => hidx_le, rfl,
        ⟨stR', hsyncL'.syncRM, fun _ => hsyncL', by rw [hinv.ss_eq, hstR', hstR_mk]; rfl,
          by rw [hstR'], hsyncL'.not_ended, ?_, hok', ?_, ?_,
          by dsimp only; rw [hbk_uncorr, hsyncL'.uncorr]; rfl,
          by dsimp only; rw [hinT', hinv.bk_trans, List.filter_map]; rfl⟩⟩
      · have h1 : stR'.challengesInTransit = sM'.1.challengesInTransit := by rw [hstR'_mk]; rfl
        rw [← h1, hstR']; simp [hinv.chal_nil]
      · intro r' hr'; rw [hinT', List.mem_filter] at hr'; exact hinv.pub_inTransit r' hr'.1
      · have h1 : stR'.lastSentIdx = sM'.1.lastSentIdx := by rw [hstR'_mk]; rfl
        dsimp only; rw [hinv.bk_count, ← h1, hstR']

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthBridgeHopHalt
