/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7 -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import Computational.Specifications.Pqxdh.Game
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic

/-!
# `transmit` Query Step for Coupled Invariant

Proves `firstNECoupledInvD_transmit_query_step_aux`, preserving `FirstNECoupledInvD` across a
`transmit` query on `firstNESimImpl'` and `cellSimRun`.-/

namespace CryptoVerification.LibsignalSession.HeadlineV1
public section

set_option autoImplicit false

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory


open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem simulateQ_firstNESimImpl'_transmit_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F) :
    (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)).run
      (sC, (g, fl, dead), tr) =
    ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r).run (sC, (g, fl), tr) >>=
      fun x =>
        (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u x.1)).run
          (x.2.1, (x.2.2.1.1, x.2.2.1.2, dead), x.2.2.2)) := by
  have hlift : ∀ {β : Type} (m : ProbComp β),
      (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ β).run (sC, (g, fl, dead), tr) =
        (m >>= fun a => pure (a, (sC, (g, fl, dead), tr))) := fun _ => rfl
  rw [simulateQ_query_bind, StateT.run_bind]
  change ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (.inr (.inl (.inl (.inl (.inl (Q, m₀, r))))))).run (sC, (g, fl, dead), tr) >>=
    fun p => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
      (u p.1)).run p.2) = _
  simp only [firstNESimImpl', StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
    hlift, bind_assoc, pure_bind]
  rfl

theorem epMgmt_corrs_st_and_epoch_le {St Msg C : Type}
    {g g₁ : SM.GameState St Msg C} {Δ qep : ℕ} {Q : Party} {bad : Bool}
    (hep : g.epMgmt Δ (qep + 1) Q bad = some g₁)
    (hle : ∀ P, g.epoch P ≤ qep + 1) :
    g₁.corrs = g.corrs ∧ g₁.st = g.st ∧ (∀ P, g₁.epoch P ≤ qep + 1) := by
  unfold SM.GameState.epMgmt SM.GameState.leak at hep
  split_ifs at hep with hs hlt hbad hlt2
  · injection hep with h
    subst h
    refine ⟨rfl, rfl, fun P => ?_⟩
    by_cases hPQ : P = Q
    · subst hPQ; simp only [Function.update_self]; omega
    · simp only [Function.update_of_ne hPQ]; exact hle P
  · injection hep with h
    subst h
    refine ⟨rfl, rfl, fun P => ?_⟩
    by_cases hPQ : P = Q
    · subst hPQ; simp only [Function.update_self]; omega
    · simp only [Function.update_of_ne hPQ]; exact hle P
  · injection hep with h
    subst h
    exact ⟨rfl, rfl, hle⟩

theorem fig8SenderSync_and_id_send_step
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m_msg : LibsignalMsgPublicPart × Plain ℓ) (coins : BitVec 256) (bad isChall : Bool)
    {g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hfig8 : Fig8SenderSync g)
    (hid : ∀ R, (g.st R).id = R)
    (hwf : SM.Thm1L17.WFState 3 g)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) Q bad = some g₁) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let st' := (fig.send (g₁.st Q) m_msg coins).1
    let c := (fig.send (g₁.st Q) m_msg coins).2
    let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, m_msg, c⟩
    let g' := g₁.record (2 + 1) Q st' rec_r isChall
    Fig8SenderSync g' ∧ (∀ R, (g'.st R).id = R) := by
  intro fig st' c rec_r g'
  obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf hep_g
  have hst_g₁ : g₁.st = g.st := by
    unfold SM.GameState.epMgmt SM.GameState.leak at hep_g
    split_ifs at hep_g <;> { injection hep_g with h; subst h; rfl }
  have hep_cases :
      (Q.sendsIn (g.epoch Q + 1) = true ∧
        g₁.epoch = Function.update g.epoch Q (g.epoch Q + 1) ∧
        g₁.idx = Function.update g.idx Q 0) ∨
      (Q.sendsIn (g.epoch Q + 1) = false ∧ g₁.epoch = g.epoch ∧ g₁.idx = g.idx) := by
    unfold SM.GameState.epMgmt SM.GameState.leak at hep_g
    by_cases hs : Q.sendsIn (g.epoch Q + 1) = true
    · simp only [hs, ↓reduceIte] at hep_g
      split_ifs at hep_g <;> { injection hep_g with h; subst h; exact Or.inl ⟨hs, rfl, rfl⟩ }
    · have hsf : Q.sendsIn (g.epoch Q + 1) = false := Bool.eq_false_iff.mpr hs
      simp only [hsf, Bool.false_eq_true, ↓reduceIte] at hep_g
      split_ifs at hep_g
      injection hep_g with h; subst h
      exact Or.inr ⟨hsf, rfl, rfl⟩
  rcases hep_cases with ⟨hs_succ, hep₁, hidx₁⟩ | ⟨hs_succ, hep₁, hidx₁⟩
  · have hs_st : (g.st Q).id.sendsIn ((g.st Q).tcur + 1) = true := by
      rw [hid Q, hfig8.htcur Q]; exact hs_succ
    have hsend_st :
        st'.id = Q ∧
        st'.tcur = g.epoch Q + 1 ∧
        st'.γ = .exp coins ∧
        (∃ v', st'.vS = some v' ∧ v'.lastIndex = 1) ∧
        st'.vR = (g.st Q).vR := by
      dsimp only [st', fig, lFig8, SM.Construction.scheme, SM.Construction.send,
        lFS, FSAEAD.fromAEADPRG, dhScheme]
      simp only [hst_g₁, hs_st, ↓reduceIte]
      cases (g.st Q).γ <;> refine ⟨hid Q, by rw [hfig8.htcur Q], rfl, ⟨_, rfl, rfl⟩, trivial⟩
    rcases hsend_st with ⟨hid', htcur', hγ', ⟨v', hvS', hlast'⟩, hvR'⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro R
      dsimp only [g', SM.GameState.record]
      rw [hep₁, hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ; simp only [Function.update_self]; exact htcur'
      · simp only [Function.update_of_ne hRQ]; exact hfig8.htcur R
    · intro R hR_sends
      dsimp only [g', SM.GameState.record, rec_r] at hR_sends ⊢
      rw [hep₁] at hR_sends
      rw [hst_g₁, hidx₁]
      by_cases hRQ : R = Q
      · subst hRQ
        simp only [Function.update_self]
        exact ⟨coins, v', hγ', hvS', hlast'⟩
      · simp only [Function.update_of_ne hRQ] at hR_sends ⊢
        exact hfig8.hvS R hR_sends
    · intro R t
      dsimp only [g', SM.GameState.record]
      rw [hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ
        simp only [Function.update_self, hvR', htcur']
        rw [hfig8.hvR R t, hfig8.htcur R]
        constructor
        · rintro ⟨hle, hns⟩; exact ⟨by omega, hns⟩
        · rintro ⟨hle, hns⟩
          refine ⟨?_, hns⟩
          rcases Nat.of_le_succ hle with hle' | rfl
          · exact hle'
          · rw [hs_succ] at hns; cases hns
      · simp only [Function.update_of_ne hRQ]
        exact hfig8.hvR R t
    · intro R
      dsimp only [g', SM.GameState.record]
      rw [hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ; simp only [Function.update_self]; exact hid'
      · simp only [Function.update_of_ne hRQ]; exact hid R
  · have hs_st : (g.st Q).id.sendsIn ((g.st Q).tcur + 1) = false := by
      rw [hid Q, hfig8.htcur Q]; exact hs_succ
    have hsends_Q : Q.sendsIn (g.epoch Q) = true := by
      rw [hep₁] at hsends₁; exact hsends₁
    rcases hfig8.hvS Q hsends_Q with ⟨x, v, hγ, hvS, hlast⟩
    have hsend_st :
        st'.id = Q ∧
        st'.tcur = g.epoch Q ∧
        st'.γ = .exp x ∧
        (∃ v', st'.vS = some v' ∧ v'.lastIndex = g.idx Q + 1) ∧
        st'.vR = (g.st Q).vR := by
      dsimp only [st', fig, lFig8, SM.Construction.scheme, SM.Construction.send,
        lFS, FSAEAD.fromAEADPRG]
      simp only [hst_g₁, hs_st, Bool.false_eq_true, ↓reduceIte, hvS]
      exact ⟨hid Q, hfig8.htcur Q, hγ, ⟨_, rfl, by dsimp only; rw [hlast]⟩, trivial⟩
    rcases hsend_st with ⟨hid', htcur', hγ', ⟨v', hvS', hlast'⟩, hvR'⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro R
      dsimp only [g', SM.GameState.record]
      rw [hep₁, hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ; simp only [Function.update_self]; exact htcur'
      · simp only [Function.update_of_ne hRQ]; exact hfig8.htcur R
    · intro R hR_sends
      dsimp only [g', SM.GameState.record, rec_r] at hR_sends ⊢
      rw [hep₁] at hR_sends
      rw [hst_g₁, hidx₁]
      by_cases hRQ : R = Q
      · subst hRQ
        simp only [Function.update_self]
        exact ⟨x, v', hγ', hvS', hlast'⟩
      · simp only [Function.update_of_ne hRQ] at hR_sends ⊢
        exact hfig8.hvS R hR_sends
    · intro R t
      dsimp only [g', SM.GameState.record]
      rw [hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ
        simp only [Function.update_self, hvR', htcur', ← hfig8.htcur R]
        exact hfig8.hvR R t
      · simp only [Function.update_of_ne hRQ]
        exact hfig8.hvR R t
    · intro R
      dsimp only [g', SM.GameState.record]
      rw [hst_g₁]
      by_cases hRQ : R = Q
      · subst hRQ; simp only [Function.update_self]; exact hid'
      · simp only [Function.update_of_ne hRQ]; exact hid R

theorem corrsKeptRecvInv_updSimStateCSend
    {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (Q : Party) (m₀ : Plain ℓ) (isChall : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : PQ) (pn : BitVec 32) (c : Fig8C Pt)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ)
    {g g' : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hkept_corr : CorrsKeptRecvInv sC g)
    (hkept : KeptInv P Dh encPt encT idOf lam sC g)
    (hcorrs_le : CorrsLeEpoch g)
    (hfig8 : Fig8SenderSync g)
    (hcorrs_eq : g'.corrs = g.corrs) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    CorrsKeptRecvInv (updSimStateCSend fig Q m₀ isChall s₁ pq' pn c sC) g' := by
  intro fig R e hmem t hle hrecv
  rw [hcorrs_eq] at hmem
  dsimp only [updSimStateCSend]
  by_cases hRQ : R = Q
  · subst hRQ
    simp only [Function.update_self]
    unfold Kept.send
    cases hfull : (sC.kept R).full with
    | none =>
      simpa [hfull] using hkept_corr R e hmem t hle hrecv
    | some st₀ =>
      dsimp only
      split_ifs with hs
      · right
        have hst₀ : st₀ = g.st R := hkept.hfull R st₀ hfull
        have he_le : e ≤ (g.st R).tcur := by
          rw [hfig8.htcur R]; exact hcorrs_le R e hmem
        rw [hst₀]
        exact (hkept.hvR R t).mpr ⟨le_trans hle he_le, hrecv⟩
      · left; rfl
  · simp only [Function.update_of_ne hRQ]
    exact hkept_corr R e hmem t hle hrecv

theorem syncInv_transmit_step
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (pub : LibsignalMsgPublicPart) (coins : BitVec 256) (bad : Bool)
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (pq' : List (BitVec 8)) (pn : BitVec 32)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (g g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hstop : sC.base.stopped = false)
    (hep : sC.base.mir.epMgmt 3 qep Q bad = some s₁)
    (hep_g : g.epMgmt (2 + 1) (qep + 1) Q bad = some g₁)
    (hrel0 : PPrimePaperRel (s_cell 0 none) m' g)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none)) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let c := (fig.send (g₁.st Q) (pub, m₀) coins).2
    let st' := (fig.send (g₁.st Q) (pub, m₀) coins).1
    let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, (pub, m₀), c⟩
    let m₁' := match m'.epMgmt (2 + 1) (qep + 1) Q false with
      | some m₁ => m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, (pub, m₀), c⟩ false
      | none => m'
    let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
      fun t tL =>
        if (s_cell t tL).win then s_cell t tL
        else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
          | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
          | none => s_cell t tL
    SyncInv P Dh encPt encT idOf lam qep
      (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
      (g₁.record (2 + 1) Q st' rec_r false) (s_cell₁ 0 none) := by
  intro fig c st' rec_r m₁' s_cell₁
  rcases hsync with ⟨hmeta_fn, hms, hwf, hcorrs_le, hep_le, hsnap_idx, hcorrs_snaps,
    hfig8, hkept_corr, hkept, hid, hhon_sent⟩
  rcases epMgmt_corrs_st_and_epoch_le hep_g hep_le with ⟨hcorrs_g₁, hst_g₁, hep_le₁⟩
  rcases fig8SenderSync_and_id_send_step P Dh encPt encT idOf lam qep Q (pub, m₀) coins bad false
    hfig8 hid hwf hep_g with ⟨hfig8', hid'⟩
  obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf hep_g
  have hwf' : SM.Thm1L17.WFState 3 (g₁.record (2 + 1) Q st' rec_r false) :=
    SM.Thm1L17.record_wf (by omega) hwf₁ rfl rfl rfl hsends₁ (by intro h; nomatch h)
  refine ⟨?_, ?_, hwf', ?_, hep_le₁, ?_, ?_, hfig8', ?_, ?_, hid', ?_⟩
  · intro _
    rcases hmeta_fn hstop with ⟨s_R, hmeta⟩
    rcases hmeta.epMgmt_some Q qep bad hep with
      ⟨s_R₁, g₁', _, hep_g', _, _, hmeta₁⟩
    have hg₁_eq : g₁' = g₁ := Option.some.inj (hep_g'.symm.trans hep_g)
    subst hg₁_eq
    refine ⟨s_R₁.record 3 Q (s_R₁.st Q)
      ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ false, ?_⟩
    have hbase_eq :
        (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC).base =
        { mir := s₁.record 3 Q ()
            ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ false,
          pq := Function.update sC.base.pq Q pq',
          pn := Function.update sC.base.pn Q pn,
          unackA := sC.base.unackA,
          honest := (LibsignalSim.toWire c, c) :: sC.base.honest,
          chains := sC.base.chains,
          amb := sC.base.amb,
          stopped := false } := by
      dsimp only [updSimStateCSend]
      rcases sC with ⟨⟨mir, pq, pn_b, unackA, honest, chains, amb, stopped⟩, kept, snaps, sent_c⟩
      dsimp only at hstop ⊢
      subst hstop
      rfl
    rw [hbase_eq]
    exact hmeta₁.record_preserves Q (s_R₁.st Q) st' m₀ m₀ (pub, m₀) c false
      (Function.update sC.base.pq Q pq') (Function.update sC.base.pn Q pn) sC.base.unackA
      ((LibsignalSim.toWire c, c) :: sC.base.honest) sC.base.chains sC.base.amb
  · obtain ⟨s_u₁, hep_u, _⟩ := hrel0.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
    obtain ⟨m₁, hep_m, hms₁⟩ := hms.epMgmt_step hrel0.epoch_eq hep_g hep_u
    have hrec_m : (⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, (pub, m₀), c⟩ :
        SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) = rec_r := by
      simp [rec_r, congrFun hms₁.epoch_eq Q, congrFun hms₁.idx_eq Q]
    have hm₁'_eq : m₁' = m₁.record (2 + 1) Q () rec_r false := by
      dsimp only [m₁']; rw [hep_m]; dsimp only; rw [hrec_m]
    have hdelta0 : cellDelta none 0 = 2 + 1 := by simp [cellDelta]
    have hcell0_eq :
        s_cell₁ 0 none = s_u₁.record (2 + 1) Q st' rec_r false := by
      dsimp only [s_cell₁]
      simp only [hrel0.win_df_false, Bool.false_eq_true, ↓reduceIte, hdelta0, hep_u]
    rw [hm₁'_eq, hcell0_eq]
    exact hms₁.record_step Q st' rec_r false
  · exact corrsLeEpoch_record_of_epMgmt st' rec_r false hcorrs_le hep_g hcorrs_g₁
  · exact corrsSnapIdxInv_record_of_epMgmt st' rec_r false hsnap_idx hcorrs_le hep_g hcorrs_g₁
      (by dsimp [rec_r]; omega)
  · exact corrsSnapsInv_of_corrs_eq hcorrs_snaps hcorrs_g₁
  · exact corrsKeptRecvInv_updSimStateCSend P Dh encPt encT idOf lam Q m₀ false s₁ pq' pn c sC
      hkept_corr hkept hcorrs_le hfig8 hcorrs_g₁
  · refine keptInv_send hkept Q (hid Q) (pub, m₀) coins ?_ rfl
    dsimp only [SM.GameState.record, st', fig]
    rw [hst_g₁]
  · exact honestSentSync_cons Pt hhon_sent c

/-- Exchanges `𝒟[p >>= lhs] {true} ≤ (∑ S₁) + (∑ S₂) + (∑ S₃, ∑ S₄)` across any `p : ProbComp β`
when the pointwise bound holds for every `b : β`. -/
theorem evalDist_bind_le_stage2_sum {β ι₁ ι₂ ι₃ ι₄ : Type}
    (S₁ : Finset ι₁) (S₂ : Finset ι₂) (S₃ : Finset ι₃) (S₄ : Finset ι₄)
    (p : ProbComp β) (lhs : β → ProbComp Bool)
    (rhs₁ : ι₁ → β → ProbComp Bool) (rhs₂ : ι₂ → β → ProbComp Bool)
    (rhs₃ : ι₃ → ι₄ → β → ProbComp Bool)
    (h : ∀ b, 𝒟[lhs b] {true} ≤
      (∑ t ∈ S₁, 𝒟[rhs₁ t b] {true}) + (∑ t ∈ S₂, 𝒟[rhs₂ t b] {true}) +
        (∑ tL ∈ S₃, ∑ par ∈ S₄, 𝒟[rhs₃ tL par b] {true})) :
    𝒟[p >>= lhs] {true} ≤
      (∑ t ∈ S₁, 𝒟[p >>= rhs₁ t] {true}) + (∑ t ∈ S₂, 𝒟[p >>= rhs₂ t] {true}) +
        (∑ tL ∈ S₃, ∑ par ∈ S₄, 𝒟[p >>= rhs₃ tL par] {true}) := by
  induction p using OracleComp.inductionOn with
  | pure b =>
    simp only [pure_bind]
    exact h b
  | query_bind n k ih =>
    simp only [bind_assoc]
    rw [evalDist_bind_of_discrete,
      Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    have hrhs :
        ((∑ t ∈ S₁, 𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>=
            fun u => k u >>= rhs₁ t] {true}) +
          (∑ t ∈ S₂, 𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>=
            fun u => k u >>= rhs₂ t] {true}) +
          (∑ tL ∈ S₃, ∑ par ∈ S₄,
            𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) >>=
              fun u => k u >>= rhs₃ tL par] {true})) =
        ∫⁻ u, ((∑ t ∈ S₁, 𝒟[k u >>= rhs₁ t] {true}) +
          (∑ t ∈ S₂, 𝒟[k u >>= rhs₂ t] {true}) +
          (∑ tL ∈ S₃, ∑ par ∈ S₄, 𝒟[k u >>= rhs₃ tL par] {true}))
          ∂(𝒟[(liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _)]) := by
      have hm1 : Measurable fun u => ∑ t ∈ S₁, 𝒟[k u >>= rhs₁ t] {true} :=
        Finset.measurable_sum _ (fun _ _ => Measurable.of_discrete)
      have hm2 : Measurable fun u => ∑ t ∈ S₂, 𝒟[k u >>= rhs₂ t] {true} :=
        Finset.measurable_sum _ (fun _ _ => Measurable.of_discrete)
      have hm3 : Measurable fun u => ∑ tL ∈ S₃, ∑ par ∈ S₄, 𝒟[k u >>= rhs₃ tL par] {true} :=
        Finset.measurable_sum _ (fun _ _ =>
          Finset.measurable_sum _ (fun _ _ => Measurable.of_discrete))
      have hm12 : Measurable fun u =>
          (∑ t ∈ S₁, 𝒟[k u >>= rhs₁ t] {true}) + (∑ t ∈ S₂, 𝒟[k u >>= rhs₂ t] {true}) :=
        hm1.add hm2
      rw [MeasureTheory.lintegral_add_left hm12, MeasureTheory.lintegral_add_left hm1,
        MeasureTheory.lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete),
        MeasureTheory.lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete),
        MeasureTheory.lintegral_finsetSum _ (fun _ _ =>
          Finset.measurable_sum _ (fun _ _ => Measurable.of_discrete))]
      congr 1
      · congr 1
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [evalDist_bind_of_discrete,
            Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
        · refine Finset.sum_congr rfl fun t _ => ?_
          rw [evalDist_bind_of_discrete,
            Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
      · refine Finset.sum_congr rfl fun tL _ => ?_
        rw [MeasureTheory.lintegral_finsetSum _ (fun _ _ => Measurable.of_discrete)]
        refine Finset.sum_congr rfl fun par _ => ?_
        rw [evalDist_bind_of_discrete,
          Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]
    rw [hrhs]
    exact MeasureTheory.lintegral_mono ih

private theorem cellSimRun_transmit_query_win_eq_false
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep t : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s₀ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin0 : s₀.win = false)
    (hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    {z : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) ×
      List (Fig8C Pt)) × Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hz : z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r))))))))
      sC sent m' s₀)) :
    z.2.win = false := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let q_tr : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (Option (List (BitVec 8))) :=
    liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))))
  have hg3_f : ((none : Option (Plain ℓ)).isSome && !s₁.safeCh 3 Q) = false := rfl
  change z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none q_tr sC sent m' s₀) at hz
  rw [← bind_pure q_tr, cellSimRun_transmit_query_bind,
    runCellStep_simSendC_of_guards_pass P qep fig t none Q m₀ none r s₁ sC sent m' s₀
      hg1_f hep hg3_f] at hz
  simp only [bind_assoc, MonadAttach.mem_support_bind] at hz
  rcases hz with ⟨rq, _, _rc, _, w, hw, hz⟩
  have hzw : z = w := by
    simpa [cellSimRun, simulateQ_pure, StateT.run_pure] using hz
  subst hzw
  split at hw
  · simp at hw
    rw [hw]; exact hwin0
  · rename_i pq' pub _
    simp only [simSendQFig, runCellStep_liftC_transmit, transmitImpl_run_eq, hwin0,
      Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind] at hw
    rcases hw with ⟨cb, _, hw⟩
    cases htp : transmitPure fig (cellDelta none t) (qep + 1) Q (pub, m₀) cb.1 cb.2 s₀ with
    | mk res s_out =>
      rw [htp] at hw
      have hw_out : s_out.win = false := by
        dsimp only [transmitPure] at htp
        cases hep_c : s₀.epMgmt (cellDelta none t) (qep + 1) Q cb.2 with
        | none => rw [hep_c] at htp; injection htp with _ hs; rw [← hs]; exact hwin0
        | some s₂ =>
          rw [hep_c] at htp
          dsimp only at htp
          injection htp with _ hs; rw [← hs]
          unfold SM.GameState.epMgmt SM.GameState.leak at hep_c
          split_ifs at hep_c <;>
            { injection hep_c with h; subst h
              simpa [SM.GameState.record] using hwin0 }
      cases res <;>
        { simp at hw; rw [hw]; exact hw_out }

/-- Auxiliary proof of `firstNECoupledInvD_transmit_query_step`. -/
theorem firstNECoupledInvD_transmit_query_step_aux {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hbody : FirstNECellFamilyInvT_body qep g m' s_cell)
    (horig : FirstNEInTransOriginInv qep sC.snaps g s_cell)
    (hsync : SyncInv P Dh encPt encT idOf lam qep sC sent m' g (s_cell 0 none))
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))))
      (sC₁ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g₁ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl₁ dead₁ : Bool) (tr₁ : KemFailTrackState P.C.F) (sent₁ : List (Fig8C Pt))
      (m₁' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl₁ dead₁ sC₁ sent₁ m₁' g₁ s_cell₁ →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) (u u₁)).run
          (sC₁, (g₁, fl₁, dead₁), tr₁) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep (u u₁) sC₁ sent₁ m₁' s_cell₁) :
    𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))) >>= u)
      sC sent m' s_cell := by
  rcases hbody with ⟨hcol, hrel_all⟩
  have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  have hwin0 : (s_cell 0 none).win = false := (hrel_all 0 ht0).1.win_df_false
  have hinv₀ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩)
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let q_tr : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (Option (List (BitVec 8))) :=
    liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inl (Q, m₀, r)))))))
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [simulateQ_firstNESimImpl'_transmit_query_bind,
      kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
        sC (g, false) tr (Or.inl hg1), pure_bind]
    refine le_trans (hih none sC g false false tr sent m' s_cell hinv₀) ?_
    refine sum_stage2_le_of_cell0_pure_step P ℓ Dh encPt encT decT idOf lam qep
      q_tr u none sC sC sent sent m' m' g s_cell s_cell hwin0 hwin0
      (fun t _ => ?_) (fun t _ tL _ => Or.inr ?_)
    · rw [← bind_pure q_tr, cellSimRun_transmit_query_bind,
        runCellStep_simSendC_of_guard_fail P qep fig t none Q m₀ none r sC sent m' (s_cell 0 none)
          (Or.inl hg1), pure_bind]
      simp [cellSimRun, simulateQ_pure, StateT.run_pure]
    · rw [cellSimRun_transmit_query_bind,
        runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ none r sC sent m' (s_cell t tL)
          (Or.inl hg1), pure_bind]
  · have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    have hstop : sC.base.stopped = false := by
      cases h : sC.base.stopped
      · rfl
      · rw [h] at hg1_f; cases hg1_f
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [simulateQ_firstNESimImpl'_transmit_query_bind,
        kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ none r
          sC (g, false) tr (Or.inr (Or.inl hep)), pure_bind]
      refine le_trans (hih none sC g false false tr sent m' s_cell hinv₀) ?_
      refine sum_stage2_le_of_cell0_pure_step P ℓ Dh encPt encT decT idOf lam qep
        q_tr u none sC sC sent sent m' m' g s_cell s_cell hwin0 hwin0
        (fun t _ => ?_) (fun t _ tL _ => Or.inr ?_)
      · rw [← bind_pure q_tr, cellSimRun_transmit_query_bind,
          runCellStep_simSendC_of_guard_fail P qep fig t none Q m₀ none r sC sent m' (s_cell 0 none)
            (Or.inr (Or.inl hep)), pure_bind]
        simp [cellSimRun, simulateQ_pure, StateT.run_pure]
      · rw [cellSimRun_transmit_query_bind,
          runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ none r sC sent m' (s_cell t tL)
            (Or.inr (Or.inl hep)), pure_bind]
    | some s₁ =>
      have hg3_f : ((none : Option (Plain ℓ)).isSome && !s₁.safeCh 3 Q) = false := rfl
      have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
      rcases hsync.1 hstop with ⟨s_R, hmeta⟩
      rcases hmeta.epMgmt_some Q qep r.isSome hep with
        ⟨_, g₁, _, hep_g, _, _, _⟩
      have hno_win0 : ∀ t ∈ Finset.range ((qep + 1) + 2),
          ∀ z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none
            q_tr sC sent m' (s_cell 0 none)), z.2.win = false :=
        fun t _ _ hz => cellSimRun_transmit_query_win_eq_false P ℓ Dh encPt encT decT idOf lam
          qep t Q m₀ r s₁ sC sent m' (s_cell 0 none) hwin0 hg1_f hep hz
      unfold stage2CellBucketSumRun
      rw [simulateQ_firstNESimImpl'_transmit_query_bind,
        kemFailSendStep_run_of_guards_pass P K Dh encPt encT decT idOf lam qep Q m₀ none r s₁
          sC g false tr hg1_f hep hg3_f, bind_assoc, bind_assoc]
      have hbuck_rw : ∀ tL par,
          bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par (q_tr >>= u) sC sent m'
            (s_cell 0 none, none) =
          (cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none q_tr sC sent m' (s_cell 0 none) >>=
            fun z => bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par
              (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 (z.2, none)) :=
        fun tL par => bucketSimRun_bind_eq_of_cell0_no_win P ℓ Dh encPt encT decT idOf lam qep
          tL par q_tr u sC sent m' (s_cell 0 none) hwin0 hno_win0
      have hcell0_rw :
          cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none q_tr sC sent m' (s_cell 0 none) =
          runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep 0 none
            (LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
              (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (deliverForgeHook Pt ℓ) Q m₀ none r))
            sC sent m' (s_cell 0 none) >>=
            fun z => cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none (pure z.1.1.1.1)
              z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
        rw [← bind_pure q_tr]
        exact cellSimRun_transmit_query_bind P ℓ Dh encPt encT decT idOf lam qep 0 none Q m₀ r pure
          sC sent m' (s_cell 0 none)
      dsimp only [q_tr] at hbuck_rw hcell0_rw
      simp only [hbuck_rw, hcell0_rw]
      simp only [cellSimRun_transmit_query_bind,
        runCellStep_simSendC_of_guards_pass P qep
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) _ _ Q m₀ none r s₁ sC sent m' _
          hg1_f hep hg3_f, bind_assoc]
      refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun rq => ?_
      cases hmk : LibsignalSim.mkPub (P := P) sC.base Q rq
          (if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
           else sC.base.pn Q) with
      | none =>
        simp only [evalDist_drawRc_bind_const, pure_bind]
        have hnone_pure :
            cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none
              (pure (none : Option (List (BitVec 8)))) sC sent m' (s_cell 0 none) =
              pure ((((none, sC), sent), m'), s_cell 0 none) := by
          simp [cellSimRun, simulateQ_pure, StateT.run_pure]
        simp only [hnone_pure, pure_bind]
        exact hih none sC g false false { tr with cand := (stepKemFailSend P.C.F K tr Q rq).cand }
          sent m' s_cell hinv₀
      | some p_pub =>
        rcases p_pub with ⟨pq', pub⟩
        dsimp only [Option.isSome]
        let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
          else sC.base.pn Q
        rw [kemFailSendStep_transmit_mkPub_some P qep fig Q m₀ r s₁ pq' pub pn sC g tr
          (stepKemFailSend P.C.F K tr Q rq) hwin_g]
        have hcell_pure : ∀ ans_out sC_out sent_out m_out s_out,
            cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none
              (pure (ans_out : Option (List (BitVec 8)))) sC_out sent_out m_out s_out =
              pure ((((ans_out, sC_out), sent_out), m_out), s_out) := by
          intro ans_out sC_out sent_out m_out s_out
          simp [cellSimRun, simulateQ_pure, StateT.run_pure]
        simp only [hcell_pure, pure_bind]
        simp only [evalDist_cell_transmit_mkPub_some P qep _ _
          (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ r s₁ pq' pub _
          sC sent m']
        refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun coins => ?_
        let c := (fig.send (g₁.st Q) (pub, m₀) coins).2
        let st' := (fig.send (g₁.st Q) (pub, m₀) coins).1
        let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
          ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, (pub, m₀), c⟩
        let m₁' := match m'.epMgmt (2 + 1) (qep + 1) Q false with
          | some m₁ => m₁.record (2 + 1) Q () ⟨⟨Q, m₁.epoch Q, m₁.idx Q + 1⟩, (pub, m₀), c⟩ false
          | none => m'
        let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
          fun t tL =>
            if (s_cell t tL).win then s_cell t tL
            else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
              | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
              | none => s_cell t tL
        have htr_g := (transmitPure_eq_of_pprimePaperRelShifted fig (2 + 1) qep Q (pub, m₀)
          coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g).1
        rw [htr_g]
        dsimp only
        have hcell_raw :=
          firstNECellFamilyInvT_transmit_step (m₁' := m₁') fig qep Q (pub, m₀) coins r.isSome
            (Or.inr ⟨rfl, hcol, hrel_all⟩) hep_g
        dsimp only at hcell_raw
        have hcell_next : FirstNECellFamilyInvT qep false (g₁.record (2 + 1) Q st' rec_r false) m₁'
            s_cell₁ := by
          convert hcell_raw using 1
          ext t tL
          dsimp only [s_cell₁, c, st', rec_r]
          split_ifs with hw
          · rfl
          · cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;> rfl
        have horig_next : FirstNEInTransOriginInv qep
            (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC).snaps
            (g₁.record (2 + 1) Q st' rec_r false) s_cell₁ :=
          firstNEInTransOriginInv_send_step_of_cellFamily qep sC.snaps Q r.isSome false
            st' (pub, m₀) c horig hrel_all hep_g hsync.2.2.2.1 hsync.2.2.2.2.2.1
        have hsync_next : SyncInv P Dh encPt encT idOf lam qep
            (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
            (g₁.record (2 + 1) Q st' rec_r false) (s_cell₁ 0 none) :=
          syncInv_transmit_step P ℓ Dh encPt encT idOf lam qep Q m₀ pub coins r.isSome s₁ pq' pn
            sC sent m' g g₁ s_cell hstop hep hep_g (hrel_all 0 ht0).1 hsync
        have hinv₁ : FirstNECoupledInvD P Dh encPt encT idOf lam qep false false
            (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
            (g₁.record (2 + 1) Q st' rec_r false) s_cell₁ := by
          rcases hcell_next with ⟨t, ht, tL, htL, hwin_c⟩ | ⟨_, hcol', hrel_all'⟩
          · exfalso
            rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
            · simp only [s_cell₁, hdoomed.2.2.2, ↓reduceIte, hdoomed.cellWinPred_eq_false] at hwin_c
              exact Bool.false_ne_true hwin_c
            · have hw_f : (s_cell₁ t tL).win = false := by
                simp only [s_cell₁, hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
                cases hep_c : (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
                | none => exact hrel_sh.win_df_false
                | some s₂ =>
                  unfold SM.GameState.epMgmt SM.GameState.leak at hep_c
                  split_ifs at hep_c <;>
                    { injection hep_c with h; subst h
                      simpa [SM.GameState.record] using hrel_sh.win_df_false }
              exact Bool.false_ne_true (hw_f.symm.trans (s_win_of_cellWinPred hwin_c))
          · exact Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol', hrel_all'⟩, horig_next, hsync_next⟩)
        refine le_trans
          (hih (some (LibsignalSim.toWire c))
            (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC)
            (g₁.record (2 + 1) Q st' rec_r false) false false
            (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₁' s_cell₁ hinv₁) ?_
        unfold stage2CellBucketSumRun
        have hcell_le : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
            𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
                (u (some (LibsignalSim.toWire c)))
                (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
                (s_cell₁ t tL) >>=
              fun z => pure (cellWinPred tL t z.2)] {true} ≤
            𝒟[cellTransmitPost fig qep Q m₀ s₁ pq' pub pn sC sent m'
                (fun z => cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u z.1.1.1.1)
                  z.1.1.1.2 z.1.1.2 z.1.2 z.2 >>= fun w => pure (cellWinPred tL t w.2))
                (if (s_cell t tL).win = true then (none, s_cell t tL)
                 else transmitPure fig (cellDelta tL t) (qep + 1) Q (pub, m₀) coins false
                   (s_cell t tL))] {true} := by
          intro t ht tL htL
          rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
          · simp only [s_cell₁, hdoomed.2.2.2, ↓reduceIte]
            have hcorrs_sub : ∀ x ∈ g.corrs, x ∈ (g₁.record (2 + 1) Q st' rec_r false).corrs := by
              unfold SM.GameState.epMgmt SM.GameState.leak at hep_g
              split_ifs at hep_g <;>
                { injection hep_g with h; subst h; intro x hx; exact hx }
            rw [evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed P ℓ Dh encPt encT decT idOf lam
              qep t tL (u (some (LibsignalSim.toWire c)))
              (updSimStateCSend fig Q m₀ false s₁ pq' pn c sC) (c :: sent) m₁'
              (hdoomed.of_corrs_sub hcorrs_sub)]
            exact zero_le
          · have htr_df := (transmitPure_eq_of_pprimePaperRelShifted fig (cellDelta tL t) qep Q
              (pub, m₀) coins r.isSome hrel_sh hep_g).2
            simp only [s_cell₁, hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            rw [htr_df]
            simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
            dsimp only [cellTransmitPost, m₁', rec_r, c, st', pn, fig]
            cases m'.epMgmt (2 + 1) (qep + 1) Q false <;>
              cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;>
              { dsimp only; exact le_rfl }
        refine add_le_add
          (add_le_add (Finset.sum_le_sum fun t ht => ?_) (Finset.sum_le_sum fun t ht => ?_))
          (Finset.sum_le_sum fun tL _ => Finset.sum_le_sum fun par _ => ?_)
        · refine hcell_le t (Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2) (some (t - 2)) ?_
          simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image,
            Finset.mem_range]
          exact Or.inr ⟨t - 2, by have := (Finset.mem_Ico.mp ht).1; omega, rfl⟩
        · refine hcell_le t (Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2) (some (t - 3)) ?_
          simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image,
            Finset.mem_range]
          exact Or.inr ⟨t - 3, by have := (Finset.mem_Ico.mp ht).1; omega, rfl⟩
        · have htr_0 := (transmitPure_eq_of_pprimePaperRelShifted fig (cellDelta none 0) qep Q
            (pub, m₀) coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g).2
          simp only [s_cell₁, hwin0, Bool.false_eq_true, ↓reduceIte]
          rw [htr_0]
          simp only [hwin0, Bool.false_eq_true, ↓reduceIte]
          dsimp only [cellTransmitPost, m₁', rec_r, c, st', pn, fig]
          cases m'.epMgmt (2 + 1) (qep + 1) Q false <;>
            cases (s_cell 0 none).epMgmt (cellDelta none 0) (qep + 1) Q false <;>
            { dsimp only; exact le_rfl }


end

end CryptoVerification.LibsignalSession.HeadlineV1
