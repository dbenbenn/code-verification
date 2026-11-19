/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple7 -- proof-setup: allow-public-import
public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECell -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Sync
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafDeliverProbe
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeafTransmit
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNELeaves1
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNEWinSplit4
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Sticky-Dead-Ghost `firstNESimImpl'` Coupling and Cell-Sum Bound

Proves per-query preservation of `FirstNECoupledInvD` across `firstNESimImpl'`, lifts it over
`simulateQ`, and bounds the probe probability by the `admissibleLastLeakGuesses 2` cell sum.-/

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
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

/-! ## Initialization and per-oracle steps -/

theorem firstNECoupledInvD_init
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (b : Bool) (k : BitVec 256 × BitVec 256) (pqrKey : BitVec 256) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
      initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
    let g₀ := SM.initState fig k b
    let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
    FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC₀ [] m'₀ g₀ (fun _ _ => g₀) := by
  intro fig sC₀ g₀ m'₀
  refine Or.inr (Or.inr ⟨rfl, rfl, ⟨fun _ _ _ _ => rfl, fun t _ =>
    ⟨pprimePaperRel_init_b fig k b, SM.Thm1L17.wfState_init fig (2 + 1) k b,
      fun tL _ => Or.inr ⟨(pprimePaperRel_init_b fig k b).toShifted,
        SM.Thm1L17.wfState_init fig (cellDelta tL t) k b,
        shiftedLeakRel_init fig (cellShift tL t) k b,
        cellCompRel_init fig tL t k b⟩⟩⟩,
    firstNEInTransOriginInv_init_b fig qep sC₀.snaps k b, ?_⟩)
  have hvR₀ : ∀ Q t, ((g₀.st Q).vR t).isSome ↔ (t ≤ (g₀.st Q).tcur ∧ Q.sendsIn t = false) := by
    intro Q t; cases Q <;> by_cases ht : t = 0 <;>
      simp [g₀, fig, SM.initState, lFig8, scheme, initParty, ht, Party.sendsIn]
  refine ⟨fun _ => ⟨SM.initState (libsignalSessionScheme P ℓ encPt lam).sendPart (k.1, k.2, 0, pqrKey) b,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩⟩,
    mirrorSync_init fig k b,
    SM.Thm1L17.wfState_init fig 3 k b,
    corrsLeEpoch_init_b fig k b,
    fun _ => Nat.zero_le _,
    corrsSnapIdxInv_init_b fig sC₀.snaps k b,
    corrsSnapsInv_init_b fig sC₀.snaps k b,
    ⟨fun Q => by cases Q <;> rfl,
     fun Q hQ => by cases Q with | A => cases hQ | B => exact ⟨k.2, _, rfl, rfl, rfl⟩,
     hvR₀⟩,
    corrsKeptRecvInv_init_b fig sC₀ k b,
    ⟨fun Q st hst => by simp [sC₀, initSimC, Kept.unknown] at hst,
     fun Q t v _ hrs => by simp [sC₀, initSimC, Kept.unknown] at hrs,
     hvR₀⟩,
    fun Q => by cases Q <;> rfl,
    honestSentSync_nil Pt⟩

theorem firstNECoupledInvD_corr_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inr Q)) →
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
        (List (BitVec 8))).Range (.inr (.inr Q)))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inr Q)) >>= u)
      sC sent m' s_cell :=
  firstNECoupledInvD_corr_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q u sC g tr
    sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_inject_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (w : List (BitVec 8))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))) →
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
        (List (BitVec 8))).Range (.inr (.inl (.inr (Q, w)))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inr (Q, w)))) >>= u)
      sC sent m' s_cell :=
  firstNECoupledInvD_inject_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q w u sC g
    tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_transmit_query_step {α : Type}
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
      sC sent m' s_cell :=
  firstNECoupledInvD_transmit_query_step_aux P K InvPQ ℓ Dh encPt encT decT idOf lam qep q Q m₀ r u
    sC g tr sent m' s_cell hbody horig hsync hih

private theorem cellSimRun_chall_query_win_eq_false
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep t : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (s₁ : SM.GameState Unit (Plain ℓ) (List (BitVec 8)))
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s₀ : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin0 : s₀.win = false)
    (hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false)
    (hep : sC.base.mir.epMgmt 3 qep Q r.isSome = some s₁)
    (hg3_f : ((some m₁).isSome && !s₁.safeCh 3 Q) = false)
    {z : (((Option (List (BitVec 8)) × LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ) ×
      List (Fig8C Pt)) × Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ×
      SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)}
    (hz : z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none
      (liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))))
      sC sent m' s₀)) :
    z.2.win = false := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let q_ch : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (Option (List (BitVec 8))) :=
    liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))))
  change z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none q_ch sC sent m' s₀) at hz
  rw [← bind_pure q_ch, cellSimRun_chall_query_bind,
    runCellStep_simSendC_of_guards_pass P qep fig t none Q m₀ (some m₁) r s₁ sC sent m' s₀
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
    simp only [simSendQFig, runCellStep_liftC_chall] at hw
    cases hm_ep : m'.epMgmt (2 + 1) (qep + 1) Q false with
    | none =>
      simp [hm_ep] at hw
      rw [hw]; exact hwin0
    | some m₁' =>
      simp only [hm_ep] at hw
      by_cases hs : (!(m₁'.safeCh (2 + 1) Q)) = true
      · simp [hs] at hw
        rw [hw]; exact hwin0
      · simp only [hs, Bool.false_eq_true, ↓reduceIte, transmitImpl_run_eq, hwin0,
          bind_assoc, pure_bind, MonadAttach.mem_support_bind] at hw
        rcases hw with ⟨cb, _, hw⟩
        cases htp : transmitPure fig (cellDelta none t) (qep + 1) Q
            (if m'.b then (pub, m₁) else (pub, m₀)) cb.1 cb.2 s₀ with
        | mk res s_out =>
          rw [htp] at hw
          have hw_out : s_out.win = false := by
            dsimp only [transmitPure] at htp
            cases hep_c : s₀.epMgmt (cellDelta none t) (qep + 1) Q cb.2 with
            | none => rw [hep_c] at htp; injection htp with _ hs_eq; rw [← hs_eq]; exact hwin0
            | some s₂ =>
              rw [hep_c] at htp
              dsimp only at htp
              injection htp with _ hs_eq; rw [← hs_eq]
              unfold SM.GameState.epMgmt SM.GameState.leak at hep_c
              split_ifs at hep_c <;>
                { injection hep_c with h; subst h
                  simpa [SM.GameState.record] using hwin0 }
          cases res <;>
            { simp at hw; rw [hw]; exact hw_out }

/-- Leaf per-oracle step lemma for `challenge (Q, m₀, m₁, r)`
(`.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))`). -/
theorem firstNECoupledInvD_chall_query_step {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (P : Params (List (BitVec 8)) (BitVec 512)) (K : MlKem)
    (InvPQ : ℕ → List (BitVec 8) → Prop) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option (BitVec 512))
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) →
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
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>=
          u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)
      sC sent m' s_cell := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let q_ch : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (Option (List (BitVec 8))) :=
    liftM (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
      (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))))
  rcases hbody with ⟨hcol, hrel_all⟩
  have ht0 : 0 ∈ Finset.range ((qep + 1) + 2) := Finset.mem_range.mpr (by omega)
  have hwin0 : (s_cell 0 none).win = false := (hrel_all 0 ht0).1.win_df_false
  have hcoupled₀ :
      FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC sent m' g s_cell :=
    Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol, hrel_all⟩, horig, hsync⟩)
  rcases hsync with ⟨hmeta_opt, hmsync, hwf_g, hcorrs_le, hep_le_qep, hsnap_idx, hcorrs_snaps,
    hsender_sync, hkept_corr, hkept, hid_st, hhon_sent⟩
  have hsim_chall :
      (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
          (BitVec 512) (List (BitVec 8)))
          (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r)))))) >>= u)).run
        (sC, (g, false, false), tr) =
      ((kemFailSendStep P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r).run
        (sC, (g, false), tr) >>=
        fun x =>
          (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
            (u x.1)).run (x.2.1, (x.2.2.1.1, x.2.2.1.2, false), x.2.2.2)) := by
    have hlift : ∀ {β : Type} (m : ProbComp β),
        (StateT.lift m : KemFailSimM' (List (BitVec 8)) Pt P.C.F ℓ β).run
          (sC, (g, false, false), tr) =
          (m >>= fun a => pure (a, (sC, (g, false, false), tr))) := fun _ => rfl
    rw [simulateQ_query_bind, StateT.run_bind]
    change ((firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
        (.inr (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))))).run
        (sC, (g, false, false), tr) >>=
      fun p => (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q)
        (u p.1)).run p.2) = _
    simp only [firstNESimImpl', kemFailSimImpl, StateT.run_bind, StateT.run_get, StateT.run_set,
      StateT.run_pure, hlift, bind_assoc, pure_bind]
    rfl
  by_cases hg1 : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = true
  · rw [hsim_chall,
      kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
        sC (g, false) tr (Or.inl hg1), pure_bind]
    refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
    refine sum_stage2_le_of_cell0_pure_step P ℓ Dh encPt encT decT idOf lam qep
      q_ch u none sC sC sent sent m' m' g s_cell s_cell hwin0 hwin0
      (fun t _ => ?_) (fun t _ tL _ => Or.inr ?_)
    · rw [← bind_pure q_ch, cellSimRun_chall_query_bind,
        runCellStep_simSendC_of_guard_fail P qep fig t none Q m₀ (some m₁) r sC sent m' (s_cell 0 none)
          (Or.inl hg1), pure_bind]
      simp [cellSimRun, simulateQ_pure, StateT.run_pure]
    · rw [cellSimRun_chall_query_bind,
        runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m' (s_cell t tL)
          (Or.inl hg1), pure_bind]
  · have hg1_f : (sC.base.stopped || sC.base.mir.win || !SM.noBobSendInEpoch0 sC.base.mir Q) = false :=
      Bool.eq_false_iff.mpr hg1
    cases hep : sC.base.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      rw [hsim_chall,
        kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
          sC (g, false) tr (Or.inr (Or.inl hep)), pure_bind]
      refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
      refine sum_stage2_le_of_cell0_pure_step P ℓ Dh encPt encT decT idOf lam qep
        q_ch u none sC sC sent sent m' m' g s_cell s_cell hwin0 hwin0
        (fun t _ => ?_) (fun t _ tL _ => Or.inr ?_)
      · rw [← bind_pure q_ch, cellSimRun_chall_query_bind,
          runCellStep_simSendC_of_guard_fail P qep fig t none Q m₀ (some m₁) r sC sent m' (s_cell 0 none)
            (Or.inr (Or.inl hep)), pure_bind]
        simp [cellSimRun, simulateQ_pure, StateT.run_pure]
      · rw [cellSimRun_chall_query_bind,
          runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m' (s_cell t tL)
            (Or.inr (Or.inl hep)), pure_bind]
    | some s₁ =>
      by_cases hg3 : ((some m₁).isSome && !s₁.safeCh 3 Q) = true
      · rw [hsim_chall,
          kemFailSendStep_run_of_guard_fail P K ℓ Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
            sC (g, false) tr (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
        refine le_trans (hih none sC g false false tr sent m' s_cell hcoupled₀) ?_
        refine sum_stage2_le_of_cell0_pure_step P ℓ Dh encPt encT decT idOf lam qep
          q_ch u none sC sC sent sent m' m' g s_cell s_cell hwin0 hwin0
          (fun t _ => ?_) (fun t _ tL _ => Or.inr ?_)
        · rw [← bind_pure q_ch, cellSimRun_chall_query_bind,
            runCellStep_simSendC_of_guard_fail P qep fig t none Q m₀ (some m₁) r sC sent m'
              (s_cell 0 none) (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
          simp [cellSimRun, simulateQ_pure, StateT.run_pure]
        · rw [cellSimRun_chall_query_bind,
            runCellStep_simSendC_of_guard_fail P qep fig t tL Q m₀ (some m₁) r sC sent m'
              (s_cell t tL) (Or.inr (Or.inr ⟨s₁, hep, hg3⟩)), pure_bind]
      · have hg3_f : ((some m₁).isSome && !s₁.safeCh 3 Q) = false := Bool.eq_false_iff.mpr hg3
        have hstop : sC.base.stopped = false := by
          cases h : sC.base.stopped
          · rfl
          · simp [h] at hg1_f
        have hsafe_s₁ : s₁.safeCh 3 Q = true := by
          simpa using hg3_f
        rcases hmeta_opt hstop with ⟨s_R, hmeta⟩
        rcases hmsync.chall_sync (hrel_all 0 ht0).1 hmeta.hepoch_fig8.symm hmeta.htL_fig8.symm
            hep hsafe_s₁ with
          ⟨g₁, m₁', hep_g, hsafe_g, hep_m, hsafe_m, hb_eq⟩
        have hwin_g : g.win = false := (hrel_all 0 ht0).1.win_mir_false
        have hno_win0 : ∀ t ∈ Finset.range ((qep + 1) + 2),
            ∀ z ∈ support (cellSimRun P ℓ Dh encPt encT decT idOf lam qep t none
              q_ch sC sent m' (s_cell 0 none)), z.2.win = false :=
          fun t _ _ hz => cellSimRun_chall_query_win_eq_false P ℓ Dh encPt encT decT idOf lam
            qep t Q m₀ m₁ r s₁ sC sent m' (s_cell 0 none) hwin0 hg1_f hep hg3_f hz
        unfold stage2CellBucketSumRun
        rw [hsim_chall,
          kemFailSendStep_run_of_guards_pass P K Dh encPt encT decT idOf lam qep Q m₀ (some m₁) r
            s₁ sC g false tr hg1_f hep hg3_f, bind_assoc, bind_assoc]
        have hbuck_rw : ∀ tL par,
            bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par (q_ch >>= u) sC sent m'
              (s_cell 0 none, none) =
            (cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none q_ch sC sent m' (s_cell 0 none) >>=
              fun z => bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par
                (u z.1.1.1.1) z.1.1.1.2 z.1.1.2 z.1.2 (z.2, none)) :=
          fun tL par => bucketSimRun_bind_eq_of_cell0_no_win P ℓ Dh encPt encT decT idOf lam qep
            tL par q_ch u sC sent m' (s_cell 0 none) hwin0 hno_win0
        have hcell0_rw :
            cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none q_ch sC sent m' (s_cell 0 none) =
            runCellStep (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) qep 0 none
              (LibsignalSimC.guardC (LibsignalSimC.simSendC P qep
                (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) (deliverForgeHook Pt ℓ) Q m₀ (some m₁) r))
              sC sent m' (s_cell 0 none) >>=
              fun z => cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none (pure z.1.1.1.1)
                z.1.1.1.2 z.1.1.2 z.1.2 z.2 := by
          rw [← bind_pure q_ch]
          exact cellSimRun_chall_query_bind P ℓ Dh encPt encT decT idOf lam qep 0 none Q m₀ m₁ r pure
            sC sent m' (s_cell 0 none)
        dsimp only [q_ch] at hbuck_rw hcell0_rw
        simp only [hbuck_rw, hcell0_rw]
        simp only [cellSimRun_chall_query_bind,
          runCellStep_simSendC_of_guards_pass P qep
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) _ _ Q m₀ (some m₁) r s₁ sC sent m' _
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
            sent m' s_cell hcoupled₀
        | some p_pub =>
          rcases p_pub with ⟨pq', pub⟩
          dsimp only [Option.isSome]
          let pn := if s₁.epoch Q ≠ sC.base.mir.epoch Q then BitVec.ofNat 32 (sC.base.mir.idx Q - 1)
            else sC.base.pn Q
          rw [kemFailSendStep_chall_mkPub_some P qep fig Q m₀ m₁ r s₁ pq' pub pn sC g tr
            (stepKemFailSend P.C.F K tr Q rq) hwin_g]
          have hcell_pure : ∀ ans_out sC_out sent_out m_out s_out,
              cellSimRun P ℓ Dh encPt encT decT idOf lam qep 0 none
                (pure (ans_out : Option (List (BitVec 8)))) sC_out sent_out m_out s_out =
                pure ((((ans_out, sC_out), sent_out), m_out), s_out) := by
            intro ans_out sC_out sent_out m_out s_out
            simp [cellSimRun, simulateQ_pure, StateT.run_pure]
          simp only [hcell_pure, pure_bind]
          simp only [evalDist_cell_chall_mkPub_some qep _ _
            (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam) Q m₀ m₁ r s₁ pq' pub _
            sC sent m' m₁' _ hep_m hsafe_m]
          refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun coins => ?_
          let m_ch := if m'.b then (pub, m₁) else (pub, m₀)
          let c := (fig.send (g₁.st Q) m_ch coins).2
          let st' := (fig.send (g₁.st Q) m_ch coins).1
          let rec_r : SM.Record (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            ⟨⟨Q, g₁.epoch Q, g₁.idx Q + 1⟩, m_ch, c⟩
          let m₂' := m₁'.record (2 + 1) Q () ⟨⟨Q, m₁'.epoch Q, m₁'.idx Q + 1⟩, m_ch, c⟩ true
          let s_cell₁ : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) :=
            fun t tL =>
              if (s_cell t tL).win then s_cell t tL
              else match (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false with
                | some s₂ => s₂.record (cellDelta tL t) Q st' rec_r false
                | none => s_cell t tL
          have hch_g := (challPure_eq_of_pprimePaperRelShifted fig (2 + 1) qep Q (pub, m₀) (pub, m₁)
            coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g hsafe_g hb_eq).1
          rw [hch_g]
          dsimp only
          let sC' := updSimStateCSend fig Q m₀ true s₁ pq' pn c sC
          let g' := g₁.record (2 + 1) Q st' rec_r true
          have hinv₁ : FirstNECellFamilyInvT qep false g' m₂' s_cell₁ := by
            refine Eq.ndrec (motive := fun f => FirstNECellFamilyInvT qep false g' m₂' f)
              (firstNECellFamilyInvT_chall_step (m₁' := m₂') fig qep Q m_ch coins r.isSome
                (Or.inr ⟨rfl, hcol, hrel_all⟩) hep_g hsafe_g) ?_
            funext t tL
            dsimp only [s_cell₁, st', rec_r, c]
            cases (s_cell t tL).epMgmt (cellDelta tL t) (qep + 1) Q false <;> rfl
          have hcoupled₁ :
              FirstNECoupledInvD P Dh encPt encT idOf lam qep false false sC' (c :: sent) m₂' g'
                s_cell₁ := by
            rcases hinv₁ with ⟨t, ht, tL, htL, hwin_c⟩ | ⟨_, hcol₁, hrel_all₁⟩
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
            · have horig₁ : FirstNEInTransOriginInv qep sC'.snaps g' s_cell₁ :=
                firstNEInTransOriginInv_send_step_of_cellFamily qep sC.snaps Q r.isSome true st'
                  m_ch c horig hrel_all hep_g hcorrs_le hsnap_idx
              have hst_corrs_g₁ : g₁.st = g.st ∧ g₁.corrs = g.corrs := by
                unfold SM.GameState.epMgmt at hep_g
                split_ifs at hep_g <;> { injection hep_g with h; subst h; exact ⟨rfl, rfl⟩ }
              have hst_g₁ : g₁.st = g.st := hst_corrs_g₁.1
              have hcorrs_g₁ : g₁.corrs = g.corrs := hst_corrs_g₁.2
              obtain ⟨s_R₁, g₁', _, hep_g', _, _, hmeta₁⟩ := hmeta.epMgmt_some Q qep r.isSome hep
              have hg₁_eq : g₁' = g₁ := Option.some.inj (hep_g'.symm.trans hep_g)
              subst g₁'
              have hmeta' : SameMeta
                  (s_R₁.record 3 Q (s_R₁.st Q)
                    ⟨⟨Q, s_R₁.epoch Q, s_R₁.idx Q + 1⟩, m₀, LibsignalSim.toWire c⟩ true)
                  sC'.base g' := by
                simpa [sC', g', updSimStateCSend, hstop] using
                  hmeta₁.record_preserves Q (s_R₁.st Q) st' m₀ m₀ m_ch c true
                    (Function.update sC.base.pq Q pq') (Function.update sC.base.pn Q pn)
                    sC.base.unackA ((LibsignalSim.toWire c, c) :: sC.base.honest)
                    sC.base.chains sC.base.amb
              obtain ⟨s_unsh₁, hep_u, _⟩ :=
                (hrel_all 0 ht0).1.epMgmt_step (Δ := 2 + 1) (m₁' := m') hep_g
              obtain ⟨m₁'', hep_m', hmsync₁⟩ :=
                hmsync.epMgmt_step (hrel_all 0 ht0).1.epoch_eq hep_g hep_u
              have hm₁_eq : m₁'' = m₁' := Option.some.inj (hep_m'.symm.trans hep_m)
              subst m₁''
              have hs_cell₁_0 : s_cell₁ 0 none = s_unsh₁.record (2 + 1) Q st' rec_r false := by
                have hdelta0 : cellDelta none 0 = 2 + 1 := by simp [cellDelta]
                dsimp only [s_cell₁]
                simp only [(hrel_all 0 ht0).1.win_df_false, Bool.false_eq_true, ↓reduceIte,
                  hdelta0, hep_u]
              have hm₂'_eq : m₂' = m₁'.record (2 + 1) Q () rec_r true := by
                dsimp only [m₂', rec_r]
                rw [hmsync₁.epoch_eq, hmsync₁.idx_eq]
              have hmsync' : MirrorSync m₂' g' (s_cell₁ 0 none) := by
                rw [hm₂'_eq, hs_cell₁_0]
                exact hmsync₁.record_step Q st' rec_r true
              obtain ⟨hwf₁, hsends₁⟩ := SM.Thm1L17.epMgmt_wf hwf_g hep_g
              have hwf_g' : SM.Thm1L17.WFState 3 g' :=
                SM.Thm1L17.record_wf (by omega) hwf₁ rfl rfl rfl hsends₁ (fun _ => hsafe_g)
              have hep_le_qep' : ∀ P₀, g'.epoch P₀ ≤ qep + 1 :=
                (epMgmt_corrs_st_and_epoch_le hep_g hep_le_qep).2.2
              have hkept' : KeptInv P Dh encPt encT idOf lam sC' g' :=
                keptInv_send hkept Q (hid_st Q) m_ch coins
                  (by simp [g', SM.GameState.record, st', hst_g₁, fig]) rfl
              obtain ⟨hsender_sync', hid_st'⟩ :=
                fig8SenderSync_and_id_send_step P Dh encPt encT idOf lam qep Q m_ch coins r.isSome
                  true hsender_sync hid_st hwf_g hep_g
              have hkept_corr' : CorrsKeptRecvInv sC' g' :=
                corrsKeptRecvInv_updSimStateCSend P Dh encPt encT idOf lam Q m₀ true s₁ pq' pn c sC
                  hkept_corr hkept hcorrs_le hsender_sync hcorrs_g₁
              exact Or.inr (Or.inr ⟨rfl, rfl, ⟨hcol₁, hrel_all₁⟩, horig₁,
                fun _ => ⟨_, hmeta'⟩,
                hmsync',
                hwf_g',
                corrsLeEpoch_record_of_epMgmt st' rec_r true hcorrs_le hep_g hcorrs_g₁,
                hep_le_qep',
                corrsSnapIdxInv_record_of_epMgmt st' rec_r true hsnap_idx hcorrs_le hep_g
                  hcorrs_g₁ (Nat.le_succ (g₁.idx Q)),
                corrsSnapsInv_of_corrs_eq hcorrs_snaps hcorrs_g₁,
                hsender_sync',
                hkept_corr',
                hkept',
                hid_st',
                honestSentSync_cons Pt hhon_sent c⟩)
          refine le_trans
            (hih (some (LibsignalSim.toWire c)) sC' g' false false
              (stepKemFailSend P.C.F K tr Q rq) (c :: sent) m₂' s_cell₁ hcoupled₁) ?_
          unfold stage2CellBucketSumRun
          have hcell_le : ∀ t ∈ Finset.range ((qep + 1) + 2), ∀ tL ∈ SM.admissibleLastLeakGuesses 2 t,
              𝒟[cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL
                  (u (some (LibsignalSim.toWire c))) sC' (c :: sent) m₂' (s_cell₁ t tL) >>=
                fun z => pure (cellWinPred tL t z.2)] {true} ≤
              𝒟[cellChallPost fig Q m₀ (if m'.b then (pub, m₁) else (pub, m₀)) s₁ pq' pn sC sent
                  m' m₁'
                  (fun z => cellSimRun P ℓ Dh encPt encT decT idOf lam qep t tL (u z.1.1.1.1)
                    z.1.1.1.2 z.1.1.2 z.1.2 z.2 >>= fun w => pure (cellWinPred tL t w.2))
                  (if (s_cell t tL).win = true then (none, s_cell t tL)
                   else transmitPure fig (cellDelta tL t) (qep + 1) Q
                     (if m'.b then (pub, m₁) else (pub, m₀)) coins false (s_cell t tL))] {true} := by
            intro t ht tL htL
            rcases (hrel_all t ht).2.2 tL htL with hdoomed | ⟨hrel_sh, _, _, _⟩
            · dsimp only [s_cell₁]
              simp only [hdoomed.2.2.2, ↓reduceIte]
              have hcorrs_sub : ∀ x ∈ g.corrs, x ∈ g'.corrs := by
                unfold SM.GameState.epMgmt at hep_g
                split_ifs at hep_g <;>
                  { injection hep_g with h; subst h; intro x hx; exact hx }
              rw [evalDist_cellSimRun_cellWinPred_eq_zero_of_doomed P ℓ Dh encPt encT decT idOf lam
                qep t tL (u (some (LibsignalSim.toWire c))) sC' (c :: sent) m₂'
                (hdoomed.of_corrs_sub hcorrs_sub)]
              exact zero_le
            · have htr_df := (challPure_eq_of_pprimePaperRelShifted fig (cellDelta tL t) qep Q
                (pub, m₀) (pub, m₁) coins r.isSome hrel_sh hep_g hsafe_g hb_eq).2
              dsimp only [cellChallPost, s_cell₁, sC', m₂', rec_r, c, st', m_ch, pn, fig]
              simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
              rw [htr_df]
              simp only [hrel_sh.win_df_false, Bool.false_eq_true, ↓reduceIte]
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
          · have htr_0 := (challPure_eq_of_pprimePaperRelShifted fig (cellDelta none 0) qep Q
              (pub, m₀) (pub, m₁) coins r.isSome (hrel_all 0 ht0).1.toShifted hep_g hsafe_g hb_eq).2
            dsimp only [cellChallPost, s_cell₁, sC', m₂', rec_r, c, st', m_ch, pn, fig]
            simp only [hwin0, Bool.false_eq_true, ↓reduceIte]
            rw [htr_0]
            simp only [hwin0, Bool.false_eq_true, ↓reduceIte]
            cases (s_cell 0 none).epMgmt (cellDelta none 0) (qep + 1) Q false <;>
              { dsimp only; exact le_rfl }

theorem firstNECoupledInvD_deliver_query_step {α : Type}
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
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))) →
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
        (List (BitVec 8))).Range (.inr (.inl (.inl (.inr (Q, w))))))
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
          (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)).run
        (sC, (g, false, false), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) (.inr (.inl (.inl (.inr (Q, w))))) >>= u)
      sC sent m' s_cell := by
  exact firstNECoupledInvD_deliver_query_step_aux P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT
    decT idOf hid hX hinj hdec lam qep q Q w u sC g tr sent m' s_cell hbody horig hsync hih

/-! ## 2. Step Combination, `simulateQ` Induction, and Stage-2 Cell+Bucket Sum Theorem -/

theorem bucketSimRun_inl_query_bind {α : Type}
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (par : Bool) (n : unifSpec.Domain)
    (u : (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))).Range
      (.inl n) →
      OracleComp (unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (sw : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Option ℕ) :
    bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState PQ) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) (.inl n) >>= u) sC sent m' sw =
    ((OracleSpec.query (spec := unifSpec) n : ProbComp (Fin (n + 1))) >>=
      fun u₁ => bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par (u u₁) sC sent m' sw) := by
  unfold bucketSimRun
  dsimp only
  rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
  change (simulateQ (DeliverForge.fullImplBaseDFPaperBucket _ 1 (qep + 1) _ tL par)
    ((simulateQ (DeliverForge.simImplDF'Paper (2 + 1) (qep + 1))
      ((((deliverForgeHook Pt ℓ).lift
          (liftM (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp _) :
            Fig8Comp Pt ℓ _)).run sent >>=
        fun z => pure ((z.1, sC), z.2)) >>=
      fun z => (((simulateQ (LibsignalSimC.simImplC P encT decT qep _ _
        (deliverForgeHook Pt ℓ) Dh) (u z.1.1)).run z.1.2).run z.2))).run m')).run sw = _
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFPaperBucket_liftM_probComp]

theorem bucketWinPred_with_b {St Msg C : Type} (tL : Option ℕ)
    (s : SM.GameState St Msg C) (winEp : Option ℕ) (b : Bool) :
    bucketWinPred tL (withB b s, winEp) = bucketWinPred tL (s, winEp) := by
  unfold withB bucketWinPred SM.authLosingConditionsAvoided SM.canon
  cases winEp <;> rfl

theorem fullImplBaseDFPaperBucket_step_with_b
    {Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (SM.Construction.Header T × E)) (qep : ℕ)
    (sameHdr : (SM.Construction.Header T × E) → (SM.Construction.Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (q_df : (unifSpec + DeliverForge.specDF St Msg Coins (SM.Construction.Header T × E)).Domain)
    (s : SM.GameState St Msg (SM.Construction.Header T × E)) (winEp : Option ℕ) (b : Bool) :
    (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par q_df).run
      (withB b s, winEp) =
    ((DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par q_df).run (s, winEp) >>=
      fun z => pure (z.1, (withB b z.2.1, z.2.2))) := by
  unfold DeliverForge.fullImplBaseDFPaperBucket
  rw [← fullImplBaseDFCellPaper_none_eq_fullImplBaseDFPaper sm qep sameHdr 0
    (DeliverForge.bucketAuthCfg 1 tL par)]
  have hbase :
      (fullImplBaseDFCellPaper sm (qep + 1) sameHdr none 0
        (DeliverForge.bucketAuthCfg 1 tL par) q_df).run (withB b s) =
      ((fullImplBaseDFCellPaper sm (qep + 1) sameHdr none 0
        (DeliverForge.bucketAuthCfg 1 tL par) q_df).run s >>=
        fun z => pure (z.1, withB b z.2)) := by
    rcases q_df with n | ((((⟨P, m_msg, r_c⟩ | ⟨P, m₀, m₁, r_c⟩) | ⟨Q, c⟩) | ⟨Q, c⟩) | P) | ⟨Q, c, c'⟩
    · simp [fullImplBaseDFCellPaper]
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact transmitImpl_with_b sm (cellDelta none 0) (qep + 1) P m_msg r_c s b
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl, SM.challImpl,
        DeliverForge.bucketAuthCfg, StateT.run_bind, StateT.run_get, pure_bind, withB_win]
      by_cases hw : s.win = true
      · simp [hw]
      · simp only [hw, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
          bind_assoc, pure_bind, epMgmt_with_b]
        refine congrArg (SM.samIfNec r_c >>= ·) (funext fun cb => ?_)
        cases s.epMgmt (cellDelta none 0) (qep + 1) P cb.2 <;> simp
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact deliverImpl_with_b sm (DeliverForge.bucketAuthCfg 1 tL par) Q c s b
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact injectImplCell_with_b sm (qep + 1) none 0 (DeliverForge.bucketAuthCfg 1 tL par) Q c s b
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, oracleImplCellPaper,
        QueryImpl.add_apply_inr, QueryImpl.add_apply_inl]
      exact corrImplShiftedPaper_with_b (cellShift none 0) P s b
    · simp only [fullImplBaseDFCellPaper, oracleImplBaseDFCellPaper, QueryImpl.add_apply_inr]
      exact deliverForgeBaseImplCell_with_b sm (qep + 1) none 0 sameHdr
        (DeliverForge.bucketAuthCfg 1 tL par) Q c c' s b
  unfold DeliverForge.withWinEpDF
  change ((fullImplBaseDFCellPaper sm (qep + 1) sameHdr none 0
      (DeliverForge.bucketAuthCfg 1 tL par) q_df).run (withB b s) >>=
    fun p => pure (p.1, (p.2,
      if !(withB b s).win && p.2.win then DeliverForge.dfQueryTargetEpoch (fun c => c.1.1) q_df
      else winEp))) =
    (((fullImplBaseDFCellPaper sm (qep + 1) sameHdr none 0
      (DeliverForge.bucketAuthCfg 1 tL par) q_df).run s >>=
    fun p => pure (p.1, (p.2,
      if !s.win && p.2.win then DeliverForge.dfQueryTargetEpoch (fun c => c.1.1) q_df
      else winEp))) >>= fun z => pure (z.1, (withB b z.2.1, z.2.2)))
  rw [hbase, bind_assoc, bind_assoc]
  congr 1

theorem simulateQ_fullImplBaseDFPaperBucket_with_b
    {α Key St Msg Coins T E : Type} [DecidableEq Msg] [DecidableEq T] [DecidableEq E]
    [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins (SM.Construction.Header T × E)) (qep : ℕ)
    (sameHdr : (SM.Construction.Header T × E) → (SM.Construction.Header T × E) → Bool)
    (tL : Option ℕ) (par : Bool)
    (oa : DeliverForge.AdversaryCompDF St Msg Coins (SM.Construction.Header T × E) α) :
    ∀ (s : SM.GameState St Msg (SM.Construction.Header T × E)) (winEp : Option ℕ) (b : Bool),
      (simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run
        (withB b s, winEp) =
      ((simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par) oa).run
        (s, winEp) >>= fun z => pure (z.1, (withB b z.2.1, z.2.2))) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s winEp b
    simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_df u ih =>
    intro s winEp b
    rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind]
    change ((DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par q_df).run
        (withB b s, winEp) >>=
      fun p => (simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par)
        (u p.1)).run p.2) =
      (((DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par q_df).run
        (s, winEp) >>=
      fun p => (simulateQ (DeliverForge.fullImplBaseDFPaperBucket sm 1 (qep + 1) sameHdr tL par)
        (u p.1)).run p.2) >>= fun z => pure (z.1, (withB b z.2.1, z.2.2)))
    rw [fullImplBaseDFPaperBucket_step_with_b, bind_assoc, bind_assoc]
    congr 1; funext z
    rw [pure_bind]
    exact ih z.1 z.2.1 z.2.2 b

theorem forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForge_eq
    {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    {PQ : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt)
    (qep : ℕ) (tL : Option ℕ) (par : Bool)
    (A : LibsignalSM.LibAdv PQ (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    DeliverForge.forgeBucketAdvantagePaper fig 1 (qep + 1) DeliverForge.sameHdrScheme tL par
      (DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
        (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A)) =
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState PQ Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let m'₀ : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) := { st := fun _ => (), b }
      let z ← bucketSimRun P ℓ Dh encPt encT decT idOf lam qep tL par A sC₀ [] m'₀
        (SM.initState fig k b, none)
      return bucketWinPred tL z.2] {true} := by
  intro fig
  unfold DeliverForge.forgeBucketAdvantagePaper DeliverForge.forgeGameBucketPaper
    DeliverForge.challSimDF'Paper simDeliverForge LibsignalSimC.simRunCWith bucketSimRun
  rw [OracleComp.evalDist_bind_bind_swap (γ := Bool)
    ($ᵗ Bool : ProbComp Bool) ($ᵗ (BitVec 256 × BitVec 256) : ProbComp _)]
  refine congrArg (fun m : ProbComp Bool => 𝒟[m] {true}) ?_
  refine congrArg (($ᵗ (BitVec 256 × BitVec 256) : ProbComp _) >>= ·) (funext fun k => ?_)
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    simulateQ_bind, StateT.run_bind]
  rw [simulateQ_fullImplBaseDFPaperBucket_liftM_probComp]
  simp only [bind_assoc, pure_bind]
  refine congrArg (($ᵗ Bool : ProbComp Bool) >>= ·) (funext fun b => ?_)
  rw [deliverForgeHook_lift_liftM_run]
  simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
    simulateQ_simImplDF'Paper_liftM_probComp,
    simulateQ_fullImplBaseDFPaperBucket_liftM_probComp]
  refine congrArg (($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= ·) (funext fun pqrKey => ?_)
  simp only [StateT.run_pure, simulateQ_pure, pure_bind]
  have hinit : SM.initState fig k b = withB b (SM.initState fig k false) := rfl
  rw [hinit, simulateQ_fullImplBaseDFPaperBucket_with_b]
  simp only [bind_assoc, pure_bind, bucketWinPred_with_b]
  rfl

/-- Per-query step under `FirstNECoupledInvD`. -/
theorem firstNECoupledInvD_query_step {α : Type}
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
    (q_sm : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Domain)
    (u : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))).Range q_sm →
      OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))) α)
    (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
    (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (fl dead : Bool) (tr : KemFailTrackState P.C.F)
    (sent : List (Fig8C Pt))
    (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hinv : FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell)
    (hih : ∀ (u₁ : (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
        (List (BitVec 8))).Range q_sm)
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
          (BitVec 512) (List (BitVec 8))) q_sm >>= u)).run
        (sC, (g, fl, dead), tr) >>=
      fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) q_sm >>= u)
      sC sent m' s_cell := by
  rcases hinv with hwin | hdead | ⟨hfl, hdead, hbody, horig, hsync⟩
  · exact False.elim hwin
  · rw [fl_false_of_dead_support P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
      (OracleSpec.query (spec := unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ)
        (BitVec 512) (List (BitVec 8))) q_sm >>= u)
      sC g fl dead tr hdead]
    exact zero_le
  · subst hfl; subst hdead
    rcases q_sm with n | q_game
    · unfold stage2CellBucketSumRun
      rw [simulateQ_firstNESimImpl'_inl_query_bind, bind_assoc]
      simp only [cellSimRun_inl_query_bind, bucketSimRun_inl_query_bind, bind_assoc]
      refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun u₁ => ?_
      exact hih u₁ sC g false false tr sent m' s_cell
        (firstNECoupledInvD_unif_step (Or.inr (Or.inr ⟨rfl, rfl, hbody, horig, hsync⟩)))
    · rcases q_game with (((⟨Q, m₀, r⟩ | ⟨Q, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | Q
      · exact firstNECoupledInvD_transmit_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q m₀ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_chall_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q m₀ m₁ r u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_deliver_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt
          encT decT idOf hid hX hinj hdec lam qep q Q w u sC g tr sent m' s_cell hbody horig hsync
          hih
      · exact firstNECoupledInvD_inject_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q w u sC g tr sent m' s_cell hbody horig hsync hih
      · exact firstNECoupledInvD_corr_query_step P K InvPQ ℓ Dh encPt encT decT idOf lam qep q
          Q u sC g tr sent m' s_cell hbody horig hsync hih

theorem firstNECoupledInvD_simulateQ_le_sum {α : Type}
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
    (oa : OracleComp (unifSpec + SM.spec (GhostState (List (BitVec 8))) (Plain ℓ) (BitVec 512)
      (List (BitVec 8))) α) :
    ∀ (sC : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ)
      (g : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (fl dead : Bool) (tr : KemFailTrackState P.C.F) (sent : List (Fig8C Pt))
      (m' : Mirror (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
      (s_cell : ℕ → Option ℕ → SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)),
      FirstNECoupledInvD P Dh encPt encT idOf lam qep fl dead sC sent m' g s_cell →
      𝒟[(simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) oa).run
          (sC, (g, fl, dead), tr) >>=
        fun z => pure (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
      stage2CellBucketSumRun P ℓ Dh encPt encT decT idOf lam qep oa sC sent m' s_cell := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro sC g fl dead tr sent m' s_cell hinv
    rcases hinv with hwin | ⟨_, hfl⟩ | ⟨hfl, _, _, _, _⟩
    · exact False.elim hwin
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
    · subst hfl
      simp [simulateQ_pure, StateT.run_pure]
  | query_bind q_sm u ih =>
    intro sC g fl dead tr sent m' s_cell hinv
    exact firstNECoupledInvD_query_step P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT idOf
      hid hX hinj hdec lam qep q q_sm u sC g fl dead tr sent m' s_cell hinv ih

theorem deliverForge_forgeGuessedAdvantageCellPaper_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) :
    DeliverForge.forgeGuessedAdvantageCellPaper sm qep sameHdr tL t B =
      forgeGuessedAdvantageCellPaper sm qep sameHdr tL t B := by
  unfold DeliverForge.forgeGuessedAdvantageCellPaper forgeGuessedAdvantageCellPaper
  split_ifs with h1 h2
  · unfold DeliverForge.forgeGuessedAdvantageShiftedDir2Paper
      DeliverForge.forgeGameGuessedShiftedDir2Paper
      forgeGuessedAdvantageShiftedDir2Paper forgeGameGuessedShiftedDir2Paper
    simp only [authOKDir2_eq_refinement_authOKDir2]
  · rfl
  · rfl

/-- Bounds the `fl && !cand.isSome = true` probability of `firstNESimImpl'` from initial state by
the 3-part Stage-2 sum (`B1 + B2 + (tL, par)` buckets). -/
theorem evalDist_simulateQ_firstNESimImpl'_le_sum_cells
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
    (A : LibsignalSM.LibAdv (List (BitVec 8)) (BitVec 512) ℓ) :
    let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let B := DeliverForge.challSimDF'Paper (2 + 1) (qep + 1)
      (simDeliverForge P ℓ Dh encPt encT decT idOf lam qep A)
    𝒟[do
      let b ← $ᵗ Bool
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      let pqrKey ← $ᵗ BitVec 256
      let sC₀ : LibsignalToModularSchemeSimState (List (BitVec 8)) Pt ℓ :=
        initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey)
      let ghd₀ := (SM.initState fig k b, false, false)
      let tr₀ := initKemFailTrack P.C.F pqrKey
      let z ←
        (simulateQ (firstNESimImpl' P K InvPQ ℓ Dh encPt encT decT idOf lam qep q) A).run
          (sC₀, ghd₀, tr₀)
      return (z.2.2.1.2.1 && !z.2.2.2.cand.isSome)] {true} ≤
    (∑ t ∈ Finset.Ico 2 ((qep + 1) + 2),
      DeliverForge.forgeGuessedAdvantageShiftedDir2Paper fig (qep + 1)
        DeliverForge.sameHdrScheme (t - 1) t B) +
    (∑ t ∈ Finset.Ico 3 ((qep + 1) + 2),
      DeliverForge.forgeGuessedAdvantageShiftedPaper fig (2 + 1) (qep + 1)
        DeliverForge.sameHdrScheme (t - 2) t B) +
    (∑ tL ∈ SM.admissibleLastLeakGuesses 4 ((qep + 1) + 1), ∑ par ∈ ({false, true} : Finset Bool),
      DeliverForge.forgeBucketAdvantagePaper fig 1 (qep + 1)
        DeliverForge.sameHdrScheme tL par B) := by
  intro fig B
  have hB1 : ∀ t ∈ Finset.Ico 2 ((qep + 1) + 2),
      DeliverForge.forgeGuessedAdvantageShiftedDir2Paper fig (qep + 1)
        DeliverForge.sameHdrScheme (t - 1) t B =
      forgeGuessedAdvantageCellPaper fig (qep + 1) DeliverForge.sameHdrScheme (some (t - 2)) t B := by
    intro t ht
    have ht2 : 2 ≤ t := (Finset.mem_Ico.mp ht).1
    rw [← deliverForge_forgeGuessedAdvantageCellPaper_eq]
    simp [DeliverForge.forgeGuessedAdvantageCellPaper, ht2]
  have hB2 : ∀ t ∈ Finset.Ico 3 ((qep + 1) + 2),
      DeliverForge.forgeGuessedAdvantageShiftedPaper fig (2 + 1) (qep + 1)
        DeliverForge.sameHdrScheme (t - 2) t B =
      forgeGuessedAdvantageCellPaper fig (qep + 1) DeliverForge.sameHdrScheme (some (t - 3)) t B := by
    intro t ht
    have ht3 : 3 ≤ t := (Finset.mem_Ico.mp ht).1
    have hne : some (t - 3) ≠ some (t - 2) := by intro h; injection h with h'; omega
    rw [← deliverForge_forgeGuessedAdvantageCellPaper_eq]
    simp [DeliverForge.forgeGuessedAdvantageCellPaper, ht3, hne]
  rw [Finset.sum_congr rfl hB1, Finset.sum_congr rfl hB2]
  dsimp only [B, fig]
  simp_rw [forgeGuessedAdvantageCellPaper_challSimDF'Paper_simDeliverForge_eq,
    forgeBucketAdvantagePaper_challSimDF'Paper_simDeliverForge_eq]
  refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun b => ?_
  refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun k => ?_
  refine evalDist_bind_le_stage2_sum _ _ _ _ _ _ _ _ _ fun pqrKey => ?_
  exact firstNECoupledInvD_simulateQ_le_sum P K hspqr_eq InvPQ hInv_top ℓ Dh hDh encPt encT decT
    idOf hid hX hinj hdec lam qep q A
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))
    (SM.initState fig k b) false false
    (initKemFailTrack P.C.F pqrKey) []
    { st := fun _ => (), b }
    (fun _ _ => SM.initState fig k b)
    (firstNECoupledInvD_init P ℓ Dh encPt encT idOf lam qep b k pqrKey)


end

end CryptoVerification.LibsignalSession.HeadlineV1

