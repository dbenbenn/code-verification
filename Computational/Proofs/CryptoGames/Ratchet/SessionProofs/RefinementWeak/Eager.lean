/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSpqrHyp -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement.Simulation -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Refinement

/-!
# Eager coins under the weak SPQR hypothesis

Adapts the eager-coin simulation equivalences of `Refinement/Simulation.lean` and
`Refinement.lean` to `SimInvW` and `SpqrWLocal`, showing that simulator steps preserve `Inv`
on SPQR states.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

theorem mkPub_isSomeW (P : Params PQ PQC) (Inv : PQ → Prop) {ℓ : ℕ}
    (s : SimState PQ Pt ℓ) (Q : Party) (rq : PQC) (pn : BitVec 32)
    (hpq : ∀ Q, Inv (s.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    (LibsignalSim.mkPub (P := P) s Q rq pn).isSome := by
  simp [LibsignalSim.mkPub, hW0 (s.pq Q) rq (hpq Q)]

theorem stepSim_send_run_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
    let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) ProbComp) +
      SM.oracleImpl sm 3 (qep + 1) SM.Config.h1
    (simulateQ impl ((LibsignalSim.guard (LibsignalSim.simSend (P := P) (qep := qep) Q m₀ chal r)).run st.1)).run st.2 >>=
      (fun x => pure (x.1.1, (x.1.2, x.2))) =
    if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
    else match st.1.mir.epMgmt 3 qep Q r.isSome with
    | none => pure (none, st)
    | some s₁ =>
      if chal.isSome && !(s₁.safeCh 3 Q) then pure (none, st)
      else
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ chal r.isSome s₁ rq c_cka st) := by
  intro sm impl
  unfold LibsignalSim.guard LibsignalSim.simSend
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : st.1.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, Bool.false_or, ite_false,
      StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hmir : st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q)
    · simp [hmir]
    · simp only [hmir, Bool.false_eq_true, ite_false]
      cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => simp [hep]
      | some s₁ =>
        simp only [hep]
        by_cases hch : chal.isSome && !(s₁.safeCh 3 Q)
        · simp [hch]
        · simp only [hch, Bool.false_eq_true, ite_false]
          cases r with
          | some rq =>
            simp only [pure_bind, map_eq_bind_pure_comp, Function.comp_apply, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext c_cka
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q)
              hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, pure_bind]
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka true st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
          | none =>
            simp only [pure_bind, bind_assoc]
            rw [simulateQ_coin_run]
            simp only [bind_assoc, pure_bind]
            congr 1; funext rq
            unfold simSendStep
            have hmk := Option.isSome_iff_exists.mp (mkPub_isSomeW P Inv st.1 Q rq
              (if s₁.epoch Q ≠ st.1.mir.epoch Q then BitVec.ofNat 32 (st.1.mir.idx Q - 1) else st.1.pn Q)
              hpq hW0)
            rcases hmk with ⟨⟨pq', pub⟩, hmk⟩
            simp only [hmk]
            cases chal with
            | none =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_transmitQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (transmitPure sm 3 (qep + 1) Q (pub, m₀) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]
            | some m₁ =>
              simp only [LibsignalSim.liftQ, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              rw [simulateQ_challQuery_run]
              simp only [hwin, Bool.false_eq_true, ite_false, SM.samIfNec, map_eq_bind_pure_comp,
                Function.comp_apply, bind_assoc, pure_bind]
              congr 1; funext c_cka
              cases hz : (challPure sm 3 (qep + 1) SM.Config.h1 Q (pub, m₀) (pub, m₁) c_cka false st.2).1 <;>
                simp [hz, sm, hstop, LibsignalSim.putS, StateT.run_bind, StateT.run_set, Option.isSome]

theorem stepSimNone_transmit_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eqW P Inv ℓ Dh encPt encT idOf lam qep Q m₀ none r st hwin hpq hW0
  simpa [stepSimNone, LibsignalSim.simImpl] using h

theorem stepSimNone_chall_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSimNone P ℓ Dh encPt encT decT idOf lam qep (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  have h := stepSim_send_run_eqW P Inv ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r st hwin hpq hW0
  simpa [stepSimNone, LibsignalSim.simImpl] using h

theorem stepSim_transmit_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
        ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
        pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_transmit_eqW P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ r st hwin hpq hW0

theorem stepSim_chall_eqW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (hwin : st.2.win = false)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st =
      if st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q) then pure (none, st)
      else match st.1.mir.epMgmt 3 qep Q r.isSome with
      | none => pure (none, st)
      | some s₁ =>
        if !(s₁.safeCh 3 Q) then pure (none, st)
        else
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC)) >>= fun rq =>
          ($ᵗ BitVec 256 : ProbComp (BitVec 256)) >>= fun c_cka =>
          pure (simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) := by
  cases k <;> exact stepSimNone_chall_eqW P Inv ℓ Dh encPt encT decT idOf lam qep Q m₀ m₁ r st hwin hpq hW0

theorem evalDist_stepSimEagerTransmitW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerTransmit P ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerTransmit
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inl (Q, m₀, r))))) st) G
    | some s₁ =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
      refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
        (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
        (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ none r.isSome s₁ rq c_cka st) G).trans ?_
      rw [stepSim_transmit_eqW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ r st hwin hpq hW0]
      rw [hstop, hep]
      rfl

theorem evalDist_stepSimEagerChallW (P : Params PQ PQC) (Inv : PQ → Prop) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (k : Option ℕ)
    (Q : Party) (m₀ m₁ : Plain ℓ) (r : Option PQC)
    (st : SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt))
    (G : Option (List (BitVec 8)) →
      (SimState PQ Pt ℓ × SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt)) →
      (Party → BitVec 256) → ProbComp Bool)
    (hpq : ∀ Q, Inv (st.1.pq Q))
    (hW0 : Corr.SpqrSendTotalOn P.spqr Inv) :
    𝒟[withEagerCoins st.1.mir (fun ec =>
        stepSimEagerChall P ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st ec >>= fun res =>
        G res.1 res.2.1 res.2.2)] =
      𝒟[stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st >>= fun res =>
        withEagerCoins res.2.1.mir (G res.1 res.2)] := by
  unfold stepSimEagerChall
  cases hcond : !st.2.win && inReceiveOnlyEpoch st.1.mir Q && !(st.1.stopped || st.1.mir.win || !(SM.noBobSendInEpoch0 st.1.mir Q))
  · exact evalDist_withEagerCoins_unused_pair st.1.mir
      (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
  · cases hep : st.1.mir.epMgmt 3 qep Q r.isSome with
    | none =>
      exact evalDist_withEagerCoins_unused_pair st.1.mir
        (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G
    | some s₁ =>
      dsimp only
      cases hch : !(s₁.safeCh 3 Q)
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
        rcases hcond with ⟨⟨hwin, hinw⟩, hstop⟩
        refine (evalDist_withEagerCoins_used_pair Q st.1.mir hinw
          (match r with | some rq => pure rq | none => ($ᵗ PQC : ProbComp PQC))
          (fun rq c_cka => simSendStep P ℓ Dh encPt encT idOf lam qep Q m₀ (some m₁) r.isSome s₁ rq c_cka st) G).trans ?_
        rw [stepSim_chall_eqW P Inv ℓ Dh encPt encT decT idOf lam qep k Q m₀ m₁ r st hwin hpq hW0]
        rw [hstop, hep]
        dsimp only
        rw [hch]
        rfl
      · exact evalDist_withEagerCoins_unused_pair st.1.mir
          (stepSim P ℓ Dh encPt encT decT idOf lam qep k (.inl (.inl (.inl (.inr (Q, m₀, m₁, r))))) st) G

namespace WP2A.E4

end WP2A.E4

namespace WP2A.E5

private theorem evalDist_bind_congr_support {α : Type}
    (mx : ProbComp α) (f g : α → ProbComp Bool)
    (h : ∀ a ∈ support mx, 𝒟[f a] = 𝒟[g a]) :
    𝒟[mx >>= f] = 𝒟[mx >>= g] := by
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    exact h a (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact evalDist_bind_congr _ _ _ fun u =>
      ih u fun a ha => h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)

end WP2A.E5

namespace WP2A.E6

end WP2A.E6

end CryptoGames.LibsignalSM.Proofs.Refinement
