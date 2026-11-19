/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Defs
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.RefinementC.Recv

/-!
# Coupling salt mismatches to steering injections

**Checked by Lean.** Proves that any salt mismatch on an honest wire delivered while `safeInj 3 = false` requires either an earlier accepted steering injection while `safeInj 3 = true` or a failure of `SpqrNoWrongSaltOnUnsafedTrace`. Consequently, along an unsafed SPQR trace satisfying `SpqrNoWrongSaltOnUnsafedTrace`, `simRecvStepC` coincides with `simRecvStepCGen … false` and leaves the probe flag unchanged.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.Refinement

open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst CryptoGames.Ratchet.LibsignalSim
open CryptoGames.Ratchet.LibsignalSimC
open HMAC HKDF CBC LibsignalAead WireAEAD FSAEAD

variable {Pt PQ PQC : Type} [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ]
  [SampleableType PQC] {ℓ : ℕ}

/-! ## Unsafed SPQR traces -/

/-- Single-step SPQR state transition at `Q` via `Q`'s own sends or deliveries of honest wires in `honest` from `Q.other`. -/
def UnsafedSpqrStep (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq pq' : PQ) : Prop :=
  pq' = pq ∨
  (∃ rq pqrKey pqrMsg, P.spqr.send pq rq = some (pq', pqrKey, pqrMsg)) ∨
  (∃ w c h body salt,
    (w, c) ∈ honest ∧
    Party.senderOf c.1.1 = Q.other ∧
    ¬ w.length < 9 ∧
    (signalWireCodec P.codec).parse (w.take (w.length - 8)) = some (h, body) ∧
    P.spqr.recv pq h.pqRatchet = .ok (pq', salt))

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrStep.mono {P : Params PQ PQC}
    {honest₁ honest₂ : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq pq' : PQ}
    (hsub : ∀ wc ∈ honest₁, wc ∈ honest₂)
    (h : UnsafedSpqrStep P honest₁ Q pq pq') :
    UnsafedSpqrStep P honest₂ Q pq pq' := by
  rcases h with rfl | hsend | ⟨w, c, hd, body, salt, hmem, hsender, hlen, hparse, hrcv⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl hsend)
  · exact Or.inr (Or.inr ⟨w, c, hd, body, salt, hsub (w, c) hmem, hsender, hlen, hparse, hrcv⟩)

/-- Reflexive-transitive closure of `UnsafedSpqrStep` from `pq₀` at party `Q`. -/
inductive UnsafedSpqrTrace (P : Params PQ PQC)
    (honest : List (List (BitVec 8) × Fig8C Pt)) (Q : Party) (pq₀ : PQ) : PQ → Prop where
  | refl : UnsafedSpqrTrace P honest Q pq₀ pq₀
  | step {pq₁ pq₂ : PQ} :
      UnsafedSpqrTrace P honest Q pq₀ pq₁ →
      UnsafedSpqrStep P honest Q pq₁ pq₂ →
      UnsafedSpqrTrace P honest Q pq₀ pq₂

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.single {P : Params PQ PQC}
    {honest : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq₁ : PQ}
    (h : UnsafedSpqrStep P honest Q pq₀ pq₁) :
    UnsafedSpqrTrace P honest Q pq₀ pq₁ :=
  UnsafedSpqrTrace.step .refl h

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.trans {P : Params PQ PQC}
    {honest : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq₁ pq₂ : PQ}
    (h₀₁ : UnsafedSpqrTrace P honest Q pq₀ pq₁)
    (h₁₂ : UnsafedSpqrTrace P honest Q pq₁ pq₂) :
    UnsafedSpqrTrace P honest Q pq₀ pq₂ := by
  induction h₁₂ with
  | refl => exact h₀₁
  | step _ hstep ih => exact UnsafedSpqrTrace.step ih hstep

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] [SampleableType PQC] in
theorem UnsafedSpqrTrace.mono {P : Params PQ PQC}
    {honest₁ honest₂ : List (List (BitVec 8) × Fig8C Pt)} {Q : Party} {pq₀ pq : PQ}
    (hsub : ∀ wc ∈ honest₁, wc ∈ honest₂)
    (htr : UnsafedSpqrTrace P honest₁ Q pq₀ pq) :
    UnsafedSpqrTrace P honest₂ Q pq₀ pq := by
  induction htr with
  | refl => exact .refl
  | step _ hstep ih => exact .step ih (hstep.mono hsub)

/-! ### Trace preservation across simulator steps -/

omit [Zero Pt] [DecidableEq Pt] [SampleableType Pt] [Inhabited PQ] in
theorem onAcceptPure_honest_eq (qep : ℕ) (P_party : Party) (w : List (BitVec 8))
    (isDel : Bool) (t i : ℕ) (m : Plain ℓ) (ci? : Option ℕ) (T : PublicKey) (pq' : PQ)
    (s : SimState PQ Pt ℓ) :
    (onAcceptPure qep P_party w isDel t i m ci? T pq' s).2.honest = s.honest := by
  unfold onAcceptPure
  dsimp only
  split
  · cases s.mir.inTransit P_party.other w <;> rfl
  · split
    · rfl
    · split <;> rfl

@[expose] def simCorrPureCSteer (P : Params PQ PQC) {ℓ : ℕ} (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    Option (GhostState PQ) × JointC PQ Pt ℓ :=
  let sC := x.1
  let s := sC.base
  let s_fig8 := x.2.1
  let fl := x.2.2
  if s.stopped then (none, x)
  else if s.mir.win || !(s.mir.corrAllowed Q) || inReceiveOnlyEpoch s.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 s.mir Q) then
    (none, x)
  else
    let z := corrPure Q s_fig8
    match z.1 with
    | none => (none, (sC, z.2, fl))
    | some figSt =>
      let chains := if Q == Party.B && s.mir.epoch Party.B == 0 then
          match figSt.γ with
          | .exp x_exp => Function.update s.chains Party.A ((s.chains Party.A).map fun g =>
              if g.key.isNone then { g with key := some (encT (Dh.dh x_exp Dh.base)) } else g)
          | _ => s.chains
        else s.chains
      let g := LibsignalSim.toGhost (P := P) { s with chains } Q figSt
      (some g,
       ({ sC with base := { s with mir := s.mir.afterCorr Q, chains },
                  kept := Function.update sC.kept Q (Kept.ofSt figSt),
                  snaps := (Q, s.mir.epoch Q, g) :: sC.snaps }, z.2, fl))

omit [Zero Pt] [SampleableType Pt] in
private theorem probeHook_lift_corrQuery_run_steer
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party)
    (gh : SM.GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift
      (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh =
      pure ((corrPure Q gh.1).1, ((corrPure Q gh.1).2, gh.2)) := by
  change ((simulateQ (fig8ImplH1 fig qepF)
    (SM.corrQuery (Msg := LibsignalMsgPublicPart × Plain ℓ) (Coins := BitVec 256) (C := Fig8C Pt) Q)).run gh.1 >>=
    fun p => pure (p.1, (p.2, gh.2))) = _
  have hq := simulateQ_corrQuery_run fig 3 qepF SM.Config.h1 Q pure gh.1
  rw [bind_pure] at hq
  change (simulateQ (fig8ImplH1 fig qepF) (SM.corrQuery Q)).run gh.1 =
    pure ((corrPure Q gh.1).1, (corrPure Q gh.1).2) at hq
  rw [hq, pure_bind]

omit [SampleableType Pt] [Inhabited PQ] in
theorem stepSimCNone_corr_eq_steer (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (Q : Party)
    (x : JointC PQ Pt ℓ) :
    stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr Q) x =
      pure (simCorrPureCSteer P Dh encT Q x) := by
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  change (((guardC (simCorrC (P := P) (encT := encT) (H := probeHook fig (qep + 1)) Dh Q)).run
    x.1).run x.2) >>= (fun r => pure (r.1.1, (r.1.2, r.2))) =
    pure (simCorrPureCSteer P Dh encT Q x)
  unfold guardC simCorrC simCorrPureCSteer
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hstop : x.1.base.stopped
  · simp [hstop]
  · simp only [hstop, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_get, pure_bind]
    by_cases hcond : x.1.base.mir.win || !(x.1.base.mir.corrAllowed Q) ||
        inReceiveOnlyEpoch x.1.base.mir Q || !(SM.noAliceCorrWhileAliceBelowEpoch10 x.1.base.mir Q)
    · simp [hcond]
    · simp only [hcond, Bool.false_eq_true, ite_false, LibsignalSimC.liftC,
        StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
      rw [probeHook_lift_corrQuery_run_steer]
      simp only [pure_bind]
      cases h : (corrPure Q x.2.1).1 with
      | none => simp
      | some figSt =>
        cases hγ : figSt.γ <;>
          simp [hγ, StateT.run_set, StateT.run_pure]

omit [SampleableType Pt] [Inhabited PQ] in
/-- A `corr` step under `stepSimCNone` preserves `base.honest`, `base.pq`, `base.mir.epoch`, `inReceiveOnlyEpoch base.mir`, and `s_fig8.st`. -/
theorem stepSimCNone_corr_invariants (P : Params PQ PQC) (ℓ : ℕ) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ) (P_party : Party)
    (x : JointC PQ Pt ℓ) :
    ∀ w ∈ support (stepSimCNone P ℓ Dh encPt encT decT idOf lam qep (.inr P_party) x),
      w.2.1.base.honest = x.1.base.honest ∧
      w.2.1.base.pq = x.1.base.pq ∧
      w.2.1.base.mir.epoch = x.1.base.mir.epoch ∧
      (∀ Q, inReceiveOnlyEpoch w.2.1.base.mir Q = inReceiveOnlyEpoch x.1.base.mir Q) ∧
      w.2.2.1.st = x.2.1.st := by
  intro w hw
  have hst : (corrPure P_party x.2.1).2.st = x.2.1.st := by
    unfold corrPure
    split <;> rfl
  rw [stepSimCNone_corr_eq_steer] at hw
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst hw
  unfold simCorrPureCSteer
  dsimp only
  split
  · exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl⟩
    · cases (corrPure P_party x.2.1).1 <;>
        exact ⟨rfl, rfl, rfl, fun _ => rfl, hst⟩

/-! ## No-wrong-salt predicates -/

/-! ## Steering injections -/

/-! ## Consequences under no-wrong-salt -/

end CryptoGames.LibsignalSM.Proofs.Refinement
