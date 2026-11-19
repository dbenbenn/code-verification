/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.BlankedPrivRed -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import Computational.Proofs.CryptoGames.SM.Theorem6 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.FSAEAD.PubProofDefs
import Computational.Proofs.CryptoGames.SM.Theorem12
import Computational.Proofs.CryptoGames.SM.Theorem8
public import Computational.Proofs.CryptoGames.SM.BucketAuthBridge -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth
import Computational.Proofs.CryptoGames.SM.SessionProofs.BlankLemma18
import Computational.Proofs.CryptoGames.SM.Theorem1
import VCVio.CryptoFoundations.SecExp.Measure
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs
public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuthDefs
public import Computational.Proofs.CryptoGames.SM.Theorem8.Stage2Defs

/-!
# Theorem 6 on the Libsignal Chain

**Checked by Lean.** Proves `theorem6_h1_blank_concrete`, the ACD19 Theorem 6 bound for hybrid
`Config.h1` (DEV-LS6) with blanked privacy reductions `ThmB.privRedB` on equal-public-part challenge
adversaries (DEV-LS13).-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM

variable {Key St Msg Coins C Pub : Type} [DecidableEq Msg] [DecidableEq C] [DecidableEq Pub]
  [SampleableType Key] [SampleableType Coins]

section Stage2Blank

open CryptoGames.LibsignalSM.Proofs.BlankLemma18 CryptoGames.SM.Thm1 CryptoGames.SM.Thm1.L18

private def hybBranchAllB (sm : SMScheme Key St Msg Coins C) (Δ qep i : ℕ)
    (challMsg : ℕ → Option (Msg → Msg)) (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', h) ← runB sm Δ qep challMsg b A
  if lastLeakGuessAdmissible Δ (canon i h) i then return (b == b' || h.win)
  else $ᵗ Bool

private lemma evalDist_privRedB_run_all (sm : SMScheme Key St Msg Coins C) (Δ qep i : ℕ)
    (blank : Msg → Msg) (b_priv : Bool) (A : Adversary St Msg Coins C) :
    𝒟[do
        let (out, s) ← run sm Δ qep (Config.priv i) b_priv (ThmB.privRedB Δ qep i blank A)
        if lastLeakGuessAdmissible Δ (canon i s) i then return (b_priv == out)
        else $ᵗ Bool] =
      𝒟[do
        let z ← hybBranchAllB sm Δ qep i (challMsgHybB i blank b_priv) A
        return (b_priv == z)] := by
  unfold hybBranchAllB runB run ThmB.privRedB ThmB.simRun
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, Function.comp_def, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc,
    simulateQ_liftM_unif]
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Key : ProbComp Key) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b_sim => ?_
  refine evalDist_bind_congr ($ᵗ Key : ProbComp Key) _ _ fun k => ?_
  refine simulateQ_privRedB sm Δ qep i blank b_priv A
    (initState sm k b_priv)
    ({ st := fun _ => (), b := b_sim } : Mirror Msg C)
    (initState sm k b_sim)
    (SimRel.init sm i k b_priv b_sim)
    (fun b' _ s' =>
      if lastLeakGuessAdmissible Δ (canon i s') i = true then pure (b_priv == (b_sim == b'))
      else $ᵗ Bool)
    (fun b' h' =>
      (if lastLeakGuessAdmissible Δ (canon i h') i = true then pure (b_sim == b' || h'.win)
       else $ᵗ Bool) >>= fun z => pure (b_priv == z))
    (fun b' s' m' h' hr' => ?_)
  rw [hr'.canon_s i, hr'.win_h, Bool.or_false]
  by_cases hcond : lastLeakGuessAdmissible Δ (canon i h') i = true
  · simp [hcond]
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    cases b_priv
    · simpa using (ProbComp.evalDist_bind_not_uniformBool (pure : Bool → ProbComp Bool)).symm
    · simp

private lemma privAllGame_mix_boolBias_eq {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (oa : ProbComp α) (blank : Msg → Msg) (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => privAllGame (sm o) Δ qep i (ThmB.privRedB Δ qep i blank (A o))].boolBias =
      𝒟[oa >>= fun o => hybBranchAllB (sm o) Δ qep i (challMsgB i blank) (A o)].boolDist
        𝒟[oa >>= fun o => hybBranchAllB (sm o) Δ qep i (challMsgB (i + 1) blank) (A o)] := by
  rw [← evalDist_boolBias_bind_uniformBool
    (oa >>= fun o => hybBranchAllB (sm o) Δ qep i (challMsgB i blank) (A o))
    (oa >>= fun o => hybBranchAllB (sm o) Δ qep i (challMsgB (i + 1) blank) (A o))]
  unfold privAllGame
  congr 1
  rw [OracleComp.evalDist_bind_bind_swap oa ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b_priv => ?_
  have hbody : 𝒟[oa >>= fun o => do
        let (b', s) ← run (sm o) Δ qep (Config.priv i) b_priv (ThmB.privRedB Δ qep i blank (A o))
        if lastLeakGuessAdmissible Δ (canon i s) i then return (b_priv == b')
        else $ᵗ Bool] =
      𝒟[oa >>= fun o => do
        let z ← hybBranchAllB (sm o) Δ qep i (challMsgHybB i blank b_priv) (A o)
        return (b_priv == z)] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_privRedB_run_all (sm o) Δ qep i blank b_priv (A o)
  rw [hbody]
  cases b_priv <;> simp only [challMsgHybB, ↓reduceIte, Bool.false_eq_true, bind_assoc]

private lemma evalDist_select_gameB_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (hΔ : 0 < Δ) (oa : ProbComp α) (challMsg : ℕ → Option (Msg → Msg))
    (A : α → Adversary St Msg Coins C) :
    𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameB (sm o) Δ qep challMsg (A o)
        else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then
          oa >>= fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i) challMsg (A o)
        else
          oa >>= fun o => hybBranchAllB (sm o) Δ qep i challMsg (A o)] := by
  have hcoin : 𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameB (sm o) Δ qep challMsg (A o)
        else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameB (sm o) Δ qep challMsg (A o)
        else oa >>= fun _ => $ᵗ Bool] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact (OracleComp.evalDist_bind_const oa ($ᵗ Bool : ProbComp Bool)).symm
    · rfl
  rw [hcoin]
  simp only [ite_bind oa]
  conv_lhs => rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) oa]
  conv_rhs => rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) oa]
  refine evalDist_bind_congr oa _ _ fun o => ?_
  have hcoin2 : 𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameB (sm o) Δ qep challMsg (A o)
        else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameB (sm o) Δ qep challMsg (A o)
        else do
          let b ← $ᵗ Bool
          let _ ← runB (sm o) Δ qep challMsg b (A o)
          $ᵗ Bool] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← bind_assoc, OracleComp.evalDist_bind_const]
    · rfl
  rw [hcoin2]
  unfold gameB gameKillB hybBranchAllB
  simp only [ite_bind ($ᵗ Bool : ProbComp Bool)]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  simp only [ite_bind (runB (sm o) Δ qep challMsg b (A o))]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool)
      (runB (sm o) Δ qep challMsg b (A o))]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool)
      (runB (sm o) Δ qep challMsg b (A o))]
  refine evalDist_bind_congr (runB (sm o) Δ qep challMsg b (A o)) _ _ fun p => ?_
  by_cases hval : lastLeakGuessAdmissible Δ (canon i p.2) i = true
  · have hmem : canon i p.2 ∈ admissibleLastLeakGuesses Δ i := by
      have hv := hval
      unfold admissibleLastLeakGuesses
      rcases hcan : canon i p.2 with _ | l
      · simp
      · rw [hcan] at hv
        unfold lastLeakGuessAdmissible healedBy at hv
        simp only [decide_eq_true_eq] at hv
        simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
          Option.some.injEq, exists_eq_right, false_or]
        omega
    simp only [hval, hmem, ↓reduceIte]
    exact evalDist_select_swap (pure (b == p.1 || p.2.win)) ($ᵗ Bool)
  · have hmem : canon i p.2 ∉ admissibleLastLeakGuesses Δ i := fun hm =>
      hval (validGuess_of_mem_targetsL Δ hΔ hm)
    simp [hval, hmem]

private lemma h3B_mix_step {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (hΔ : 0 < Δ) (oa : ProbComp α) (blank : Msg → Msg)
    (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)].boolBias ≤
      𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)].boolBias +
        2 * 𝒟[oa >>= fun o => privAllGame (sm o) Δ qep i
          (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  refine (boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)]
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)]).trans ?_
  gcongr
  rw [privAllGame_mix_boolBias_eq]
  have hsel := boolDist_le_of_select_eq _ _ _ _ _ _
    (evalDist_select_gameB_mix sm Δ qep i hΔ oa (challMsgB i blank) A)
    (evalDist_select_gameB_mix sm Δ qep i hΔ oa (challMsgB (i + 1) blank) A)
  have hkill :
      𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i)
          (challMsgB i blank) (A o)] =
        𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i)
          (challMsgB (i + 1) blank) (A o)] :=
    evalDist_bind_congr oa _ _ fun o =>
      evalDist_gameKillB_targetsL_eq (sm o) Δ qep hΔ i blank (A o)
  rw [hkill, Measure.boolDist_self, zero_add] at hsel
  exact hsel

private lemma h3B_mix_telescope {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (hΔ : 0 < Δ) (oa : ProbComp α) (blank : Msg → Msg)
    (A : α → Adversary St Msg Coins C) (n : ℕ) :
    𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)].boolBias ≤
      𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB n blank) (A o)].boolBias +
        2 * ∑ i ∈ Finset.range n,
          𝒟[oa >>= fun o => privAllGame (sm o) Δ qep i
            (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  induction n with
  | zero =>
    have h0 : (oa >>= fun o => gameB (sm o) Δ qep (challMsgB 0 blank) (A o)) =
        (oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)) := by
      rw [challMsgB_zero]
      rfl
    simp [h0]
  | succ n ih =>
    refine ih.trans ?_
    have h := h3B_mix_step sm Δ qep n hΔ oa blank A
    rw [Finset.sum_range_succ, mul_add]
    calc _ ≤ (𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (n + 1) blank) (A o)].boolBias +
            2 * 𝒟[oa >>= fun o => privAllGame (sm o) Δ qep n
              (ThmB.privRedB Δ qep n blank (A o))].boolBias) +
          2 * ∑ i ∈ Finset.range n,
            𝒟[oa >>= fun o => privAllGame (sm o) Δ qep i
              (ThmB.privRedB Δ qep i blank (A o))].boolBias := add_le_add h le_rfl
      _ = _ := by ring

private lemma h3B_mix_final {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (oa : ProbComp α)
    (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : α → Adversary St Msg Coins C) (heq : ∀ o ∈ support oa, EqualPubChalls pubOf (A o)) :
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (qep + 1) blank) (A o)].boolBias = 0 := by
  let realMix : ProbComp Bool := oa >>= fun o => do
    let (b', _) ← runB (sm o) Δ qep (challMsgB (qep + 1) blank) false (A o)
    return b'
  rw [← Measure.boolDist_self 𝒟[realMix],
    ← evalDist_boolBias_bind_uniformBool realMix realMix]
  congr 1
  unfold gameB
  rw [OracleComp.evalDist_bind_bind_swap oa ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  have hstep : 𝒟[oa >>= fun o =>
        runB (sm o) Δ qep (challMsgB (qep + 1) blank) b (A o) >>=
          fun (b', s') => pure (b == b' || s'.win)] =
      𝒟[realMix >>= fun z => pure (b == z)] := by
    unfold realMix
    rw [bind_assoc]
    refine evalDist_bind_congr_of_support oa _ _ fun o ho => ?_
    congr 1
    unfold runB
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun k => ?_
    exact simulateQ_h3B_final (sm o) Δ qep
      pubOf blank hblank (A o) (heq o ho) (initState (sm o) k b) rfl
      (fun b' s' => pure (b == b' || s'.win))
      (fun b' _ => pure (b == b'))
      (fun b' s' hw => by simp [hw])
  cases b <;> exact hstep

end Stage2Blank

/-- Stage-2 mixture Lemma 18 at `Config.h2` with blanked privacy reductions: bounds the mixture
`Config.h2` bias over `oa : ProbComp α` by `2` times the sum over `i < qep + 1` of the mixture
unified (`tL`-free) `privAllGame` bias. -/
theorem lemma18_h2_blank_mix_stage2 {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (hΔ : 0 < Δ) (oa : ProbComp α)
    (pubOf : Msg → Pub) (blank : Msg → Msg)
    (hblank : ∀ m₀ m₁, pubOf m₀ = pubOf m₁ → blank m₀ = blank m₁)
    (A : α → Adversary St Msg Coins C) (heq : ∀ o ∈ support oa, EqualPubChalls pubOf (A o)) :
    𝒟[oa >>= fun o => game (sm o) Δ qep Config.h2 (A o)].boolBias ≤
      2 * ∑ i ∈ Finset.range (qep + 1),
        𝒟[oa >>= fun o => privAllGame (sm o) Δ qep i
          (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  have htel := h3B_mix_telescope sm Δ qep hΔ oa blank A (qep + 1)
  rw [h3B_mix_final sm Δ qep oa pubOf blank hblank A heq, zero_add] at htel
  exact htel

end CryptoGames.SM

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [DecidableEq Pub]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end CryptoGames.SM.Construction
