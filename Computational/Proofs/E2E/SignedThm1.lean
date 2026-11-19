/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.SessionProofs.BlankLemma18 -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma17 -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.SignedPrims -- proof-setup: allow-public-import
import Computational.Proofs.CryptoGames.SM.Theorem1
import Computational.Proofs.E2E.SignedAdv
import Computational.Proofs.E2E.SignedThm12
import Computational.Proofs.E2E.SignedThm8

/-!
# Blanked ACD19 Theorems 1 and 6 at `H1` on mixtures

Lifts the blanked `H1` security bounds (`theorem1_h1_blank_mix` and `theorem6_h1_blank_mix`) to
prefix-indexed mixtures, with single averaged CKA and PRF-PRNG reductions.
-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

open CryptoGames CryptoGames.SM CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17
  CryptoGames.SM.Thm1.L18 CryptoGames.LibsignalSM.Proofs.BlankLemma18

section Generic

variable {Key St Msg Coins C Pub : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins]

theorem boolBias_mix_eq_zero {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (h : ∀ a, 𝒟[f a].boolBias = 0) : 𝒟[oa >>= f].boolBias = 0 := by
  let _ : MeasurableSpace α := ⊤
  have h' : ∀ a, 𝒟[f a] {true} = 𝒟[f a] {false} := fun a =>
    ENNReal.absDiff_eq_zero.mp (h a)
  change ENNReal.absDiff _ _ = 0
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  simp only [h', ENNReal.absDiff_self]

theorem evalDist_select_mix {α : Type} (oa : ProbComp α) (x y : α → ProbComp Bool) :
    𝒟[do let sel ← $ᵗ Bool; if sel then oa >>= x else oa >>= y] =
      𝒟[oa >>= fun o => do let sel ← $ᵗ Bool; if sel then x o else y o] := by
  have h : (do let sel ← ($ᵗ Bool : ProbComp Bool); if sel then oa >>= x else oa >>= y) =
      (($ᵗ Bool : ProbComp Bool) >>= fun sel => oa >>= fun o => if sel then x o else y o) := by
    refine bind_congr fun sel => ?_
    cases sel <;> rfl
  rw [h, OracleComp.evalDist_bind_bind_swap]

theorem evalDist_mix_uniformBool {α : Type} (oa : ProbComp α) :
    𝒟[oa >>= fun _ => ($ᵗ Bool : ProbComp Bool)] = 𝒟[($ᵗ Bool : ProbComp Bool)] :=
  OracleComp.evalDist_bind_const _ _

theorem evalDist_select_gameKillB_insert_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (S : Finset (Option ℕ)) (tL : Option ℕ) (htL_not : tL ∉ S)
    (hval : lastLeakGuessAdmissible Δ tL i = true) (challMsg : ℕ → Option (Msg → Msg)) (oa : ProbComp α)
    (A : α → Adversary St Msg Coins C) :
    𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o) else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) challMsg (A o)
        else oa >>= fun o => hybBranchB (sm o) Δ qep tL i challMsg (A o)] := by
  have h0 : 𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o) else $ᵗ Bool] =
      𝒟[do
        let sel ← ($ᵗ Bool : ProbComp Bool)
        if sel then oa >>= fun o => gameKillB (sm o) Δ qep i S challMsg (A o)
        else oa >>= fun _ => ($ᵗ Bool : ProbComp Bool)] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · exact (evalDist_mix_uniformBool oa).symm
    · rfl
  rw [h0, evalDist_select_mix, evalDist_select_mix]
  exact evalDist_bind_congr oa _ _ fun o =>
    evalDist_select_gameKillB_insert (sm o) Δ qep i S tL htL_not hval challMsg (A o)

theorem boolBias_mix_privGame_privRedB {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep : ℕ) (tL : Option ℕ) (i : ℕ) (blank : Msg → Msg) (oa : ProbComp α)
    (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias =
      𝒟[oa >>= fun o => hybBranchB (sm o) Δ qep tL i (challMsgB i blank) (A o)].boolDist
        𝒟[oa >>= fun o => hybBranchB (sm o) Δ qep tL i (challMsgB (i + 1) blank) (A o)] := by
  rw [← evalDist_boolBias_bind_uniformBool]
  congr 1
  unfold privGame
  rw [OracleComp.evalDist_bind_bind_swap]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  rw [evalDist_bind_congr oa _
    (fun o => do
      let z ← hybBranchB (sm o) Δ qep tL i (challMsgHybB i blank b) (A o)
      return (b == z))
    fun o => evalDist_privRedB_run (sm o) Δ qep tL i blank b (A o)]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
    rfl
  · simp only [↓reduceIte, bind_assoc]
    rfl

theorem gameKillB_mix_union_le {α : Type} (sm : α → SMScheme Key St Msg Coins C)
    (Δ qep i : ℕ) (blank : Msg → Msg) (oa : ProbComp α) (A : α → Adversary St Msg Coins C)
    (T : Finset (Option ℕ)) (hval : ∀ tL ∈ T, lastLeakGuessAdmissible Δ tL i = true) :
    ∀ S : Finset (Option ℕ), Disjoint S T →
      𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB i blank) (A o)].boolDist
          𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB (i + 1) blank) (A o)] ≤
        𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (S ∪ T) (challMsgB i blank) (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (S ∪ T) (challMsgB (i + 1) blank) (A o)] +
          ∑ tL ∈ T, 𝒟[oa >>= fun o =>
            privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  induction T using Finset.induction_on with
  | empty =>
    intro S _
    simp
  | @insert tL T htL_not_T ih =>
    intro S hdisj
    have htL_not_S : tL ∉ S := Finset.disjoint_insert_right.mp hdisj |>.1
    have hdisj' : Disjoint (insert tL S) T := by
      rw [Finset.disjoint_insert_left]
      exact ⟨htL_not_T, Finset.disjoint_insert_right.mp hdisj |>.2⟩
    have hvtL := hval tL (Finset.mem_insert_self tL T)
    have hstep :
        𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB i blank) (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i S (challMsgB (i + 1) blank) (A o)] ≤
          𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) (challMsgB i blank)
              (A o)].boolDist
            𝒟[oa >>= fun o => gameKillB (sm o) Δ qep i (insert tL S) (challMsgB (i + 1) blank)
              (A o)] +
          𝒟[oa >>= fun o =>
            privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
      rw [boolBias_mix_privGame_privRedB]
      exact boolDist_le_of_select_eq _ _ _ _ _ _
        (evalDist_select_gameKillB_insert_mix sm Δ qep i S tL htL_not_S hvtL
          (challMsgB i blank) oa A)
        (evalDist_select_gameKillB_insert_mix sm Δ qep i S tL htL_not_S hvtL
          (challMsgB (i + 1) blank) oa A)
    have hih := ih (fun x hx => hval x (Finset.mem_insert_of_mem hx)) (insert tL S) hdisj'
    have hunion : insert tL S ∪ T = S ∪ insert tL T := by
      ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert htL_not_T]
    calc _ ≤ _ := hstep
      _ ≤ _ := add_le_add hih le_rfl
      _ = _ := by ring

theorem lemma18B_mix {α : Type} (sm : α → SMScheme Key St Msg Coins C) (Δ qep : ℕ) (hΔ : 0 < Δ)
    (blank : Msg → Msg) (i : ℕ) (oa : ProbComp α) (A : α → Adversary St Msg Coins C) :
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)].boolBias ≤
      𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)].boolBias +
        2 * ∑ tL ∈ admissibleLastLeakGuesses Δ i, 𝒟[oa >>= fun o =>
          privGame (sm o) Δ qep tL i (ThmB.privRedB Δ qep i blank (A o))].boolBias := by
  refine (boolBias_le_add_two_mul_boolDist
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB i blank) (A o)]
    𝒟[oa >>= fun o => gameB (sm o) Δ qep (challMsgB (i + 1) blank) (A o)]).trans ?_
  gcongr
  have hunion := gameKillB_mix_union_le sm Δ qep i blank oa A (admissibleLastLeakGuesses Δ i)
    (fun tL htL => validGuess_of_mem_targetsL Δ hΔ htL) ∅ (Finset.disjoint_empty_left _)
  simp only [Finset.empty_union, gameKillB_empty] at hunion
  rw [evalDist_bind_congr oa
      (fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB i blank) (A o))
      (fun o => gameKillB (sm o) Δ qep i (admissibleLastLeakGuesses Δ i) (challMsgB (i + 1) blank) (A o))
      fun o => evalDist_gameKillB_targetsL_eq (sm o) Δ qep hΔ i blank (A o),
    Measure.boolDist_self, zero_add] at hunion
  exact hunion

end Generic

section Scheme

open CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E Pub : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E] [DecidableEq Pub]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

end Scheme

end CryptoVerification.E2E.Signed
