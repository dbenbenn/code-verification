/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem1.Lemma18Sim -- proof-setup: allow-public-import
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proof of Lemma 18

**Checked by Lean.** Proves the `H3,i → H3,i+1` hybrid hop of ACD19 Appendix A, Lemma 18,
bounding the advantage gap by twice the privacy advantages of `privRed i m̄ A` summed over
admissible leak guesses (`DEV-SM19`, `DEV-SM20`).
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Thm1.L18

variable {Key St Msg Coins C : Type}

section InvAndMask

variable (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)

lemma sendsIn_other_not (P : Party) (t : ℕ) (h : P.sendsIn t = true) :
    P.other.sendsIn t = false := by
  cases P <;> simp [Party.sendsIn, Party.other] at h ⊢ <;> omega

lemma sendsIn_succ_not (P : Party) (t : ℕ) (h : P.sendsIn t = true) :
    P.sendsIn (t + 1) = false := by
  cases P <;> simp [Party.sendsIn] at h ⊢ <;> omega

lemma healedBy_mono {tL : Option ℕ} {t₁ t₂ : ℕ} (hle : t₁ ≤ t₂)
    (h : healedBy tL Δ t₁ = true) : healedBy tL Δ t₂ = true := by
  cases tL
  · rfl
  · simp only [healedBy, decide_eq_true_eq] at h ⊢
    omega

lemma canon_leak_of_le (s : GameState St Msg C) {i l : ℕ} (hil : i ≤ l) :
    canon i (s.leak l) = canon i s := by
  have hnot : ¬ (maxOpt s.tL l < i) := by
    cases s.tL <;> simp [maxOpt] <;> omega
  simp [canon, GameState.leak, hnot]

lemma max?_mem_targetsL_of_forall {L : List ℕ} {i : ℕ}
    (hL : ∀ l ∈ L, l + Δ ≤ i) : L.max? ∈ admissibleLastLeakGuesses Δ i := by
  cases hm : L.max? with
  | none =>
    unfold admissibleLastLeakGuesses
    exact Finset.mem_insert_self none _
  | some m =>
    have hmem : m ∈ L := List.max?_mem hm
    have hm_le : m + Δ ≤ i := hL m hmem
    unfold admissibleLastLeakGuesses
    rw [Finset.mem_insert, Finset.mem_image]
    right
    refine ⟨m, Finset.mem_range.mpr (by omega), rfl⟩

/-! ### Epoch and leak invariant `InvEpoch` -/

/-- Epoch and leak ordering invariant preserved by `Config.h3`. -/
structure InvEpoch (s : GameState St Msg C) : Prop where
  win_false : s.win = false
  leaks_le_tL : ∀ l ∈ s.leaks, ∃ m, s.tL = some m ∧ l ≤ m
  trans_ep : ∀ r ∈ s.trans, r.pos.epoch ≤ s.epoch r.pos.sender
  comp_ep : ∀ pos ∈ s.comp, pos.epoch ≤ s.epoch pos.sender
  ep_lead : ∀ P : Party,
    s.epoch P ≤ s.epoch P.other + 1 ∧
      (s.epoch P.other < s.epoch P → P.sendsIn (s.epoch P) = true)

lemma InvEpoch.init (k : Key) (b : Bool) : InvEpoch (initState sm k b) where
  win_false := rfl
  leaks_le_tL := by rintro _ ⟨⟩
  trans_ep := by rintro _ ⟨⟩
  comp_ep := by rintro _ ⟨⟩
  ep_lead := by
    intro P
    refine ⟨Nat.zero_le _, ?_⟩
    intro h
    exact absurd h (Nat.lt_irrefl 0)

lemma leaks_le_tL_leak {s : GameState St Msg C}
    (hleaks : ∀ l ∈ s.leaks, ∃ m, s.tL = some m ∧ l ≤ m) (l₀ : ℕ) :
    ∀ l ∈ (s.leak l₀).leaks, ∃ m, (s.leak l₀).tL = some m ∧ l ≤ m := by
  intro l hl
  simp only [GameState.leak, List.mem_cons] at hl ⊢
  refine ⟨maxOpt s.tL l₀, rfl, ?_⟩
  rcases hl with rfl | hl_old
  · exact le_rfl
  · rcases hleaks l hl_old with ⟨m, hm, hlm⟩
    simp [hm, maxOpt]
    omega

lemma InvEpoch.sendsIn_next_epoch_eq {s : GameState St Msg C} (hi : InvEpoch s)
    {P : Party} (hsend : P.sendsIn (s.epoch P + 1) = true) :
    s.epoch P = s.epoch P.other := by
  rcases hi.ep_lead P with ⟨hle₁, hlt₁⟩
  rcases hi.ep_lead P.other with ⟨hle₂, hlt₂⟩
  rw [Party.other_other] at hle₂ hlt₂
  by_cases hgt : s.epoch P.other < s.epoch P
  · have h0 := hlt₁ hgt
    have h1 := sendsIn_succ_not P (s.epoch P) h0
    rw [hsend] at h1
    cases h1
  · by_cases hlt : s.epoch P < s.epoch P.other
    · have heq : s.epoch P.other = s.epoch P + 1 := by omega
      have h0 := hlt₂ hlt
      rw [heq, sendsIn_other_not P (s.epoch P + 1) hsend] at h0
      cases h0
    · omega

lemma InvEpoch.epMgmt {s s₁ : GameState St Msg C} (hi : InvEpoch s)
    {P : Party} {bad : Bool} (hep : s.epMgmt Δ qep P bad = some s₁) :
    InvEpoch s₁ ∧ (∀ Q, s.epoch Q ≤ s₁.epoch Q) ∧
      (∀ i, i ≤ max (s.epoch .A) (s.epoch .B) → canon i s₁ = canon i s) := by
  unfold GameState.epMgmt at hep
  by_cases h1 : P.sendsIn (s.epoch P + 1) = true
  · by_cases h2 : qep < s.epoch P + 1
    · simp [h1, h2] at hep
    · have heq_other : s.epoch P = s.epoch P.other := hi.sendsIn_next_epoch_eq h1
      have hmax_eq : max (s.epoch .A) (s.epoch .B) = s.epoch P := by
        cases P <;> simp [Party.other] at heq_other <;> omega
      simp only [h1, h2, ↓reduceIte, Option.some.injEq] at hep
      set s' : GameState St Msg C := if bad && !s.safeCh Δ P then s.leak (s.epoch P + 1) else s
      have hs'_ep : s'.epoch = s.epoch := by dsimp [s']; split_ifs <;> rfl
      have hs'_win : s'.win = false := by dsimp [s']; split_ifs <;> exact hi.win_false
      have hs'_trans : s'.trans = s.trans := by dsimp [s']; split_ifs <;> rfl
      have hs'_comp : s'.comp = s.comp := by dsimp [s']; split_ifs <;> rfl
      have hs'_leaks : ∀ l ∈ s'.leaks, ∃ m, s'.tL = some m ∧ l ≤ m := by
        dsimp [s']
        split_ifs
        · exact leaks_le_tL_leak hi.leaks_le_tL (s.epoch P + 1)
        · exact hi.leaks_le_tL
      have hs₁_eq : s₁ = { s' with
          epoch := Function.update s'.epoch P (s'.epoch P + 1)
          idx := Function.update s'.idx P 0 } := hep.symm
      rw [hs₁_eq]
      have hmono_ep : ∀ Q, s.epoch Q ≤ Function.update s'.epoch P (s'.epoch P + 1) Q := by
        intro Q
        rw [hs'_ep]
        by_cases hQ : Q = P
        · subst hQ; simp
        · simp [hQ]
      refine ⟨?_, hmono_ep, ?_⟩
      · refine {
          win_false := hs'_win
          leaks_le_tL := hs'_leaks
          trans_ep := by
            intro r hr
            dsimp only at hr ⊢
            rw [hs'_trans] at hr
            exact (hi.trans_ep r hr).trans (hmono_ep r.pos.sender)
          comp_ep := by
            intro pos hpos
            dsimp only at hpos ⊢
            rw [hs'_comp] at hpos
            exact (hi.comp_ep pos hpos).trans (hmono_ep pos.sender)
          ep_lead := by
            intro Q
            dsimp only
            rw [hs'_ep]
            by_cases hQ : Q = P
            · subst hQ
              simp only [Function.update_self, Function.update_of_ne (Party.other_ne Q)]
              refine ⟨by omega, fun _ => h1⟩
            · have hQo : Q.other = P := by cases Q <;> cases P <;> first | contradiction | rfl
              have hPQ : s.epoch Q = s.epoch P := by
                have hPo : P.other = Q := by rw [← hQo, Party.other_other]
                rw [← hPo]
                exact heq_other.symm
              rw [hQo]
              simp only [Function.update_self, Function.update_of_ne hQ]
              refine ⟨by omega, fun hlt => absurd hlt (by omega)⟩
        }
      · intro i hi_le
        rw [hmax_eq] at hi_le
        have hcan_s₁ : canon i { s' with
            epoch := Function.update s'.epoch P (s'.epoch P + 1)
            idx := Function.update s'.idx P 0 } = canon i s' := rfl
        rw [hcan_s₁]
        dsimp [s']
        split_ifs
        · exact canon_leak_of_le s (by omega)
        · rfl
  · by_cases h2 : qep < s.epoch P
    · simp [h1, h2] at hep
    · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hep
      subst hep
      exact ⟨hi, fun _ => le_rfl, fun _ _ => rfl⟩

lemma InvEpoch.record {s₁ : GameState St Msg C} (hi : InvEpoch s₁)
    (P : Party) (st' : St) (msg : Msg) (ct : C) (isChall : Bool) :
    let r : Record Msg C := ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, msg, ct⟩
    InvEpoch (s₁.record Δ P st' r isChall) ∧
      (s₁.record Δ P st' r isChall).epoch = s₁.epoch ∧
      ∀ i, canon i (s₁.record Δ P st' r isChall) = canon i s₁ := by
  intro r
  refine ⟨{
    win_false := hi.win_false
    leaks_le_tL := hi.leaks_le_tL
    trans_ep := by
      intro r' hr'
      simp only [GameState.record, List.mem_cons] at hr'
      rcases hr' with rfl | hr_old
      · exact le_rfl
      · exact hi.trans_ep r' hr_old
    comp_ep := by
      intro pos hpos
      simp only [GameState.record] at hpos
      split_ifs at hpos
      · exact hi.comp_ep pos hpos
      · simp only [List.mem_cons] at hpos
        rcases hpos with rfl | hpos_old
        · exact le_rfl
        · exact hi.comp_ep pos hpos_old
    ep_lead := hi.ep_lead
  }, rfl, fun _ => rfl⟩

lemma InvEpoch.accept {s : GameState St Msg C} (hi : InvEpoch s)
    (P : Party) (st' : St) (pos : Pos) (hpos : pos.epoch ≤ s.epoch P.other) :
    InvEpoch (s.accept P st' pos) ∧
      (∀ Q, s.epoch Q ≤ (s.accept P st' pos).epoch Q) ∧
      ∀ i, canon i (s.accept P st' pos) = canon i s := by
  have hmono_ep : ∀ Q, s.epoch Q ≤ (s.accept P st' pos).epoch Q := by
    intro Q
    simp only [GameState.accept, GameState.delete]
    by_cases hQ : Q = P
    · subst hQ; simp
    · simp [hQ]
  refine ⟨{
    win_false := hi.win_false
    leaks_le_tL := hi.leaks_le_tL
    trans_ep := by
      intro r hr
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hr
      exact (hi.trans_ep r hr.1).trans (hmono_ep r.pos.sender)
    comp_ep := by
      intro pos₀ hpos₀
      simp only [GameState.accept, GameState.delete, List.mem_filter] at hpos₀
      exact (hi.comp_ep pos₀ hpos₀.1).trans (hmono_ep pos₀.sender)
    ep_lead := by
      intro Q
      have hep_acc : (s.accept P st' pos).epoch =
          Function.update s.epoch P (max (s.epoch P) pos.epoch) := rfl
      rw [hep_acc]
      by_cases hle_p : pos.epoch ≤ s.epoch P
      · have hmax : max (s.epoch P) pos.epoch = s.epoch P := Nat.max_eq_left hle_p
        rw [hmax, Function.update_eq_self]
        exact hi.ep_lead Q
      · have hpeq : max (s.epoch P) pos.epoch = s.epoch P.other := by
          rcases hi.ep_lead P.other with ⟨hle_o, _⟩
          rw [Party.other_other] at hle_o
          omega
        rw [hpeq]
        by_cases hQ : Q = P
        · subst hQ
          simp only [Function.update_self, Function.update_of_ne (Party.other_ne Q)]
          exact ⟨by omega, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
        · have hQo : Q.other = P := by cases Q <;> cases P <;> first | contradiction | rfl
          have hPo : P.other = Q := by rw [← hQo, Party.other_other]
          rw [hQo, hPo]
          simp only [Function.update_self, Function.update_of_ne hQ]
          exact ⟨by omega, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
  }, hmono_ep, fun _ => rfl⟩

lemma InvEpoch.afterCorr {s : GameState St Msg C} (hi : InvEpoch s) (P : Party) :
    InvEpoch (s.afterCorr P) ∧
      (s.afterCorr P).epoch = s.epoch ∧
      (∀ i, i ≤ max (s.epoch .A) (s.epoch .B) → canon i (s.afterCorr P) = canon i s) := by
  refine ⟨{
    win_false := hi.win_false
    leaks_le_tL := leaks_le_tL_leak hi.leaks_le_tL (max (s.epoch .A) (s.epoch .B))
    trans_ep := hi.trans_ep
    comp_ep := by
      intro pos hpos
      simp only [GameState.afterCorr, GameState.leak, List.mem_append, List.mem_map,
        List.mem_filter] at hpos
      rcases hpos with ⟨r, ⟨hr_mem, _⟩, rfl⟩ | hpos_old
      · exact hi.trans_ep r hr_mem
      · exact hi.comp_ep pos hpos_old
    ep_lead := hi.ep_lead
  }, rfl, fun i hi_le => canon_leak_of_le _ hi_le⟩

lemma inTransit_mem_and_sender [DecidableEq C] {s : GameState St Msg C} {Q : Party} {c : C}
    {r : Record Msg C} (htr : s.inTransit Q c = some r) : r ∈ s.trans ∧ r.pos.sender = Q := by
  unfold GameState.inTransit at htr
  have hmem := List.mem_of_find?_eq_some htr
  have hpred := List.find?_some htr
  simp only [Bool.and_eq_true, beq_iff_eq] at hpred
  exact ⟨hmem, hpred.1⟩

lemma trivial_epoch_le {s : GameState St Msg C} (hi : InvEpoch s)
    (hsafe : s.safeInj Δ = true) {P : Party} {pos : Pos} (hsend : pos.sender = P.other)
    (htriv : s.trivial Δ pos = true) : pos.epoch ≤ s.epoch P.other := by
  unfold GameState.trivial at htriv
  simp only [Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true,
    Bool.not_eq_true'] at htriv
  rcases htriv with hcomp | ⟨_, hnot_healed⟩
  · rw [← hsend]
    exact hi.comp_ep pos hcomp
  · unfold GameState.safeInj at hsafe
    have hmin_le : min (s.epoch .A) (s.epoch .B) ≤ s.epoch P.other := by
      cases P <;> simp [Party.other]
    have hhealed_other : healedBy s.tL Δ (s.epoch P.other) = true :=
      healedBy_mono Δ hmin_le hsafe
    by_contra hlt
    have hle : s.epoch P.other ≤ pos.epoch := by omega
    have hh := healedBy_mono Δ hle hhealed_other
    rw [hh] at hnot_healed
    cases hnot_healed

lemma canon_mem_targetsL_of_safeCh (_hΔ : 0 < Δ) {s₁ : GameState St Msg C} (hi : InvEpoch s₁)
    {P : Party} {i : ℕ} (hsafe : s₁.safeCh Δ P = true) (hti : s₁.epoch P = i) :
    canon i s₁ ∈ admissibleLastLeakGuesses Δ i := by
  unfold canon
  refine max?_mem_targetsL_of_forall Δ ?_
  intro l hl
  simp only [List.mem_filter] at hl
  rcases hi.leaks_le_tL l hl.1 with ⟨m, hm, hlm⟩
  unfold GameState.safeCh at hsafe
  rw [hm, hti] at hsafe
  simp only [healedBy, decide_eq_true_eq] at hsafe
  omega

/-! ### Freezing `canon i` -/

variable [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]

/-! ### Pre-epoch agreement of `Config.h3` -/

/-! ### Telescoping over leak guesses -/

variable [SampleableType Key]

def gameKill (i : ℕ) (S : Finset (Option ℕ)) (cfg : Config Msg)
    (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (b', h) ← run sm Δ qep cfg b A
  if canon i h ∈ S then $ᵗ Bool
  else return (b == b' || h.win)

lemma gameKill_empty (i : ℕ) (cfg : Config Msg) (A : Adversary St Msg Coins C) :
    gameKill sm Δ qep i ∅ cfg A = game sm Δ qep cfg A := by
  simp [gameKill, game]

lemma ite_bind {m : Type → Type} [Monad m] {α β : Type} {c : Bool}
    (x : m α) (f g : α → m β) :
    (if c then x >>= f else x >>= g) = (x >>= fun a => if c then f a else g a) := by
  cases c <;> rfl

lemma evalDist_select_swap (x y : ProbComp Bool) :
    𝒟[do let sel ← $ᵗ Bool; if sel then x else y] =
      𝒟[do let sel ← $ᵗ Bool; if sel then y else x] := by
  rw [← ProbComp.evalDist_bind_not_uniformBool (fun sel => if sel then y else x)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
  cases sel <;> rfl

lemma evalDist_select_gameKill_insert (i : ℕ) (S : Finset (Option ℕ)) (tL : Option ℕ)
    (htL_not : tL ∉ S) (hval : lastLeakGuessAdmissible Δ tL i = true)
    (cfg : Config Msg) (A : Adversary St Msg Coins C) :
    𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameKill sm Δ qep i S cfg A else $ᵗ Bool] =
      𝒟[do
        let sel ← $ᵗ Bool
        if sel then gameKill sm Δ qep i (insert tL S) cfg A
        else hybBranch sm Δ qep tL i cfg A] := by
  have hcoin : 𝒟[do
      let sel ← $ᵗ Bool
      if sel then gameKill sm Δ qep i S cfg A else $ᵗ Bool] =
    𝒟[do
      let sel ← $ᵗ Bool
      if sel then gameKill sm Δ qep i S cfg A
      else do
        let b ← $ᵗ Bool
        let _ ← run sm Δ qep cfg b A
        $ᵗ Bool] := by
    refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun sel => ?_
    cases sel
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← bind_assoc, OracleComp.evalDist_bind_const]
    · rfl
  rw [hcoin]
  unfold gameKill hybBranch
  simp only [ite_bind ($ᵗ Bool : ProbComp Bool)]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) ($ᵗ Bool : ProbComp Bool)]
  refine evalDist_bind_congr ($ᵗ Bool : ProbComp Bool) _ _ fun b => ?_
  simp only [ite_bind (run sm Δ qep cfg b A)]
  conv_lhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) (run sm Δ qep cfg b A)]
  conv_rhs =>
    rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool : ProbComp Bool) (run sm Δ qep cfg b A)]
  refine evalDist_bind_congr (run sm Δ qep cfg b A) _ _ fun p => ?_
  by_cases hcan : canon i p.2 = tL
  · simp only [hcan, htL_not, ↓reduceIte, Finset.mem_insert_self, hval, beq_self_eq_true,
      Bool.and_self]
    exact evalDist_select_swap (pure (b == p.1 || p.2.win)) ($ᵗ Bool)
  · have hmem_iff : canon i p.2 ∈ insert tL S ↔ canon i p.2 ∈ S := by
      simp [Finset.mem_insert, hcan]
    have hbeq : (canon i p.2 == tL) = false := beq_false_of_ne hcan
    simp [hmem_iff, hbeq]

lemma evalDist_uniformBool_ite_true (x y : ProbComp Bool) :
    𝒟[do let sel ← $ᵗ Bool; if sel then x else y] {true} =
      (𝒟[x] {true} + 𝒟[y] {true}) / 2 := by
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply (measurableSet_singleton true) Measurable.of_discrete.aemeasurable,
    lintegral_fintype, Fintype.sum_bool]
  simp [div_eq_mul_inv, add_mul]

lemma boolDist_le_of_select_eq (x₀ x₁ y₀ y₁ z₀ z₁ : ProbComp Bool)
    (h₀ : 𝒟[do let sel ← $ᵗ Bool; if sel then x₀ else $ᵗ Bool] =
      𝒟[do let sel ← $ᵗ Bool; if sel then y₀ else z₀])
    (h₁ : 𝒟[do let sel ← $ᵗ Bool; if sel then x₁ else $ᵗ Bool] =
      𝒟[do let sel ← $ᵗ Bool; if sel then y₁ else z₁]) :
    𝒟[x₀].boolDist 𝒟[x₁] ≤ 𝒟[y₀].boolDist 𝒟[y₁] + 𝒟[z₀].boolDist 𝒟[z₁] := by
  have ht₀ : (𝒟[do let sel ← $ᵗ Bool; if sel then x₀ else $ᵗ Bool] {true}).toReal =
      (𝒟[do let sel ← $ᵗ Bool; if sel then y₀ else z₀] {true}).toReal := by rw [h₀]
  have ht₁ : (𝒟[do let sel ← $ᵗ Bool; if sel then x₁ else $ᵗ Bool] {true}).toReal =
      (𝒟[do let sel ← $ᵗ Bool; if sel then y₁ else z₁] {true}).toReal := by rw [h₁]
  rw [evalDist_uniformBool_ite_true, evalDist_uniformBool_ite_true] at ht₀ ht₁
  have hfin : ∀ w : ProbComp Bool, 𝒟[w] {true} ≠ ⊤ := fun w => measure_ne_top 𝒟[w] {true}
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_add (hfin _) (hfin _)] at ht₀ ht₁
  rw [← ENNReal.toReal_le_toReal (Measure.boolDist_ne_top 𝒟[x₀] 𝒟[x₁])
      (ENNReal.add_ne_top.mpr ⟨Measure.boolDist_ne_top 𝒟[y₀] 𝒟[y₁],
        Measure.boolDist_ne_top 𝒟[z₀] 𝒟[z₁]⟩),
    ENNReal.toReal_add (Measure.boolDist_ne_top 𝒟[y₀] 𝒟[y₁])
      (Measure.boolDist_ne_top 𝒟[z₀] 𝒟[z₁]),
    Measure.toReal_boolDist, Measure.toReal_boolDist, Measure.toReal_boolDist]
  have hdiff : (𝒟[x₀] {true}).toReal - (𝒟[x₁] {true}).toReal =
      ((𝒟[y₀] {true}).toReal - (𝒟[y₁] {true}).toReal) +
        ((𝒟[z₀] {true}).toReal - (𝒟[z₁] {true}).toReal) := by linarith
  rw [hdiff]
  exact abs_add_le _ _

lemma gameKill_boolDist_insert (i : ℕ) (mbar : Msg) (A : Adversary St Msg Coins C)
    (S : Finset (Option ℕ)) (tL : Option ℕ) (htL_not : tL ∉ S)
    (hval : lastLeakGuessAdmissible Δ tL i = true) :
    𝒟[gameKill sm Δ qep i S (Config.h3 i mbar) A].boolDist
        𝒟[gameKill sm Δ qep i S (Config.h3 (i + 1) mbar) A] ≤
      𝒟[gameKill sm Δ qep i (insert tL S) (Config.h3 i mbar) A].boolDist
          𝒟[gameKill sm Δ qep i (insert tL S) (Config.h3 (i + 1) mbar) A] +
        privAdvantage sm Δ qep tL i (privRed Δ qep i mbar A) := by
  rw [privAdvantage_privRed_eq]
  exact boolDist_le_of_select_eq _ _ _ _ _ _
    (evalDist_select_gameKill_insert sm Δ qep i S tL htL_not hval (Config.h3 i mbar) A)
    (evalDist_select_gameKill_insert sm Δ qep i S tL htL_not hval (Config.h3 (i + 1) mbar) A)

lemma gameKill_boolDist_union_le (i : ℕ) (mbar : Msg) (A : Adversary St Msg Coins C)
    (T : Finset (Option ℕ)) (hval : ∀ tL ∈ T, lastLeakGuessAdmissible Δ tL i = true) :
    ∀ S : Finset (Option ℕ), Disjoint S T →
      𝒟[gameKill sm Δ qep i S (Config.h3 i mbar) A].boolDist
          𝒟[gameKill sm Δ qep i S (Config.h3 (i + 1) mbar) A] ≤
        𝒟[gameKill sm Δ qep i (S ∪ T) (Config.h3 i mbar) A].boolDist
            𝒟[gameKill sm Δ qep i (S ∪ T) (Config.h3 (i + 1) mbar) A] +
          ∑ tL ∈ T, privAdvantage sm Δ qep tL i (privRed Δ qep i mbar A) := by
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
    have hstep := gameKill_boolDist_insert sm Δ qep i mbar A S tL htL_not_S
      (hval tL (Finset.mem_insert_self tL T))
    have hih := ih (fun x hx => hval x (Finset.mem_insert_of_mem hx)) (insert tL S) hdisj'
    have hunion : insert tL S ∪ T = S ∪ insert tL T := by
      ext x; simp
    rw [hunion] at hih
    rw [Finset.sum_insert htL_not_T]
    calc _ ≤ _ := hstep
      _ ≤ (𝒟[gameKill sm Δ qep i (S ∪ insert tL T) (Config.h3 i mbar) A].boolDist
            𝒟[gameKill sm Δ qep i (S ∪ insert tL T) (Config.h3 (i + 1) mbar) A] +
          ∑ x ∈ T, privAdvantage sm Δ qep x i (privRed Δ qep i mbar A)) +
          privAdvantage sm Δ qep tL i (privRed Δ qep i mbar A) := add_le_add hih le_rfl
      _ = _ := by ring

lemma validGuess_of_mem_targetsL (_hΔ : 0 < Δ) {i : ℕ} {tL : Option ℕ}
    (htL : tL ∈ admissibleLastLeakGuesses Δ i) : lastLeakGuessAdmissible Δ tL i = true := by
  unfold admissibleLastLeakGuesses at htL
  unfold lastLeakGuessAdmissible healedBy
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range] at htL
  rcases htL with rfl | ⟨m, hm, rfl⟩
  · rfl
  · simp only [decide_eq_true_eq]
    omega

lemma boolBias_le_add_two_mul_boolDist (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    μ.boolBias ≤ ν.boolBias + 2 * μ.boolDist ν := by
  rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ,
    Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν,
    Measure.boolDist, ← mul_add]
  gcongr
  rw [add_comm]
  exact ENNReal.absDiff_triangle (μ {true}) (ν {true}) (1 / 2)

end InvAndMask

end CryptoGames.SM.Thm1.L18
