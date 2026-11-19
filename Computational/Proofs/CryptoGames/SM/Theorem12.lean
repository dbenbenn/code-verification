/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Reductions -- proof-setup: allow-public-import
public import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2Defs
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma13
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma14
import Computational.Proofs.CryptoGames.SM.Theorem12.Lemma15
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L13USend
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L14U
import Computational.Proofs.CryptoGames.SM.Theorem12.Stage2L15Uni

/-!
# Theorem 12: privacy of the Fig. 8 SM scheme

**Checked by Lean.** Proves `theorem12` (ACD19 §5.3.3, Lemmas 13–15), bounding the privacy
advantage of the Fig. 8 SM scheme via the concrete reductions `redCKAPriv`, `redPRNGPriv`,
`redFSPriv`, and `redFSPrivCoin` (`SM/Reductions.lean`).-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy

namespace CryptoGames.SM.Construction

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

/-! ### Stage-2 switch-back privacy reductions (`redCKAPrivU`, `redFSPrivUni`, `redFSPrivUniCoin`) -/

section Stage2SwitchBack

private def postPred {β : Type} (p : β → Bool) (m : ProbComp (Bool × β)) : ProbComp Bool := do
  let x ← m
  if p x.2 then pure x.1 else $ᵗ Bool

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma evalDist_bind_apply_local {α β : Type} [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (oa : ProbComp α) (f : α → ProbComp β) (s : Set β) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f] s = ∫⁻ a, 𝒟[f a] s ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma apply_le_add_boolDist_local (μ ν : Measure Bool) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (v : Bool) : μ {v} ≤ ν {v} + μ.boolDist ν := by
  cases v
  · have h := Measure.apply_true_le_add_boolDist ν μ
    rw [Measure.boolDist_comm] at h
    have : μ {false} + μ {true} ≤ (ν {false} + μ.boolDist ν) + μ {true} :=
      calc μ {false} + μ {true} = 1 := by
            rw [add_comm]; exact PrivL15.measure_bool_true_add_false μ
        _ = ν {true} + ν {false} := (PrivL15.measure_bool_true_add_false ν).symm
        _ ≤ (μ {true} + μ.boolDist ν) + ν {false} := by gcongr
        _ = (ν {false} + μ.boolDist ν) + μ {true} := by ring
    exact (ENNReal.add_le_add_iff_right (measure_ne_top μ _)).1 this
  · exact Measure.apply_true_le_add_boolDist μ ν

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma boolDist_bind_le_lintegral_local {α : Type} (oa : ProbComp α)
    (f g : α → ProbComp Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f].boolDist 𝒟[oa >>= g] ≤ ∫⁻ a, 𝒟[f a].boolDist 𝒟[g a] ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  refine Measure.boolDist_le_of_apply_le _ _ fun v => ?_
  rw [evalDist_bind_apply_local, evalDist_bind_apply_local,
    ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono fun a => apply_le_add_boolDist_local _ _ v

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma evalDist_postPred_or_add_coin {β : Type} (p₁ p₂ : β → Bool)
    (hdisj : ∀ c, ¬(p₁ c = true ∧ p₂ c = true)) (m : ProbComp (Bool × β)) (v : Bool) :
    𝒟[postPred (fun c => p₁ c || p₂ c) m] {v} + 𝒟[($ᵗ Bool : ProbComp Bool)] {v} =
      𝒟[postPred p₁ m] {v} + 𝒟[postPred p₂ m] {v} := by
  let _ : MeasurableSpace (Bool × β) := ⊤
  have _ : DiscreteMeasurableSpace (Bool × β) := ⟨fun _ => trivial⟩
  have hcoin : 𝒟[($ᵗ Bool : ProbComp Bool)] {v} =
      ∫⁻ _ : Bool × β, 𝒟[($ᵗ Bool : ProbComp Bool)] {v} ∂𝒟[m] := by
    rw [lintegral_const, measure_univ, mul_one]
  unfold postPred
  rw [evalDist_bind_apply_local, evalDist_bind_apply_local, evalDist_bind_apply_local]
  conv_lhs => rw [hcoin]
  rw [← lintegral_add_left Measurable.of_discrete,
    ← lintegral_add_left Measurable.of_discrete]
  refine lintegral_congr fun x => ?_
  dsimp only
  by_cases hp₁ : p₁ x.2 = true <;> by_cases hp₂ : p₂ x.2 = true
  · exact False.elim (hdisj x.2 ⟨hp₁, hp₂⟩)
  · have hp₂f : p₂ x.2 = false := Bool.eq_false_iff.mpr hp₂
    simp only [hp₁, hp₂f, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
  · have hp₁f : p₁ x.2 = false := Bool.eq_false_iff.mpr hp₁
    simp only [hp₁f, hp₂, Bool.false_or, Bool.false_eq_true, ↓reduceIte, add_comm]
  · have hp₁f : p₁ x.2 = false := Bool.eq_false_iff.mpr hp₁
    have hp₂f : p₂ x.2 = false := Bool.eq_false_iff.mpr hp₂
    simp only [hp₁f, hp₂f, Bool.false_or, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma boolDist_postPred_or_le {β : Type} (p₁ p₂ : β → Bool)
    (hdisj : ∀ c, ¬(p₁ c = true ∧ p₂ c = true))
    (m₁ m₂ : ProbComp (Bool × β)) :
    𝒟[postPred (fun c => p₁ c || p₂ c) m₁].boolDist
        𝒟[postPred (fun c => p₁ c || p₂ c) m₂] ≤
      𝒟[postPred p₁ m₁].boolDist 𝒟[postPred p₁ m₂] +
        𝒟[postPred p₂ m₁].boolDist 𝒟[postPred p₂ m₂] := by
  refine Measure.boolDist_le_of_apply_le _ _ fun v => ?_
  set u := 𝒟[($ᵗ Bool : ProbComp Bool)] {v}
  have hu : u ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.add_le_add_iff_right hu,
    evalDist_postPred_or_add_coin p₁ p₂ hdisj m₁ v]
  calc 𝒟[postPred p₁ m₁] {v} + 𝒟[postPred p₂ m₁] {v}
      ≤ (𝒟[postPred p₁ m₂] {v} + 𝒟[postPred p₁ m₁].boolDist 𝒟[postPred p₁ m₂]) +
          (𝒟[postPred p₂ m₂] {v} + 𝒟[postPred p₂ m₁].boolDist 𝒟[postPred p₂ m₂]) :=
        add_le_add (apply_le_add_boolDist_local _ _ v) (apply_le_add_boolDist_local _ _ v)
    _ = (𝒟[postPred p₁ m₂] {v} + 𝒟[postPred p₂ m₂] {v}) +
          (𝒟[postPred p₁ m₁].boolDist 𝒟[postPred p₁ m₂] +
            𝒟[postPred p₂ m₁].boolDist 𝒟[postPred p₂ m₂]) := by ring
    _ = 𝒟[postPred (fun c => p₁ c || p₂ c) m₂] {v} +
          (𝒟[postPred p₁ m₁].boolDist 𝒟[postPred p₁ m₂] +
            𝒟[postPred p₂ m₁].boolDist 𝒟[postPred p₂ m₂]) + u := by
        rw [← evalDist_postPred_or_add_coin p₁ p₂ hdisj m₂ v]; ring

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma boolDist_postPred_finset_le {β : Type} [DecidableEq β] [BEq β] [LawfulBEq β]
    (S : Finset β) (m₁ m₂ : ProbComp (Bool × β)) :
    𝒟[postPred (fun c => decide (c ∈ S)) m₁].boolDist
        𝒟[postPred (fun c => decide (c ∈ S)) m₂] ≤
      ∑ b ∈ S, 𝒟[postPred (fun c => c == b) m₁].boolDist
        𝒟[postPred (fun c => c == b) m₂] := by
  induction S using Finset.induction_on with
  | empty =>
    have h0 : ∀ m : ProbComp (Bool × β), 𝒟[postPred (fun c => decide (c ∈ (∅ : Finset β))) m] =
        𝒟[($ᵗ Bool : ProbComp Bool)] := fun m => by
      unfold postPred
      simp only [Finset.notMem_empty, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact OracleComp.evalDist_bind_const _ _
    rw [h0 m₁, h0 m₂, Measure.boolDist_self, Finset.sum_empty]
  | @insert a s ha ih =>
    have heq : (fun c : β => decide (c ∈ insert a s)) =
        (fun c : β => (c == a) || decide (c ∈ s)) := by
      ext c
      apply Bool.eq_iff_iff.mpr
      simp [Finset.mem_insert]
    rw [heq, Finset.sum_insert ha]
    refine (boolDist_postPred_or_le (fun c => c == a) (fun c => decide (c ∈ s)) ?_ m₁ m₂).trans
      (add_le_add le_rfl ih)
    intro c ⟨h1, h2⟩
    have hca : c = a := beq_iff_eq.mp h1
    have hcs : c ∈ s := decide_eq_true_eq.mp h2
    exact ha (hca ▸ hcs)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma lastLeakGuessAdmissible_eq_decide_mem (Δ t : ℕ) (_hΔ : 0 < Δ) (c : Option ℕ) :
    lastLeakGuessAdmissible Δ c t = decide (c ∈ admissibleLastLeakGuesses Δ t) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  constructor
  · intro hv
    unfold admissibleLastLeakGuesses
    rcases hc : c with _ | l
    · simp
    · rw [hc] at hv
      unfold lastLeakGuessAdmissible healedBy at hv
      simp only [decide_eq_true_eq] at hv
      simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
        Option.some.injEq, exists_eq_right, false_or]
      omega
  · intro hm
    unfold admissibleLastLeakGuesses at hm
    rcases c with _ | l
    · rfl
    · simp only [Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_range,
        Option.some.injEq, exists_eq_right, false_or] at hm
      unfold lastLeakGuessAdmissible healedBy
      simp only [decide_eq_true_eq]
      omega

omit [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I] in
private lemma boolBias_mix_fsCoin_eq_lintegral {α β : Type} (oa : ProbComp α)
    (fsFam : α → FSAEADScheme K SS RS (Header T) M E)
    (C : α → FSAEAD.AdversaryComp SS RS (Header T) M E β) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
        (show FSAEAD.Adversary SS RS (Header T) M E from
          show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from C o >>= fun _ => sampleT Bool)].boolBias =
      ∫⁻ o, FSAEAD.advantage (fsFam o)
        (show FSAEAD.Adversary SS RS (Header T) M E from
          show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from C o >>= fun _ => sampleT Bool) ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  let W : α → ProbComp Bool := fun o => do
    let b ← $ᵗ Bool
    let k ← $ᵗ K
    let (_, st) ← (simulateQ (PrivL15.fsFullImpl (fsFam o)) (C o)).run (FSAEAD.initState (fsFam o) k b)
    pure st.win
  have hgame : 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
        (show FSAEAD.Adversary SS RS (Header T) M E from
          show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from C o >>= fun _ => sampleT Bool)] =
      𝒟[(oa >>= W) >>= fun w => if w then pure true else ($ᵗ Bool : ProbComp Bool)] := by
    rw [bind_assoc]
    refine evalDist_bind_congr oa _ _ fun o => ?_
    refine DEq.evalDist_eq ?_
    unfold FSAEAD.game W
    simp only [bind_assoc, pure_bind]
    refine DEq.bind_right _ fun b => DEq.bind_right _ fun k => ?_
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine DEq.bind_right _ fun z => PrivL15.DEq.of_evalDist_eq ?_
    exact PrivL15.evalDist_coin_or_win (fsFam o) b z.2
  rw [hgame, PrivL15.boolBias_coin_or_win, evalDist_bind_apply_local]
  refine lintegral_congr fun o => ?_
  exact (PrivL15.advantage_bind_sampleT_bool (fs := fsFam o) (C o)).symm

private lemma boolDist_branch_redPRNGPriv_game_le_local
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E)
    (hvalid : lastLeakGuessAdmissible (2 + Δcka) tL t = true) :
    𝒟[PRFPRNG.branch prng true (redPRNGPriv cka prng fs lam Δcka qep tL t A)].boolDist
        𝒟[FSAEAD.game fs (redFSPriv cka prng fs lam Δcka qep tL t A)] ≤
      FSAEAD.advantage fs (redFSPrivCoin cka prng fs lam Δcka qep tL t A) := by
  rw [PrivL15.branch_true_eq_eager]
  simp only [PrivL15.simulateQ_redPRNGPriv]
  rw [PrivL15.evalDist_swap_three, PrivL15.evalDist_game_redFSPriv,
    PrivL15.advantage_redFSPrivCoin]
  refine PrivL15.boolDist_le_of_closeBy ?_
  refine PrivL15.closeBy_bind ($ᵗ Bool) fun b => ?_
  refine PrivL15.closeBy_bind ($ᵗ K) fun k_fs => ?_
  simp only [PrivL15.runHM_initPRNG_eq, PrivL15.runHM_initFS_eq, bind_assoc]
  refine PrivL15.closeBy_bind ($ᵗ KR) fun kr => ?_
  refine PrivL15.closeBy_bind ($ᵗ KC) fun kc => ?_
  exact PrivL15.closeBy_init_after_keys cka prng fs lam Δcka qep tL t A hvalid b k_fs kr kc

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
private lemma canon_zero_eq_none {St Msg C : Type} (s : GameState St Msg C) :
    canon 0 s = none := by
  unfold canon
  have hf : s.leaks.filter (fun l => decide (l < 0)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro l _; simp
  rw [hf]
  rfl

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
private lemma evalDist_postPred_rawReal_all
    (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[postPred (fun c => decide (c ∈ admissibleLastLeakGuesses (2 + Δcka) t))
        (do
          let b ← $ᵗ Bool
          let p ← SM.run (scheme cka prng fs lam) (2 + Δcka) qep (Config.priv t) b A
          pure (b == p.1, canon t p.2))] =
      𝒟[privAllGame (scheme cka prng fs lam) (2 + Δcka) qep t A] := by
  unfold postPred privAllGame
  simp only [bind_assoc, pure_bind,
    ← lastLeakGuessAdmissible_eq_decide_mem (2 + Δcka) t (by omega)]

omit [DecidableEq I] [SampleableType I] [SampleableType K] in
private lemma evalDist_postPred_rawReal_at
    (tL : Option ℕ) (t : ℕ) (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[postPred (fun c => c == tL)
        (do
          let b ← $ᵗ Bool
          let p ← SM.run (scheme cka prng fs lam) (2 + Δcka) qep (Config.priv t) b A
          pure (b == p.1, canon t p.2))] =
      𝒟[privGame (scheme cka prng fs lam) (2 + Δcka) qep tL t A] := by
  unfold postPred privGame
  simp only [bind_assoc, pure_bind, hvg, Bool.true_and]

private def rawUni (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    ProbComp (Bool × Option ℕ) := do
  let kc ← $ᵗ KC
  let b ← $ᵗ Bool
  let r ← (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
    (runCKAUUni cka prng fs lam Δcka qep t b A)).run (CKA.initState cka kc false)
  match r.1 with
  | none => pure (false, some t)
  | some (b', es) => pure (b == b', if es.abort then some t else canon t es.g)

omit [DecidableEq I] in
private lemma evalDist_postPred_rawUni_all
    (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[postPred (fun c => decide (c ∈ admissibleLastLeakGuesses (2 + Δcka) t))
        (rawUni cka prng fs lam Δcka qep t A)] =
      𝒟[CKA.branch cka Δcka 0 false (redCKAPrivUUniAll cka prng fs lam Δcka qep t A)] := by
  have hnot_mem : some t ∉ admissibleLastLeakGuesses (2 + Δcka) t := by
    intro hm
    have hv := (Bool.eq_iff_iff.mp (lastLeakGuessAdmissible_eq_decide_mem (2 + Δcka) t (by omega) (some t))).mpr
      (decide_eq_true hm)
    unfold lastLeakGuessAdmissible healedBy at hv
    simp only [decide_eq_true_eq] at hv
    omega
  refine DEq.evalDist_eq ?_
  unfold postPred rawUni
  rw [bind_assoc]
  unfold CKA.branch
  change DEq _ (do
    let kc ← $ᵗ KC
    Prod.fst <$> (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
      (redCKAPrivUUniAll cka prng fs lam Δcka qep t A)).run (CKA.initState cka kc false))
  refine DEq.bind_right ($ᵗ KC) fun kc => ?_
  unfold redCKAPrivUUniAll
  dsimp only
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, PrivL15.simulateQ_outerFull_sampleT,
    bind_map_left, map_bind]
  refine DEq.bind_right ($ᵗ Bool) fun b => DEq.bind_right _ fun ⟨r, os₁⟩ => ?_
  cases r with
  | none =>
    simp [hnot_mem, PrivL15.simulateQ_outerFull_sampleT]
    exact DEq.refl _
  | some bes =>
    rcases bes with ⟨b', es⟩
    cases hab : es.abort
    · simp only [hab, Bool.false_eq_true, ↓reduceIte, pure_bind, privValidUni, Bool.not_false,
        Bool.true_and, lastLeakGuessAdmissible_eq_decide_mem (2 + Δcka) t (by omega)]
      split <;> simp [PrivL15.simulateQ_outerFull_sampleT] <;> exact DEq.refl _
    · simp [hab, hnot_mem, privValidUni, PrivL15.simulateQ_outerFull_sampleT]
      exact DEq.refl _

omit [DecidableEq I] in
private lemma evalDist_postPred_rawUni_at
    (tL : Option ℕ) (t : ℕ) (hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[postPred (fun c => c == tL)
        (rawUni cka prng fs lam Δcka qep t A)] =
      𝒟[CKA.branch cka Δcka 0 false (redCKAPrivUUniAt cka prng fs lam Δcka qep tL t A)] := by
  have hne : some t ≠ tL := by
    intro heq
    rw [← heq] at hvg
    unfold lastLeakGuessAdmissible healedBy at hvg
    simp only [decide_eq_true_eq] at hvg
    omega
  refine DEq.evalDist_eq ?_
  unfold postPred rawUni
  rw [bind_assoc]
  unfold CKA.branch
  change DEq _ (do
    let kc ← $ᵗ KC
    Prod.fst <$> (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
      (redCKAPrivUUniAt cka prng fs lam Δcka qep tL t A)).run (CKA.initState cka kc false))
  refine DEq.bind_right ($ᵗ KC) fun kc => ?_
  unfold redCKAPrivUUniAt
  dsimp only
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, PrivL15.simulateQ_outerFull_sampleT,
    bind_map_left, map_bind]
  refine DEq.bind_right ($ᵗ Bool) fun b => DEq.bind_right _ fun ⟨r, os₁⟩ => ?_
  cases r with
  | none =>
    simp [hne, PrivL15.simulateQ_outerFull_sampleT]
    exact DEq.refl _
  | some bes =>
    rcases bes with ⟨b', es⟩
    have hpo := PrivL15.simulateQ_outerFull_privOut (CKA.oracleImpl cka Δcka 0) (2 + Δcka)
      (Mode.mk false tL t).policy b b' es os₁
    change Prod.fst <$> (simulateQ (PrivL15.outerFull (CKA.oracleImpl cka Δcka 0))
        (Engine.privOut (2 + Δcka) ⟨false, tL, t⟩ b b' es)).run os₁ = _ at hpo
    rw [hpo]
    unfold PrivL15.privOutP Mode.policy
    cases hab : es.abort
    · simp [hab, hvg]
      exact DEq.refl _
    · simp [hab, hne]
      exact DEq.refl _

/-- Mixture (`oa : ProbComp α`) Stage-2 switch-back Theorem 12: bounds the unified epoch-`t`
mixture privacy bias by one unified mixture FS-AEAD hop (`redFSPrivUni` + `2 * redFSPrivUniCoin`)
plus, for each admissible `tL`, `2` times the mixture `boolDist` of `redCKAPriv`, `redCKAPrivU`,
and `redPRNGPriv`. -/
theorem theorem12_stage2_mix {α : Type} (hc : cka.Correct) (oa : ProbComp α)
    (fsFam : α → FSAEADScheme K SS RS (Header T) M E) (t : ℕ)
    (A : α → SchemeAdversary Γ T Sig SS RS M CCoins E) :
    𝒟[oa >>= fun o => privAllGame (scheme cka prng (fsFam o) lam) (2 + Δcka) qep t (A o)].boolBias ≤
      (∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
          (2 * (𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
                (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
                (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))])
            + 2 * (𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
                (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
                (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))])
            + 2 * (𝒟[oa >>= fun o => PRFPRNG.branch prng true
                (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => PRFPRNG.branch prng false
                (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))])))
        + 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
            (redFSPrivUni cka prng (fsFam o) lam Δcka qep t (A o))].boolBias
        + 2 * 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
            (redFSPrivUniCoin cka prng (fsFam o) lam Δcka qep t (A o))].boolBias := by
  let _ : MeasurableSpace α := ⊤
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hadm0 : admissibleLastLeakGuesses (2 + Δcka) 0 = {none} := by
      unfold admissibleLastLeakGuesses
      have hr : 0 + 1 - (2 + Δcka) = 0 := by omega
      simp [hr]
    have hpriv0 : ∀ o, privAllGame (scheme cka prng (fsFam o) lam) (2 + Δcka) qep 0 (A o) =
        privGame (scheme cka prng (fsFam o) lam) (2 + Δcka) qep none 0 (A o) := fun o => by
      unfold privAllGame privGame
      refine bind_congr fun b => bind_congr fun p => ?_
      rcases p with ⟨b', s⟩
      dsimp only
      rw [canon_zero_eq_none s]
      rfl
    have hpol0 : polUni12 Δcka 0 = (Mode.mk false none 0).policy := by
      unfold polUni12 Mode.policy; simp
    have hfs0 : ∀ o, redFSPrivUni cka prng (fsFam o) lam Δcka qep 0 (A o) =
        redFSPriv cka prng (fsFam o) lam Δcka qep none 0 (A o) := fun o => by
      unfold redFSPrivUni redFSPriv runFSUni runFS
      rw [hpol0]
      refine bind_congr fun r => ?_
      cases r with
      | none => rfl
      | some bes =>
        rcases bes with ⟨b', es⟩
        have hv : privValidUni (2 + Δcka) 0 es = Engine.privValid (2 + Δcka) ⟨false, none, 0⟩ es := by
          unfold privValidUni Engine.privValid
          rw [canon_zero_eq_none es.g]
          simp
        simp [hv]
    have hfsc0 : ∀ o, redFSPrivUniCoin cka prng (fsFam o) lam Δcka qep 0 (A o) =
        redFSPrivCoin cka prng (fsFam o) lam Δcka qep none 0 (A o) := fun o => by
      unfold redFSPrivUniCoin redFSPrivCoin runFSUni runFS
      rw [hpol0]; rfl
    rw [hadm0, Finset.sum_singleton]
    simp_rw [hpriv0, hfs0, hfsc0]
    set cT := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch none) true
      (redCKAPriv cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set cF := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch none) false
      (redCKAPriv cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set cUT := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch none) true
      (redCKAPrivU cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set cUF := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch none) false
      (redCKAPrivU cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set pT := 𝒟[oa >>= fun o => PRFPRNG.branch prng true
      (redPRNGPriv cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set pF := 𝒟[oa >>= fun o => PRFPRNG.branch prng false
      (redPRNGPriv cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set G := 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
      (redFSPriv cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    set GC := 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
      (redFSPrivCoin cka prng (fsFam o) lam Δcka qep none 0 (A o))]
    have h13 : 𝒟[oa >>= fun o =>
        privGame (scheme cka prng (fsFam o) lam) (2 + Δcka) qep none 0 (A o)] = cF :=
      evalDist_bind_congr oa _ _ fun o =>
        (PrivL13.privGame_dEq_redCKAPriv cka prng (fsFam o) lam Δcka qep none 0 hc (A o)).evalDist_eq
    have h14 : cT = pF :=
      evalDist_bind_congr oa _ _ fun o =>
        (PrivL14.branch_redCKAPriv_dEq_redPRNGPriv cka prng (fsFam o) lam Δcka qep none 0 (A o)).evalDist_eq
    have hGC : GC.boolBias =
        ∫⁻ o, FSAEAD.advantage (fsFam o)
          (redFSPrivCoin cka prng (fsFam o) lam Δcka qep none 0 (A o)) ∂𝒟[oa] :=
      boolBias_mix_fsCoin_eq_lintegral oa fsFam
        (fun o => runFS cka prng (fsFam o) lam Δcka qep ⟨false, none, 0⟩ 0 false (A o))
    have h15 : pT.boolDist G ≤ GC.boolBias := by
      rw [hGC]
      exact (boolDist_bind_le_lintegral_local oa _ _).trans (lintegral_mono fun o =>
        boolDist_branch_redPRNGPriv_game_le_local cka prng (fsFam o) lam Δcka qep none 0 (A o) rfl)
    have hc' : cF.boolBias ≤ cT.boolBias + 2 * cT.boolDist cF := by
      rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist cF cT
    have hp' : pF.boolBias ≤ pT.boolBias + 2 * pT.boolDist pF := by
      rw [Measure.boolDist_comm]; exact boolBias_le_add_two_mul_boolDist pF pT
    have hg : pT.boolBias ≤ G.boolBias + 2 * pT.boolDist G :=
      boolBias_le_add_two_mul_boolDist pT G
    rw [h13]
    calc cF.boolBias
        ≤ cT.boolBias + 2 * cT.boolDist cF := hc'
      _ ≤ (pT.boolBias + 2 * pT.boolDist pF) + 2 * cT.boolDist cF := by
          rw [h14]; exact add_le_add hp' le_rfl
      _ ≤ ((G.boolBias + 2 * GC.boolBias) + 2 * pT.boolDist pF) + 2 * cT.boolDist cF := by
          gcongr; exact hg.trans (add_le_add le_rfl (mul_le_mul_right h15 2))
      _ = (2 * cT.boolDist cF + 0 + 2 * pT.boolDist pF) + G.boolBias + 2 * GC.boolBias := by ring
      _ ≤ (2 * cT.boolDist cF + 2 * cUT.boolDist cUF + 2 * pT.boolDist pF) +
            G.boolBias + 2 * GC.boolBias := by gcongr; exact zero_le
  · -- Case `0 < t`
    set G0 := 𝒟[oa >>= fun o => privAllGame (scheme cka prng (fsFam o) lam) (2 + Δcka) qep t (A o)]
    set GU := 𝒟[oa >>= fun o => CKA.branch cka Δcka 0 false
      (redCKAPrivUUniAll cka prng (fsFam o) lam Δcka qep t (A o))]
    set GFS := 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
      (redFSPrivUni cka prng (fsFam o) lam Δcka qep t (A o))]
    set GFSC := 𝒟[oa >>= fun o => FSAEAD.game (fsFam o)
      (redFSPrivUniCoin cka prng (fsFam o) lam Δcka qep t (A o))]
    have hGFSC : GFSC.boolBias =
        ∫⁻ o, FSAEAD.advantage (fsFam o)
          (redFSPrivUniCoin cka prng (fsFam o) lam Δcka qep t (A o)) ∂𝒟[oa] :=
      boolBias_mix_fsCoin_eq_lintegral oa fsFam
        (fun o => runFSUni cka prng (fsFam o) lam Δcka qep t false (A o))
    have h15U : GU.boolDist GFS ≤ GFSC.boolBias := by
      rw [hGFSC]
      exact (boolDist_bind_le_lintegral_local oa _ _).trans (lintegral_mono fun o =>
        boolDist_redCKAPrivUUniAll_redFSPrivUni_le cka prng (fsFam o) lam Δcka qep t ht (A o))
    let mReal : ProbComp (Bool × Option ℕ) := oa >>= fun o => do
      let b ← $ᵗ Bool
      let p ← SM.run (scheme cka prng (fsFam o) lam) (2 + Δcka) qep (Config.priv t) b (A o)
      pure (b == p.1, canon t p.2)
    let mUni : ProbComp (Bool × Option ℕ) := oa >>= fun o =>
      rawUni cka prng (fsFam o) lam Δcka qep t (A o)
    have hG0_eq : G0 = 𝒟[postPred (fun c => decide (c ∈ admissibleLastLeakGuesses (2 + Δcka) t)) mReal] := by
      symm
      unfold postPred mReal G0
      rw [bind_assoc]
      exact evalDist_bind_congr oa _ _ fun o =>
        evalDist_postPred_rawReal_all cka prng (fsFam o) lam Δcka qep t (A o)
    have hGU_eq : GU = 𝒟[postPred (fun c => decide (c ∈ admissibleLastLeakGuesses (2 + Δcka) t)) mUni] := by
      symm
      unfold postPred mUni GU
      rw [bind_assoc]
      exact evalDist_bind_congr oa _ _ fun o =>
        evalDist_postPred_rawUni_all cka prng (fsFam o) lam Δcka qep t (A o)
    have hUnion : G0.boolDist GU ≤
        ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
          𝒟[postPred (fun c => c == tL) mReal].boolDist
            𝒟[postPred (fun c => c == tL) mUni] := by
      rw [hG0_eq, hGU_eq]
      exact boolDist_postPred_finset_le (admissibleLastLeakGuesses (2 + Δcka) t) mReal mUni
    have hPerTL : ∀ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
        2 * (𝒟[postPred (fun c => c == tL) mReal].boolDist
              𝒟[postPred (fun c => c == tL) mUni]) ≤
          2 * (𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
                (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
                (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))])
            + 2 * (𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
                (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
                (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))])
            + 2 * (𝒟[oa >>= fun o => PRFPRNG.branch prng true
                (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))].boolDist
              𝒟[oa >>= fun o => PRFPRNG.branch prng false
                (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))]) := by
      intro tL htL
      have hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true := by
        rw [lastLeakGuessAdmissible_eq_decide_mem (2 + Δcka) t (by omega) tL]
        exact decide_eq_true htL
      set cT := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
        (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))]
      set cF := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
        (redCKAPriv cka prng (fsFam o) lam Δcka qep tL t (A o))]
      set cUT := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) true
        (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))]
      set cUF := 𝒟[oa >>= fun o => CKA.branch cka Δcka (healEpoch tL) false
        (redCKAPrivU cka prng (fsFam o) lam Δcka qep tL t (A o))]
      set pT := 𝒟[oa >>= fun o => PRFPRNG.branch prng true
        (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))]
      set pF := 𝒟[oa >>= fun o => PRFPRNG.branch prng false
        (redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o))]
      have hmR : 𝒟[postPred (fun c => c == tL) mReal] = cF := by
        have hbindR : postPred (fun c => c == tL) mReal =
            (oa >>= fun o => postPred (fun c => c == tL) (do
              let b ← $ᵗ Bool
              let p ← SM.run (scheme cka prng (fsFam o) lam) (2 + Δcka) qep (Config.priv t) b (A o)
              pure (b == p.1, canon t p.2))) := by
          unfold postPred mReal; rw [bind_assoc]
        rw [hbindR]
        refine evalDist_bind_congr oa _ _ fun o => ?_
        rw [evalDist_postPred_rawReal_at cka prng (fsFam o) lam Δcka qep tL t hvg (A o)]
        exact (PrivL13.privGame_dEq_redCKAPriv cka prng (fsFam o) lam Δcka qep tL t hc (A o)).evalDist_eq
      have hmU : 𝒟[postPred (fun c => c == tL) mUni] = cUF := by
        have hbindU : postPred (fun c => c == tL) mUni =
            (oa >>= fun o => postPred (fun c => c == tL)
              (rawUni cka prng (fsFam o) lam Δcka qep t (A o))) := by
          unfold postPred mUni; rw [bind_assoc]
        rw [hbindU]
        refine evalDist_bind_congr oa _ _ fun o => ?_
        rw [evalDist_postPred_rawUni_at cka prng (fsFam o) lam Δcka qep tL t hvg (A o)]
        exact (PrivL13U.branch_redCKAPrivUUniAt_dEq_redCKAPrivU_false cka prng (fsFam o) lam Δcka qep
          hc tL t ht hvg (A o)).evalDist_eq
      have h14 : cT = pF :=
        evalDist_bind_congr oa _ _ fun o =>
          (PrivL14.branch_redCKAPriv_dEq_redPRNGPriv cka prng (fsFam o) lam Δcka qep tL t (A o)).evalDist_eq
      have h14U : cUT = pT :=
        evalDist_bind_congr oa _ _ fun o =>
          (branch_redCKAPrivU_true_dEq_redPRNGPriv_true cka prng (fsFam o) lam Δcka qep
            tL t ht hvg (A o)).evalDist_eq
      rw [hmR, hmU]
      have htri : cF.boolDist cUF ≤ cT.boolDist cF + cUT.boolDist cUF + pT.boolDist pF := by
        calc cF.boolDist cUF
            ≤ cF.boolDist cT + cT.boolDist cUF := Measure.boolDist_triangle cF cT cUF
          _ ≤ cF.boolDist cT + (cT.boolDist pT + pT.boolDist cUF) :=
              add_le_add le_rfl (Measure.boolDist_triangle cT pT cUF)
          _ = cT.boolDist cF + cUT.boolDist cUF + pT.boolDist pF := by
              rw [Measure.boolDist_comm cF cT, h14, Measure.boolDist_comm pF pT, ← h14U]
              ring
      calc 2 * cF.boolDist cUF
          ≤ 2 * (cT.boolDist cF + cUT.boolDist cUF + pT.boolDist pF) := by gcongr
        _ = 2 * cT.boolDist cF + 2 * cUT.boolDist cUF + 2 * pT.boolDist pF := by ring
    have h0U : G0.boolBias ≤ GU.boolBias + 2 * G0.boolDist GU :=
      boolBias_le_add_two_mul_boolDist G0 GU
    have hUFS : GU.boolBias ≤ GFS.boolBias + 2 * GU.boolDist GFS :=
      boolBias_le_add_two_mul_boolDist GU GFS
    calc G0.boolBias
        ≤ GU.boolBias + 2 * G0.boolDist GU := h0U
      _ ≤ (GFS.boolBias + 2 * GFSC.boolBias) +
            2 * ∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
              𝒟[postPred (fun c => c == tL) mReal].boolDist
                𝒟[postPred (fun c => c == tL) mUni] := by
          refine add_le_add ?_ (by gcongr)
          exact hUFS.trans (add_le_add le_rfl (by gcongr))
      _ = (∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
              2 * 𝒟[postPred (fun c => c == tL) mReal].boolDist
                𝒟[postPred (fun c => c == tL) mUni]) +
            GFS.boolBias + 2 * GFSC.boolBias := by
          rw [Finset.mul_sum]; ring
      _ ≤ _ := add_le_add (add_le_add (Finset.sum_le_sum hPerTL) le_rfl) le_rfl

/-- Stage-2 switch-back Theorem 12: bounds the unified epoch-`t` privacy advantage
`privAllAdvantage` by one unified FS-AEAD term (`redFSPrivUni` + `2 * redFSPrivUniCoin`) plus, for
each admissible `tL`, `2 * CKA(redCKAPriv)` + `2 * CKA(redCKAPrivU)` + `2 * PRNG(redPRNGPriv)`. -/
theorem theorem12_stage2 (hc : cka.Correct) (t : ℕ)
    (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    privAllAdvantage (scheme cka prng fs lam) (2 + Δcka) qep t A ≤
      (∑ tL ∈ admissibleLastLeakGuesses (2 + Δcka) t,
          (2 * CKA.advantage cka Δcka (healEpoch tL)
              (redCKAPriv cka prng fs lam Δcka qep tL t A)
            + 2 * CKA.advantage cka Δcka (healEpoch tL)
              (redCKAPrivU cka prng fs lam Δcka qep tL t A)
            + 2 * PRFPRNG.advantage prng
              (redPRNGPriv cka prng fs lam Δcka qep tL t A)))
        + FSAEAD.advantage fs (redFSPrivUni cka prng fs lam Δcka qep t A)
        + 2 * FSAEAD.advantage fs (redFSPrivUniCoin cka prng fs lam Δcka qep t A) := by
  have h := theorem12_stage2_mix cka prng lam Δcka qep hc (pure ()) (fun _ => fs) t (fun _ => A)
  simpa only [pure_bind, privAllAdvantage, CKA.advantage_eq_boolDist, PRFPRNG.advantage_eq_boolDist,
    FSAEAD.advantage] using h

end Stage2SwitchBack

end CryptoGames.SM.Construction
