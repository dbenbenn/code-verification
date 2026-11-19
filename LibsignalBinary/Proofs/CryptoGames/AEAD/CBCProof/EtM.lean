/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# OT-CCA security of Encrypt-then-MAC

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves one-time chosen-ciphertext (OT-CCA) security of `AEADScheme.etm` (`EtMDefs.lean`) from
one-time IND-CPA security of the cipher (`redCipher`) and PRF security of the MAC (`redMACChall`,
`redMACForge`), plus a tag-guessing term `qd / Fintype.card T` over at most `qd` decryption
queries.
-/

public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames

namespace AEADScheme

section EtM

variable {KE KM AD M C T : Type}

/-! ### Proof of `etm_otcca` -/

namespace EtMProof

variable {KE KM AD M C T : Type}

/-- A stateful simulation is preserved by a state map `F` under an invariant `I`. -/
theorem run_map {ι : Type} {spec : OracleSpec ι} {σ₁ σ₂ : Type}
    (impl₁ : QueryImpl spec (StateT σ₁ ProbComp)) (impl₂ : QueryImpl spec (StateT σ₂ ProbComp))
    (F : σ₂ → σ₁) (I : σ₂ → Prop)
    (hstep : ∀ t s, I s → (impl₁ t).run (F s) = Prod.map id F <$> (impl₂ t).run s ∧
      ∀ z ∈ support ((impl₂ t).run s), I z.2)
    {α : Type} (oa : OracleComp spec α) :
    ∀ s, I s → (simulateQ impl₁ oa).run (F s) = Prod.map id F <$> (simulateQ impl₂ oa).run s := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro s _; simp
  | query_bind t k ih =>
    intro s hI
    obtain ⟨h1, h2⟩ := hstep t s hI
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [h1, bind_map_left, map_bind]
    exact bind_congr_of_forall_mem_support _ fun z hz => ih z.1 z.2 (h2 z hz)

/-- Uniform product sampling splits into sequential uniform sampling. -/
theorem uniform_prod (α β : Type) [SampleableType α] [SampleableType β] :
    ($ᵗ (α × β) : ProbComp (α × β)) =
      (do let a ← $ᵗ α; let b ← $ᵗ β; pure (a, b)) := by
  simp only [uniformSample, SampleableType.selectElem, seq_eq_bind_map, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp_apply]
  rfl

/-- Adversary coins in any `StateT σ ProbComp`. -/
abbrev coin {σ : Type} (n : ℕ) : StateT σ ProbComp (Fin (n + 1)) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT σ ProbComp) n

theorem mem_support_coin {σ : Type} {n : ℕ} {s : σ} {z : Fin (n + 1) × σ}
    (hz : z ∈ support ((coin n : StateT σ ProbComp _).run s)) : z.2 = s := by
  simp only [coin, QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, StateT.run_monadLift,
    MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨u, _, rfl⟩ := hz
  rfl

variable [DecidableEq AD] [DecidableEq C] [DecidableEq T]

/-- Oracle implementation of `cipher.branch`. -/
@[expose] def cImpl [SampleableType C] (cipher : CipherScheme KE M C) :
    QueryImpl (unifSpec + CipherScheme.indcpaSpec M C)
      (StateT (CipherScheme.INDCPAState KE) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (CipherScheme.INDCPAState KE) ProbComp) + CipherScheme.indcpaEncrypt cipher

omit [DecidableEq C] in
theorem cipher_branch_eq [SampleableType KE] [SampleableType C]
    (cipher : CipherScheme KE M C) (b : Bool) (A : CipherScheme.INDCPAAdversary M C) :
    cipher.branch b A = (do
      let key ← $ᵗ KE
      (simulateQ (cImpl cipher) A).run' { key, b }) := rfl

/-! #### Reject-decryption flag game `implNF` -/

theorem const_true_eq_one {α : Type} (mx : ProbComp α) :
    𝒟[mx >>= fun _ => (pure true : ProbComp Bool)] {true} = 1 :=
  le_antisymm (le_trans (measure_mono (Set.subset_univ _)) (evalDist_apply_univ_eq_one _).le)
    (le_evalDist_bind_apply_of_support _ _ (measurableSet_singleton _) fun _ _ => by simp)

theorem apply_le_one {α : Type} [MeasurableSpace α] (mx : ProbComp α) (E : Set α) :
    𝒟[mx] E ≤ 1 :=
  le_trans (measure_mono (Set.subset_univ _)) (evalDist_apply_univ_eq_one _).le

/-! #### Bounding the flag via `redMACForge` -/

/-- Union bound for a flag raised before a continuation. -/
theorem union_step {α : Type} (mx : ProbComp α) (a : α → Bool) (g : α → ProbComp Bool) :
    𝒟[mx >>= fun x => (a x || ·) <$> g x] {true} ≤
      𝒟[mx >>= fun x => pure (a x)] {true} + 𝒟[mx >>= g] {true} := by
  refine evalDist_bind_apply_le_add_of_support mx _ _ _ (measurableSet_singleton _)
    fun x _ => ?_
  cases a x
  · simp
  · simp only [Bool.true_or]
    refine le_add_right ?_
    calc _ ≤ 𝒟[(Function.const Bool true <$> g x)] Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := evalDist_apply_univ_eq_one _
      _ ≤ _ := by simp

/-! #### Bounding `mac.branch true (redMACForge cipher j B)` by `(Fintype.card T)⁻¹` -/

theorem bind_le_of_support {α β : Type} [MeasurableSpace β] (mx : ProbComp α)
    (f : α → ProbComp β) {E : Set β} (hE : MeasurableSet E) {r : ℝ≥0∞}
    (h : ∀ a ∈ support mx, 𝒟[f a] E ≤ r) : 𝒟[mx >>= f] E ≤ r := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      Measure.bind_apply hE Measurable.of_discrete.aemeasurable]
    calc _ ≤ ∫⁻ _u, r ∂𝒟[(query t : ProbComp _)] :=
          lintegral_mono fun u => ih u fun a ha =>
            h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)
      _ = r := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem apply_eq_beq (mx : ProbComp Bool) (x : Bool) :
    𝒟[mx] {x} = 𝒟[(· == x) <$> mx] {true} := by
  rw [evalDist_map _ Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  congr 1; ext y; simp

end EtMProof

open EtMProof

end EtM

end AEADScheme

end CryptoGames
