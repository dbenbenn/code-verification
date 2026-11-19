/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import VCVio.CryptoFoundations.PRG
import ProofLib.Lemmas

/-!
# Prefix-Averaged PRG and PRF Distinguishers

Defines the prefix-averaged distinguishers `prgAvg` and `prfAvg` (`o ← oa; D o`) and proves that
their PRG real/ideal and PRF branch distributions equal the `oa`-mixtures of the `D o` worlds.
-/

public section

open OracleComp OracleSpec MeasureTheory ENNReal

namespace CryptoVerification.E2E.Signed

/-! ## PRG mixtures -/

section PRG

variable {S R : Type}

/-- Prefix-averaged PRG distinguisher sampling `o` from `oa` before running `D o`. -/
@[expose] def prgAvg {α : Type} (oa : ProbComp α) (D : α → PRGScheme.PRGAdversary R) :
    PRGScheme.PRGAdversary R := fun r => oa >>= fun o => D o r

theorem prgReal_avg {α : Type} [SampleableType S] (prg : PRGScheme S R) (oa : ProbComp α)
    (D : α → PRGScheme.PRGAdversary R) :
    𝒟[prg.prgRealExperiment (prgAvg oa D)] =
      𝒟[oa >>= fun o => prg.prgRealExperiment (D o)] := by
  unfold PRGScheme.prgRealExperiment prgAvg
  exact evalDist_bind_bind_swap_of_uniform _ _ _

theorem prgIdeal_avg {α : Type} [SampleableType R] (oa : ProbComp α) (D : α →
PRGScheme.PRGAdversary R) :
    𝒟[PRGScheme.prgIdealExperiment (prgAvg oa D)] =
      𝒟[oa >>= fun o => PRGScheme.prgIdealExperiment (D o)] := by
  unfold PRGScheme.prgIdealExperiment prgAvg
  exact evalDist_bind_bind_swap_of_uniform _ _ _

end PRG

/-! ## PRF mixtures -/

section PRF

open CryptoGames

variable {Key Input Tag : Type} [DecidableEq Input] [SampleableType Tag]

/-- Prefix-averaged PRF distinguisher sampling `o` from `oa` before running `D o`. -/
@[expose] def prfAvg {α : Type} (oa : ProbComp α) (D : α → MACScheme.PRFAdversary Input Tag) :
    MACScheme.PRFAdversary Input Tag :=
  bind (m := OracleComp (unifSpec + MACScheme.prfSpec Input Tag))
    (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α) D

theorem simulateQ_prfImpl_liftM_run {α : Type} (mac : MACScheme Key Input Tag)
    (oa : ProbComp α) (st : MACScheme.PRFState Key Input Tag) :
    (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT (MACScheme.PRFState Key Input Tag) ProbComp) + MACScheme.prfEval mac)
      (liftM oa : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α)).run st =
      oa >>= fun a => pure (a, st) := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change ((liftM (OracleSpec.query (spec := unifSpec) t) : ProbComp _) >>= fun u =>
        (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (MACScheme.PRFState Key Input Tag) ProbComp) + MACScheme.prfEval mac)
          (liftM (k u) : OracleComp (unifSpec + MACScheme.prfSpec Input Tag) α)).run st) = _
    simp only [ih, bind_assoc]

/-- World `b` of `prfAvg oa D` is the `oa`-mixture of the `D o` worlds. -/
theorem prfBranch_avg {α : Type} [SampleableType Key] (mac : MACScheme Key Input Tag) (b : Bool)
    (oa : ProbComp α) (D : α → MACScheme.PRFAdversary Input Tag) :
    𝒟[mac.branch b (prfAvg oa D)] = 𝒟[oa >>= fun o => mac.branch b (D o)] := by
  unfold MACScheme.branch prfAvg
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, simulateQ_prfImpl_liftM_run,
    bind_assoc, pure_bind, map_bind]
  exact OracleComp.evalDist_bind_bind_swap _ _ _

end PRF

/-! ## Prefix integration helpers -/

section Integrate

theorem evalDist_bind_apply_lintegral {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (v : Bool) :
    letI : MeasurableSpace α := ⊤
    𝒟[oa >>= f] {v} = ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_of_discrete,
    Measure.bind_apply MeasurableSet.of_discrete Measurable.of_discrete.aemeasurable]

theorem evalDist_bind_apply_le_add {α : Type} (oa : ProbComp α) (f g h : α → ProbComp Bool)
    (c : ℝ≥0∞) (v w : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + (c + 𝒟[h a] {w})) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + (c + 𝒟[oa >>= h] {w}) := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral,
    evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + (c + 𝒟[h a] {w})) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + (c + ∫⁻ a, 𝒟[h a] {w} ∂𝒟[oa]) := by
      rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left measurable_const,
        lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem evalDist_bind_apply_le_add_const {α : Type} (oa : ProbComp α) (f g : α → ProbComp Bool)
    (c : ℝ≥0∞) (v : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ 𝒟[g a] {v} + c) :
    𝒟[oa >>= f] {v} ≤ 𝒟[oa >>= g] {v} + c := by
  let _ : MeasurableSpace α := ⊤
  have _ : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
  rw [evalDist_bind_apply_lintegral, evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa]
      ≤ ∫⁻ a, (𝒟[g a] {v} + c) ∂𝒟[oa] := lintegral_mono H
    _ = ∫⁻ a, 𝒟[g a] {v} ∂𝒟[oa] + c := by
      rw [lintegral_add_right _ measurable_const, lintegral_const, evalDist_apply_univ_eq_one,
        mul_one]

theorem evalDist_bind_apply_le_const {α : Type} (oa : ProbComp α) (f : α → ProbComp Bool)
    (c : ℝ≥0∞) (v : Bool) (H : ∀ a, 𝒟[f a] {v} ≤ c) : 𝒟[oa >>= f] {v} ≤ c := by
  let _ : MeasurableSpace α := ⊤
  rw [evalDist_bind_apply_lintegral]
  calc ∫⁻ a, 𝒟[f a] {v} ∂𝒟[oa] ≤ ∫⁻ _a, c ∂𝒟[oa] := lintegral_mono H
    _ = c := by rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

theorem hybrid_chain_le (R T a : ℕ → ℝ≥0∞) (ε : ℝ≥0∞) (n : ℕ) (h1 : ∀ k, R k ≤ a k + T k)
    (h2 : ∀ k < n, T k ≤ R (k + 1) + ε) :
    R 0 ≤ (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
  have hm : ∀ m ≤ n, R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hmn
      calc R 0 ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + R m := ih (by omega)
        _ ≤ (∑ k ∈ Finset.range m, a k) + (m : ℝ≥0∞) * ε + (a m + (R (m + 1) + ε)) := by
          gcongr
          exact (h1 m).trans (add_le_add le_rfl (h2 m (by omega)))
        _ = (∑ k ∈ Finset.range (m + 1), a k) + ((m + 1 : ℕ) : ℝ≥0∞) * ε + R (m + 1) := by
          rw [Finset.sum_range_succ]; push_cast; ring
  calc R 0 ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + R n := hm n le_rfl
    _ ≤ (∑ k ∈ Finset.range n, a k) + (n : ℝ≥0∞) * ε + (a n + T n) := by gcongr; exact h1 n
    _ = (∑ k ∈ Finset.range (n + 1), a k) + (n : ℝ≥0∞) * ε + T n := by
      rw [Finset.sum_range_succ]; ring

end Integrate

end CryptoVerification.E2E.Signed
