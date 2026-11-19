/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhGrow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepPows -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthCoreSimSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhFinish
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepRecv
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSend
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepSmall
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

/-!
# Evaluation Equivalence for `fgAuthGapDhProg`

Proves that simulating `(fgAuthGapDhProg S b.q_total).eval` yields the same output distribution as
the shallow reduction `fgAuthGapDhAdv4 S b A`, via per-query handler equivalence and bounded
state-list invariants.
-/

public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp
open scoped ENNReal

section Dispatch

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)} [h₁ : Ext Γ₁ Δ] [h₂ : Ext Γ₂ Δ]
  [h₃ : Ext Γ₃ Δ] (env : Env Δ) (st : FgAuthSimState S) (U V : Bytes) (useDh1 : Bool)
  (t sIdx : Nat)

end Dispatch

/-- With `k` game queries still allowed, every state list has at most `K - k` entries. -/
@[expose] def AgInv {S : Setup} (K k : Nat) (st : FgAuthSimState S) : Prop :=
  k + st.base.principals.length ≤ K ∧
  k + st.base.spkBundles.length ≤ K ∧
  k + st.base.opkEntries.length ≤ K ∧
  k + st.base.sessions.length ≤ K ∧
  k + st.base.usedSendSessions.length ≤ K ∧
  k + st.base.usedRecvOPK.length ≤ K ∧
  k + st.base.usedRecvNoOPK.length ≤ K ∧
  k + st.base.seenKyberBaseKeys.length ≤ K ∧
  k + st.base.roCache.length ≤ K ∧
  k + st.base.rootRoCache.length ≤ K ∧
  k + st.base.advKeys.length ≤ K ∧
  k + st.rawRoCache.length ≤ K ∧
  k + st.advKeyPows.length ≤ K

theorem AgInv.mono {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInv K (k + 1) st) :
    AgInv K k st := by
  simp only [AgInv] at h ⊢; omega

theorem AgInv.of_grow {S : Setup} (K k : Nat) (st st' : FgAuthSimState S)
    (h : AgInv K (k + 1) st) (hg : AGrow st st') : AgInv K k st' := by
  simp only [AgInv, AGrow] at h hg ⊢; omega

theorem AgInv.empty (S : Setup) (K : Nat) (secb : Bool) :
    AgInv K K (FgAuthSimState.empty S secb) := by
  simp only [AgInv, FgAuthSimState.empty, AuthState.empty, List.length_nil, Nat.add_zero,
    Nat.le_refl, and_self]

theorem AgInv.bnd {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInv K k st) :
    AgBnd K st := by
  simp only [AgInv] at h
  exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩, by omega, by omega⟩

theorem agEmbedPrim_eq {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) :
    FgGapDh.embedPrim (spec := spec) mx = Security.embedPrim (spec := spec) mx := rfl

theorem agValToAuthResp_authRespToVal (r : AuthResponse) :
    valToAuthResp (authRespToVal r) = r := valToAuthResp_authRespToVal r

/-- `AgInv` strengthened with `respRecs` length tracking for `K`-clamped extraction. -/
def AgInvResp {S : Setup} (K k : Nat) (st : FgAuthSimState S) : Prop :=
  AgInv K k st ∧ k + st.respRecs.length ≤ K

theorem AgInvResp.mono {S : Setup} (K k : Nat) (st : FgAuthSimState S)
    (h : AgInvResp K (k + 1) st) : AgInvResp K k st :=
  ⟨h.1.mono, by have := h.2; omega⟩

theorem AgInvResp.of_grow {S : Setup} (K k : Nat) (st st' : FgAuthSimState S)
    (h : AgInvResp K (k + 1) st) (hg : AGrow st st')
    (hr : st'.respRecs.length ≤ st.respRecs.length + 1) : AgInvResp K k st' :=
  ⟨AgInv.of_grow K k st st' h.1 hg, by have := h.2; omega⟩

theorem AgInvResp.empty (S : Setup) (K : Nat) (secb : Bool) :
    AgInvResp K K (FgAuthSimState.empty S secb) :=
  ⟨AgInv.empty S K secb, by simp [FgAuthSimState.empty]⟩

theorem AgInvResp.bnd {S : Setup} (K k : Nat) (st : FgAuthSimState S) (h : AgInvResp K k st) :
    AgBnd K st := h.1.bnd

open _root_.SignalPqxdh.Security.FgGapDh (sampleIndexRange)

private theorem simulateQ_unifGdh {α : Type} (P : Primitives)
    (ddhImpl : QueryImpl gapDhOracleSpec ProbComp) (mx : ProbComp α) :
    simulateQ (primBaseImpl P + ddhImpl) (unifGdh mx) = mx := by
  unfold unifGdh FgGapDh.embedUnif
  rw [agEmbedPrim_eq]
  unfold _root_.SignalPqxdh.Security.embedPrim
  induction mx using OracleComp.inductionOn with
  | pure a =>
    simp [simulateQ_pure]
  | query_bind k cont ih =>
    rw [liftComp_bind, liftComp_query]
    simp [primBaseImpl]
    exact bind_congr ih

private theorem evalDist_sampleIndexRange_bind_singleton {N : ℕ} (hN : 0 < N)
    (g : ℕ → ProbComp Bool) (z : Bool) :
    𝒟[sampleIndexRange N >>= g] {z} =
      ∑ k ∈ Finset.range N, 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹ := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let : MeasurableSpace (Fin N) := ⊤
  simp only [sampleIndexRange, hN, ↓reduceDIte, bind_assoc, pure_bind]
  rw [evalDist_bind_of_discrete,
    MeasureTheory.Measure.bind_apply (MeasurableSet.singleton z)
      (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_fintype]
  simp_rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun k => 𝒟[g k] {z} * (N : ℝ≥0∞)⁻¹) N

private theorem sum_range_mul_div_mod_ennreal (M N : ℕ) (g : ℕ → ℕ → ℝ≥0∞) :
    ∑ k ∈ Finset.range (M * N), g (k / N) (k % N) =
      ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range N, g i j := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_one_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hPos : 0 < N := by omega
    rw [Nat.add_comm (m * N) j, Nat.add_mul_div_right j m hPos, Nat.div_eq_of_lt hj,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem mul_evalDist_sampleIndexRange {N : ℕ} (hN : 0 < N)
    (f : ℕ → ProbComp Bool) (z : Bool) :
    (N : ℝ≥0∞) * 𝒟[sampleIndexRange N >>= f] {z} =
      ∑ i ∈ Finset.range N, 𝒟[f i] {z} := by
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [evalDist_sampleIndexRange_bind_singleton hN, ← Finset.sum_mul,
    ← mul_assoc, mul_comm (N : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hN0 hNtop, mul_one]

end SignalPqxdh.Security.ReductionDsl.AuthHs
