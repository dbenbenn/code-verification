/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDhProofs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Soundness
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhStepBase
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthGapDhEvalEq
import Computational.Proofs.SpecLemmas.SignalPqxdh.Game
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure
public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthHandshake -- proof-setup: allow-public-import

/-!
# Cost Bounds and Advantage Wiring for `fgAuthGapDhDslAdv`

Defines the `ReductionDsl` `GapDH` adversary `fgAuthGapDhDslAdv` and establishes its step-cost,
AST-size, and query-budget bounds together with `GapDH` advantage equality against `fgAuthGapDhAdv4`.
-/

public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

abbrev fgAuthGapDhDslProg (S : Setup) (b : QueryBudget) :=
  fgAuthGapDhProg S b.q_total

/-- The `GapDhAdv` obtained by running `fgAuthGapDhProg S b.q_total` with `primQueryBudget S b`. -/
@[expose] def fgAuthGapDhDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) : GapDhAdv where
  run U V := (fgAuthGapDhProg S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh := (fgAuthGapDhAdv4 S b A).q_ddh
  q_prim := primQueryBudget S b

theorem fgAuthGapDhProg_totalChalQueries_le_q_ddh (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (fgAuthGapDhProg S b.q_total).totalQueries gdhChalW gdhWS b.q_total ≤
      (fgAuthGapDhDslAdv S b A).q_ddh := by
  dsimp only [CostedReduction.totalQueries]
  have hH := fg_handle_chal_le S b.q_total
  have hF := fg_finish_chal_le S b.q_total
  have hI := fg_init_chal S b.q_total
  rw [hI, Nat.zero_add]
  simp only [fgAuthGapDhDslAdv, fgAuthGapDhAdv4]
  generalize (fgAuthGapDhProg S b.q_total).handle.queries gdhChalW gdhWS = h at hH ⊢
  generalize (fgAuthGapDhProg S b.q_total).finish.queries gdhChalW gdhWS = f at hF ⊢
  have h1 : b.q_total * h ≤ b.q_total * (5 * b.q_total) := Nat.mul_le_mul_left b.q_total hH
  have h2 : b.q_total * (5 * b.q_total) = 5 * b.q_total ^ 2 := by ring
  omega

theorem fgAuthGapDhDslAdv_q_ddh_le (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (fgAuthGapDhDslAdv S b A).q_ddh ≤ 5 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  Nat.le_refl _

theorem fgAuthGapDhProg_chalBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) q)
    (U V : Bytes) :
    ((fgAuthGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q : (PrimBaseSpec + gapDhDdhOracle.spec).Domain => q.isRight = true)
      ((fgAuthGapDhProg S K).totalQueries gdhChalW gdhWS q) :=
  CostedReduction.queryBound_eval (fgAuthGapDhProg S K)
    (fun q : (PrimBaseSpec + gapDhDdhOracle.spec).Domain => q.isRight = true) gdhChalW gdhWS
    (fun g _ hg => by cases g with | inl _ => cases hg | inr _ => exact le_rfl)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec + gapDhDdhOracle.spec)
      (fun q : (PrimBaseSpec + gapDhDdhOracle.spec).Domain => q.isRight = true)
      (Sum.inl (Sum.inl n)) 0).2 (fun h => by cases h))
    A q hA (U, V)

theorem fgAuthGapDhProg_primBounded (S : Setup) (K q : Nat)
    (A : Unit → OracleComp (unifSpec + authSpec S) Bool)
    (hA : ∀ u, (A u).IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) q)
    (U V : Bytes) :
    ((fgAuthGapDhProg S K).eval A (U, V)).IsQueryBoundP
      (fun q => SignalPqxdh.isPrimQuery q = true)
      ((fgAuthGapDhProg S K).totalQueries gdhPrimW gdhWS q) :=
  CostedReduction.queryBound_eval (fgAuthGapDhProg S K)
    (fun q => SignalPqxdh.isPrimQuery q = true) gdhPrimW gdhWS
    (fun g _ hg => by cases g with | inl _ => exact le_rfl | inr _ => cases hg)
    (fun n => (isQueryBoundP_query_iff (spec := PrimBaseSpec + gapDhDdhOracle.spec)
      (fun q => SignalPqxdh.isPrimQuery q = true)
      (Sum.inl (Sum.inl n)) 0).2 (fun h => by cases h))
    A q hA (U, V)

theorem fgAuthGapDhDslProg_size_le_clamped (S : Setup) (b : QueryBudget) :
    (fgAuthGapDhDslProg S b).size ≤ 185 * bits b.q_total + 20000 :=
  fgAuthGapDhProg_size_le_clamped S b.q_total

/-- `fgAuthGapDhDslAdv` respects its declared DDH and primitive query budgets. -/
theorem fgAuthGapDhDslAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (AuthAdversary S) b) :
    (fgAuthGapDhDslAdv S b A).Bounded := by
  have hA : ∀ u : Unit,
      A.1.run.IsQueryBoundP (_root_.ReductionDsl.isGameQuery (G := authSpec S)) b.q_total := by
    intro _
    have h := SignalPqxdh.QueryBounded.auth_total A.2
    convert h using 1; funext q; cases q <;>
      simp [_root_.ReductionDsl.isGameQuery, SignalPqxdh.isGameQuery]
  refine ⟨fun U V => ?_, fun U V => ?_⟩
  · exact (fgAuthGapDhProg_chalBounded S b.q_total b.q_total (fun _ => A.1.run) hA U V).mono
      (fgAuthGapDhProg_totalChalQueries_le_q_ddh S b A)
  · exact (fgAuthGapDhProg_primBounded S b.q_total b.q_total (fun _ => A.1.run) hA U V).mono
      (fgAuthGapDhProg_totalPrimQueries_le S b)

end SignalPqxdh.Security.ReductionDsl.AuthHs
