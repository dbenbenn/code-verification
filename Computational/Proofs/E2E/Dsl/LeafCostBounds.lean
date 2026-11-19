/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.E2E.Dsl.TablesHonest
public import Computational.Specifications.Game.StatementBinaryHarnessCore
public import Computational.Proofs.SpecLemmas.Pqxdh.Security.BoundProofDefs
public import Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds

/-!
# Closed-Form Cost Budgets for E2E Reductions

Defines concrete step-cost budgets for the binary-harness adapter (`e2eAdapterCostBudget`) and
end-to-end composition reductions (`e2eCompositionCostBudget`, `bhE2ECostBudgetHonest`), proves
dominance relations and modular `totalCost` / `GRed2Bounded` constructors, and checks numerical
bounds at `SignalPqxdh.deploymentSetup`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.LeafCostBounds

open Nat
open OracleSpec OracleComp
open ReductionDsl (Sig Ty Ops Samplers Iface GameCodec CostedReduction TwoStageCostedReduction
  OpsSizeHonest SampSizeHonest bits reductionSizeBudget)
open CryptoVerification.LibsignalSession (CostedFits CostedOpsSizeHonest CostedSampSizeHonest
  GRedBounded)
open CryptoGames.LibsignalSession (maxForwardJumps)
open CryptoVerification.E2E (GRed2Bounded)
open CryptoVerification.E2E.Costed (e2eSig prefixCtxT costedFits_iff_fits
  costedOpsSizeHonest_of_opsSizeHonest costedSampSizeHonest_of_sampSizeHonest
  gRedBounded_of_bounds)

/-! ## Closed-form step-cost budgets -/

/-- Closed-form step-cost budget for the binary-harness to model-state adapter. -/
@[expose] def e2eAdapterCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 8 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

abbrev bhAdapterCostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  e2eAdapterCostBudget S b qStart qDR ℓ

/-- Pre-block-cost adapter step-cost budget covering `E2EPureOp.pbytesEq 1568 1568` unconditionally. -/
@[expose] def e2eAdapterCostBudgetPreBlock (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 8 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

/-- Uniform-coefficient adapter step-cost budget with leading factor `2 ^ 12`. -/
@[expose] def e2eAdapterCostBudgetUniform12 (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8)

/-- Conservative upper adapter step-cost envelope with leading factor `2 ^ 17`. -/
@[expose] def m0AdapterCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR ℓ : ℕ) : ℕ :=
  2 ^ 17 * (b.q_total + qStart + qDR + 1) *
    (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 16)

/-- Closed-form step-cost budget for the end-to-end composition reductions (`kindRed` and `prefixRed`). -/
@[expose] def e2eCompositionCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Honest end-to-end composition step-cost budget covering multi-arm handshake, session-start, and
one-shot `finishPrefixCost` overhead. -/
@[expose] def bhE2ECostBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 15 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Linear-in-`qDR` variant of `e2eCompositionCostBudget` for `O(1)` per-epoch table lookup. -/
@[expose] def e2eCompositionCostBudgetLinearSm (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 * (b.q_total + qStart + qDR + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + qDR + qep + ℓ + 2 ^ 12)

/-- Conservative upper composition step-cost envelope with leading factor `2 ^ 24`. -/
@[expose] def m0CompositionCostBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 24 * (b.q_total + qStart + qDR + S.N_send_tot + S.N_recv_tot + 1) *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-! ## Budget monotonicity and dominance -/

theorem e2eAdapterCostBudget_le_m0AdapterCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudget S b qStart qDR ℓ ≤ m0AdapterCostBudget S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudget m0AdapterCostBudget
  refine Nat.mul_le_mul ?_ (by omega)
  exact Nat.mul_le_mul_right _ (by decide)

theorem e2eAdapterCostBudgetPreBlock_le_uniform12 (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ ≤
      e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudgetPreBlock e2eAdapterCostBudgetUniform12
  have hEq :
      2 ^ 12 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8) =
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (16 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 8)) := by
    ring
  rw [hEq]
  exact Nat.mul_le_mul_left _ (by omega)

theorem e2eAdapterCostBudgetUniform12_le_m0AdapterCostBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ) :
    e2eAdapterCostBudgetUniform12 S b qStart qDR ℓ ≤ m0AdapterCostBudget S b qStart qDR ℓ := by
  unfold e2eAdapterCostBudgetUniform12 m0AdapterCostBudget
  refine Nat.mul_le_mul ?_ (by omega)
  exact Nat.mul_le_mul_right _ (by decide)

/-! ## Modular `totalCost` and `GRed2Bounded` constructors -/

/-- Upper-bounds `CostedReduction.totalCost` from component bounds on `init`, `uCost`, `handle`, and `finish`. -/
theorem totalCost_le_of_parts {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    {q initB stepB finB : ℕ}
    (hInit : R.init.cost ≤ initB)
    (hU : I.uCost ≤ stepB)
    (hStep : R.handle.cost + C.codecCost ≤ stepB)
    (hFin : R.finish.cost ≤ finB) :
    R.totalCost q ≤ initB + q * stepB + finB := by
  dsimp only [CostedReduction.totalCost]
  have hMax : max I.uCost (R.handle.cost + C.codecCost) ≤ stepB := max_le hU hStep
  have hMul : q * max I.uCost (R.handle.cost + C.codecCost) ≤ q * stepB :=
    Nat.mul_le_mul_left q hMax
  omega

theorem fits_bool_two {S0 : Sig} (b : (Ty.bool (S := S0)).denote) :
    CostedFits 2 (Ty.bool (S := S0)) b := by
  rw [costedFits_iff_fits]
  simp [Ty.Fits]

/-! ## Leaf-sum inequalities -/

/-- Per-step linear capacity of `e2eAdapterCostBudget`. -/
@[expose] def adapterPerStepBudget (S : SignalPqxdh.Setup) (qStart ℓ : ℕ) : ℕ :=
  2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

@[expose] def adapterPerStepBudgetPreBlock (S : SignalPqxdh.Setup) (qStart ℓ : ℕ) : ℕ :=
  2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)

theorem totalCost_le_e2eAdapterCostBudgetPreBlock_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤ adapterPerStepBudgetPreBlock S qStart ℓ)
    (hU : I.uCost ≤ adapterPerStepBudgetPreBlock S qStart ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ adapterPerStepBudgetPreBlock S qStart ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eAdapterCostBudgetPreBlock S b qStart qDR ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := adapterPerStepBudgetPreBlock S qStart ℓ)
    (finB := R.finish.cost) le_rfl hU hStep le_rfl
  unfold e2eAdapterCostBudgetPreBlock adapterPerStepBudgetPreBlock at *
  have hEq :
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) =
      (b.q_total + qStart + qDR) *
        (2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)) +
      2 ^ 8 * (S.N_id + 16 * S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) := by
    ring
  omega

theorem totalCost_le_e2eAdapterCostBudget_of_step {S0 : Sig} {O : Ops S0} {ι κ : Type}
    {T : OracleSpec ι} {I : Iface S0 T} {G : OracleSpec κ}
    {C : GameCodec S0 G} {rIn aIn aOut out : Ty S0}
    (R : CostedReduction O I G C rIn aIn aOut out)
    (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget) (qStart qDR ℓ : ℕ)
    (hInitFin : R.init.cost + R.finish.cost ≤ adapterPerStepBudget S qStart ℓ)
    (hU : I.uCost ≤ adapterPerStepBudget S qStart ℓ)
    (hStep : R.handle.cost + C.codecCost ≤ adapterPerStepBudget S qStart ℓ) :
    R.totalCost (b.q_total + qStart + qDR) ≤ e2eAdapterCostBudget S b qStart qDR ℓ := by
  have hParts := totalCost_le_of_parts R (q := b.q_total + qStart + qDR)
    (initB := R.init.cost) (stepB := adapterPerStepBudget S qStart ℓ) (finB := R.finish.cost)
    le_rfl hU hStep le_rfl
  unfold e2eAdapterCostBudget adapterPerStepBudget at *
  have hEq :
      2 ^ 8 * (b.q_total + qStart + qDR + 1) *
        (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) =
      (b.q_total + qStart + qDR) *
        (2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10)) +
      2 ^ 8 * (S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + qStart + ℓ + 2 ^ 10) := by
    ring
  omega

/-- Per-step capacity of `e2eCompositionCostBudget`. -/
@[expose] def compositionPerStepBudget (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 12 *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Aggregates PQXDH, session-start, SPQR, Double Ratchet, and codec step costs inside
`compositionPerStepBudget`. -/
theorem e2eLeafSum_le_compositionPerStepBudget (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {pqxdhCost startCost spqrCost drCost codecCost : ℕ}
    (hPqxdh :
      pqxdhCost ≤ 1024 *
        (b.q_total + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 65536)
    (hStart :
      startCost ≤ 1024 *
        (qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot) + 131072)
    (hSpqr : spqrCost ≤ 2000000)
    (hDr : drCost ≤ 1024 * (qDR + 1) * (qDR + qep + ℓ + 1) + 4000000)
    (hCodec : codecCost ≤ 1024) :
    pqxdhCost + startCost + spqrCost + drCost + codecCost ≤
      compositionPerStepBudget S b qStart qDR qep ℓ := by
  have hJumps : maxForwardJumps = 25000 := rfl
  rw [Nat.mul_assoc 1024 (qDR + 1) _] at hDr
  unfold compositionPerStepBudget
  rw [hJumps]
  omega

/-- Per-step capacity of `bhE2ECostBudgetHonest`. -/
@[expose] def compositionPerStepBudgetHonest (S : SignalPqxdh.Setup) (b : SignalPqxdh.QueryBudget)
    (qStart qDR qep ℓ : ℕ) : ℕ :=
  2 ^ 15 *
    (b.q_total + qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot +
      maxForwardJumps + ℓ + (qDR + 1) * (qDR + qep + ℓ + 1))

/-- Aggregates multi-arm PQXDH, session-start, SPQR, Double Ratchet, and codec step costs inside
`compositionPerStepBudgetHonest`. -/
theorem e2eLeafSumM3_le_compositionPerStepBudgetHonest (S : SignalPqxdh.Setup)
    (b : SignalPqxdh.QueryBudget) (qStart qDR qep ℓ : ℕ)
    {pqxdhCost startCost spqrCost drCost codecCost : ℕ}
    (hPqxdh :
      pqxdhCost ≤ 16384 *
        (b.q_total + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 524288)
    (hStart :
      startCost ≤ 8192 *
        (qStart + S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot + S.N_recv_tot) + 524288)
    (hSpqr : spqrCost ≤ 4000000)
    (hDr : drCost ≤ 8192 * (qDR + 1) * (qDR + qep + ℓ + 1) + 8000000)
    (hCodec : codecCost ≤ 8192) :
    pqxdhCost + startCost + spqrCost + drCost + codecCost ≤
      compositionPerStepBudgetHonest S b qStart qDR qep ℓ := by
  have hJumps : maxForwardJumps = 25000 := rfl
  rw [Nat.mul_assoc 8192 (qDR + 1) _] at hDr
  unfold compositionPerStepBudgetHonest
  rw [hJumps]
  omega

/-! ## Numerical bounds at `SignalPqxdh.deploymentSetup` -/

@[expose] def deploymentQueryBudget40 : SignalPqxdh.QueryBudget :=
  { q_ro := 2 ^ 40, q_roRoot := 2 ^ 40, q_total := 2 ^ 40, q_on := 2 ^ 40 }

theorem e2eAdapterCostBudget_deployment_lt :
    e2eAdapterCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40 (2 ^ 20) (2 ^ 40) 1024 <
      2 ^ 90 := by
  unfold e2eAdapterCostBudget SignalPqxdh.deploymentSetup deploymentQueryBudget40
    SignalPqxdh.Setup.N_spk_tot SignalPqxdh.Setup.N_opk_tot SignalPqxdh.Setup.N_send_tot
  decide

end Computational.Proofs.E2E.Dsl.LeafCostBounds
