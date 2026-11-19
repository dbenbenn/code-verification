/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhProofs -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyGapDh
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval
import Computational.Proofs.SignalPqxdh.Security.FgGapDh1KeyPre
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhSessionSplit
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhEvalEq
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsAccept
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhProofsInit

/-!
# Cost and Query Bounds for `fgKeyInd1KeyGapDhDslAdv`

**Checked by Lean.** Packages the one-key `KeyInd` `ReductionDsl` reduction as a `GapDhWithSignAdv`
(`fgKeyInd1KeyGapDhDslAdv`) and establishes its step-cost bound, semantic query-budget compliance,
advantage equality with `fgKeyInd1KeyGapDhAdv4`, and the imperfect-correctness `G3 -> G3.5` bound.
-/

public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh SignalPqxdh.Security.FgGapDh1Key
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

open SignalPqxdh.Security.ReductionDsl.KeyInd
open SignalPqxdh.Security.ReductionDsl.KeyIndGapDh

/-- The `ReductionDsl` program instantiated at `K = b.q_total` for one-key `KeyInd` `GapDhWithSign`. -/
abbrev fgKeyInd1KeyGapDhDslProg (S : Setup) (b : QueryBudget) :=
  fgKeyInd1KeyGapDh2Prog S b.q_total

/-- The `ReductionDsl` one-key `KeyInd` reduction packaged as a `GapDhWithSignAdv`. -/
@[expose] def fgKeyInd1KeyGapDhDslAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := (fgKeyInd1KeyGapDh2Prog S b.q_total).eval (fun _ => A.1.run) (U, V)
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

/-- Step-cost bound for `fgKeyInd1KeyGapDhProg` against `stepCostBudget`. -/
theorem fgKeyInd1KeyGapDhProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhProg S b.q_total).totalCost b.q_total ≤
      _root_.SignalPqxdh.LegacyCosted.stepCostBudget S b :=
  (fgKeyInd1KeyGapDhProg_totalCost_le S b).trans (securityStepCostBudget_le_legacy S b)

section TupleKeyedSyntactic

private theorem tk_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem tk_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

end TupleKeyedSyntactic

section BilinearDdh

set_option allowUnsafeReducibility true
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle Env.get Ext.wk
  CostedReduction.σ fgKeyInd1KeyGapDhProg

private def Ddh1KeyStep {α : Type} (m : ℕ) (Q : α → Prop)
    (oa : OracleComp (PrimBaseSpec + sigAndDdhOracle.spec) α) : Prop :=
  oa.IsQueryBoundP (fun q => isDdhChalQuery q = true) m ∧ ∀ x ∈ support oa, Q x

end BilinearDdh

theorem fgKeyInd1KeyGapDhProg_evalDist_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A)] =
      𝒟[gapDhWithSignExp P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A)] :=
  Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh2Eval.fgKeyInd1KeyGapDh2Prog_evalDist_gapDhWithSignExp_eq
    P isValidDhTriple pow8 S b A

/-- Advantage equality between `fgKeyInd1KeyGapDhDslAdv` and `fgKeyInd1KeyGapDhAdv4`. -/
theorem fgKeyInd1KeyGapDhProg_gapDhWithSign_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSign P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A) =
      GapDhWithSign P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A) := by
  simp only [GapDhWithSign, fgKeyInd1KeyGapDhProg_evalDist_eq]

theorem fgKeyInd1KeyGapDhProg_gapDhWithSignReal_eq (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapDhWithSignReal P isValidDhTriple pow8 (fgKeyInd1KeyGapDhDslAdv S b A) =
      GapDhWithSignReal P isValidDhTriple pow8 (fgKeyInd1KeyGapDhAdv4 S b A) :=
  congrArg ENNReal.toReal
    (fgKeyInd1KeyGapDhProg_gapDhWithSign_eq P isValidDhTriple pow8 S b A)

/-- Imperfect-correctness `G3 -> G3.5` `GapDhWithSign` advantage bound over
    `fgKeyInd1KeyGapDhDslAdv`. -/
theorem keyIndAdvG3_1Key_le_gapDhWithSignδ_dsl
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    Proofs.SignalPqxdh.Security.keyIndAdvG3_1Key S P A.1 ≤
      2 * (((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
            (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
            (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
            GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhDslAdv S b A)) +
      kemDecapsFailureTermReal S δ := by
  rw [fgKeyInd1KeyGapDhProg_gapDhWithSignReal_eq]
  exact Proofs.SignalPqxdh.Security.keyIndAdvG3_1Key_le_gapDhWithSignδ S P hP δ hδ b A

end SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
