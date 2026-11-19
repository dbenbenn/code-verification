/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
-- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.KindedCost

/-!
# Step-Cost, Query, and Size Bounds for the AVL Random-Oracle Cache

**Checked by Lean.** Proves zero weighted oracle query counts, closed-form `Comp.cost` and
`Comp.costAt` bounds within `roTableStepCost roTableKappa cap`, and static `Comp.size` bounds for
the AVL search, insert, and lookup-or-sample combinators.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Ty Var Expr Comp Env Iface Samplers
  pqAtomicSig pqAtomicOps pqAtomicSamplers
  AtomicPureOp atomicPureOps atomicBaseSamplers unifSamplers AtomicBaseUnif
  B PB BV256 drKeyT bits one_le_bits
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.RoTableBudget (
  roTableKappa roTableStepCost
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlShapeTy avlPathItemTy avlSearchResTy avlTy avlHeightCap avlLoopAccTy
  aop avlRootE avlCountE avlKvE avlShapeE avlMkE
  maxNatE nodeHeightE mkShapeNodeE joinHeightE orBoolE avlRebalanceStepE
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
  samplePbytes32C sampleDrKey96AtomicC sampleRootPair64AtomicC
  avlRoQueryDrKeyC avlRoRootQueryPairC
)

theorem avlSearchB192C_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).queries w ws = 0 := by
  simp [avlSearchB192C, Comp.queries]

theorem avlSearchPair32C_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).queries w ws = 0 := by
  simp [avlSearchPair32C, Comp.queries]

theorem avlInsertAtPathC_queries {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ) (cap : ℕ)
    {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).queries w ws = 0 := by
  simp [avlInsertAtPathC, Comp.queries]

theorem samplePbytes32C_queries_zero {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) (w : I.Tag → ℕ) (ws : I.smp.Samp → ℕ)
    (hws : ∀ s, ws s = 0) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).queries w ws = 0 := by
  simp [samplePbytes32C, Comp.queries, hws]

theorem samplePbytes32C_cost_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).cost = 37 := by
  revert hSmp
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hSmp; dsimp only at hSmp; cases hSmp
  dsimp [samplePbytes32C, cast, aop, Comp.cost, Expr.cost, Expr.v0,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost,
    pqAtomicSamplers, atomicBaseSamplers, unifSamplers, AtomicBaseUnif.cost]

theorem sampleDrKey96AtomicC_cost_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (sampleDrKey96AtomicC (I := I) hSmp (Γ := Γ)).cost = 120 := by
  have h1 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := Γ)
  have h2 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := PB 32 :: Γ)
  have h3 := samplePbytes32C_cost_eq (I := I) hSmp (Γ := PB 32 :: PB 32 :: Γ)
  dsimp only [sampleDrKey96AtomicC, Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2]
  omega

theorem avlSearchB192C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).cost ≤
      1108 * bits cap + 489 + tblE.cost + keyE.cost := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchB192C, avlHeightCap, avlRootE, avlKvE, avlShapeE, aop,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, hb0]
  norm_num [Nat.max_def]
  omega

theorem avlSearchPair32C_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).cost ≤
      768 * bits cap + 243 + tblE.cost + keyE.cost := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchPair32C, avlHeightCap, avlRootE, avlKvE, avlShapeE, aop, orBoolE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.cost, hb0]
  norm_num [Nat.max_def]
  omega

theorem avlInsertAtPathC_cost_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).cost ≤
      3312 * bits cap + 340 + tblE.cost + pathE.cost + keyE.cost + valE.cost := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [avlInsertAtPathC, avlHeightCap, avlRebalanceStepE,
    avlCountE, avlKvE, avlShapeE, avlMkE,
    maxNatE, nodeHeightE, mkShapeNodeE, joinHeightE,
    Comp.cost, Expr.cost, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    hb0, hb1]
  norm_num [Nat.max_def]
  omega

theorem samplePbytes32C_size_eq {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (hSmp : I.smp = pqAtomicSamplers) {Γ : List (Ty pqAtomicSig)} :
    (samplePbytes32C (I := I) hSmp (Γ := Γ)).size = 6 := by
  revert hSmp
  rcases I with ⟨_, _, _, _, _, _, _, _, smp⟩
  intro hSmp; dsimp only at hSmp; cases hSmp
  dsimp [samplePbytes32C, cast, aop, Comp.size, Expr.size, Expr.v0,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize]

theorem avlSearchB192C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) :
    (avlSearchB192C (I := I) cap tblE keyE).size ≤
      200 + bits (avlHeightCap cap) + tblE.size + keyE.size := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchB192C, avlRootE, avlKvE, avlShapeE, aop,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, hb0]
  omega

theorem avlSearchPair32C_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) :
    (avlSearchPair32C (I := I) cap tblE keyE).size ≤
      250 + bits (avlHeightCap cap) + tblE.size + keyE.size := by
  have hb0 : bits 0 = 1 := rfl
  simp only [avlSearchPair32C, avlRootE, avlKvE, avlShapeE, aop, orBoolE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2,
    pqAtomicOps, atomicPureOps, AtomicPureOp.opSize, hb0]
  omega

theorem avlInsertAtPathC_size_le {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    (cap : ℕ) {Γ : List (Ty pqAtomicSig)} {K V : Ty pqAtomicSig}
    (tblE : Expr pqAtomicOps Γ (avlTy K V))
    (pathE : Expr pqAtomicOps Γ (.list avlPathItemTy))
    (keyE : Expr pqAtomicOps Γ K) (valE : Expr pqAtomicOps Γ V) :
    (avlInsertAtPathC (I := I) cap tblE pathE keyE valE).size ≤
      1500 + bits (avlHeightCap cap) + tblE.size + pathE.size + keyE.size + valE.size := by
  have hb0 : bits 0 = 1 := rfl
  have hb1 : bits 1 = 1 := rfl
  simp only [avlInsertAtPathC, avlRebalanceStepE, avlCountE, avlKvE, avlShapeE, avlMkE,
    maxNatE, nodeHeightE, mkShapeNodeE, joinHeightE,
    Comp.size, Expr.size, Expr.v0, Expr.v1, Expr.v2, Expr.v3, Expr.v4, Expr.v5,
    hb0, hb1]
  omega

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableCost
