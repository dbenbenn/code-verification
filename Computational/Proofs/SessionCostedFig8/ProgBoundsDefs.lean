/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.Fig8WeightedParts -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.Bundles -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Fig8ExcessCosts
import Computational.Proofs.ReductionDsl.Fig8Atomic

/-!
# Shared Cost-Budget Helpers for Atomic Figure 8 Reductions

Lightweight arithmetic budget lemmas and `ckaOpMacro_cost_le` shared by `ProgBounds` and the
`DFProgBounds*` modules without waiting on full Figure 8 reduction proofs.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SessionCostedFig8.ProgBoundsDefs

open _root_.ReductionDsl (bits)
open _root_.CryptoGames (Party)
open _root_.CryptoVerification.LibsignalSession (ratchetCostBudget)
open Computational.Proofs.ReductionDsl.Fig8ExcessCosts (ckaOpC)
open Computational.Proofs.ReductionDsl.Fig8WeightedParts (fig8AtomicStepBound
  add_mul_le_ratchetCostBudget_atomic)
open Computational.Proofs.ReductionDsl.Fig8Atomic (ckaInitAExpr_cost ckaInitBExpr_cost
  ckaSendExpr_cost ckaRecvExpr_cost prngInitExpr_cost prngUpExpr_cost fsInitSendExpr_cost
  fsInitRecvExpr_cost fsSendExpr_cost fsRecvExpr_cost eqPtExpr_cost eqMExpr_cost eqEExpr_cost
  lamIExpr_cost defaultEExpr_cost)
open Computational.Proofs.SessionCostedFig8.Bundles (ckaOpMacro)

theorem const_le_fig8AtomicStepBound {q qep c : ℕ} (hc : c ≤ 25000000) :
    c ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  omega

theorem linear_le_fig8AtomicStepBound {q qep k a b : ℕ}
    (hk : k ≤ 200) (ha : a ≤ 15000) (hb : b ≤ 25000000) :
    k * bits qep + a * (q + 1) + b ≤ fig8AtomicStepBound q qep := by
  unfold fig8AtomicStepBound
  dsimp only
  have hk' := Nat.mul_le_mul_right (bits qep) hk
  have ha' := Nat.mul_le_mul_right (q + 1) ha
  generalize bits qep = bq at hk' ⊢
  generalize (q + 1) * (q + 1) = qq
  generalize (q + 1) * (3 * bq + 60) = qbq
  generalize (q + 1) * (CryptoGames.LibsignalSession.maxForwardJumps + 1) = B
  generalize q + 1 = L at ha' ⊢
  omega

theorem compiled_totalCost_le_ratchetCostBudget
    {q qep initW handleW finishW ovhI uC ovhH ovhF : ℕ}
    (hIF : initW + finishW + 100000 ≤ fig8AtomicStepBound q qep)
    (hH : handleW + 200000 ≤ fig8AtomicStepBound q qep)
    (hovhIF : ovhI + ovhF ≤ 100000)
    (huC : uC ≤ 200000)
    (hovhH : ovhH ≤ 200000) :
    (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) ≤
      ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have hmax : max uC (handleW + ovhH) ≤ fig8AtomicStepBound q qep :=
    max_le (huC.trans h200k) (by omega)
  have h1 : (initW + ovhI) + (finishW + ovhF) ≤ fig8AtomicStepBound q qep := by omega
  have h2 :
      (initW + ovhI) + q * max uC (handleW + ovhH) + (finishW + ovhF) =
        ((initW + ovhI) + (finishW + ovhF)) + q * max uC (handleW + ovhH) := by omega
  rw [h2]
  exact add_mul_le_ratchetCostBudget_atomic h1 hmax

theorem compiled_le_ratchetCostBudget {q qep iW hW fW sI aI aQ aR cc aO aOut u : ℕ}
    (hIF : iW + fW + 100000 ≤ fig8AtomicStepBound q qep)
    (hH : hW + 200000 ≤ fig8AtomicStepBound q qep)
    (hs : sI + aI + aO + aOut ≤ 50000) (hu : u ≤ 200000) (hq : aQ + aR + cc ≤ 100000) :
    (iW + sI + aI + 24) + q * max u (hW + aQ + aR + cc + 28) + (fW + aO + aOut + 22) ≤
      ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have hmax : max u (hW + aQ + aR + cc + 28) ≤ fig8AtomicStepBound q qep :=
    max_le (hu.trans h200k) (by omega)
  have h1 : (iW + sI + aI + 24) + (fW + aO + aOut + 22) ≤ fig8AtomicStepBound q qep := by omega
  have := add_mul_le_ratchetCostBudget_atomic h1 hmax
  omega

theorem dummy_le_ratchetCostBudget {q qep x y z : ℕ} (hxz : x + z ≤ 100000) (hy : y ≤ 200000) :
    x + q * y + z ≤ ratchetCostBudget q qep := by
  have h200k : 200000 ≤ fig8AtomicStepBound q qep := const_le_fig8AtomicStepBound (by decide)
  have := add_mul_le_ratchetCostBudget_atomic (q := q) (qep := qep) (a := x + z) (b := y)
    (by omega) (by omega)
  omega

section CkaMacroCost

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt]
  (C : CryptoGames.LibsignalSession.Crypto) (Dh : CryptoGames.CKA.DHFun (BitVec 256) Pt)
  (encPt : Pt → List (BitVec 8)) (encT : Pt → CryptoGames.LibsignalSession.PublicKey)
  (idOf : Party → CryptoGames.LibsignalSession.IdentityKey) (lam : Pt)

theorem ckaOpMacro_cost_le (hℓ : ℓ < 10 ^ 6) (B0 : ℕ) (o : CryptoGames.CKA.CKAOp) :
    (ckaOpMacro ℓ Pt C Dh encPt encT idOf lam B0 o).cost + 1 ≤ ckaOpC B0 o := by
  have h1 := ckaInitAExpr_cost ℓ Pt C Dh encPt encT lam
  have h2 := ckaInitBExpr_cost ℓ Pt C Dh encPt encT lam
  have h3 := ckaSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h4 := ckaRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h5 := prngInitExpr_cost ℓ Pt C Dh encPt encT lam
  have h6 := prngUpExpr_cost ℓ Pt C Dh encPt encT lam
  have h7 := fsInitSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h8 := fsInitRecvExpr_cost ℓ Pt C Dh encPt encT lam
  have h9 := fsSendExpr_cost ℓ Pt C Dh encPt encT lam
  have h10 := eqPtExpr_cost ℓ Pt C Dh encPt encT lam
  have h11 := eqMExpr_cost ℓ Pt C Dh encPt encT lam
  have h12 := eqEExpr_cost ℓ Pt C Dh encPt encT lam
  have h13 := lamIExpr_cost ℓ Pt C Dh encPt encT lam
  have h14 := defaultEExpr_cost ℓ Pt C Dh encPt encT lam
  cases o with
  | fsReceive B' =>
    have h15 := fsRecvExpr_cost ℓ Pt C Dh encPt encT lam B0 B'
    simp only [ckaOpMacro, ckaOpC]
    omega
  | _ => simp only [ckaOpMacro, ckaOpC]; omega

end CkaMacroCost

end Computational.Proofs.SessionCostedFig8.ProgBoundsDefs
