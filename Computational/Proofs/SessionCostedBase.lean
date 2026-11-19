/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Computational.Proofs.ReductionDsl.Soundness
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRG.CostedTables
import Computational.Proofs.SpecLemmas.Session.ACD19.SM.CostedTables
public import Computational.Specifications.Reductions.ReductionDsl.Samplers
public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Computational.Proofs.ReductionDsl.LibsignalBoundDDHChain
public import Computational.Proofs.ReductionDsl.Size -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.GRedBoundedOfBounds
public import Computational.Specifications.Session.ACD19.Ratchet.LibsignalBound

/-!
# Costed DSL Base Helpers and Ratchet Budget Bounds

Provides `gredBounded_of_bounds`, `gtwoStageBounded_of_bounds`, and `ratchetCostBudget` comparison
lemmas for the Libsignal session security proofs.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalSession

open OracleComp OracleSpec CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst
  LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA AEADScheme MACScheme
  WireAEAD FSAEAD

section GRedBoundedHelper

variable {S : ReductionDsl.Sig} {O : ReductionDsl.Ops S} {ι κ : Type}
  {T : OracleSpec ι} {I : ReductionDsl.Iface S T} {G : OracleSpec κ}
  {C : ReductionDsl.GameCodec S G}

lemma costedFits_iff_fits (B : ℕ) (t : ReductionDsl.Ty S) (x : t.denote) :
    CostedFits B t x ↔ t.Fits B x :=
  Iff.rfl

lemma costedOpsSizeHonest_of_opsSizeHonest (hO : ReductionDsl.OpsSizeHonest O) :
    CostedOpsSizeHonest O :=
  hO

lemma costedSampSizeHonest_of_sampSizeHonest (hS : ReductionDsl.SampSizeHonest I.smp) :
    CostedSampSizeHonest I.smp :=
  hS

lemma expr_cost_pos {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (e : ReductionDsl.Expr O Γ t) : 1 ≤ e.cost := by
  induction e <;> simp only [ReductionDsl.Expr.cost]
  case nat n => exact ReductionDsl.one_le_bits n
  all_goals omega

lemma comp_nq_le_cost {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (c : ReductionDsl.Comp O I Γ t) : c.nq ≤ c.cost := by
  induction c with
  | ret e => simp [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries]
  | bind c1 c2 ih1 ih2 =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | ite e c1 c2 ih1 ih2 =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | caseOpt e n s ihn ihs =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | caseSum e l r ihl ihr =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    omega
  | sample s a =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost]
    have := expr_cost_pos a
    omega
  | query g a =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost]
    have := expr_cost_pos a
    omega
  | iter k init step ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * step.queries (fun _ => 1) (fun _ => 1) ≤ k * (step.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | findM k l pred ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * pred.queries (fun _ => 1) (fun _ => 1) ≤ k * (pred.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | anyM k xs pred ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * pred.queries (fun _ => 1) (fun _ => 1) ≤ k * (pred.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | mapM k xs body ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * body.queries (fun _ => 1) (fun _ => 1) ≤ k * (body.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | consumeFirstM k l p mk ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * p.queries (fun _ => 1) (fun _ => 1) ≤ k * (p.cost + mk.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega
  | foldM k xs init step ih =>
    simp only [ReductionDsl.Comp.nq, ReductionDsl.Comp.queries, ReductionDsl.Comp.cost] at *
    have hmul : k * step.queries (fun _ => 1) (fun _ => 1) ≤ k * (step.cost + 1) :=
      Nat.mul_le_mul_left k (by omega)
    omega

lemma gredBounded_of_bounds {rIn aIn aOut out : ReductionDsl.Ty S}
    {R : ReductionDsl.CostedReduction O I G C rIn aIn aOut out}
    {wTag : I.Tag → ℕ} {wSamp : I.smp.Samp → ℕ}
    {q qOut costBudget : ℕ}
    (hcost : R.totalCost q ≤ costBudget)
    (hsize : R.size ≤ ReductionDsl.reductionSizeBudget + 2 ^ 12 * ReductionDsl.bits costBudget)
    (hq : R.totalQueries wTag wSamp q ≤ qOut)
    (hO : ReductionDsl.OpsSizeHonest O)
    (hS : ReductionDsl.SampSizeHonest I.smp) :
    GRedBounded R wTag wSamp q qOut costBudget :=
  CryptoVerification.E2E.Costed.gRedBounded_of_bounds R wTag wSamp q qOut costBudget
    hcost hsize hq hO hS

lemma comp_cost_pos {Γ : List (ReductionDsl.Ty S)} {t : ReductionDsl.Ty S}
    (c : ReductionDsl.Comp O I Γ t) : 1 ≤ c.cost := by
  induction c with
  | ret e => have := expr_cost_pos e; simp only [ReductionDsl.Comp.cost]; omega
  | bind _ _ _ _ | ite _ _ _ _ _ | caseOpt _ _ _ _ _ | caseSum _ _ _ _ _ =>
    simp only [ReductionDsl.Comp.cost]; omega
  | sample _ a | query _ a =>
    have := expr_cost_pos a; simp only [ReductionDsl.Comp.cost]; omega
  | iter _ s _ _ | findM _ s _ _ | anyM _ s _ _ | mapM _ s _ _
  | consumeFirstM _ s _ _ _ | foldM _ s _ _ _ =>
    have := expr_cost_pos s; simp only [ReductionDsl.Comp.cost]; omega

end GRedBoundedHelper

section ChainCosted

lemma fsRatchetCostBudget_le_ratchetCostBudget (q qep : ℕ) :
    fsRatchetCostBudget q qep ≤ ratchetCostBudget q qep :=
  Nat.min_le_left _ _

lemma ratchetCostBudget_pos (q qep : ℕ) :
    16777216 * (q + 1) ≤ ratchetCostBudget q qep := by
  unfold ratchetCostBudget maxForwardJumps
  have hb : 1 ≤ ReductionDsl.bits qep := ReductionDsl.one_le_bits qep
  nlinarith

end ChainCosted

section DDHCosted

variable {Pt : Type} [Zero Pt]

end DDHCosted

end CryptoVerification.LibsignalSession
