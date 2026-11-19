/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.Game.PromotedCostedReds.SessionProgCommon -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSim -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping -- proof-setup: allow-public-import
public import Computational.Proofs.E2E.Dsl.DrSessionSimRecv -- proof-setup: allow-public-import
public import Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge -- proof-setup: allow-public-import
import Computational.Proofs.E2E.Dsl.SpqrSim

/-!
# Shared Exact Static Cost Preservation for Atomic Session Reductions

Factors `exprAllOps`, `compAllOps`, `sessionCostExactOp`, `NoKemKeyGenExpr`, `NoKemKeyGenComp`,
`liftExpr_cost_exact`, `liftCompEmpty_cost_exact`, `liftCompCoins_cost_exact`, `noKemKeyGen*`
structural lemmas, `drSendAtomicC_cost_exact`, `drReceiveAtomicC_cost_exact`, and `BoxEq`/`box_le`
once across `SpkHop2*` and `SpkLeakRed*` promoted costed reductions.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs

open OracleSpec
open _root_.ReductionDsl (Sig Ty Var Ops Iface Expr Comp UniformSamplerTag
  atomicSig atomicSessionOps atomicSamplers
  BV256 BV512 PtT GhostStT PlainT B)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM (orE boolEq isSomeE otherE pGet)
open CryptoGames.LibsignalSession (Crypto PublicKey)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.E2E (Bytes)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (zeroPqxdhPrims
  cost_sessPureOp cost_sessSymOp cost_sessCurveOp
  liftTy liftExpr liftExpr_cost renExpr renExpr_cost renComp
  wk1Expr wk1Expr_cost wk1Comp wk1Comp_cost
  emptyE2EIface liftCompEmpty coinE2EIface coinE2ESamplers liftSampComp liftCompCoins
  drReceiveAtomicC)

/-- Opaque equality wrapper hiding large `Expr.cost`/`Comp.cost` ASTs from `omega` kernel proof terms. -/
structure BoxEq (a b : ℕ) : Prop where
  eq : a = b

theorem box_le {x y : ℕ} (h : x ≤ y) : ∃ n : ℕ, BoxEq x n ∧ n ≤ y :=
  ⟨x, ⟨rfl⟩, h⟩

section SessionCostExact

open Computational.Proofs.E2E.Dsl.TablesHonest (e2ePureOp e2eCurveOp e2eCryptoOp)
open Computational.Proofs.E2E.Dsl.SpqrSim (spqrDslHooks spqrSendComp spqrSendComp_cost
  spqrRecvComp spqrRecvComp_cost)
open Computational.Proofs.E2E.Dsl.DrSessionSim (drSendC drSendC_cost drReceiveC drReceiveC_cost
  drTrArmC drChArmC drDlArmC drIjArmC drCrArmC)
open Computational.Proofs.Game.PromotedCostedReds.AtomicSessionBridge (liftRen wk1Ren
  liftPureOpExpr liftCurveOpExpr liftCryptoOpExpr liftOpExpr liftSampComp
  cost_sessSpqrKemOp spqrSendAtomicC spqrRecvAtomicC drSendAtomicC)

@[expose] def exprAllOps {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool) :
    {Γ : List (Ty S0)} → {t : Ty S0} → Expr O0 Γ t → Bool
  | _, _, .var _ => true
  | _, _, .unit => true
  | _, _, .bool _ => true
  | _, _, .nat _ => true
  | _, _, .add a b => exprAllOps p a && exprAllOps p b
  | _, _, .sub a b => exprAllOps p a && exprAllOps p b
  | _, _, .mulK _ a => exprAllOps p a
  | _, _, .divK _ a => exprAllOps p a
  | _, _, .modK _ a => exprAllOps p a
  | _, _, .lt a b => exprAllOps p a && exprAllOps p b
  | _, _, .eqN a b => exprAllOps p a && exprAllOps p b
  | _, _, .not a => exprAllOps p a
  | _, _, .and a b => exprAllOps p a && exprAllOps p b
  | _, _, .ite c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .pair a b => exprAllOps p a && exprAllOps p b
  | _, _, .fst a => exprAllOps p a
  | _, _, .snd a => exprAllOps p a
  | _, _, .inl a => exprAllOps p a
  | _, _, .inr a => exprAllOps p a
  | _, _, .none => true
  | _, _, .some a => exprAllOps p a
  | _, _, .caseOpt c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .caseSum c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .letE a b => exprAllOps p a && exprAllOps p b
  | _, _, .op o a => p o && exprAllOps p a
  | _, _, .nil => true
  | _, _, .cons a b => exprAllOps p a && exprAllOps p b
  | _, _, .len a => exprAllOps p a
  | _, _, .take a b => exprAllOps p a && exprAllOps p b
  | _, _, .appendL _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .findB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .anyB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .mapB _ a b => exprAllOps p a && exprAllOps p b
  | _, _, .foldrB _ c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b
  | _, _, .tconst a => exprAllOps p a
  | _, _, .tget a b => exprAllOps p a && exprAllOps p b
  | _, _, .tset c a b => exprAllOps p c && exprAllOps p a && exprAllOps p b

@[expose] def compAllOps {S0 : Sig} {O0 : Ops S0} {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T}
    (p : O0.Op → Bool) :
    {Γ : List (Ty S0)} → {t : Ty S0} → Comp O0 I0 Γ t → Bool
  | _, _, .ret e => exprAllOps p e
  | _, _, .bind c k => compAllOps p c && compAllOps p k
  | _, _, .ite b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .caseOpt b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .caseSum b c d => exprAllOps p b && compAllOps p c && compAllOps p d
  | _, _, .sample _ e => exprAllOps p e
  | _, _, .query _ e => exprAllOps p e
  | _, _, .iter _ e body => exprAllOps p e && compAllOps p body
  | _, _, .findM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .anyM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .mapM _ e body => exprAllOps p e && compAllOps p body
  | _, _, .consumeFirstM _ l body mk =>
    exprAllOps p l && compAllOps p body && exprAllOps p mk
  | _, _, .foldM _ l z body =>
    exprAllOps p l && exprAllOps p z && compAllOps p body

theorem exprAllOps_renExpr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (e : Expr O0 Γ₁ t) :
    exprAllOps p (renExpr f e) = exprAllOps p e := by
  induction e generalizing Γ₂ with
  | var _ | unit | bool _ | nat _ | none | nil => rfl
  | add _ _ ha hb | sub _ _ ha hb | lt _ _ ha hb | eqN _ _ ha hb | and _ _ ha hb
  | pair _ _ ha hb | cons _ _ ha hb | take _ _ ha hb | appendL _ _ _ ha hb
  | tget _ _ ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [ha, hb]
  | letE _ _ ha hb | findB _ _ _ ha hb | anyB _ _ _ ha hb | mapB _ _ _ ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [ha, hb]
  | mulK _ _ ha | divK _ _ ha | modK _ _ ha | not _ ha | fst _ ha | snd _ ha
  | inl _ ha | inr _ ha | some _ ha | len _ ha | tconst _ ha | op _ _ ha =>
    dsimp only [renExpr, exprAllOps]; rw [ha]
  | ite _ _ _ hc ha hb | caseOpt _ _ _ hc ha hb | caseSum _ _ _ hc ha hb
  | foldrB _ _ _ _ hc ha hb | tset _ _ _ hc ha hb =>
    dsimp only [renExpr, exprAllOps]; rw [hc, ha, hb]

theorem exprAllOps_wk1Expr {S0 : Sig} {O0 : Ops S0} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (e : Expr O0 [a] b) :
    exprAllOps p (wk1Expr (Γ := Γ) e) = exprAllOps p e :=
  exprAllOps_renExpr p wk1Ren e

theorem compAllOps_renComp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {Γ₁ Γ₂ : List (Ty S0)} {t : Ty S0}
    (f : ∀ {u}, Var Γ₁ u → Var Γ₂ u) (c : Comp O0 I0 Γ₁ t) :
    compAllOps p (renComp f c) = compAllOps p c := by
  induction c generalizing Γ₂ with
  | ret e | sample _ e | query _ e =>
    dsimp only [renComp, compAllOps]; exact exprAllOps_renExpr p f e
  | bind _ _ hc hk =>
    dsimp only [renComp, compAllOps]; rw [hc, hk]
  | ite b _ _ hc hk | caseOpt b _ _ hc hk | caseSum b _ _ hc hk =>
    dsimp only [renComp, compAllOps]; rw [exprAllOps_renExpr p f b, hc, hk]
  | iter _ e _ hb | findM _ e _ hb | anyM _ e _ hb | mapM _ e _ hb =>
    dsimp only [renComp, compAllOps]; rw [exprAllOps_renExpr p f e, hb]
  | consumeFirstM _ l _ mk hb =>
    dsimp only [renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, hb, exprAllOps_renExpr p (liftRen f) mk]
  | foldM _ l z _ hb =>
    dsimp only [renComp, compAllOps]
    rw [exprAllOps_renExpr p f l, exprAllOps_renExpr p f z, hb]

theorem compAllOps_wk1Comp {S0 : Sig} {O0 : Ops S0}
    {ι : Type} {T : OracleSpec ι} {I0 : Iface S0 T} (p : O0.Op → Bool)
    {a b : Ty S0} {Γ : List (Ty S0)} (c : Comp O0 I0 [a] b) :
    compAllOps p (wk1Comp (Γ := Γ) c) = compAllOps p c :=
  compAllOps_renComp p wk1Ren c

@[expose, simp] def sessionCostExactCryptoOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp → Bool
  | .x25519 => false
  | .x25519Base => false
  | .pow8 => false
  | .sigSign => false
  | .kemKeyGen => false
  | .hkdfDerive96 => false
  | _ => true

@[expose, simp] def sessionCostExactOp :
    Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp ⊕
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp ⊕
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp) → Bool
  | .inl _ => true
  | .inr (.inl _) => true
  | .inr (.inr c) => sessionCostExactCryptoOp c

/-- Predicate on `e2eOps` expressions excluding PQXDH crypto stubs whose lifted cost exceeds `1×`. -/
abbrev NoKemKeyGenExpr {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)}
    (e : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT) Γ t) : Bool :=
  exprAllOps sessionCostExactOp e

abbrev NoKemKeyGenComp {ℓ : ℕ} {Pt : Type} {P : SignalPqxdh.Primitives}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    {ι : Type} {T : OracleSpec ι}
    {I0 : Iface (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ) T}
    {Γ : List (Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ))}
    {t : Ty (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ)}
    (c : Comp (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT) I0 Γ t) : Bool :=
  compAllOps sessionCostExactOp c

section ExactCostProofs

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT

private theorem liftPureOpExpr_cost_exact {Γ : List (Ty ASig)}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (o.dom ℓ))) :
    (liftPureOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost = a.cost + o.cost ℓ := by
  cases o <;> (dsimp only [liftPureOpExpr]; rw [cost_sessPureOp]; rfl)

private theorem liftCurveOpExpr_cost_exact {Γ : List (Ty ASig)}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr AOps Γ (liftTy (Pt := Pt)
      ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc))) :
    (liftCurveOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) cc a).cost =
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).cost cc := by
  cases cc <;> (dsimp only [liftCurveOpExpr]; rw [cost_sessCurveOp])

private theorem liftCryptoOpExpr_cost_exact {Γ : List (Ty ASig)}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (hc : sessionCostExactCryptoOp c = true)
    (a : Expr AOps Γ (liftTy (Pt := Pt) (c.dom ℓ))) :
    (liftCryptoOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) c a).cost ≤ a.cost + c.cost ℓ := by
  match c with
  | .x25519 | .x25519Base | .pow8 | .sigSign | .kemKeyGen | .hkdfDerive96 =>
    simp [sessionCostExactCryptoOp] at hc
  | .isCanonical | .sigVerify | .kemEncaps | .kemDecaps =>
    dsimp only [liftCryptoOpExpr, ReductionDsl.Expr.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .sessionKeyPairGen | .sessionRootCreateChain | .chainStep | .deriveMsgKeys
  | .aes256CbcEnc | .aes256CbcDec | .signalMsgEncode | .signalMsgVerifyMac =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSymOp]
    dsimp only [ReductionDsl.AtomicSymOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega
  | .spqrV1InitOp | .spqrNegotiateInit | .spqrBraidSend | .spqrBraidRecv
  | .spqrChainFromVn | .spqrChainAddEpoch | .spqrChainNextKey =>
    dsimp only [liftCryptoOpExpr]
    rw [cost_sessSpqrKemOp]
    dsimp only [ReductionDsl.AtomicSpqrKemOp.cost,
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp.cost]
    omega

private theorem liftOpExpr_cost_exact {Γ : List (Ty ASig)} (o : (EOps).Op)
    (ho : sessionCostExactOp o = true)
    (a : Expr AOps Γ (liftTy (Pt := Pt) ((EOps).dom o))) :
    (liftOpExpr (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o a).cost ≤ a.cost + (EOps).cost o := by
  rcases o with o | (cc | c)
  · exact le_of_eq (liftPureOpExpr_cost_exact o a)
  · exact le_of_eq (liftCurveOpExpr_cost_exact cc a)
  · exact liftCryptoOpExpr_cost_exact c ho a

private theorem mul_cost_step_exact (Kb x y : ℕ) (h : x ≤ y) :
    Kb * (x + 1) ≤ Kb * (y + 1) :=
  Nat.mul_le_mul_left Kb (by omega)

private theorem mul_cost_step2_exact (Kb x1 x2 y1 y2 : ℕ) (h1 : x1 ≤ y1) (h2 : x2 ≤ y2) :
    Kb * (x1 + x2 + 1) ≤ Kb * (y1 + y2 + 1) :=
  Nat.mul_le_mul_left Kb (by omega)

theorem liftExpr_cost_exact {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr EOps Γ t)
    (he : NoKemKeyGenExpr e = true) :
    (liftExpr (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) e).cost ≤ e.cost := by
  induction e with
  | var _ | unit | bool _ | nat _ | none | nil =>
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | add a b ha hb | sub a b ha hb | lt a b ha hb | eqN a b ha hb | and a b ha hb
  | pair a b ha hb | cons a b ha hb | take a b ha hb | appendL _ a b ha hb
  | letE a b ha hb | tget a b ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | mulK _ a ha | divK _ a ha | modK _ a ha | not a ha | fst a ha | snd a ha
  | inl a ha | inr a ha | some a ha | len a ha | tconst a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    have h1 := ha he
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | ite c a b hc ha hb | caseOpt c a b hc ha hb | caseSum c a b hc ha hb
  | tset c a b hc ha hb =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hc he0; have h1 := ha he1; have h2 := hb he2
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | op o a ha =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := ha he2
    have ho := liftOpExpr_cost_exact (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) o he1 (liftExpr a)
    dsimp only [liftExpr, ReductionDsl.Expr.cost] at ho ⊢
    omega
  | findB Kb l p hl hp | anyB Kb l p hl hp | mapB Kb l p hl hp =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true] at he; rcases he with ⟨he1, he2⟩
    have h1 := hl he1; have hm := mul_cost_step_exact Kb _ _ (hp he2)
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega
  | foldrB Kb l z f hl hz hf =>
    dsimp only [NoKemKeyGenExpr, exprAllOps] at he
    rw [Bool.and_eq_true, Bool.and_eq_true] at he; rcases he with ⟨⟨he0, he1⟩, he2⟩
    have h0 := hl he0; have h1 := hz he1; have hm := mul_cost_step_exact Kb _ _ (hf he2)
    dsimp only [liftExpr, ReductionDsl.Expr.cost]; omega

theorem liftCompEmpty_cost_exact {ι : Type} {T : OracleSpec ι} {I' : Iface ASig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (emptyE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompEmpty (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) (I' := I') c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | sample s _ => exact s.elim
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hmk := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hz := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompEmpty, ReductionDsl.Comp.cost]; omega

private theorem liftSampComp_cost_local [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt) {Γ : List (Ty ASig)}
    (s : UniformSamplerTag Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EUnifBase)
    (a : Expr AOps Γ .unit) :
    (liftSampComp (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' hsmp s a).cost =
      a.cost + (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSamplers ℓ).sCost s := by
  rcases I' with ⟨fwdU, uCost, Tag, dom, cod, enc, dec, qCost, smp⟩
  dsimp only at hsmp; subst hsmp
  rcases s with _ | N | (_ | _) <;> rfl

theorem liftCompCoins_cost_exact [SampleableType Pt] {ι : Type} {T : OracleSpec ι}
    {I' : Iface ASig T} (hsmp : I'.smp = atomicSamplers ℓ Pt)
    {Γ : List (Ty ESig)} {t : Ty ESig} (c : Comp EOps (coinE2EIface I') Γ t)
    (hc : NoKemKeyGenComp c = true) :
    (liftCompCoins (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) hsmp c).cost ≤ c.cost := by
  induction c with
  | ret e =>
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | bind _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | ite b _ _ ih1 ih2 | caseOpt b _ _ ih1 ih2 | caseSum b _ _ ih1 ih2 =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hb := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) b hc0
    have h1 := ih1 hc1; have h2 := ih2 hc2
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | sample s a =>
    have ha := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) a hc
    have hs := liftSampComp_cost_local (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) hsmp s (liftExpr a)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost, coinE2EIface] at hs ⊢
    omega
  | query g _ => exact g.elim
  | iter n e _ ih | findM n e _ ih | anyM n e _ ih | mapM n e _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true] at hc; rcases hc with ⟨hc1, hc2⟩
    have he := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) e hc1
    have hm := mul_cost_step_exact n _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | consumeFirstM Kb l _ mk ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hmk := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) mk hc2
    have hm := mul_cost_step2_exact Kb _ _ _ _ (ih hc1) hmk
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega
  | foldM Kb l z _ ih =>
    dsimp only [NoKemKeyGenComp, compAllOps] at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc; rcases hc with ⟨⟨hc0, hc1⟩, hc2⟩
    have hl := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) l hc0
    have hz := liftExpr_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
      (encT := encT) (decT := decT) (lam := lam) z hc1
    have hm := mul_cost_step_exact Kb _ _ (ih hc2)
    dsimp only [liftCompCoins, ReductionDsl.Comp.cost]; omega

end ExactCostProofs

section SimExactLemmas

variable {ℓ : ℕ} {Pt : Type}
  {P : SignalPqxdh.Primitives}
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}

local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "POps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ P C K decT encT

@[simp] theorem noKemKeyGenExpr_renExpr {Γ Δ : List (Ty ESig)} {t : Ty ESig}
    (f : ∀ {u}, Var Γ u → Var Δ u) (e : Expr POps Γ t) :
    NoKemKeyGenExpr (renExpr f e) = NoKemKeyGenExpr e :=
  exprAllOps_renExpr (O0 := POps) sessionCostExactOp f e

@[simp] theorem noKemKeyGenExpr_wk1Expr {a b : Ty ESig} {Γ : List (Ty ESig)}
    (e : Expr POps [a] b) :
    NoKemKeyGenExpr (wk1Expr (Γ := Γ) e) = NoKemKeyGenExpr e :=
  exprAllOps_wk1Expr (O0 := POps) sessionCostExactOp e

@[simp] theorem noKemKeyGenComp_renComp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ Δ : List (Ty ESig)} {t : Ty ESig} (f : ∀ {u}, Var Γ u → Var Δ u) (c : Comp POps I0 Γ t) :
    NoKemKeyGenComp (renComp f c) = NoKemKeyGenComp c :=
  compAllOps_renComp (O0 := POps) sessionCostExactOp f c

@[simp] theorem noKemKeyGenComp_wk1Comp {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {a b : Ty ESig} {Γ : List (Ty ESig)} (c : Comp POps I0 [a] b) :
    NoKemKeyGenComp (wk1Comp (Γ := Γ) c) = NoKemKeyGenComp c :=
  compAllOps_wk1Comp (O0 := POps) sessionCostExactOp c

@[simp] theorem noKemKeyGenComp_ret {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr POps Γ t) :
    NoKemKeyGenComp (.ret e : Comp POps I0 Γ t) = NoKemKeyGenExpr e := rfl
@[simp] theorem noKemKeyGenComp_bind {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (c1 : Comp POps I0 Γ t) (c2 : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.bind c1 c2) = (NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[simp] theorem noKemKeyGenComp_ite {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (b : Expr POps Γ .bool) (c1 c2 : Comp POps I0 Γ t) :
    NoKemKeyGenComp (.ite b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[simp] theorem noKemKeyGenComp_caseOpt {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (b : Expr POps Γ (.opt t))
    (c1 : Comp POps I0 Γ u) (c2 : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.caseOpt b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[simp] theorem noKemKeyGenComp_caseSum {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u w : Ty ESig} (b : Expr POps Γ (.sum t u))
    (c1 : Comp POps I0 (t :: Γ) w) (c2 : Comp POps I0 (u :: Γ) w) :
    NoKemKeyGenComp (.caseSum b c1 c2) = (NoKemKeyGenExpr b && NoKemKeyGenComp c1 && NoKemKeyGenComp c2) := rfl
@[simp] theorem noKemKeyGenComp_sample {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} (s : I0.smp.Samp) (a : Expr POps Γ (I0.smp.sDom s)) :
    NoKemKeyGenComp (.sample s a : Comp POps I0 Γ (I0.smp.sTy s)) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenComp_query {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} (g : I0.Tag) (a : Expr POps Γ (I0.dom g)) :
    NoKemKeyGenComp (.query g a : Comp POps I0 Γ (I0.cod g)) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenComp_iter {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ t) (body : Comp POps I0 (t :: Γ) t) :
    NoKemKeyGenComp (.iter n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[simp] theorem noKemKeyGenComp_findM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.findM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[simp] theorem noKemKeyGenComp_anyM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) :
    NoKemKeyGenComp (.anyM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[simp] theorem noKemKeyGenComp_mapM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (n : ℕ) (e : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) u) :
    NoKemKeyGenComp (.mapM n e body) = (NoKemKeyGenExpr e && NoKemKeyGenComp body) := rfl
@[simp] theorem noKemKeyGenComp_consumeFirstM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ) (l : Expr POps Γ (.list t))
    (body : Comp POps I0 (t :: Γ) .bool) (mk : Expr POps (t :: Γ) t) :
    NoKemKeyGenComp (.consumeFirstM Kb l body mk) =
      (NoKemKeyGenExpr l && NoKemKeyGenComp body && NoKemKeyGenExpr mk) := rfl
@[simp] theorem noKemKeyGenComp_foldM {ι : Type} {T : OracleSpec ι} {I0 : Iface ESig T}
    {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ) (l : Expr POps Γ (.list t))
    (z : Expr POps Γ u) (body : Comp POps I0 (t :: u :: Γ) u) :
    NoKemKeyGenComp (.foldM Kb l z body) =
      (NoKemKeyGenExpr l && NoKemKeyGenExpr z && NoKemKeyGenComp body) := rfl

@[simp] theorem noKemKeyGenExpr_optBytes32LitE {Γ : List (Ty ESig)} (opt : Option Bytes) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.optBytes32LitE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) (Γ := Γ) opt) = true := by
  cases opt <;> rfl

@[simp] theorem noKemKeyGenExpr_var {Γ : List (Ty ESig)} {t : Ty ESig} (v : Var Γ t) :
    NoKemKeyGenExpr (Expr.var v : Expr POps Γ t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v0 {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (Expr.v0 : Expr POps (t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v1 {Γ : List (Ty ESig)} {t a : Ty ESig} :
    NoKemKeyGenExpr (Expr.v1 : Expr POps (a :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v2 {Γ : List (Ty ESig)} {t a b : Ty ESig} :
    NoKemKeyGenExpr (Expr.v2 : Expr POps (a :: b :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v3 {Γ : List (Ty ESig)} {t a b c : Ty ESig} :
    NoKemKeyGenExpr (Expr.v3 : Expr POps (a :: b :: c :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v4 {Γ : List (Ty ESig)} {t a b c d : Ty ESig} :
    NoKemKeyGenExpr (Expr.v4 : Expr POps (a :: b :: c :: d :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v5 {Γ : List (Ty ESig)} {t a b c d e : Ty ESig} :
    NoKemKeyGenExpr (Expr.v5 : Expr POps (a :: b :: c :: d :: e :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_v6 {Γ : List (Ty ESig)} {t a b c d e f : Ty ESig} :
    NoKemKeyGenExpr (Expr.v6 : Expr POps (a :: b :: c :: d :: e :: f :: t :: Γ) t) = true := rfl
@[simp] theorem noKemKeyGenExpr_unit {Γ : List (Ty ESig)} :
    NoKemKeyGenExpr (.unit : Expr POps Γ .unit) = true := rfl
@[simp] theorem noKemKeyGenExpr_bool {Γ : List (Ty ESig)} (b : Bool) :
    NoKemKeyGenExpr (.bool b : Expr POps Γ .bool) = true := rfl
@[simp] theorem noKemKeyGenExpr_nat {Γ : List (Ty ESig)} (n : ℕ) :
    NoKemKeyGenExpr (.nat n : Expr POps Γ .nat) = true := rfl
@[simp] theorem noKemKeyGenExpr_none {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (.none : Expr POps Γ (.opt t)) = true := rfl
@[simp] theorem noKemKeyGenExpr_nil {Γ : List (Ty ESig)} {t : Ty ESig} :
    NoKemKeyGenExpr (.nil : Expr POps Γ (.list t)) = true := rfl
@[simp] theorem noKemKeyGenExpr_add {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.add a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_sub {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.sub a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_mulK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.mulK k a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_divK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.divK k a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_modK {Γ : List (Ty ESig)} (k : ℕ) (a : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.modK k a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_lt {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.lt a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_eqN {Γ : List (Ty ESig)} (a b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.eqN a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_not {Γ : List (Ty ESig)} (a : Expr POps Γ .bool) :
    NoKemKeyGenExpr (.not a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_and {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (.and a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_ite {Γ : List (Ty ESig)} {t : Ty ESig}
    (c : Expr POps Γ .bool) (a b : Expr POps Γ t) :
    NoKemKeyGenExpr (.ite c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_pair {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps Γ u) :
    NoKemKeyGenExpr (.pair a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_fst {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ (.prod t u)) :
    NoKemKeyGenExpr (.fst a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_snd {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ (.prod t u)) :
    NoKemKeyGenExpr (.snd a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_inl {Γ : List (Ty ESig)} {t u : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.inl a : Expr POps Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_inr {Γ : List (Ty ESig)} {t u : Ty ESig} (a : Expr POps Γ u) :
    NoKemKeyGenExpr (.inr a : Expr POps Γ (.sum t u)) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_some {Γ : List (Ty ESig)} {t : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.some a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_caseOpt {Γ : List (Ty ESig)} {t u : Ty ESig}
    (c : Expr POps Γ (.opt t)) (a : Expr POps Γ u) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.caseOpt c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_caseSum {Γ : List (Ty ESig)} {t u w : Ty ESig}
    (c : Expr POps Γ (.sum t u)) (a : Expr POps (t :: Γ) w) (b : Expr POps (u :: Γ) w) :
    NoKemKeyGenExpr (.caseSum c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_letE {Γ : List (Ty ESig)} {t u : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.letE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_cons {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ t) (b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.cons a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_len {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.len a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_take {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ .nat) (b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.take a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_appendL {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a b : Expr POps Γ (.list t)) :
    NoKemKeyGenExpr (.appendL Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_findB {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) .bool) :
    NoKemKeyGenExpr (.findB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_anyB {Γ : List (Ty ESig)} {t : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) .bool) :
    NoKemKeyGenExpr (.anyB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_mapB {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ)
    (a : Expr POps Γ (.list t)) (b : Expr POps (t :: Γ) u) :
    NoKemKeyGenExpr (.mapB Kb a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_foldrB {Γ : List (Ty ESig)} {t u : Ty ESig} (Kb : ℕ)
    (c : Expr POps Γ (.list t)) (a : Expr POps Γ u) (b : Expr POps (t :: u :: Γ) u) :
    NoKemKeyGenExpr (.foldrB Kb c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_tconst {Γ : List (Ty ESig)} {t : Ty ESig} (a : Expr POps Γ t) :
    NoKemKeyGenExpr (.tconst a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_tget {Γ : List (Ty ESig)} {t : Ty ESig}
    (a : Expr POps Γ (.tbl t)) (b : Expr POps Γ .nat) :
    NoKemKeyGenExpr (.tget a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_tset {Γ : List (Ty ESig)} {t : Ty ESig}
    (c : Expr POps Γ (.tbl t)) (a : Expr POps Γ .nat) (b : Expr POps Γ t) :
    NoKemKeyGenExpr (.tset c a b) = (NoKemKeyGenExpr c && NoKemKeyGenExpr a && NoKemKeyGenExpr b) := rfl
@[simp] theorem noKemKeyGenExpr_e2ePureOp {Γ : List (Ty ESig)}
    (o : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2EPureOp)
    (a : Expr POps Γ (o.dom ℓ)) :
    NoKemKeyGenExpr (e2ePureOp o a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_e2eCurveOp {Γ : List (Ty ESig)}
    (cc : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECurveCheckOp)
    (a : Expr POps Γ
      ((Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eCurveCheckOps ℓ decT encT).dom cc)) :
    NoKemKeyGenExpr (e2eCurveOp cc a) = NoKemKeyGenExpr a := rfl
@[simp] theorem noKemKeyGenExpr_e2eCryptoOp {Γ : List (Ty ESig)}
    (c : Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.E2ECryptoOp)
    (a : Expr POps Γ (c.dom ℓ)) :
    NoKemKeyGenExpr (e2eCryptoOp c a) = (sessionCostExactCryptoOp c && NoKemKeyGenExpr a) := rfl

@[simp] theorem noKemKeyGenExpr_orE {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (orE a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, orE, exprAllOps]; cases exprAllOps sessionCostExactOp a <;> rfl
@[simp] theorem noKemKeyGenExpr_boolEq {Γ : List (Ty ESig)} (a b : Expr POps Γ .bool) :
    NoKemKeyGenExpr (boolEq a b) = (NoKemKeyGenExpr a && NoKemKeyGenExpr b) := by
  dsimp only [NoKemKeyGenExpr, boolEq, exprAllOps]
  cases exprAllOps sessionCostExactOp a <;> cases exprAllOps sessionCostExactOp b <;> rfl
@[simp] theorem noKemKeyGenExpr_isSomeE {Γ : List (Ty ESig)} {t : Ty ESig} (e : Expr POps Γ (.opt t)) :
    NoKemKeyGenExpr (isSomeE e) = NoKemKeyGenExpr e := by
  dsimp only [NoKemKeyGenExpr, isSomeE, exprAllOps]; cases exprAllOps sessionCostExactOp e <;> rfl
@[simp] theorem noKemKeyGenExpr_otherE {Γ : List (Ty ESig)} (e : Expr POps Γ .bool) :
    NoKemKeyGenExpr (otherE e) = NoKemKeyGenExpr e := rfl
@[simp] theorem noKemKeyGenExpr_pGet {Γ : List (Ty ESig)} {t : Ty ESig}
    (m : Expr POps Γ (.prod t t)) (q : Expr POps Γ .bool) :
    NoKemKeyGenExpr (pGet m q) = (NoKemKeyGenExpr m && NoKemKeyGenExpr q) := by
  dsimp only [NoKemKeyGenExpr, pGet, exprAllOps, Expr.v0]
  cases exprAllOps sessionCostExactOp m <;> cases exprAllOps sessionCostExactOp q <;> rfl

@[simp] theorem noKemKeyGenExpr_sendAddrsE {Γ : List (Ty ESig)} (isB : Expr POps Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sendAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[simp] theorem noKemKeyGenExpr_expectedAddrsE {Γ : List (Ty ESig)} (isB : Expr POps Γ .bool) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) isB) =
      NoKemKeyGenExpr isB := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimHooks.expectedAddrsE]
  simp only [noKemKeyGenExpr_ite, noKemKeyGenExpr_optBytes32LitE, Bool.and_true]

@[simp] theorem noKemKeyGenComp_spqrSendComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)) :
    NoKemKeyGenComp
      (spqrSendComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [spqrSendComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[simp] theorem noKemKeyGenComp_spqrRecvComp {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))) :
    NoKemKeyGenComp
      (spqrRecvComp (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) I0 e) =
      NoKemKeyGenExpr e := by
  dsimp only [spqrRecvComp, NoKemKeyGenComp, compAllOps]
  change (NoKemKeyGenExpr e && true) = NoKemKeyGenExpr e
  exact Bool.and_true _

@[simp] theorem noKemKeyGenExpr_drSendPostE {Γ : List (Ty ESig)}
    (gE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT)
    (mE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT)
    (partsE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ)))
    (scE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drSenderChainT (ℓ := ℓ)))
    (remIdE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (pqOutE : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.prod (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)
        (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      gE mE partsE scE remIdE pqOutE) =
      (NoKemKeyGenExpr gE && NoKemKeyGenExpr mE &&
        (NoKemKeyGenExpr partsE &&
          (NoKemKeyGenExpr scE && (NoKemKeyGenExpr remIdE && NoKemKeyGenExpr pqOutE)))) := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimSend.drSendPostE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpIsB,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpVer,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpLocId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRemId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRk,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPrevCtr,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPend,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpEp,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpCEps,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRcs,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpMk,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.sessionVersionEffE]
  simp
  intros; rfl

@[simp] theorem noKemKeyGenComp_drSendC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))) :
    NoKemKeyGenComp (drSendC (spqrDslHooks ℓ P C K decT encT) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [drSendC, spqrDslHooks, Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; rfl

@[simp] theorem noKemKeyGenExpr_drRecvFinishE {Γ : List (Ty ESig)}
    (cE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (partsE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.ghostPartsT (ℓ := ℓ)))
    (remIdE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.IdKey)
    (msgCtrE : Expr POps Γ Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
    (msgCtE : Expr POps Γ (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32))
    (midE : Expr POps Γ (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRatchetMidT ℓ))
    (consOutE : Expr POps Γ (.prod
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.U32)
      (.list (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.drRecvChainT (ℓ := ℓ)))))
    (pqOutE : Expr POps Γ (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
      (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenExpr (Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE
      (ℓ := ℓ) (P := P) (C := C) (K := K) (decT := decT) (encT := encT)
      cE partsE remIdE msgCtrE msgCtE midE consOutE pqOutE) =
      ((NoKemKeyGenExpr cE && NoKemKeyGenExpr partsE) &&
        ((NoKemKeyGenExpr remIdE && (NoKemKeyGenExpr msgCtrE && NoKemKeyGenExpr msgCtE)) &&
          (NoKemKeyGenExpr midE && (NoKemKeyGenExpr consOutE && NoKemKeyGenExpr pqOutE)))) := by
  dsimp only [Computational.Proofs.E2E.Dsl.DrSessionSimRecv.drRecvFinishE,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpIsB,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpVer,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpLocId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpRemId,
    Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpMk]
  simp

@[simp] theorem noKemKeyGenComp_drReceiveC {ι : Type} {T : OracleSpec ι} (I0 : Iface ESig T)
    {Γ : List (Ty ESig)}
    (e : Expr POps Γ (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256))) :
    NoKemKeyGenComp (drReceiveC (spqrDslHooks ℓ P C K decT encT) I0 e) = NoKemKeyGenExpr e := by
  dsimp only [drReceiveC, spqrDslHooks, Computational.Proofs.E2E.Dsl.DrSessionSimHooks.gpPqSt]
  simp
  intros; refine ⟨rfl, rfl, rfl⟩

@[simp] theorem noKemKeyGenComp_drTrArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (trArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (.prod .bool (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))) :
    NoKemKeyGenComp
      (drTrArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2ESamplers I') q Δ qep gsE trArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr trArg) := by
  dsimp only [drTrArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[simp] theorem noKemKeyGenComp_drChArmC {ι : Type} {T : OracleSpec ι}
    (I' : Iface (atomicSig ℓ Pt) T) (q Δ qep : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (chArg : Expr (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT)
      Γ (.prod .bool (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          (.opt Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512))))) :
    NoKemKeyGenComp
      (drChArmC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (coinE2ESamplers I') q Δ qep gsE chArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr chArg) := by
  dsimp only [drChArmC]
  simp
  intros; repeat (first | refine ⟨?_, ?_⟩ | rfl)

@[simp] theorem noKemKeyGenComp_drCrArmC {ι : Type} {T : OracleSpec ι}
    (I0 : Iface ESig T) (q : ℕ) {Γ : List (Ty ESig)}
    (gsE : Expr POps Γ (Computational.Proofs.E2E.Dsl.DrSessionSimBookkeeping.e2eGsTy ℓ))
    (crArg : Expr POps Γ .bool) :
    NoKemKeyGenComp
      (drCrArmC (I := I0) (P := P) (C := C) (K := K) (decT := decT) (encT := encT) q gsE crArg) =
      (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) := by
  dsimp only [drCrArmC, NoKemKeyGenComp, compAllOps, NoKemKeyGenExpr, exprAllOps]
  change ((NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg) && true) =
    (NoKemKeyGenExpr gsE && NoKemKeyGenExpr crArg)
  exact Bool.and_true _

section StepSimulatorsExact

variable {ℓ : ℕ} {Pt : Type} [DecidableEq Pt] [Zero Pt]
  {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
  {Dh : DHFun (BitVec 256) Pt} {encPt : Pt → Bytes}
  {encT : Pt → PublicKey} {decT : PublicKey → Option Pt} {lam : Pt}

local notation "ASig" => atomicSig ℓ Pt
local notation "AOps" => atomicSessionOps ℓ Pt C K Dh encPt encT decT lam
local notation "ESig" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eSig ℓ
local notation "EOps" => Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.e2eOps ℓ zeroPqxdhPrims C K decT encT

theorem drSendAtomicC_cost_exact {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod PlainT BV512))) :
    (drSendAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 67815 + 10 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drSendC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]) .v0)
    (by simp)
  have h2 := drSendC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.PlainT
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV512)))
  simp only [drSendAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

theorem drReceiveAtomicC_cost_exact {ι : Type} {T : OracleSpec ι} (I' : Iface ASig T)
    {Γ : List (Ty ASig)} (inpE : Expr AOps Γ (.prod GhostStT (.prod (B 32) BV256))) :
    (drReceiveAtomicC (C := C) (K := K) (Dh := Dh) (encPt := encPt) (encT := encT)
      (decT := decT) (lam := lam) I' inpE).cost ≤
      inpE.cost + 5104015 + 8 * (ℓ / 32 + 1) := by
  have h1 := liftCompEmpty_cost_exact (Pt := Pt) (C := C) (K := K) (Dh := Dh) (encPt := encPt)
    (encT := encT) (decT := decT) (lam := lam) (I' := I')
    (drReceiveC (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
      (Γ := [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]) .v0)
    (by simp)
  have h2 := drReceiveC_cost (spqrDslHooks ℓ zeroPqxdhPrims C K decT encT) (emptyE2EIface I')
    (.v0 : Expr EOps [.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
      (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
        Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)]
      (.prod Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.GhostStT
        (.prod (Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.B 32)
          Computational.Proofs.SpecLemmas.Reductions.E2E.CompositionCostedTables.BV256)))
  simp only [drReceiveAtomicC, ReductionDsl.Comp.cost, wk1Comp_cost, ReductionDsl.Expr.v0,
    ReductionDsl.Expr.cost] at h1 h2 ⊢
  omega

end StepSimulatorsExact

end SimExactLemmas

end SessionCostExact
end Computational.Proofs.Game.PromotedCostedReds.SessionCostExactDefs
