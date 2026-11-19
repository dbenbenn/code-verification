/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.CallSpecs
public meta import LibsignalBinary.Proofs.Common.InImageKit -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.InImageKit -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
public meta import Lean -- shake: keep
public meta import ProofLib
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] calleeSavedVRegs_writeVReg128_0

@[arm64_norm, wp_norm]
theorem ispoll_extra_add_eqs (a sp v1 v2 : BitVec 64) :
    a + 0#64 = a ∧
    a + 8#64 + 8#64 = a + 16#64 ∧
    a + 16#64 + 8#64 = a + 24#64 ∧
    sp - 0x80#64 + 8#64 = sp - 0x78#64 ∧
    (v2 ++ v1 : BitVec 128).extractLsb' 0 64 = v1 ∧
    (v2 ++ v1 : BitVec 128).extractLsb' 64 64 = v2 := by
  refine ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_bits, by bv_bits⟩

@[expose, simp, arm64_norm, wp_norm] def offAfterGet     : BitVec 64 := 68#64
@[expose, simp, arm64_norm, wp_norm] def offAfterDecode  : BitVec 64 := 104#64
@[expose, simp, arm64_norm, wp_norm] def offAfterDealloc : BitVec 64 := 220#64
@[expose, simp, arm64_norm, wp_norm] def offAfterEq      : BitVec 64 := 304#64
@[expose, simp, arm64_norm, wp_norm] def offErrShuffle   : BitVec 64 := 316#64
@[expose, simp, arm64_norm, wp_norm] def offErrLdr60     : BitVec 64 := 332#64
@[expose, simp, arm64_norm, wp_norm] def offErrStur11    : BitVec 64 := 352#64
@[expose, simp, arm64_norm, wp_norm] def offOkTail       : BitVec 64 := 400#64
@[expose, simp, arm64_norm, wp_norm] def offAfterSer     : BitVec 64 := 412#64
@[expose, simp, arm64_norm, wp_norm] def offAfterPut     : BitVec 64 := 440#64
@[expose, simp, arm64_norm, wp_norm] def offEpilogue     : BitVec 64 := 444#64
@[expose, simp, arm64_norm, wp_norm] def offEpiLdur11    : BitVec 64 := 472#64
@[expose, simp, arm64_norm, wp_norm] def offEpiStr44     : BitVec 64 := 488#64

theorem sepWP_conseq {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hw : SepWP prog pc s P' post oom) :
    SepWP prog pc s P post oom := by
  unfold SepWP at hw ⊢
  exact fun R hm => hw R (Satisfies.mono (sepConj_mono_left h) hm)

theorem sepWP_step_to {prog : Program} {mid target : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s P (fun sm Pm => SepWP prog target sm Pm post)) :
    SepWP prog target s P post :=
  SepWP.seq (mid := mid) h fun _ _ _ _ hnext => hnext

theorem sepWPp_frame_fold {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest)
    (hw : SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL =>
    hw R (Satisfies.mono (sepConj_mono_left (Entails.trans (Entails.of_eq heq) (sepConj_mono_left h))) hm) hL

theorem ispoll_sep_assoc_r (P Q R : SepProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by ac_rfl
theorem ispoll_sep_swap (A B : SepProp) : A ∗ B = B ∗ A := by ac_rfl
theorem ispoll_sep_pull (B A R : SepProp) : B ∗ (A ∗ R) = A ∗ (B ∗ R) := by ac_rfl
theorem ispoll_sep_emp_r (P : SepProp) : P ∗ emp = P := sepConj_emp P
theorem ispoll_sep_congr_l {P P' : SepProp} (Q : SepProp) (h : P = P') : P ∗ Q = P' ∗ Q :=
  congrArg (· ∗ Q) h
theorem ispoll_sep_congr_r (P : SepProp) {Q Q' : SepProp} (h : Q = Q') : P ∗ Q = P ∗ Q' :=
  congrArg (P ∗ ·) h

section FrameTactics
open Lean Elab Tactic Meta

private meta partial def spineFnArgs (e : Expr) : Expr × Array Expr :=
  let rec go (e : Expr) (acc : List Expr) : Expr × Array Expr :=
    match e with
    | .mdata _ b => go b acc
    | .app f a   => go f (a.consumeMData :: acc)
    | _          => (e, acc.toArray)
  go e []

private meta partial def flattenSep (e : Expr) : Array Expr :=
  let (fn, args) := spineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    flattenSep args[0]! ++ flattenSep args[1]!
  else
    #[e.consumeMData]

private meta def mkSepList (es : List Expr) : Expr :=
  match es with
  | [] => mkConst ``Arm64.emp
  | [x] => x
  | x :: xs => mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList xs)

private meta def atomsMatch (p a : Expr) : MetaM Bool := do
  let p := p.consumeMData
  let a := a.consumeMData
  if p == a then return true
  let (pfn, pargs) := spineFnArgs p
  let (afn, aargs) := spineFnArgs a
  if pfn != afn || pargs.size != aargs.size then
    return false
  for i in [0 : pargs.size] do
    let pi := pargs[i]!
    let ai := aargs[i]!
    if pi != ai then
      let ty ← inferType pi
      let ok ← if ty.consumeMData.isConstOf ``Arm64.SepProp then pure false
               else withoutModifyingState (isDefEq pi ai)
      if !ok then return false
  return true

private meta def appendNorm (xs ys : List Expr) : MetaM Expr := do
  if ys.isEmpty then
    return mkApp (mkConst ``ispoll_sep_emp_r) (mkSepList xs)
  match xs with
  | [] => mkEqRefl (mkSepList ys)
  | [x] => mkEqRefl (mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList ys))
  | x :: rest =>
    let restSep := mkSepList rest
    let ySep := mkSepList ys
    let rySep := mkSepList (rest ++ ys)
    let h_ry ← appendNorm rest ys
    let h1 := mkAppN (mkConst ``ispoll_sep_assoc_r) #[x, restSep, ySep]
    let h2 := mkAppN (mkConst ``ispoll_sep_congr_r)
      #[x, mkApp2 (mkConst ``Arm64.sepConj) restSep ySep, rySep, h_ry]
    mkEqTrans h1 h2

private meta partial def normSep (e : Expr) : MetaM (List Expr × Expr) := do
  let (fn, args) := spineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    let (xs, hx) ← normSep args[0]!
    let (ys, hy) ← normSep args[1]!
    let xSep := mkSepList xs
    let ySep := mkSepList ys
    let h_l := mkAppN (mkConst ``ispoll_sep_congr_l) #[args[0]!, xSep, args[1]!, hx]
    let h_r := mkAppN (mkConst ``ispoll_sep_congr_r) #[xSep, args[1]!, ySep, hy]
    let h_app ← appendNorm xs ys
    return (xs ++ ys, ← mkEqTrans h_l (← mkEqTrans h_r h_app))
  else
    let a := e.consumeMData
    return ([a], ← mkEqRefl a)

private meta def extractOne (ps : List Expr) (a : Expr) :
    MetaM (Option (Expr × List Expr × Expr)) := do
  match ps with
  | [] => return none
  | [p] =>
    if ← atomsMatch p a then return some (p, [], ← mkEqRefl p)
    else return none
  | p :: rest =>
    if ← atomsMatch p a then
      return some (p, rest, ← mkEqRefl (mkSepList (p :: rest)))
    else
      match ← extractOne rest a with
      | none => return none
      | some (m, rem', h_sub) =>
        let restSep := mkSepList rest
        let mRemSep := mkSepList (m :: rem')
        let h1 := mkAppN (mkConst ``ispoll_sep_congr_r) #[p, restSep, mRemSep, h_sub]
        match rem' with
        | [] =>
          let h2 := mkAppN (mkConst ``ispoll_sep_swap) #[p, m]
          return some (m, [p], ← mkEqTrans h1 h2)
        | _ :: _ =>
          let remSep := mkSepList rem'
          let h2 := mkAppN (mkConst ``ispoll_sep_pull) #[p, m, remSep]
          return some (m, p :: rem', ← mkEqTrans h1 h2)

private meta def extractMany (pExpr : Expr) (ps : List Expr) :
    List Expr → MetaM (List Expr × List Expr × Expr)
  | [] => do return ([], ps, ← mkEqRefl (mkSepList ps))
  | a :: tailAtoms => do
    let some (m, rem1, h1) ← extractOne ps a
      | throwError "ispoll_frame: atom not found in precondition:\n  {a}\npre:\n  {pExpr}"
    let (ms, remFinal, h2) ← extractMany pExpr rem1 tailAtoms
    if rem1.isEmpty then
      return ([m], [], h1)
    else
      let h_step := mkAppN (mkConst ``ispoll_sep_congr_r)
        #[m, mkSepList rem1, mkSepList (ms ++ remFinal), h2]
      return (m :: ms, remFinal, ← mkEqTrans h1 h_step)

private meta def mkSplitEqProof (pExpr aExpr : Expr) : TacticM (Expr × Expr) := do
  let (ps, hpNorm) ← normSep pExpr
  let (aAtoms, haNorm) ← normSep aExpr
  let (matched, rem, hPerm) ← extractMany pExpr ps aAtoms
  let restExpr := mkSepList rem
  let aSep := mkSepList aAtoms
  let hApp ← appendNorm matched rem
  let g1 ← mkEqTrans hpNorm (← mkEqTrans hPerm (← mkEqSymm hApp))
  let g2 := mkAppN (mkConst ``ispoll_sep_congr_l) #[aSep, aExpr, restExpr, ← mkEqSymm haNorm]
  let heq ← mkEqTrans g1 g2
  return (restExpr, heq)

/-- Close `lhs = rhs` between permutations of `SepProp` atoms in O(N²) steps without `ac_rfl`. -/
elab "ispoll_ac_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let gty ← instantiateMVars (← g.getType)
  let (efn, eargs) := spineFnArgs gty
  if efn.constName? != some ``Eq || eargs.size != 3 then
    throwError "ispoll_ac_rfl expected equality goal, got: {gty}"
  let lhs := eargs[1]!
  let rhs := eargs[2]!
  let (rem, heq) ← mkSplitEqProof lhs rhs
  if !rem.isConstOf ``Arm64.emp then
    throwError "ispoll_ac_rfl: leftover atoms on LHS:\n  {rem}"
  let hEmp := mkApp (mkConst ``ispoll_sep_emp_r) rhs
  g.assign (← mkEqTrans heq hEmp)
  let gs ← getGoals
  setGoals (gs.filter (· != g))

elab "ispoll_rw_pre " h:term : tactic => withMainContext do
  let g0 ← getMainGoal
  let gty0 ← instantiateMVars (← g0.getType)
  let gty := gty0.consumeMData.headBeta.consumeMData
  let g ← if gty == gty0 then pure g0 else g0.replaceTargetDefEq gty
  let otherGoals := (← getGoals).filter (· != g0)
  let hExpr ← elabTerm h none
  let hTy := (← instantiateMVars (← inferType hExpr)).consumeMData.headBeta.consumeMData
  let (hfn, hargs) := spineFnArgs hTy
  if hfn.constName? != some ``Eq || hargs.size != 3 then
    throwError "ispoll_rw_pre expects an equality proof, got: {hTy}"
  let aExpr := hargs[1]!
  let bExpr := hargs[2]!
  let (fn, args) := spineFnArgs gty
  if args.size < 4 then
    throwError "ispoll_rw_pre expected goal of arity ≥ 4, got: {gty}"
  let pExpr := args[3]!
  let (restExpr, heqExpr) ← mkSplitEqProof pExpr aExpr
  let rhs2 := mkApp2 (mkConst ``Arm64.sepConj) bExpr restExpr
  let lamSep := Lean.mkLambda `x .default (mkConst ``Arm64.SepProp)
    (mkApp2 (mkConst ``Arm64.sepConj) (.bvar 0) restExpr)
  let hpEq ← mkEqTrans heqExpr (← mkCongrArg lamSep hExpr)
  let newGoalTy := mkAppN fn (args.set! 3 rhs2)
  let hwMVar ← mkFreshExprMVar (some newGoalTy)
  let ctxLam := Lean.mkLambda `P .default (mkConst ``Arm64.SepProp)
    (mkAppN fn (args.set! 3 (.bvar 0)))
  let hGoalEq ← mkCongrArg ctxLam (← mkEqSymm hpEq)
  g.assign (← mkEqMP hGoalEq hwMVar)
  setGoals (hwMVar.mvarId! :: otherGoals)

elab "ispoll_fold_pre " h:term : tactic => withMainContext do
  let g0 ← getMainGoal
  let gty0 ← instantiateMVars (← g0.getType)
  let gty := gty0.consumeMData.headBeta.consumeMData
  let g ← if gty == gty0 then pure g0 else g0.replaceTargetDefEq gty
  let otherGoals := (← getGoals).filter (· != g0)
  let hExpr ← elabTerm h none
  let hTy := (← instantiateMVars (← inferType hExpr)).consumeMData.headBeta.consumeMData
  let (_, hargs) := spineFnArgs hTy
  let aExpr := hargs[0]!
  let bExpr := hargs[1]!
  let (fn, args) := spineFnArgs gty
  if args.size < 7 then
    throwError "ispoll_fold_pre expected 7-arg SepWPp goal, got {args.size}: {gty}"
  let #[prog, ret, s, pExpr, qExpr, qpExpr, oom] := args | unreachable!
  let (restExpr, heqExpr) ← mkSplitEqProof pExpr aExpr
  let rhs2 := mkApp2 (mkConst ``Arm64.sepConj) bExpr restExpr
  let hwMVar ← mkFreshExprMVar
    (some (mkAppN fn #[prog, ret, s, rhs2, qExpr, qpExpr, oom]))
  g.assign (mkAppN (mkConst ``sepWPp_frame_fold)
    #[prog, ret, s, aExpr, bExpr, pExpr, restExpr, qExpr, qpExpr, oom, hExpr, heqExpr, hwMVar])
  setGoals (hwMVar.mvarId! :: otherGoals)

elab "ispoll_close_frame" : tactic => do
  evalTactic (← `(tactic| refine Entails.of_eq ?_))
  evalTactic (← `(tactic| (conv => lhs; simp only [wp_norm, arm64_norm, *])))
  evalTactic (← `(tactic| (conv => rhs; arg 1; simp only [wp_norm, arm64_norm, *])))
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := spineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "ispoll_close_frame expected equality goal, got: {gty}"
    let lhs := eargs[1]!
    let rhs := eargs[2]!
    let (_, rargs) := spineFnArgs rhs
    let calleePre := rargs[0]!
    let fMVar := rargs[1]!
    let (restExpr, heqExpr) ← mkSplitEqProof lhs calleePre
    fMVar.mvarId!.assign restExpr
    g.assign heqExpr
    let gs ← getGoals
    setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)

end FrameTactics

end CryptoVerification.SignalSession.Cli.Store.IdSavePoll.Helpers
