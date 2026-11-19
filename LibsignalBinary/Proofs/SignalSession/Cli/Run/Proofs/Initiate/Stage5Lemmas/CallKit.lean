/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.Common.InImageKit -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.InImageKit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage5Lemmas.Vtables
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public meta import Lean -- shake: keep
public meta import ProofLib

/-!
# Stage 5 Call Combinators, Frame Tactics, and Stack Splits

`SepProp` frame-extraction tactics, `.data.rel.ro` injection, panic-aware `SepWPp` call
combinators (`s5_call_raw`, `s5_call_futDrop`, `s5_call_dealloc`, `s5_call_dropSS`), symbolic
offsets, and stack-budget split equalities for Stage 5.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688

/-! ## `SepWPp` Combinators and Frame Tactics -/

theorem sepWPp_conseq {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hp : P ⊢ P') (hw : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hw R (Satisfies.mono (sepConj_mono_left hp) hm) hL

theorem sepWPp_with_oom {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sf, hst, hout⟩ := h R hm hL
  exact ⟨sf, hst, hout.elim Or.inl fun h2 => h2.elim (Or.inr ∘ Or.inl) fun h3 =>
    (not_satisfies_false_sepConj h3.2).elim⟩

theorem s5_with_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {RO P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {X : SepProp}, s.mem ⊨ X → s.mem ⊨ (RO ∗ X))
    (hw : SepWPp prog ret s (RO ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  fun R hm hL => hw R (by rw [sepConj_assoc]; exact hro hm) hL

theorem s5_frame_fold {prog : Program} {ret : BitVec 64} {s : State}
    {A B P Rest : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : A ⊢ B) (heq : P = A ∗ Rest)
    (hw : SepWPp prog ret s (B ∗ Rest) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL =>
    hw R (Satisfies.mono (sepConj_mono_left
      (Entails.trans (Entails.of_eq heq) (sepConj_mono_left h))) hm) hL

theorem s5_sep_assoc_r (P Q R : SepProp) : (P ∗ Q) ∗ R = P ∗ (Q ∗ R) := by ac_rfl
theorem s5_sep_swap (A B : SepProp) : A ∗ B = B ∗ A := by ac_rfl
theorem s5_sep_pull (B A R : SepProp) : B ∗ (A ∗ R) = A ∗ (B ∗ R) := by ac_rfl
theorem s5_sep_emp_r (P : SepProp) : P ∗ emp = P := sepConj_emp P
theorem s5_sep_congr_l {P P' : SepProp} (Q : SepProp) (h : P = P') : P ∗ Q = P' ∗ Q :=
  congrArg (· ∗ Q) h
theorem s5_sep_congr_r (P : SepProp) {Q Q' : SepProp} (h : Q = Q') : P ∗ Q = P ∗ Q' :=
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

private meta def mkSepList (es : List Expr) : Expr :=
  match es with
  | [] => mkConst ``Arm64.emp
  | [x] => x
  | x :: xs => mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList xs)

private meta partial def normBvExpr (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  match e with
  | .fvar fvarId =>
    match ← fvarId.getValue? with
    | some val => normBvExpr val
    | none => return e
  | .letE _ _ val body _ =>
    normBvExpr (body.instantiate1 val)
  | .proj typeName idx structExpr =>
    let s' ← normBvExpr structExpr
    let (sfn, sargs) := spineFnArgs s'
    match sfn.constName? with
    | some cname =>
      match (← getEnv).find? cname with
      | some (.ctorInfo ci) =>
        if h : ci.numParams + idx < sargs.size then
          normBvExpr sargs[ci.numParams + idx]
        else
          return .proj typeName idx s'
      | _ => return .proj typeName idx s'
    | none => return .proj typeName idx s'
  | _ =>
    let (fn, args) := spineFnArgs e
    if (fn.constName? == some ``idVt || fn.constName? == some ``sessVt) && args.size == 1 then
      match ← unfoldDefinition? e with
      | some e' => normBvExpr e'
      | none => return e
    else
      return e

private meta partial def fastBvDefEq (e1 e2 : Expr) : MetaM Bool := do
  let e1 := e1.consumeMData
  let e2 := e2.consumeMData
  if e1 == e2 then return true
  let e1' ← normBvExpr e1
  let e2' ← normBvExpr e2
  if e1' == e2' then return true
  let (f1, a1) := spineFnArgs e1'
  let (f2, a2) := spineFnArgs e2'
  let isAddSub1 := (f1.constName? == some ``HAdd.hAdd || f1.constName? == some ``HSub.hSub) && a1.size == 6
  let isAddSub2 := (f2.constName? == some ``HAdd.hAdd || f2.constName? == some ``HSub.hSub) && a2.size == 6
  if (isAddSub1 || isAddSub2) && (e1'.hasFVar || e2'.hasFVar) then
    if isAddSub1 && isAddSub2 && f1.constName? == f2.constName? then
      if !(← fastBvDefEq a1[4]! a2[4]!) then return false
      return ← fastBvDefEq a1[5]! a2[5]!
    else
      return false
  withoutModifyingState (isDefEq e1' e2')

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
      let ty := (← inferType pi).consumeMData
      let (tfn, _) := spineFnArgs ty
      let ok ←
        if ty.isConstOf ``Arm64.SepProp then
          pure false
        else if tfn.constName? == some ``BitVec && !pi.hasExprMVar && !ai.hasExprMVar then
          fastBvDefEq pi ai
        else
          withoutModifyingState (isDefEq pi ai)
      if !ok then return false
  return true

private meta def appendNorm (xs ys : List Expr) : MetaM Expr := do
  if ys.isEmpty then
    return mkApp (mkConst ``s5_sep_emp_r) (mkSepList xs)
  match xs with
  | [] => mkEqRefl (mkSepList ys)
  | [x] => mkEqRefl (mkApp2 (mkConst ``Arm64.sepConj) x (mkSepList ys))
  | x :: rest =>
    let restSep := mkSepList rest
    let ySep := mkSepList ys
    let rySep := mkSepList (rest ++ ys)
    let h_ry ← appendNorm rest ys
    let h1 := mkAppN (mkConst ``s5_sep_assoc_r) #[x, restSep, ySep]
    let h2 := mkAppN (mkConst ``s5_sep_congr_r)
      #[x, mkApp2 (mkConst ``Arm64.sepConj) restSep ySep, rySep, h_ry]
    mkEqTrans h1 h2

private meta partial def normSep (e : Expr) : MetaM (List Expr × Expr) := do
  let (fn, args) := spineFnArgs e
  if fn.constName? == some ``Arm64.sepConj && args.size == 2 then
    let (xs, hx) ← normSep args[0]!
    let (ys, hy) ← normSep args[1]!
    let xSep := mkSepList xs
    let ySep := mkSepList ys
    let h_l := mkAppN (mkConst ``s5_sep_congr_l) #[args[0]!, xSep, args[1]!, hx]
    let h_r := mkAppN (mkConst ``s5_sep_congr_r) #[xSep, args[1]!, ySep, hy]
    let h_app ← appendNorm xs ys
    return (xs ++ ys, ← mkEqTrans h_l (← mkEqTrans h_r h_app))
  else
    let a := e.consumeMData
    return ([a], ← mkEqRefl a)

private meta def unifyAtomArgsIfMVar (p a : Expr) : MetaM Unit := do
  if a.hasExprMVar then
    let (_, pargs) := spineFnArgs p.consumeMData
    let (_, aargs) := spineFnArgs a.consumeMData
    if pargs.size == aargs.size then
      for i in [0 : pargs.size] do
        let _ ← isDefEq pargs[i]! aargs[i]!

private meta def extractOne (ps : List Expr) (a : Expr) :
    MetaM (Option (Expr × List Expr × Expr)) := do
  match ps with
  | [] => return none
  | [p] =>
    if ← atomsMatch p a then
      unifyAtomArgsIfMVar p a
      return some (p, [], ← mkEqRefl p)
    else return none
  | p :: rest =>
    if ← atomsMatch p a then
      unifyAtomArgsIfMVar p a
      return some (p, rest, ← mkEqRefl (mkSepList (p :: rest)))
    else
      match ← extractOne rest a with
      | none => return none
      | some (m, rem', h_sub) =>
        let restSep := mkSepList rest
        let mRemSep := mkSepList (m :: rem')
        let h1 := mkAppN (mkConst ``s5_sep_congr_r) #[p, restSep, mRemSep, h_sub]
        match rem' with
        | [] =>
          let h2 := mkAppN (mkConst ``s5_sep_swap) #[p, m]
          return some (m, [p], ← mkEqTrans h1 h2)
        | _ :: _ =>
          let remSep := mkSepList rem'
          let h2 := mkAppN (mkConst ``s5_sep_pull) #[p, m, remSep]
          return some (m, p :: rem', ← mkEqTrans h1 h2)

private meta def extractMany (pExpr : Expr) (ps : List Expr) :
    List Expr → MetaM (List Expr × List Expr × Expr)
  | [] => do return ([], ps, ← mkEqRefl (mkSepList ps))
  | a :: tailAtoms => do
    let some (m, rem1, h1) ← extractOne ps a
      | throwError "s5_frame: atom not found in precondition:\n  {a}\npre:\n  {pExpr}"
    let (ms, remFinal, h2) ← extractMany pExpr rem1 tailAtoms
    if rem1.isEmpty then
      return ([m], [], h1)
    else
      let h_step := mkAppN (mkConst ``s5_sep_congr_r)
        #[m, mkSepList rem1, mkSepList (ms ++ remFinal), h2]
      return (m :: ms, remFinal, ← mkEqTrans h1 h_step)

private meta def mkSplitEqProof (pExpr aExpr : Expr) : TacticM (Expr × Expr) := do
  let (ps, hpNorm) ← normSep pExpr
  let (aAtoms0, haNorm0) ← normSep aExpr
  let (matched, rem, hPerm) ← extractMany pExpr ps aAtoms0
  let aExpr ← instantiateMVars aExpr
  let aAtoms ← aAtoms0.mapM instantiateMVars
  let haNorm ← instantiateMVars haNorm0
  let restExpr := mkSepList rem
  let aSep := mkSepList aAtoms
  let hApp ← appendNorm matched rem
  let g1 ← mkEqTrans hpNorm (← mkEqTrans hPerm (← mkEqSymm hApp))
  let g2 := mkAppN (mkConst ``s5_sep_congr_l) #[aSep, aExpr, restExpr, ← mkEqSymm haNorm]
  let heq ← mkEqTrans g1 g2
  return (restExpr, heq)

elab "s5_ac_rfl" : tactic => withMainContext do
  let g ← getMainGoal
  let gty ← instantiateMVars (← g.getType)
  let (efn, eargs) := spineFnArgs gty
  if efn.constName? != some ``Eq || eargs.size != 3 then
    throwError "s5_ac_rfl expected equality goal, got: {gty}"
  let lhs := eargs[1]!
  let rhs := eargs[2]!
  let (rfn, rargs) := spineFnArgs rhs
  let isDirectTailMVar ←
    if rfn.constName? == some ``Arm64.sepConj && rargs.size == 2 && rargs[1]!.isMVar then
      not <$> rargs[1]!.mvarId!.isAssigned
    else pure false
  if isDirectTailMVar then
    let aExpr := rargs[0]!
    let fMVar := rargs[1]!
    let (restExpr, heq) ← mkSplitEqProof lhs aExpr
    fMVar.mvarId!.assign restExpr
    g.assign heq
    let gs ← getGoals
    setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)
  else
    let (rAtoms, _) ← normSep rhs
    let hasLastMVar ←
      if rAtoms.length >= 2 && rAtoms.getLast!.isMVar then
        not <$> rAtoms.getLast!.mvarId!.isAssigned
      else pure false
    if hasLastMVar then
      let fMVar := rAtoms.getLast!
      let prefixAtoms := rAtoms.dropLast
      let (ps, _) ← normSep lhs
      let (_, rem, _) ← extractMany lhs ps prefixAtoms
      fMVar.mvarId!.assign (mkSepList rem)
      let rhsInst ← instantiateMVars rhs
      let (rem2, heq) ← mkSplitEqProof lhs rhsInst
      if !rem2.isConstOf ``Arm64.emp then
        throwError "s5_ac_rfl: leftover atoms on LHS:\n  {rem2}"
      let hEmp := mkApp (mkConst ``s5_sep_emp_r) rhsInst
      g.assign (← mkEqTrans heq hEmp)
      let gs ← getGoals
      setGoals (gs.filter fun m => m != g && m != fMVar.mvarId!)
    else
      let (rem, heq) ← mkSplitEqProof lhs rhs
      if !rem.isConstOf ``Arm64.emp then
        throwError "s5_ac_rfl: leftover atoms on LHS:\n  {rem}"
      let hEmp := mkApp (mkConst ``s5_sep_emp_r) rhs
      g.assign (← mkEqTrans heq hEmp)
      let gs ← getGoals
      setGoals (gs.filter (· != g))

elab "s5_have_eq " h:ident " : " rhsStx:term " := " prfStx:term : tactic =>
  withMainContext do
    let g0 ← getMainGoal
    let gty := (← instantiateMVars (← g0.getType)).consumeMData.headBeta.consumeMData
    let (fn, args) := spineFnArgs gty
    let lhsExpr ←
      if fn.constName? == some ``Arm64.Entails && args.size == 2 then pure args[0]!
      else if args.size >= 4 then pure args[3]!
      else throwError "s5_have_eq: unsupported goal {gty}"
    let (rhsExpr, holeMVars) ←
      elabTermWithHoles rhsStx (some (mkConst ``Arm64.SepProp)) `s5_have_eq true
    let eqTy ← mkEq lhsExpr rhsExpr
    let eqProof0 ← elabTermEnsuringType prfStx (some eqTy)
    for m in holeMVars do
      unless ← m.isAssigned do
        throwError "s5_have_eq: unassigned hole {mkMVar m}"
    let eqProof ← instantiateMVars eqProof0
    let eqTyInst ← instantiateMVars eqTy
    let (_, g1) ← (← g0.assert h.getId eqTyInst eqProof).intro1P
    replaceMainGoal [g1]

elab "s5_clear_callees" : tactic => withMainContext do
  let g ← getMainGoal
  let lctx ← getLCtx
  let mut toClear : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let (fn, _) := spineFnArgs decl.type.consumeMData
      if fn.constName? == some ``Arm64.subroutine_ok then
        toClear := toClear.push decl.fvarId
  let g' ← g.tryClearMany toClear
  replaceMainGoal [g']

elab "s5_rw_pre " h:term : tactic => withMainContext do
  let g0 ← getMainGoal
  let gty0 ← instantiateMVars (← g0.getType)
  let gty := gty0.consumeMData.headBeta.consumeMData
  let g ← if gty == gty0 then pure g0 else g0.replaceTargetDefEq gty
  let otherGoals := (← getGoals).filter (· != g0)
  let hExpr ← elabTerm h none
  let hTy := (← instantiateMVars (← inferType hExpr)).consumeMData.headBeta.consumeMData
  let (hfn, hargs) := spineFnArgs hTy
  if hfn.constName? != some ``Eq || hargs.size != 3 then
    throwError "s5_rw_pre expected an equality proof, got: {hTy}"
  let aExpr := hargs[1]!
  let bExpr := hargs[2]!
  let (fn, args) := spineFnArgs gty
  if args.size < 4 then
    throwError "s5_rw_pre expected goal of arity ≥ 4, got: {gty}"
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

elab "s5_fold_pre " h:term : tactic => withMainContext do
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
    throwError "s5_fold_pre expected 7-arg SepWPp goal, got {args.size}: {gty}"
  let #[prog, ret, s, pExpr, qExpr, qpExpr, oom] := args | unreachable!
  let (restExpr, heqExpr) ← mkSplitEqProof pExpr aExpr
  let rhs2 := mkApp2 (mkConst ``Arm64.sepConj) bExpr restExpr
  let hwMVar ← mkFreshExprMVar
    (some (mkAppN fn #[prog, ret, s, rhs2, qExpr, qpExpr, oom]))
  g.assign (mkAppN (mkConst ``s5_frame_fold)
    #[prog, ret, s, aExpr, bExpr, pExpr, restExpr, qExpr, qpExpr, oom, hExpr, heqExpr, hwMVar])
  setGoals (hwMVar.mvarId! :: otherGoals)

elab "inImageKitClearInvHyps" : tactic => pure ()

elab "s5_close_frame" : tactic => do
  evalTactic (← `(tactic| refine Entails.of_eq ?_))
  evalTactic (← `(tactic| (conv => lhs; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, *])))
  evalTactic (← `(tactic| (conv => rhs; arg 1; simp (config := { zetaDelta := false, failIfUnchanged := false }) only [wp_norm, arm64_norm, *])))
  withMainContext do
    let g ← getMainGoal
    let gty ← instantiateMVars (← g.getType)
    let (efn, eargs) := spineFnArgs gty
    if efn.constName? != some ``Eq || eargs.size != 3 then
      throwError "s5_close_frame expected equality goal, got: {gty}"
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

@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offEpilogue         : BitVec 64 := 848#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offErrTramp         : BitVec 64 := 4828#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offEntry            : BitVec 64 := 5252#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterUnackMsg    : BitVec 64 := 5288#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterUnackKyb    : BitVec 64 := 5304#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterRegShim     : BitVec 64 := 5320#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterRegPoll     : BitVec 64 := 5348#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offErrDealloc       : BitVec 64 := 5488#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offErrAfterDealloc  : BitVec 64 := 5500#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offRegDrop          : BitVec 64 := 5620#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offRegDealloc       : BitVec 64 := 5664#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offRegDeallocDone   : BitVec 64 := 5684#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offSave             : BitVec 64 := 5692#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterSaveShim    : BitVec 64 := 5732#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterSavePoll    : BitVec 64 := 5760#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offSaveDrop         : BitVec 64 := 5876#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offSaveDealloc      : BitVec 64 := 5920#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offSaveDeallocDone  : BitVec 64 := 5940#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offPromote          : BitVec 64 := 5948#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterMemcpy      : BitVec 64 := 5972#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offStore            : BitVec 64 := 5992#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterStoreShim   : BitVec 64 := 6012#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offAfterStorePoll   : BitVec 64 := 6040#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offStoreDrop        : BitVec 64 := 6096#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offStoreDealloc     : BitVec 64 := 6140#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offStoreDeallocDone : BitVec 64 := 6160#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offOkClean          : BitVec 64 := 6168#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offOkAfterDealloc   : BitVec 64 := 6192#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offOkAfterDrop      : BitVec 64 := 6216#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offErrEntry         : BitVec 64 := 6232#64
@[expose, scoped simp, scoped arm64_norm, scoped wp_norm] def offErrEntryDropDone : BitVec 64 := 6248#64

theorem spAligned_fsp {s0 s : State}
    (h0 : s0.spAligned = true) (hsp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame) :
    s.spAligned = true := by
  simp only [State.spAligned, hsp, beq_iff_eq, cliInitiateFrame_eq] at h0 ⊢
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_and, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.and_two_pow_sub_one_eq_mod _ 4] at h1 ⊢
  omega

theorem s5_stackAt_sub_split (sp : BitVec 64) {sub full : Nat}
    (hle : sub ≤ full) (hfull : full ≤ 2 ^ 64) :
    stackAt sp full =
      memRegion (sp - BitVec.ofNat 64 full) (full - sub) ∗ stackAt sp sub := by
  dsimp only [stackAt]
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 full)
    (n := full - sub) (k := sub) (b' := sp - BitVec.ofNat 64 sub)
    (Nat.sub_add_cancel hle).symm
    (by have hs : BitVec.ofNat 64 full = BitVec.ofNat 64 (full - sub) + BitVec.ofNat 64 sub := by
          rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
        rw [hs]; bv_omega)
    hfull

theorem stkSub_hi {stk : Nat} (h64 : stk ≤ 2 ^ 63) : stk - cliInitiateFrame ≤ 2 ^ 64 := by omega

theorem extHook_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    extHookStack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : extHookStack ≤ 65536 := by decide
  omega

theorem dropSS_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    FromRecordCallees.dropSessionStructureLocal2Stack ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : FromRecordCallees.dropSessionStructureLocal2Stack ≤ 65536 := by decide
  omega

theorem unack_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    allocHookStack + 176 ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : allocHookStack + 176 ≤ 65536 := by decide
  omega

theorem prom_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    96 ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  omega

theorem unack_ext_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    extHookStack + 176 ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : extHookStack + 176 ≤ 65536 := by decide
  omega

theorem prom_ext_le_stkSub {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    extHookStack + 32 ≤ stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 : extHookStack + 32 ≤ 65536 := by decide
  omega

private theorem memRegion_eq_cells :
    ∀ (k : Nat), 8 * k ≤ 2 ^ 64 → ∀ (b : BitVec 64), memRegion b (8 * k) = cells b k
  | 0, _, b => by simp [cells, memRegion_zero]
  | k + 1, hk, b => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega,
        ProofLib.memRegion_split' (b := b) (n := 8) (k := 8 * k)
          (b' := b + 8#64) rfl (by bv_omega) (by omega),
        ProofLib.memRegion_eight b, memRegion_eq_cells k (by omega) (b + 8#64)]
    simp [cells]

theorem stackAt_split_setUnack (fsp : BitVec 64) :
    stackAt fsp (allocHookStack + 176) =
      stackAt (fsp - 144#64) (allocHookStack + 32) ∗
      cells (fsp - 144#64) 18 := by
  have hle : allocHookStack + 176 ≤ 2 ^ 64 := by decide
  dsimp only [stackAt]
  have hb : fsp - BitVec.ofNat 64 (allocHookStack + 176) =
      (fsp - 144#64) - BitVec.ofNat 64 (allocHookStack + 32) := by
    dsimp only [allocHookStack]
    bv_omega
  rw [hb,
      ProofLib.memRegion_split'
        (b := (fsp - 144#64) - BitVec.ofNat 64 (allocHookStack + 32))
        (n := allocHookStack + 32) (k := 144)
        (b' := fsp - 144#64) (by omega)
        (by dsimp only [allocHookStack]; bv_omega) hle]
  exact congrArg (memRegion _ _ ∗ ·) (memRegion_eq_cells 18 (by decide) (fsp - 144#64))

theorem stackAt_96_eq_promoteState_cells (fsp : BitVec 64) :
    stackAt fsp 96 = cells (fsp - 96#64) 8 ∗ cells (fsp - 32#64) 4 := by
  dsimp only [stackAt]
  rw [show fsp - BitVec.ofNat 64 96 = fsp - 96#64 from rfl,
      ProofLib.memRegion_split' (b := fsp - 96#64) (n := 64) (k := 32)
        (b' := fsp - 32#64) rfl (by bv_omega) (by decide)]
  exact congrArg₂ sepConj
    (memRegion_eq_cells 8 (by decide) (fsp - 96#64))
    (memRegion_eq_cells 4 (by decide) (fsp - 32#64))

theorem stackAt_split_setUnack_ext (fsp : BitVec 64) :
    stackAt fsp (extHookStack + 176) =
      stackAt (fsp - 144#64) (extHookStack + 32) ∗
      cells (fsp - 144#64) 18 := by
  have hle : extHookStack + 176 ≤ 2 ^ 64 := by decide
  dsimp only [stackAt]
  have hb : fsp - BitVec.ofNat 64 (extHookStack + 176) =
      (fsp - 144#64) - BitVec.ofNat 64 (extHookStack + 32) := by
    dsimp only [extHookStack]
    bv_omega
  rw [hb,
      ProofLib.memRegion_split'
        (b := (fsp - 144#64) - BitVec.ofNat 64 (extHookStack + 32))
        (n := extHookStack + 32) (k := 144)
        (b' := fsp - 144#64) (by omega)
        (by dsimp only [extHookStack]; bv_omega) hle]
  exact congrArg (memRegion _ _ ∗ ·) (memRegion_eq_cells 18 (by decide) (fsp - 144#64))

@[scoped arm64_norm, scoped wp_norm]
theorem fsp_epilogue_eqs (sp0 : BitVec 64) :
    let fsp := sp0 - BitVec.ofNat 64 cliInitiateFrame
    fsp + 4096#64 + 3216#64 = sp0 - 0x60#64 ∧
    (sp0 - 0x60#64) + 0x60#64 = sp0 ∧
    (sp0 - 0x60#64) + 0#64 = sp0 - 0x60#64 ∧
    (sp0 - 0x60#64) + 80#64 = (sp0 - 0x60#64) + 0x50#64 ∧
    (sp0 - 0x60#64) + 64#64 = (sp0 - 0x60#64) + 0x40#64 ∧
    (sp0 - 0x60#64) + 48#64 = (sp0 - 0x60#64) + 0x30#64 ∧
    (sp0 - 0x60#64) + 32#64 = (sp0 - 0x60#64) + 0x20#64 ∧
    (sp0 - 0x60#64) + 16#64 = (sp0 - 0x60#64) + 0x10#64 := by
  dsimp only [cliInitiateFrame]
  exact ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega,
         by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

@[scoped arm64_norm, scoped wp_norm]
theorem out48_add_eqs (out : BitVec 64) :
    out + 0#64 = out ∧
    out + 16#64 = out + 0x10#64 ∧
    out + 32#64 = out + 0x20#64 ∧
    out + 0x10#64 + 8#64 = out + 0x18#64 ∧
    out + 0x20#64 + 8#64 = out + 0x28#64 :=
  ⟨by bv_omega, by bv_omega, by bv_omega, by bv_omega, by bv_omega⟩

/-! ## Specialized Call Helpers -/

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
