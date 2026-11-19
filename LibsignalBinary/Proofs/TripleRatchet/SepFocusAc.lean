/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import ProofLib
public import LibsignalBinary.Proofs.Common.SharedHelpers -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- proof-setup: allow-public-import
public meta import Lean
public meta import ProofLib
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import

/-!
# Polymorphic `sep_focus_ac` and Congruence-Aware `sep_ac_rfl_defeq` Tactics

Solves `P = A ∗ ?Frame` (`sep_focus_ac`) and ground `P = Q` (`sep_ac_rfl_defeq`) via
`eqACOfTblPoly`, matching atoms syntactically first and falling back to head-preserving
argument `isDefEq` (e.g. `261760` vs `rootStack - closureStack` or `-1#64` vs `0xffffffffffffffff#64`)
so leaf `SepProp` definitions are never unfolded in either the elaborator or the Lean kernel.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.SepFocusAc

private meta partial def flattenSepAtoms (e : Lean.Expr) (acc : Array Lean.Expr := #[]) :
    Array Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    flattenSepAtoms (e.getArg! 1) (flattenSepAtoms (e.getArg! 0) acc)
  else if e.isConstOf ``Arm64.SepProp.emp then
    acc
  else
    acc.push e

private meta def mkSepChain (atoms : Array Lean.Expr) : Lean.Expr :=
  if h : atoms.size = 0 then
    Lean.mkConst ``Arm64.SepProp.emp
  else
    let last := atoms[atoms.size - 1]'(by omega)
    (atoms.extract 0 (atoms.size - 1)).foldr
      (fun a acc => Lean.mkApp2 (Lean.mkConst ``Arm64.SepProp.sepConj) a acc)
      last

private meta def boundedIsDefEq (a b : Lean.Expr) (hb : Nat := 50000 * 1000) : Lean.MetaM Bool := do
  if a == b then
    return true
  Lean.tryCatchRuntimeEx
    (withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := hb }) <|
      Lean.Core.withCurrHeartbeats do
        if ← Lean.Meta.withReducibleAndInstances (Lean.Meta.isDefEq a b) then
          return true
        Lean.Meta.isDefEq a b)
    (fun _ => pure false)

private meta partial def atomCongrDefEq (a b : Lean.Expr) : Lean.MetaM Bool := do
  let a := a.consumeMData
  let b := b.consumeMData
  if a == b then
    return true
  if ← Lean.tryCatchRuntimeEx
      (withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := 10000 * 1000 }) <|
        Lean.Core.withCurrHeartbeats (Lean.Meta.withReducibleAndInstances (Lean.Meta.isDefEq a b)))
      (fun _ => pure false) then
    return true
  if a.isAppOfArity ``Arm64.SepProp.sepExists 2 && b.isAppOfArity ``Arm64.SepProp.sepExists 2 then
    if ← boundedIsDefEq (a.getArg! 0) (b.getArg! 0) then
      return ← Lean.Meta.withLocalDeclD `_x (a.getArg! 0) fun x =>
        atomCongrDefEq ((a.getArg! 1).beta #[x]) ((b.getArg! 1).beta #[x])
    return false
  if a.isAppOfArity ``Arm64.SepProp.sepConj 2 && b.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    if ← atomCongrDefEq (a.getArg! 0) (b.getArg! 0) then
      return ← atomCongrDefEq (a.getArg! 1) (b.getArg! 1)
    return false
  if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
    let argsA := a.getAppArgs
    let argsB := b.getAppArgs
    for k in [:argsA.size] do
      let i := argsA.size - 1 - k
      if !(← boundedIsDefEq argsA[i]! argsB[i]!) then
        return false
    return true
  return false

private meta partial def reifyLhsTree (e : Lean.Expr) :
    StateRefT (Array Lean.Expr) Lean.MetaM Lean.Expr := do
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let l ← reifyLhsTree (e.getArg! 0)
    let r ← reifyLhsTree (e.getArg! 1)
    return Lean.mkApp2 (Lean.mkConst ``ProofLib.SepTree.sep) l r
  else if e.isConstOf ``Arm64.SepProp.emp then
    return Lean.mkConst ``ProofLib.SepTree.nil
  else
    let tbl ← get
    let idx := tbl.size
    set (tbl.push e)
    return Lean.mkApp (Lean.mkConst ``ProofLib.SepTree.atom) (Lean.mkRawNatLit idx)

private meta partial def reifyRhsTree (tbl : Array Lean.Expr) (e : Lean.Expr) :
    StateRefT (Array Bool) Lean.MetaM (Option Lean.Expr) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Arm64.SepProp.sepConj 2 then
    let some l ← reifyRhsTree tbl (e.getArg! 0) | return none
    let some r ← reifyRhsTree tbl (e.getArg! 1) | return none
    return some (Lean.mkApp2 (Lean.mkConst ``ProofLib.SepTree.sep) l r)
  else if e.isConstOf ``Arm64.SepProp.emp then
    return some (Lean.mkConst ``ProofLib.SepTree.nil)
  else
    let used ← get
    for i in [:tbl.size] do
      if !used[i]! && tbl[i]! == e then
        set (used.set! i true)
        return some (Lean.mkApp (Lean.mkConst ``ProofLib.SepTree.atom) (Lean.mkRawNatLit i))
    for i in [:tbl.size] do
      if !used[i]! then
        if ← atomCongrDefEq tbl[i]! e then
          set (used.set! i true)
          return some (Lean.mkApp (Lean.mkConst ``ProofLib.SepTree.atom) (Lean.mkRawNatLit i))
    return none

private meta def tryCloseEqACCongr (g : Lean.MVarId) (lhs rhs : Lean.Expr) :
    Lean.MetaM Bool := do
  if lhs == rhs then
    g.assign (← Lean.Meta.mkEqRefl lhs)
    return true
  if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
    g.assign (← eqACOfTblPoly lhs rhs tbl tA tB)
    return true
  let (tA, tbl) ← reifyLhsTree lhs |>.run #[]
  let (some tB, used) ← reifyRhsTree tbl rhs |>.run (Array.replicate tbl.size false)
    | return false
  if !(used.all id) then
    return false
  g.assign (← eqACOfTblPoly lhs rhs tbl tA tB)
  return true

open Lean Meta Elab Tactic in
/-- Congruence-aware `sep_ac_rfl` that handles argument-level definitional equalities without
falling back to kernel-heavy `ac_rfl`. -/
elab "sep_ac_rfl_defeq" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if let some (_, lhs, rhs) := ty.eq? then
      if ← tryCloseEqACCongr g lhs rhs then
        replaceMainGoal []
        return
    evalTactic (← `(tactic| sep_ac_rfl))

open Lean Meta Elab Tactic in
/-- Instantiate `?Frame` in `lhs = pat ∗ ?Frame` by atom cancellation and close via
`tryCloseEqACCongr` (`eqACOfTblPoly`). -/
elab "sep_focus_ac" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    if let some (_, lhs, rhs) := ty.eq? then
      let rhs := rhs.consumeMData
      if rhs.isAppOfArity ``Arm64.SepProp.sepConj 2 then
        let pat := (rhs.getArg! 0).consumeMData
        let frameArg := (rhs.getArg! 1).consumeMData
        if frameArg.isMVar then
          let saved ← saveState
          let lhsAtoms := flattenSepAtoms lhs
          let mut used := Array.replicate lhsAtoms.size false
          let mut allMatched := true
          if pat.isAppOfArity ``Arm64.SepProp.pure 1 && (pat.getArg! 0).consumeMData.isMVar then
            let mut found := false
            for i in [:lhsAtoms.size] do
              if !found && lhsAtoms[i]!.isAppOfArity ``Arm64.SepProp.pure 1 then
                if ← isDefEq (pat.getArg! 0) (lhsAtoms[i]!.getArg! 0) then
                  used := used.set! i true
                  found := true
            allMatched := found
          else
            let patAtoms := flattenSepAtoms pat
            for pa in patAtoms do
              let mut matched := false
              for i in [:lhsAtoms.size] do
                if !matched && !used[i]! && pa == lhsAtoms[i]! then
                  used := used.set! i true
                  matched := true
              if !matched then
                for i in [:lhsAtoms.size] do
                  if !matched && !used[i]! then
                    if ← atomCongrDefEq pa lhsAtoms[i]! then
                      used := used.set! i true
                      matched := true
              if !matched then
                allMatched := false
          if allMatched then
            let mut rem : Array Lean.Expr := #[]
            for i in [:lhsAtoms.size] do
              if !used[i]! then
                rem := rem.push lhsAtoms[i]!
            let _ ← isDefEq frameArg (mkSepChain rem)
            let rhsInst := (← instantiateMVars rhs).consumeMData
            if ← tryCloseEqACCongr g lhs rhsInst then
              replaceMainGoal []
              return
          saved.restore
      else if ← tryCloseEqACCongr g lhs rhs then
        replaceMainGoal []
        return
    evalTactic (← `(tactic| sep_ac_rfl))

private meta partial def mkExceptionProg (prog : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let p := prog.consumeMData
  if p.isAppOfArity ``Arm64.Program.rebase 4 then
    let args := p.getAppArgs
    let args := args.set! 2
      (Lean.mkApp (Lean.mkConst ``LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException) args[2]!)
    return Lean.mkAppN p.getAppFn args
  if p.isAppOfArity ``Arm64.Obj.MultiPlacedLib.blockProgram 6 then
    let args := p.getAppArgs
    let args := args.set! 3
      (Lean.mkApp (Lean.mkConst ``LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException) args[3]!)
    return Lean.mkAppN p.getAppFn args
  if let some p' ← Lean.Meta.unfoldDefinition? p then
    return ← mkExceptionProg p'
  throwError "wp_steps_sync_pool_chk: cannot extract Program.rebase from {prog}"

open Lean Meta Elab Tactic in
/-- Drop-in fast replacement for `wp_steps_sync_pool mid` that accepts pre-proved `hlib` and
`hchk : checkBlockNoSvc0 blkLib.text = true` (avoiding repeated `by rfl` evaluation of the block
instruction list) and frames `A.pool` via `sep_focus_ac`. -/
elab "wp_steps_sync_pool_chk " hlib:term:max ppSpace hchk:term:max ppSpace mid:term : tactic => do
  let g0 ← getMainGoal
  let (isSepWPp, qStx, sExpr) ← g0.withContext do
    let ty := (← instantiateMVars (← g0.getType)).consumeMData
    if ty.isAppOfArity ``ProofLib.SepWPp 7 then
      let qExpr ← mkExceptionProg (ty.getArg! 0)
      let qStx ← Lean.Elab.Term.exprToSyntax qExpr
      pure (true, qStx, (ty.getArg! 2).consumeMData)
    else if ty.isAppOfArity ``ProofLib.SepWP 6 then
      let qExpr ← mkExceptionProg (ty.getArg! 0)
      let qStx ← Lean.Elab.Term.exprToSyntax qExpr
      pure (false, qStx, (ty.getArg! 2).consumeMData)
    else
      throwError "wp_steps_sync_pool_chk: expected SepWP or SepWPp goal"
  if isSepWPp then
    evalTactic (← `(tactic|
      (refine LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWPp_seg_ls_vm (Q := $qStx) $hlib $hchk (mid := $mid) ?_
       intro _m_strip)))
  else
    evalTactic (← `(tactic|
      (refine LibsignalBinary.Proofs.Placed.BudgetPoolSync.sepWP_seg_ls_vm (Q := $qStx) $hlib $hchk (mid := $mid) ?_
       intro _m_strip)))
  let g1 ← getMainGoal
  let g2 ← g1.withContext do
    let ty1 := (← instantiateMVars (← g1.getType)).consumeMData
    let sStrip := (ty1.getArg! 2).consumeMData
    let mut copies : Array (Lean.Name × Lean.Expr × Lean.Expr) := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dty := (← instantiateMVars decl.type).consumeMData
        if (← inferType dty).isProp then
          let dty' := dty.replace fun e =>
            if e.consumeMData == sExpr then some sStrip else none
          if dty' != dty then
            if ← Lean.tryCatchRuntimeEx
                (withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := 10000 * 1000 }) <|
                  Lean.Core.withCurrHeartbeats
                    (Lean.Meta.withReducibleAndInstances (Lean.Meta.isDefEq dty' dty)))
                (fun _ => pure false) then
              copies := copies.push (decl.userName.appendAfter "_strip", dty', decl.toExpr)
    let mut gCur := g1
    for (nm, dty', prf) in copies do
      gCur ← gCur.assert nm dty' prf
      let (_, gNext) ← gCur.intro1P
      gCur := gNext
    return gCur
  replaceMainGoal [g2]
  if isSepWPp then
    evalTactic (← `(tactic| (
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      refine ProofLib.SepWPp.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      try simp only [Arm64.State.setMem_setMem])))
  else
    evalTactic (← `(tactic| (
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
      refine ProofLib.SepWP.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
      try simp only [Arm64.State.setMem_setMem])))

private theorem sepFocusAc_keep : True := trivial

end LibsignalBinary.Proofs.TripleRatchet.SepFocusAc
