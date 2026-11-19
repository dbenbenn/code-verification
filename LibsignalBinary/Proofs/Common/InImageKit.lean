/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib -- shake: keep
public import ProofLib.SepLogic.WPp

/-!
# Shared Call-Site Setup and `SepWPp` Spatial-Context Tactic Helpers

Provides `inImageKitClearByName`, `inImageKitDestructureSat`, `inImageKitCloseAddrEq`,
`inImageKitCloseSetup`, and `inImageKitElimSpatialWPp` used by `[LibsignalPlacement]` call tactics.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib
open Lean Elab Tactic Meta

/-- Last string component of a constant name. -/
meta def inImageKitLastStr : Name → String
  | .str _ s => s
  | .num p _ => inImageKitLastStr p
  | .anonymous => ""

/-- Clear the hypothesis with user name `n` from the main goal, if present. -/
meta def inImageKitClearByName (n : Name) : TacticM Unit := do
  let g ← getMainGoal
  let some decl := (← g.getDecl).lctx.findFromUserName? n | return
  replaceMainGoal [← g.tryClear decl.fvarId]

/-- Copy of the engine's private `destructureSatHyps`. -/
meta def inImageKitDestructureSat : TacticM Unit := do
  for _ in [0:16] do
    if (← getGoals).isEmpty then return
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let mut progress := false
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isAuxDecl && !decl.userName.hasMacroScopes then
        let ty ← g.withContext (instantiateMVars decl.type)
        if (ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``And 2) &&
           (ty.find? (·.isConstOf ``SepProp.Satisfies)).isSome then
          let id := mkIdent decl.userName
          let vId ← freshIdent `v_stk
          if ← tryTacticCatchRuntimeBool
              (evalTactic (← `(tactic| rcases $id:ident with ⟨$vId:ident, $id:ident⟩))) then
            progress := true
            break
    if !progress then break

/-- Copy of the engine's private `closeCallAddrEqSubgoal`. -/
meta def inImageKitCloseAddrEq (g : MVarId) (preferGoal : Bool) : TacticM Bool := do
  setGoals [g]
  let (closedFastMeta, distinctFastMeta) ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | return (false, false)
    if rhs.hasMVar then return (false, false)
    let (lhsAddr, hPc?) ← do
      if lhs.isAppOfArity ``State.pc 1 then
        let s := lhs.getArg! 0
        if let some (pc, prf) ← provePcEq? s then
          Pure.pure (pc, some prf)
        else if s.isFVar then
          let mut found : Option (Expr × Expr) := none
          for decl in (← getLCtx) do
            if !decl.isImplementationDetail && !decl.isAuxDecl then
              let dty ← instantiateMVars decl.type
              if let some (_, l, r) := dty.eq? then
                if l.isAppOfArity ``State.pc 1 && l.getArg! 0 == s then
                  found := some (r, decl.toExpr)
                  break
          match found with
          | some (pc, prf) => Pure.pure (pc, some prf)
          | none => Pure.pure (lhs, none)
        else
          Pure.pure (lhs, none)
      else
        Pure.pure (lhs, none)
    if let some hAddr ← proveSepAddrEqMeta? lhsAddr rhs then
      let prf ← match hPc? with
        | some hp => mkEqTrans hp hAddr
        | none => Pure.pure hAddr
      g.assign (← mkExpectedTypeHint prf ty)
      return (true, false)
    let (lhsNorm0, _) ← SepSolver.normAddrMeta lhsAddr
    let (rhsNorm0, _) ← SepSolver.normAddrMeta rhs
    let (b1, o1) ← sepAddrBaseOff lhsNorm0
    let (b2, o2) ← sepAddrBaseOff rhsNorm0
    if o1 != o2 && (b1 == b2 || (← withReducible (isDefEq b1 b2))) then
      return (false, true)
    return (false, false)
  if closedFastMeta then
    replaceMainGoal []
    return true
  if distinctFastMeta then
    return false
  let saved ← saveState
  let closer ← if preferGoal then
      `(tactic| wp_focus_close (first | wp_norm_goal | wp_norm_lhs))
    else
      `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))
  if ← tryTacticCatchRuntimeBool (evalTactic closer) then
    return true
  saved.restore
  setGoals [g]
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_norm_goal)))
  if (← getGoals).isEmpty then
    return true
  let g1 ← getMainGoal
  let closedAfterNorm ← g1.withContext do
    let ty ← instantiateMVars (← g1.getType)
    let some (_, lhs, rhs) := ty.eq? | return false
    if !rhs.hasMVar then
      if let some prf ← proveSepAddrEqMeta? lhs rhs then
        g1.assign (← mkExpectedTypeHint prf ty)
        return true
    let (lhsNorm, hLhs?) ← SepSolver.normAddrMeta lhs
    let (rhsNorm, hRhs?) ← SepSolver.normAddrMeta rhs
    if !rhs.hasMVar &&
        (lhsNorm == rhsNorm || (← withReducibleAndInstances (isDefEq lhsNorm rhsNorm))) then
      let hLhs ← match hLhs? with | some p => Pure.pure p | none => mkEqRefl lhs
      let hRhs ← match hRhs? with | some p => Pure.pure p | none => mkEqRefl rhs
      let prf ← mkEqTrans hLhs (← mkEqSymm hRhs)
      g1.assign (← mkExpectedTypeHint prf ty)
      return true
    return false
  if closedAfterNorm then
    replaceMainGoal []
    return true
  saved.restore
  setGoals [g]
  return false

/-- Close the 4 call-site goals (`pc`, `status`, `spAligned`, `lr`); copy of the engine's private
    `closeCallSiteSetupSubgoals` with plain error messages. -/
meta def inImageKitCloseSetup (tacName : String) : TacticM Unit := do
  let gs ← getGoals
  let gPc :: gRun :: gSp :: gLr :: rest := gs
    | throwError "{tacName}: unexpected subgoals after applying the call lemma"
  if !(← inImageKitCloseAddrEq gPc (preferGoal := true)) then
    throwError "{tacName}: call target address does not match callee entry:{indentD (MessageData.ofGoal gPc)}"
  setGoals [gRun]
  if !(← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| wp_focus_close wp_norm_lhs)))) then
    throwError "{tacName}: failed to prove machine status is `.Running`:{indentD (MessageData.ofGoal gRun)}"
  setGoals [gSp]
  if !(← tryTacticCatchRuntimeBool
      (evalTactic (← `(tactic| wp_focus_close (first | wp_norm_lhs | wp_norm_goal))))) then
    throwError "{tacName}: failed to prove `s.spAligned = true`:{indentD (MessageData.ofGoal gSp)}"
  if !(← inImageKitCloseAddrEq gLr (preferGoal := false)) then
    throwError "{tacName}: failed to resolve link register (`s.readReg64 .lr = ret_pc`):{indentD (MessageData.ofGoal gLr)}"
  setGoals (← rest.filterM fun m => not <$> m.isAssigned)

/-- `SepWPp` analogue of the engine's `wpElimSpatialContext`. -/
meta def inImageKitElimSpatialWPp (hEq : Ident) : TacticM Unit := do
  let _ ← tryTacticCatchRuntimeBool (evalTactic (← `(tactic| (
    conv =>
      arg 4
      simp (config := { decide := true }) only [
        stackFrame16, stackFrame32, stackFrame16At_def, stackFrame32At_def,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
        wp_norm, arm64_norm, $hEq:ident]))))
  for _ in [0:64] do
    let g ← getMainGoal
    let ty ← g.withContext (instantiateMVars (← g.getType))
    unless ty.isAppOfArity ``SepWPp 7 do return
    let P := (ty.getArg! 3).consumeMData
    if P.isAppOfArity ``SepProp.sepExists 2 then
      let wId ← freshIdent `w
      evalTactic (← `(tactic| (apply ProofLib.SepWPp.exists_elim; intro $wId:ident)))
      betaReduceTarget
    else if P.isAppOfArity ``SepProp.sepConj 2 &&
        (P.getArg! 0).isAppOfArity ``SepProp.pure 1 then
      let hId ← freshIdent `hpost
      evalTactic (← `(tactic| (apply ProofLib.SepWPp.pure_elim; intro $hId:ident)))
      wpNormAndSplitHyp hId
    else
      return

end CryptoVerification.LibsignalTripleRatchet
