/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.Decomp.Norm
public import ProofLib.BV.Linear
public import ProofLib.BV.ReflectROBDD

/-!
# `decomp_eq`: Deterministic Ladder for Pure Decompiled Equations

`decomp_eq` proves a pure equation `lhs = rhs` between a decompiled term and a Lean model
(`BitVec` / `Nat` / `Bool`, `Option`s and tuples of those). It runs a fixed ladder; each rung sees
only what the previous rungs left open:

| Rung | Tactic | Closes |
|---|---|---|
| 1 | `with_reducible rfl` | syntactically equal sides |
| 2 | `simp only [decomp_norm, extra*]`, then `rfl` | equal after normalization (`ProofLib.Decomp.Norm`) |
| 3 | `bv_lin` | linear `BitVec` identities |
| 4 | `grind` | ring identities, congruence |
| 5 | `bv_omega`, then `(repeat' split) <;> bv_omega` | `toNat` range facts, carries, hypotheses in context |
| 6 | `bv_slice` on the goal with the context cleared to what it mentions | byte/lane shuffles: `++`, `extractLsb'`, shifts, bitwise operators, only when the goal contains `++` or `extractLsb'` |
| 7 | `bv_robdd` | bit tricks, only when every `BitVec` width in the goal and context is a literal `≤ decompEq.robddMaxWidth` (default 16) |

Rung 2 splits a normalized conjunction (`some (a, b) = some (c, d)` becomes `a = c ∧ b = d`) and runs
rungs 3-7 on each conjunct. Its simp discharger is `first | assumption | omega | bv_omega | fail`, so
conditional range rules (`(x - y).toNat = x.toNat - y.toNat` when `y ≤ x`) fire when the side
condition follows from the context.

Every rung is speculative: it runs on the isolated goal with error recovery off
(`withoutRecover`), `errToSorry` off (`Term.withoutErrToSorry`), runtime exceptions caught, and a
heartbeat budget of `decompEq.budget` (in `maxHeartbeats` units, default 1000;
`decomp_eq (budget := k)` overrides it), never above the enclosing `maxHeartbeats`. A rung that
throws, logs an error, or produces a proof containing `sorry` (`Expr.hasSorry`) is rolled back.

On failure, `decomp_eq` leaves the normalized residual goals open and logs
"decomp_eq: could not close `lhs = rhs`; tried rfl, decomp_norm, bv_lin, grind, omega, bv_slice,
bv_robdd; residual goal left open", followed by the residual goals. `decomp_eq!` throws that message
instead. `set_option trace.decomp_eq true` reports which rung closed each goal.
-/

public meta section

namespace ProofLib.Decomp

open Lean Meta Elab Tactic Lean.Parser.Tactic

initialize registerTraceClass `decomp_eq

register_option decompEq.budget : Nat := {
  defValue := 1000
  descr := "heartbeat budget for each rung of `decomp_eq`, in `maxHeartbeats` units (thousands \
    of heartbeats; 0 = only the enclosing `maxHeartbeats`)"
}

register_option decompEq.robddMaxWidth : Nat := {
  defValue := 16
  descr := "`decomp_eq` runs `bv_robdd` only when every `BitVec` width in the goal and local \
    context is a literal at most this bound"
}

/-- `(budget := k)`: per-rung heartbeat budget of `decomp_eq`, in `maxHeartbeats` units. -/
syntax decompEqBudget := atomic(" (" &"budget" " := ") num ")"

/-- `decomp_eq` proves a pure equation between a decompiled term and a model with the
    deterministic ladder `rfl`, `simp only [decomp_norm]`, `bv_lin`, `grind`, `omega`,
    `bv_robdd` (see `ProofLib.Decomp.NormTactic`). On failure it leaves the normalized residual goal
    open with a note. Options: `decomp_eq (budget := k)` sets the per-rung heartbeat budget (in
    `maxHeartbeats` units); `decomp_eq [h, f]` adds simp lemmas (e.g. model definitions) to
    rung 2. -/
syntax (name := decompEq) "decomp_eq" (decompEqBudget)? (simpArgs)? : tactic

/-- `decomp_eq!` is `decomp_eq` that fails with an error instead of leaving a residual goal. -/
syntax (name := decompEqBang) "decomp_eq!" (decompEqBudget)? (simpArgs)? : tactic

/-- The rungs of `decomp_eq`, in order, as listed in its failure message. -/
def decompEqRungs : String := "rfl, decomp_norm, bv_lin, grind, omega, bv_slice, bv_robdd"

/-- Run `x` with a fresh heartbeat budget of `budget` (in `maxHeartbeats` units; `0` = no extra
    limit), never above the enclosing `maxHeartbeats`. -/
def withBudget {α : Type} (budget : Nat) (x : TacticM α) : TacticM α :=
  if budget == 0 then x else
  withTheReader Core.Context (fun ctx =>
    let cap := budget * 1000
    { ctx with
      maxHeartbeats := if ctx.maxHeartbeats == 0 then cap else Nat.min ctx.maxHeartbeats cap })
    (withCurrHeartbeats x)

/-- Run `tac` speculatively on the isolated goal `g`: error recovery and `errToSorry` off, runtime
    exceptions caught, heartbeat budget `budget`. Returns the remaining goals, or `none` (with state
    and messages restored) if `tac` throws, logs an error, leaves a `sorry` in the proof of `g`, or
    (when `close`) leaves goals open. -/
def runRungM (g : MVarId) (tac : TacticM Unit) (budget : Nat) (close : Bool) :
    TacticM (Option (List MVarId)) := do
  let saved ← saveState
  let savedMsgs ← Core.getMessageLog
  Core.setMessageLog {}
  let res? ← try
      tryCatchRuntimeEx
        (some <$> withBudget budget
          (Term.withoutErrToSorry (Tactic.run g (withoutRecover tac))))
        (fun _ => pure none)
    catch _ => pure none
  let newMsgs ← Core.getMessageLog
  let ok ← match res? with
    | none => pure false
    | some gs =>
      if newMsgs.hasErrors || (close && !gs.isEmpty) then pure false
      else pure !(← instantiateMVars (mkMVar g)).hasSorry
  if ok then
    Core.setMessageLog (savedMsgs ++ newMsgs)
    return res?
  else
    restoreState saved
    Core.setMessageLog savedMsgs
    return none

/-- `runRungM` with the tactic syntax `tac`. -/
def runRung (g : MVarId) (tac : Syntax) (budget : Nat) (close : Bool) :
    TacticM (Option (List MVarId)) :=
  runRungM g (evalTactic tac) budget close

/-- Try to close `g` with the rung `name` (`tac`); trace the rung on success. -/
def tryClose (g : MVarId) (name : String) (tac : Syntax) (budget : Nat) : TacticM Bool := do
  if (← runRung g tac budget true).isSome then
    trace[decomp_eq] "closed by {name}"
    return true
  return false

/-- Split a conjunction goal into its conjuncts (recursively). -/
partial def splitAnds (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    match ← g.apply (mkConst ``And.intro) with
    | [g1, g2] => return (← splitAnds g1) ++ (← splitAnds g2)
    | gs => return gs
  else
    return [g]

/-- A `Nat` literal (`OfNat.ofNat n` or a raw literal). -/
def natLit? (e : Expr) : Option Nat := e.nat? <|> e.rawNatLit?

/-- `true` iff some `BitVec w` in `e` has a non-literal width or a width above `bound`. -/
def hasWideBitVec (bound : Nat) (e : Expr) : Bool :=
  (e.find? fun t =>
    t.isAppOfArity ``BitVec 1 &&
      match natLit? t.appArg! with
      | some n => bound < n
      | none => true).isSome

/-- `true` iff every `BitVec` width in the target and local context of `g` is a literal at most
    `bound` (the gate of the `bv_robdd` rung). -/
def bitVecWidthsWithin (g : MVarId) (bound : Nat) : MetaM Bool := g.withContext do
  if hasWideBitVec bound (← instantiateMVars (← g.getType)) then return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if hasWideBitVec bound (← instantiateMVars d.type) then return false
  return true

/-- `true` iff `e` contains a `BitVec` concatenation `++` or an `extractLsb'` (the gate of the
    `bv_slice` rung). -/
def hasSliceOp (e : Expr) : Bool :=
  (e.find? fun t =>
    t.isAppOf ``BitVec.extractLsb' ||
      (t.isAppOfArity ``HAppend.hAppend 6 && (t.getArg! 0).isAppOf ``BitVec)).isSome

/-- `decomp_slice`: `bv_slice` on the main goal after clearing every hypothesis the goal does not
    mention (`MVarId.cleanup`), so unrelated arithmetic facts in the context (a `pc = base + k`)
    do not put the goal outside the `bv_slice` grammar. -/
syntax (name := decompSlice) "decomp_slice" : tactic

elab_rules : tactic
  | `(tactic| decomp_slice) => do
    let g ← (← getMainGoal).cleanup (indirectProps := false)
    replaceMainGoal [g]
    evalTactic (← `(tactic| bv_slice))

/-- Run the `decomp_eq` ladder on the main goal (`strict`: `decomp_eq!`). -/
def runDecompEq (strict : Bool) (budgetStx : Option Syntax) (extra : Array Syntax) :
    TacticM Unit := do
  let g ← getMainGoal
  let opts ← getOptions
  let budget := (budgetStx.bind fun b => b.getArgs.findSome? (·.isNatLit?)).getD
    (decompEq.budget.get opts)
  let robddMax := decompEq.robddMaxWidth.get opts
  let tgt ← instantiateMVars (← g.getType)
  let goalMsg := match tgt.eq? with
    | some (_, l, r) => m!"{l} = {r}"
    | none => m!"{tgt}"
  -- Rung 1: syntactic / reducible equality.
  if ← tryClose g "rfl" (← `(tactic| with_reducible rfl)) budget then
    replaceMainGoal []
    return
  -- Rung 2: `decomp_norm` normalization.
  let extraArgs : Syntax.TSepArray ``simpLemma "," := .ofElems (extra.map (⟨·⟩))
  -- `first` runs its last alternative with error recovery on, so a failing `bv_omega` there would
  -- log an error and admit the side condition; the terminal `fail` keeps every attempt strict.
  let simpTac ← `(tactic| simp (disch := first | assumption | omega | bv_omega | fail)
    only [decomp_norm, $extraArgs,*])
  let leaves ← match ← runRung g simpTac budget false with
    | some gs => pure gs
    | none => pure [g]
  if leaves.isEmpty then
    trace[decomp_eq] "closed by decomp_norm"
    replaceMainGoal []
    return
  let mut residual : Array MVarId := #[]
  for leaf0 in leaves do
    for leaf in ← splitAnds leaf0 do
      if ← tryClose leaf "decomp_norm" (← `(tactic| with_reducible_and_instances rfl)) budget then
        continue
      if ← tryClose leaf "bv_lin" (← `(tactic| bv_lin)) budget then continue
      if ← tryClose leaf "grind" (← `(tactic| grind)) budget then continue
      if ← tryClose leaf "omega"
          (← `(tactic| first | bv_omega | ((repeat' split) <;> bv_omega))) budget then
        continue
      if hasSliceOp (← instantiateMVars (← leaf.getType)) then
        if ← tryClose leaf "bv_slice" (← `(tactic| decomp_slice)) budget then continue
      if ← bitVecWidthsWithin leaf robddMax then
        if ← tryClose leaf "bv_robdd" (← `(tactic| bv_robdd)) budget then continue
      residual := residual.push leaf
  if residual.isEmpty then
    replaceMainGoal []
    return
  let resMsg := MessageData.joinSep (residual.toList.map fun r => m!"\n{MessageData.ofGoal r}")
    m!""
  g.withContext do
    if strict then
      throwError m!"decomp_eq!: could not close `{goalMsg}`;\ntried {decompEqRungs}; \
        residual goal:{resMsg}"
    logInfo m!"decomp_eq: could not close `{goalMsg}`;\ntried {decompEqRungs}; residual goal \
      left open{resMsg}"
  replaceMainGoal residual.toList

/-- The extra simp arguments of a `decomp_eq [...]` call. -/
def decompEqExtraArgs (args? : Option (TSyntax ``simpArgs)) : Array Syntax :=
  match args? with
  | some args => args.raw[1].getSepArgs
  | none => #[]

elab_rules : tactic
  | `(tactic| decomp_eq $[$b:decompEqBudget]? $[$args:simpArgs]?) =>
    runDecompEq false (b.map (·.raw)) (decompEqExtraArgs args)
  | `(tactic| decomp_eq! $[$b:decompEqBudget]? $[$args:simpArgs]?) =>
    runDecompEq true (b.map (·.raw)) (decompEqExtraArgs args)

end ProofLib.Decomp

end
