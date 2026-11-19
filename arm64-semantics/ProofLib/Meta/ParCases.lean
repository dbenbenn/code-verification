/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# `par_cases`: Elaborating Independent Goals in Parallel

Lean elaborates the tactic proof of one declaration on one thread; only whole declarations are
elaborated in parallel. `par_cases` closes independent goals of one proof in parallel:

```lean
  par_cases
    case ret_0x10 => tac₁
    case ret_0x14 => tac₂
    all_goals tac
```

means exactly `case ret_0x10 => tac₁; case ret_0x14 => tac₂; all_goals tac`, but each alternative
(and each goal of the final `all_goals`) is first run speculatively as a separate task on a copy of
the elaboration state, with error recovery off. The results are then merged in the order of the
alternatives: a speculative run that closed its goal without errors contributes its proof term, its
messages and its info trees, and the auxiliary declarations it created (such as `omega`'s
`_proof_i` and `simp`'s `_simp_i`) are added to the main environment, dependencies first. The runs
are started in the order of the alternatives, each with its own child name generator, so the names
of the auxiliary declarations, the environment and the final term do not depend on scheduling.
Constants realized during a run (for example equation lemmas) are inlined into the proof. Any other
alternative is run again sequentially at its position, as the plain `case` / `all_goals` would, so
failures report the same errors at the same places; when one goal of the final `all_goals` fails,
the whole `all_goals` is run again sequentially. The kernel checks the final proof term and the
added auxiliary declarations as usual, so `par_cases` does not affect soundness.

**Heartbeats.** Each speculative run starts with the heartbeats used so far and has the usual
`maxHeartbeats` limit. When an alternative is merged, the heartbeats of its runs are added to the
main thread (once, after all of its goals are merged), and an alternative that would take the total
over `maxHeartbeats` is redone sequentially (and fails there, as it would without `par_cases`): the
limit applies to the sum over all alternatives, as for a sequential proof, so `N` alternatives
cannot use more than one declaration's budget. An alternative that is redone sequentially is charged
only for the sequential run. (When the budget is exhausted exactly between two alternatives, the
timeout is reported at `par_cases` instead of the enclosing tactic block.)

`set_option parCases.enabled false` runs the alternatives sequentially; `parCases.report` reports
how many goals were closed in parallel.
-/

public meta section

namespace ProofLib.ParCases

open Lean Meta Elab Tactic

register_option parCases.enabled : Bool := {
  defValue := true
  descr := "run the alternatives of `par_cases` in parallel (false: sequentially, like `case` and \
    `all_goals`)"
}

register_option parCases.report : Bool := {
  defValue := false
  descr := "report how many goals `par_cases` closed in parallel"
}

register_option parCases.profile : Bool := {
  defValue := false
  descr := "with `parCases.report`, also report the run times of the speculative runs"
}

/-- `par_cases (case tag => tac)* (all_goals tac)?`: `case` and `all_goals`, with the goals
    elaborated in parallel (see `ProofLib.ParCases`). -/
syntax (name := parCases) "par_cases" ppIndent(withPosition(
  (ppLine colGe Lean.Parser.Tactic.«case»)* (ppLine colGe Lean.Parser.Tactic.allGoals)?)) : tactic

/-- Result of a speculative run. -/
structure JobResult where
  prf : Expr
  /-- Auxiliary declarations of the current declaration created by the run (`omega`'s `_proof_i`,
      `simp`'s `_simp_i`, …), dependencies first, to be added to the main environment. -/
  aux : Array Declaration
  msgs : MessageLog
  trees : PersistentArray InfoTree
  traces : PersistentArray TraceElem
  heartbeats : Nat
  ms : Nat

/-- Constants of `e` absent from `env₀`, transitively: the auxiliary declarations of the current
    declaration (names under `pre`) in dependency order, and the other ones (realized in the run,
    for example equation lemmas) to inline, with their level parameters and values. -/
partial def collectNew (env₀ env : Environment) (pre : Name) (e : Expr)
    (st : Array Name × Std.HashMap Name (List Name × Expr) × NameSet) :
    Option (Array Name × Std.HashMap Name (List Name × Expr) × NameSet) := do
  let mut (aux, inl, seen) := st
  for n in e.getUsedConstants do
    if env₀.contains n || seen.contains n then continue
    seen := seen.insert n
    let ci ← env.find? n
    let v ← ci.value? (allowOpaque := true)
    (aux, inl, seen) ← collectNew env₀ env pre ci.type (aux, inl, seen)
    (aux, inl, seen) ← collectNew env₀ env pre v (aux, inl, seen)
    if pre.isPrefixOf (privateToUserName n) || pre.isPrefixOf n then aux := aux.push n
    else inl := inl.insert n (ci.levelParams, v)
  return (aux, inl, seen)

/-- `e` with the constants of `inl` replaced by their values, recursively. -/
def inline (inl : Std.HashMap Name (List Name × Expr)) (e : Expr) : Option Expr :=
  if inl.isEmpty then some e else go (inl.size + 1) e
where
  go : Nat → Expr → Option Expr
    | fuel, e =>
      if !e.getUsedConstants.any inl.contains then some e
      else match fuel with
        | 0 => none
        | fuel + 1 => go fuel (e.replace fun
            | .const n us => inl.get? n |>.map fun (ps, v) => v.instantiateLevelParams ps us
            | _ => none)

/-- The proof `prf` built in `env` (from `env₀`) with the constants realized in the run inlined,
    and the auxiliary declarations of the current declaration it uses, dependencies first. -/
def exportProof (env₀ env : Environment) (pre : Name) (prf : Expr) :
    Option (Expr × Array Declaration) := do
  let (aux, inl, _) ← collectNew env₀ env pre prf (#[], {}, {})
  let prf ← inline inl prf
  let decls ← aux.mapM fun n => do
    match ← env.find? n with
    | .thmInfo t =>
      pure (Declaration.thmDecl { t with type := ← inline inl t.type, value := ← inline inl t.value })
    | .defnInfo d =>
      pure (Declaration.defnDecl { d with type := ← inline inl d.type, value := ← inline inl d.value })
    | _ => none
  return (prf, decls)

/-- Run `tac` on the goal `g` alone with error recovery off: the closed, metavariable-free proof
    of `g` with the auxiliary declarations it uses, the messages, info trees, traces and
    heartbeats. -/
def runJob (g : MVarId) (tac : TacticM Unit) : TacticM JobResult := do
  let t₀ ← IO.monoMsNow
  let env₀ ← getEnv
  Core.setMessageLog {}
  modifyTraceState fun _ => {}
  discard getResetInfoTrees
  let hb₀ ← IO.getNumHeartbeats
  setGoals [g]
  withoutRecover tac
  unless (← getUnsolvedGoals).isEmpty do throwError "par_cases: goals remain"
  let msgs ← Core.getMessageLog
  if msgs.hasErrors then throwError "par_cases: errors"
  let prf ← instantiateMVars (mkMVar g)
  if prf.hasMVar then throwError "par_cases: unassigned metavariables"
  let some (prf, aux) := exportProof env₀ (← getEnv) (← getDeclNGen).namePrefix prf
    | throwError "par_cases: new constant without a value"
  return { prf, aux, msgs, trees := ← getInfoTrees, traces := (← getTraceState).traces,
           heartbeats := (← IO.getNumHeartbeats) - hb₀, ms := (← IO.monoMsNow) - t₀ }

/-- Start `x` as a task on a copy of the current state (the main state is unchanged). -/
def spawn {α} (x : TacticM α) : TacticM (Task (Except Exception α)) := do
  let tctx ← read
  let ts ← get
  let termCtx ← readThe Term.Context
  let termSt ← getThe Term.State
  let metaCtx ← readThe Meta.Context
  let metaSt ← getThe Meta.State
  let act : CoreM α := do
    let m : MetaM ((α × Tactic.State) × Term.State) :=
      Term.TermElabM.run ((x tctx).run ts) termCtx termSt
    let (((a, _), _), _) ← Meta.MetaM.run m metaCtx metaSt
    return a
  let w ← Core.wrapAsync (fun (_ : Unit) => act) none
  EIO.asTask (w ())

/-- Goal of `gs` selected by `case tag` (exact tag, then suffix, then prefix, as `case`). -/
def findTag? (gs : List MVarId) (tag : Name) : MetaM (Option MVarId) := do
  let tagOf (g : MVarId) : MetaM Name := return (← g.getDecl).userName.eraseMacroScopes
  if let some g ← gs.findM? fun g => return tag == (← tagOf g) then return some g
  if let some g ← gs.findM? fun g => return tag.isSuffixOf (← tagOf g) then return some g
  gs.findM? fun g => return tag.isPrefixOf (← tagOf g)

/-- The goal of `gs` that the single-tag `case` alternative `alt` selects, if any. -/
def caseGoal? (alt : Syntax) (gs : List MVarId) : MetaM (Option MVarId) := do
  let args := alt[1].getSepArgs
  unless args.size == 1 do return none
  match args[0]![0][0] with
  | .ident _ _ tag _ => findTag? gs tag.eraseMacroScopes
  | _ => return gs.head?

/-- `true` iff `g`'s type and context (the types and the values of `let` variables) mention no
    unassigned metavariables (so closing it cannot assign metavariables shared with other goals). -/
def isClosedGoal (g : MVarId) : MetaM Bool := g.withContext do
  if (← instantiateMVars (← g.getType)).hasMVar then return false
  for d in ← getLCtx do
    if (← instantiateMVars d.type).hasMVar then return false
    if let some v := d.value? then
      if (← instantiateMVars v).hasMVar then return false
  return true

/-- The `case` / `all_goals` alternatives of a `par_cases` syntax node. -/
partial def alts (s : Syntax) : Array Syntax :=
  if s.isOfKind ``Lean.Parser.Tactic.«case» || s.isOfKind ``Lean.Parser.Tactic.allGoals then #[s]
  else s.getArgs.foldl (· ++ alts ·) #[]

/-- Merge the speculative results of one alternative if together they fit in the heartbeat budget
    and their auxiliary declarations can be added (the caller restores the state on `false`). The
    goals are assigned and the messages, info trees, traces and heartbeats recorded only after the
    auxiliary declarations of every goal have been added, so a refused alternative leaves only
    environment changes (undone by the caller's restore) and is charged only for its sequential
    rerun. -/
def mergeAlt? (results : Array (MVarId × JobResult)) : TacticM Bool := do
  let ctx ← readThe Core.Context
  let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let hb := results.foldl (fun s (_, r) => s + r.heartbeats) 0
  if ctx.maxHeartbeats != 0 && used + hb > ctx.maxHeartbeats then return false
  for (_, r) in results do
    for d in r.aux do
      if d.getNames.any (← getEnv).contains then return false
      try addDecl d catch _ => return false
  for (g, r) in results do
    g.assign r.prf
    Core.setMessageLog ((← Core.getMessageLog) ++ r.msgs)
    for t in r.trees do pushInfoTree t
    modifyTraceState fun s => { s with traces := s.traces ++ r.traces }
  IO.addHeartbeats hb
  return true

@[tactic parCases] def evalParCases : Tactic := fun stx =>
  Term.withoutTacticIncrementality true do
  let alts := stx.getArgs.foldl (· ++ alts ·) #[]
  unless parCases.enabled.get (← getOptions) do
    for a in alts do evalTactic a
    return
  -- Speculative runs, started in the order of the alternatives.
  let mut remaining ← getUnsolvedGoals
  let mut plan : Array (Syntax × Array (MVarId × Task (Except Exception JobResult))) := #[]
  let mut seq := false
  for a in alts do
    if seq then plan := plan.push (a, #[]); continue
    if a.isOfKind ``Lean.Parser.Tactic.allGoals then
      let mut jobs := #[]
      for g in remaining do
        unless ← isClosedGoal g do jobs := #[]; break
        jobs := jobs.push (g, ← spawn (runJob g (evalTactic a)))
      plan := plan.push (a, jobs)
    else
      match ← caseGoal? a remaining with
      | some g =>
        remaining := remaining.erase g
        if ← isClosedGoal g then
          plan := plan.push (a, #[(g, ← spawn (runJob g (evalTactic a)))])
        else plan := plan.push (a, #[])
      | none => seq := true; plan := plan.push (a, #[])
  -- Merge in order; anything not merged runs sequentially at its position.
  let t₀ ← IO.monoMsNow
  let mut par : Nat := 0
  let mut fallbacks : Nat := 0
  let mut maxMs : Nat := 0
  let mut sumMs : Nat := 0
  let mut nAux : Nat := 0
  for (a, jobs) in plan do
    let results := jobs.filterMap fun (g, t) => match t.get with
      | .ok r => some (g, r)
      | .error _ => none
    let mut ok := !jobs.isEmpty && results.size == jobs.size
    if ok then
      let saved ← saveState
      ok ← mergeAlt? results
      if ok then
        par := par + results.size
        for (_, r) in results do
          maxMs := max maxMs r.ms; sumMs := sumMs + r.ms; nAux := nAux + r.aux.size
      else saved.restore
    unless ok do
      fallbacks := fallbacks + 1
      setGoals (← getUnsolvedGoals)
      evalTactic a
  setGoals (← getUnsolvedGoals)
  if parCases.report.get (← getOptions) then
    logInfo m!"par_cases: {par} goals in parallel, {fallbacks} sequential alternatives"
    if parCases.profile.get (← getOptions) then
      logInfo m!"par_cases: jobs max {maxMs} ms, sum {sumMs} ms, merge wait \
        {(← IO.monoMsNow) - t₀} ms, {nAux} auxiliary declarations"

end ProofLib.ParCases

end
