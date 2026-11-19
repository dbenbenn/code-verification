/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli
public import Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Defs
public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.NonVacuity.CliSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.Swarm.UA.ClassicalBridge
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.COMPOSED.CompInv
public import DY.Trace.Basic
public import DY.Trace.Monad
public import DY.Trace.Manipulation
public import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.DYBridge.DY.Trace.Basic
public import Symbolic.DYBridge.DY.Trace.Monad
public import Symbolic.DYBridge.DY.Trace.Manipulation
public import Symbolic.DYBridge.DY.Actions.Network
public import Symbolic.DYBridge.DY.Actions.PersistentLocalState
public import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
public import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.DYBridge.DY.Actions.Random

/-!
# Definitions and `Explains` Refutation for `synthetic-exit1-eager-session-commit`

Establishes satisfiability, `CoinsFresh`, and unconditional refutation of `Explains`
(`not_explains_unpinned`) for `Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.ClassicalBridge
open Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept
  (hexDigit hexBytes_ofList)

/-- Witness setup from `Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli`. -/
abbrev setup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.setup

/-- Witness interpretations and records (`cliCompFits setup`). -/
abbrev fits :=
  Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.fits

/-- Recorded 4-call CLI witness trace. -/
abbrev trace : List DY.Libsignal.HwEvents.CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.trace

/-- `setup` matches `Cheval26SmallSubgroupHighBitCli.setup` definitionally. -/
theorem setup_eq_hb : setup = Witnesses.Cheval26SmallSubgroupHighBitCli.setup := rfl

/-- `CliSetupMatchesPinned setup` implies `fits`. -/
theorem cliCompFitsPinned_sub_fits {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : CliSetupMatchesPinned setup iw r) : fits iw r :=
  ⟨hf.1.1, hf.2.1, hf.2.2⟩

/-- **Non-vacuity** of `CliSetupMatchesPinned setup`. -/
theorem cliCompFitsPinned_satisfiable : ∃ iw r, CliSetupMatchesPinned setup iw r := by
  rw [setup_eq_hb]
  exact Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.cliSetupMatchesPinned_satisfiable_hb

/-- **Non-vacuity** of `fits` (`CliSetupMatches setup`). -/
theorem nonvacuous : ∃ i r, fits i r :=
  let ⟨iw, r, hf⟩ := cliCompFitsPinned_satisfiable
  ⟨iw, r, cliCompFitsPinned_sub_fits hf⟩

/-- **`CoinsFresh`** holds for `(setup, trace)` under unpinned `fits`. -/
theorem coinsFresh_unpinned : ∀ iw r, fits iw r → CoinsFresh r trace :=
  Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_unpinned_exit1EagerSessionCommitCli

/-- **`CoinsFresh`** holds for `(setup, trace)` under `CliSetupMatchesPinned setup`. -/
theorem coinsFresh_pinned : ∀ iw r, CliSetupMatchesPinned setup iw r → CoinsFresh r trace :=
  Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_exit1EagerSessionCommitCli

def fallbackRun : RunEvent :=
  { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }

def ev0 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.trace with
  | [.run ev, _, _, _] => ev | _ => fallbackRun

def ev1 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.trace with
  | [_, .run ev, _, _] => ev | _ => fallbackRun

def ev2Rej : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.trace with
  | [_, _, .run ev, _] => ev | _ => fallbackRun

def ev3BobSend : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.Exit1EagerSessionCommitCli.trace with
  | [_, _, _, .run ev] => ev | _ => fallbackRun

theorem trace_eq_evs : trace = [.run ev0, .run ev1, .run ev2Rej, .run ev3BobSend] := rfl

theorem ev0_eq_prekey : ev0 = Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.ev0 := rfl
theorem ev1_eq_prekey : ev1 = Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.ev1 := rfl

theorem ev3BobSend_input_len : ev3BobSend.input.length = 9 := by decide +kernel

attribute [local irreducible] Symbolic.BugInjection.hexBytes

def ev1OutBytes : HwBytes :=
  match ev1.exit with | some (_, out) => out | none => []

elab "ex_chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal"

elab "ex_str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

def ev1OutChars : List Char := ex_chars_of_hex_def ev1OutBytes
theorem ev1Out_eq_hex : ev1OutBytes = hexBytes (ex_str_of_hex_def ev1OutBytes) := rfl
theorem ev1OutStr_eq : (ex_str_of_hex_def ev1OutBytes) = String.ofList ev1OutChars := rfl
def ev1OutFast : HwBytes := hexBytes.go hexDigit ev1OutChars

theorem ev1_exit_eq_fast : ev1.exit = some (0, ev1OutFast) := by
  have h : ev1OutBytes = ev1OutFast := by
    change ev1OutBytes = hexBytes.go hexDigit ev1OutChars
    rw [ev1Out_eq_hex, ev1OutStr_eq, hexBytes_ofList]
  change some (0, ev1OutBytes) = some (0, ev1OutFast)
  rw [h]

theorem runWrapped_ev1_fast : runWrapped ev1 = true := by
  unfold runWrapped
  have hcmd : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  rw [hcmd, ev1_exit_eq_fast]
  decide +kernel

theorem no_runRejected_ev0 : ¬ RunRejected ev0 := fun h => h _ rfl
theorem no_runRejected_ev1 : ¬ RunRejected ev1 := fun h => h _ rfl

def mutEvents : List CliEvent :=
  [.run ev0, .run ev1, .run ev2Rej, .run ev3BobSend]

theorem mutEvents_eq : mutEvents = trace := rfl

theorem mutEvents_breakFree : BreakFree mutEvents :=
  breakFree_run_cons.mpr (breakFree_run_cons.mpr (breakFree_run_cons.mpr
    (breakFree_run_cons.mpr breakFree_nil)))

/-- No Triple Ratchet local state entry is stored for participant `q` on `tr`. -/
private def NoTRStateFor (q : Participant) (tr : ExecTrace) : Prop :=
  ∀ (j : Nat) (st : DY.Libsignal.TripleRatchet.TRState),
    (tr.at? j : Option TRStEntry) ≠ some (TRStE q st)

private theorem noTRStateFor_nil (q : Participant) :
    NoTRStateFor q (DY.Trace.nil : ExecTrace) := by
  intro j st h
  exact Symbolic.Swarm.COMPOSED.CompInv.trStoredAt_nil h

private theorem noTRStateFor_append_other {q : Participant} {tr : ExecTrace}
    (h : NoTRStateFor q tr) {E : Type} [ExecTraceTypes.Has E] (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none) :
    NoTRStateFor q (tr.append e) := by
  intro j st hex
  rcases CompTrace.at?_append_cases hex with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j st h0
  · rw [hnone] at hp; cases hp

private theorem noTRStateFor_append_tr_ne {q p : Participant} {tr : ExecTrace}
    (h : NoTRStateFor q tr) (st₀ : DY.Libsignal.TripleRatchet.TRState) (hne : p ≠ q) :
    NoTRStateFor q (tr.append (TRStE p st₀)) := by
  intro j st hex
  rcases CompTrace.at?_append_cases hex with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j st h0
  · change some (TRStE p st₀) = some (TRStE q st) at hp
    injection hp with hp'
    cases hp'
    exact hne rfl

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type}
    (p : α × β) (f : α → β → Traceful γ)
    (hf : ∀ a b, CompTrace.Preserves Inv (f a b)) :
    CompTrace.Preserves Inv (Prod.casesOn p f) := by
  rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type}
    (o : Option α) (noneCase : Traceful β) (someCase : α → Traceful β)
    (hn : CompTrace.Preserves Inv noneCase) (hs : ∀ a, CompTrace.Preserves Inv (someCase a)) :
    CompTrace.Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem stepIn_next (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).2.val = ((c.step x).2.run tr).2.val :=
  congrArg (fun s => (s.2.run tr).2.val) (i.pf_step x).symm

private theorem stepIn_ok (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    ((reachability.step (stepIn c x)).2.run tr).1.isSome = ((c.step x).2.run tr).1.isSome :=
  congrArg (fun s => (s.2.run tr).1.isSome) (i.pf_step x).symm

private theorem preserves_genRand_noTR {q : Participant} (n : Nat) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr h => by
    simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
    rw [CompTrace.run_bind_snd, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
    exact noTRStateFor_append_other h (RndE n) rfl

private theorem preserves_sendMessage_noTR {q : Participant} (m : DY.Bytes) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Network.sendMessage m) :=
  fun tr h => by
    simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
    rw [DY.Traceful.run_mk]
    exact noTRStateFor_append_other h (NetE m) rfl

private theorem preserves_storeLocalState_pq_noTR {q : Participant} (p : Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) :
    CompTrace.Preserves (NoTRStateFor q) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr h => by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact noTRStateFor_append_other h (PQStE p st) rfl

private theorem preserves_storeLocalState_tr_ne {q p : Participant}
    (st : DY.Libsignal.TripleRatchet.TRState) (hne : p ≠ q) :
    CompTrace.Preserves (NoTRStateFor q) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr h => by
    rw [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
    exact noTRStateFor_append_tr_ne h st hne

private theorem preserves_logEventPQ_noTR {q : Participant} (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    CompTrace.Preserves (NoTRStateFor q) (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
    exact noTRStateFor_append_other h (PQEvE ev) rfl

private theorem preserves_logEventC_noTR {q : Participant} (ev : ComposedEvent) :
    CompTrace.Preserves (NoTRStateFor q) (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
    exact noTRStateFor_append_other h (CEvE ev) rfl

private theorem preserves_logEventTR_noTR {q : Participant} (ev : DY.Libsignal.TripleRatchet.TREvent) :
    CompTrace.Preserves (NoTRStateFor q) (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by
    rw [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, CompTrace.run_bind_snd, DY.Traceful.run_mk]
    dsimp only
    rw [DY.Traceful.run_pure]
    exact noTRStateFor_append_other h (TREvE ev) rfl

private theorem preserves_getKey_noTR {q : Participant} (p : Participant) (h : Nat)
    (kind : DY.Libsignal.PQXDH.KeyKind) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Libsignal.PQXDH.getKey p h kind) :=
  CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p h) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

private theorem preserves_lookupIdentity_noTR {q : Participant} (p : Participant) (h : Nat) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getEntry h) fun _ => ?_
  split
  · exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

private theorem preserves_logMessageKeyAndStore_ne {q me : Participant}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (r par : Nat)
    (st : DY.Libsignal.TripleRatchet.TRState) (hne : me ≠ q) :
    CompTrace.Preserves (NoTRStateFor q)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  CompTrace.Preserves.bind (preserves_logEventTR_noTR _) fun _ =>
    preserves_storeLocalState_tr_ne st hne

private theorem preserves_dhRatchetStep_noTR {q : Participant}
    (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ =>
    CompTrace.Preserves.bind (preserves_genRand_noTR 32) fun _ => CompTrace.Preserves.pure _

private theorem preserves_ensureReceiverChain_noTR {q : Participant}
    (st : DY.Libsignal.TripleRatchet.TRState) (pk : DY.Bytes) :
    CompTrace.Preserves (NoTRStateFor q) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.bind (preserves_dhRatchetStep_noTR st pk) fun _ =>
      CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.failure

private theorem preserves_logSkippedKeys_noTR {q : Participant}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes) (rIdx src : Nat)
    (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    CompTrace.Preserves (NoTRStateFor q)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact CompTrace.Preserves.pure _
  | succ k ih => exact CompTrace.Preserves.bind (preserves_logEventTR_noTR _) fun _ => ih _ _

local macro "noTRFor_tac" hne:ident : tactic => `(tactic| repeat (first
  | with_reducible apply CompTrace.Preserves.bind
  | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn
  | with_reducible apply CompTrace.Preserves.pure
  | with_reducible apply CompTrace.Preserves.failure
  | with_reducible apply preserves_genRand_noTR
  | with_reducible apply preserves_storeLocalState_tr_ne _ $hne
  | with_reducible apply preserves_storeLocalState_pq_noTR
  | with_reducible apply preserves_sendMessage_noTR
  | with_reducible apply CompTrace.Preserves.getLocalState_tr
  | with_reducible apply CompTrace.Preserves.getLocalState_pq
  | with_reducible apply preserves_getKey_noTR
  | with_reducible apply preserves_lookupIdentity_noTR
  | with_reducible apply CompTrace.Preserves.receiveMessage
  | with_reducible apply CompTrace.Preserves.getEntry
  | with_reducible apply CompTrace.Preserves.receiveSignalMsg
  | with_reducible apply CompTrace.Preserves.verifyMacAndDecrypt
  | with_reducible apply preserves_dhRatchetStep_noTR
  | with_reducible apply preserves_ensureReceiverChain_noTR
  | with_reducible apply preserves_logSkippedKeys_noTR
  | with_reducible apply CompTrace.Preserves.guardP
  | with_reducible apply CompTrace.Preserves.monadLiftErr
  | with_reducible apply CompTrace.Preserves.guardTrace
  | with_reducible apply CompTrace.Preserves.requireTracePredicate
  | with_reducible apply CompTrace.Preserves.traceLength
  | with_reducible apply preserves_logMessageKeyAndStore_ne _ _ _ _ _ _ _ _ $hne
  | with_reducible apply preserves_logEventPQ_noTR
  | with_reducible apply preserves_logEventC_noTR
  | with_reducible apply preserves_logEventTR_noTR
  | split
  | with_reducible intro))

private theorem preserves_aliceHandshake_noTR {q : Participant}
    (a b : Participant) (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    CompTrace.Preserves (NoTRStateFor q)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  have hne : ("alice" : Participant) ≠ "alice" → False := fun h => h rfl
  unfold DY.Libsignal.PQXDH.aliceHandshake; noTRFor_tac hne

private theorem preserves_bobHandshake_noTR {q : Participant}
    (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    CompTrace.Preserves (NoTRStateFor q)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  have hne : ("alice" : Participant) ≠ "alice" → False := fun h => h rfl
  unfold DY.Libsignal.PQXDH.bobHandshake; noTRFor_tac hne

private theorem preserves_setupAct_noTR {q : Participant}
    (a b : Participant) (withOpk : Bool) :
    CompTrace.Preserves (NoTRStateFor q) (setupAct a b withOpk) := by
  have hne : ("alice" : Participant) ≠ "alice" → False := fun h => h rfl
  unfold setupAct
  refine CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.registerIdentity; noTRFor_tac hne) fun _ => ?_
  refine CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.registerIdentity; noTRFor_tac hne) fun hB => ?_
  refine CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.genSignedPrekey; noTRFor_tac hne) fun _ => ?_
  refine CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.genPQPrekey; noTRFor_tac hne) fun _ => ?_
  cases withOpk
  · exact CompTrace.Preserves.pure ()
  · simp only [↓reduceIte]
    exact CompTrace.Preserves.bind (by unfold DY.Libsignal.PQXDH.genOneTimePrekey; noTRFor_tac hne) fun _ =>
      CompTrace.Preserves.pure ()

private theorem noTRStateFor_setupTrace (q : Participant) (r : ProtocolSetup) :
    NoTRStateFor q (setupTrace r) :=
  preserves_setupAct_noTR r.alice r.bob r.withOpk DY.Trace.nil (noTRStateFor_nil q)

private theorem noTRStateFor_step_invisible {q : Participant} {tr : ExecTrace} {s : Step}
    (hinv : s.cls = .invisible) (htr : NoTRStateFor q tr) :
    NoTRStateFor q (s.next tr) := by
  cases s <;> simp [Step.cls] at hinv
  case network m =>
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    exact preserves_sendMessage_noTR m tr htr

private theorem noTRStateFor_runSteps_invisible {q : Participant} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, x.cls = .invisible) → NoTRStateFor q tr →
      NoTRStateFor q (runSteps pre tr)
  | [], _, _, htr => htr
  | s :: pre, tr, hinv, htr =>
    noTRStateFor_runSteps_invisible pre (s.next tr)
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (noTRStateFor_step_invisible (hinv s List.mem_cons_self) htr)

private theorem noTRStateFor_step_party_ne {q p : Participant} {tr : ExecTrace} {s : Step}
    (hcls : s.cls = .party) (hp : s.party? = some p) (hne : p ≠ q)
    (htr : NoTRStateFor q tr) :
    NoTRStateFor q (s.next tr) := by
  cases s <;> simp [Step.cls, Step.party?] at hcls hp
  case aliceStart a b idStateIdx regIdxB bh =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
      refine CompTrace.Preserves.bind (preserves_aliceHandshake_noTR a b idStateIdx regIdxB bh) fun _ => ?_
      noTRFor_tac hne
    exact hpres tr htr
  case bobStart b a kh regIdxA mh pqIdx spqrMsgIdx =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqrMsgIdx) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
      refine CompTrace.Preserves.bind (preserves_bobHandshake_noTR b a kh regIdxA mh.ek mh.ct) fun _ => ?_
      noTRFor_tac hne
    exact hpres tr htr
  case messageEncrypt me stateIdx coinsLen pqIdx =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; noTRFor_tac hne
    exact hpres tr htr
  case messageEncryptAbort me stateIdx =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noTRFor_tac hne
    exact hpres tr htr
  case messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.TripleRatchet.messageDecrypt me stateIdx msgIdx pqIdx spqrMsgIdx) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      noTRFor_tac hne
    exact hpres tr htr
  case messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx =>
    subst hp
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    change NoTRStateFor q ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx).run tr).2.val
    have hpres : CompTrace.Preserves (NoTRStateFor q)
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrMsgIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; noTRFor_tac hne
    exact hpres tr htr

private theorem send_step_not_ok_of_noTRStateFor {q : Participant} {tr : ExecTrace} {s : Step}
    {peer : CryptoVerification.SignalSession.Address}
    (hp : s.party? = some q) (hfits : s.FitsCmd (.send peer))
    (htr : NoTRStateFor q tr) :
    s.ok tr = false := by
  cases s <;> try exact False.elim hfits
  case messageEncrypt me stateIdx coinsLen pqIdx =>
    simp [Step.party?] at hp; subst hp
    dsimp only [Step.ok, Step.toInput]
    erw [stepIn_ok]
    change (((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx coinsLen pqIdx).run tr).1).isSome = false
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    rw [CompTrace.run_bind_fst, CompTrace.getLocalState_tr_fst]
    rcases hat : (tr.at? stateIdx : Option TRStEntry) with _ | ⟨⟨me', st⟩⟩
    · rfl
    · by_cases hme : me' = me
      · subst hme; exact False.elim (htr stateIdx st hat)
      · simp [hme]
  case messageEncryptAbort me stateIdx =>
    simp [Step.party?] at hp; subst hp
    dsimp only [Step.ok, Step.toInput]
    erw [stepIn_ok]
    change (((DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx).run tr).1).isSome = false
    unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
    rw [CompTrace.run_bind_fst, CompTrace.getLocalState_tr_fst]
    rcases hat : (tr.at? stateIdx : Option TRStEntry) with _ | ⟨⟨me', st⟩⟩
    · rfl
    · by_cases hme : me' = me
      · subst hme; exact False.elim (htr stateIdx st hat)
      · simp [hme]

private theorem matchesEventsClassical_run_rejected_inv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hrej : ∀ out, ev.exit ≠ some (0, out))
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre ss', ss = pre ++ ss' ∧ (∀ x ∈ pre, x.cls = .invisible) ∧
      MatchesEventsClassicalAt interp r S g initIds (runSteps pre tr) ss' evs vis := by
  cases h with
  | run0 hinv _ hrest => exact ⟨_, _, rfl, hinv, hrest⟩
  | run1 _ hrm _ =>
    obtain ⟨out, hexit⟩ := hrm.2.2.2.2.2.1
    exact False.elim (hrej out hexit)

private theorem run_exit0_inv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {ev : RunEvent} {evs : List CliEvent}
    {vis : List VisEntry} {out : HwBytes}
    (hexit : ev.exit = some (0, out))
    (h : MatchesEventsClassicalAt interp r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs, ss = pre ++ s :: ss' ∧ vis = v ++ vs ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      RunMatches interp r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsClassicalAt interp r S g (nextBundleIds initIds ev)
        (s.next (runSteps pre tr)) ss' evs vs := by
  cases h with
  | run0 _ hrej _ => exact False.elim (hrej out hexit)
  | run1 hinv hrm hrest => exact ⟨_, _, _, _, _, rfl, rfl, hinv, hrm, hrest⟩

/-- **Unconditional (unpinned) refutation of `Explains` on `trace`:**
for **every** `interp`, `r`, `S`, `g`, `ss`, `vis` (without any crypto or setup pinning),
`trace` has no explanation in the composed model because Call 2 (`bob recv`) exits `1` (`run0`)
and Call 3 (`bob send`) exits `0` (`run1`) while `"bob"` has no `TRState` on the model trace. -/
theorem not_explains_unpinned {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis trace := by
  intro hex
  rw [← mutEvents_eq] at hex
  have hex_cl := explainsClassical_of hex mutEvents_breakFree
  have hne_ab : ("alice" : Participant) ≠ "bob" := by decide
  have hrej2 : ∀ out, ev2Rej.exit ≠ some (0, out) := by
    intro out h
    injection h with h
    injection h with h
    contradiction
  obtain ⟨pre₀, s₀, ss₁, _, _, _, _, hinv₀, hrm₀, hme₁⟩ := run_exit0_inv rfl hex_cl.2.2.2
  obtain ⟨pre₁, s₁, ss₂, _, _, _, _, hinv₁, hrm₁, hme₂⟩ := run_exit0_inv rfl hme₁
  obtain ⟨pre₂, ss₃, _, hinv₂, hme₃⟩ := matchesEventsClassical_run_rejected_inv hrej2 hme₂
  obtain ⟨pre₃, s₃, _, _, _, _, _, hinv₃, hrm₃, _⟩ := run_exit0_inv rfl hme₃
  have h0 := noTRStateFor_runSteps_invisible pre₀ (setupTrace r) hinv₀
    (noTRStateFor_setupTrace "bob" r)
  have h0' := noTRStateFor_step_party_ne hrm₀.1 hrm₀.2.1 hne_ab h0
  have h1 := noTRStateFor_runSteps_invisible pre₁ _ hinv₁ h0'
  have h1' := noTRStateFor_step_party_ne hrm₁.1 hrm₁.2.1 hne_ab h1
  have h2 := noTRStateFor_runSteps_invisible pre₂ _ hinv₂ h1'
  have h3 := noTRStateFor_runSteps_invisible pre₃ _ hinv₃ h2
  have hnotok := send_step_not_ok_of_noTRStateFor hrm₃.2.1 hrm₃.2.2.1 h3
  have hok : s₃.ok _ = true := hrm₃.2.2.2.2.1
  rw [hnotok] at hok
  cases hok


/-- Dropping the rejected Call 2 (`ev2Rej`, `exit 1`) from any `Explains` of the 3-call prefix
`[.run ev0, .run ev1, .run ev2Rej]` yields `Explains` of `[.run ev0, .run ev1]`. -/
theorem explains_drop_rejected_recv {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hex : Explains interp r S g ss vis [.run ev0, .run ev1, .run ev2Rej]) :
    Explains interp r S g ss vis [.run ev0, .run ev1] := by
  refine ⟨hex.1, hex.2.1, hex.2.2.1, ?_⟩
  have hrej2 : ∀ out, ev2Rej.exit ≠ some (0, out) := by
    intro out h; injection h with h; injection h with h; contradiction
  cases hex.2.2.2 with
  | run0 _ hrej _ => exact False.elim (no_runRejected_ev0 hrej)
  | run1 hinv₀ hrm₀ hme₁ =>
    cases hme₁ with
    | run0 _ hrej _ => exact False.elim (no_runRejected_ev1 hrej)
    | run1 hinv₁ hrm₁ hme₂ =>
      cases hme₂ with
      | run1 _ hrm₂ _ =>
        obtain ⟨out, hexit⟩ := hrm₂.2.2.2.2.2.1
        exact False.elim (hrej2 out hexit)
      | run0 hinv₂ _ hnil =>
        cases hnil with
        | nil hinv₃ =>
          have hinv₂₃ : ∀ x : Step, x ∈ _ ++ _ → x.cls = .invisible := fun x hx =>
            (List.mem_append.mp hx).elim (hinv₂ x) (hinv₃ x)
          exact .run1 hinv₀ hrm₀ (.run1 hinv₁ hrm₁ (.nil hinv₂₃))

end Symbolic.BugInjection.Proofs.SyntheticExit1EagerSessionCommit
