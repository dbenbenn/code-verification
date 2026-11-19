/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli
public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CliCoinSplit
public import Symbolic.BugInjection.Proofs.Common443.CliEventBridge
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PtDead
public import Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs

/-!
# Refutation of `CollisionAfterExplainedPrefix` for `synthetic-addr-key-leak-cli`

Proves `¬ CollisionAfterExplainedPrefix compI0 r S evs` for both the `(compI0, compHooks0)` carrier
trace `ImplTrace.akCarrierTrace` and the recorded witness trace `AddrKeyLeakCli.trace` (`init`
Alice from Bob's honest bundle, then `send` Alice 14-byte `"attack-at-dawn"`):
- Split 0 (`.init`): `NextEventCollidesClassical` on `.init` is `False`
  (`not_nextEventCollidesClassical_init`).
- Split 1 (`.send` after `[.run evInitAk]`): `not_nextEventCollidesClassical_send` +
  `CliCoinSplit.init_exit0_cut_eq` pins the Call-0 hardware trace to
  `.recv bundleBytes :: call0RngEvents`, where every assumed-injective memo entry in
  `prefixTerms` has byte length `> 14` (`≥ 32`), ruling out a plaintext memo collision with
  any 14-byte plaintext (`"attack-at-dawn"`) regardless of Call 1's `coins` or `exit` stdout.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoSendCollision

open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits flatEvents)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil)
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic.Witnesses
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
open Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs (akTrace akCarrierTrace rawRunAt)

section FastHex

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "chars_of_hex_ak" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_ak" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

/-- Call 0 RNG coins (192 bytes). -/
def coins0 : HwBytes :=
  hexBytes "49c93ba96e848e114ccd7a9ac6fa2f998172a9bdebc69e1b8b4e2a527db2be9e051310e3058b50f2e6340ad91254ddaf320aceff3b048bcc387f996aa41a2a1f4396fa34fcba7a943f37fed8842a7a3484bd1ae79dc7fb3af4d2112dba377abdd5c50a08141ee32e1e5622a5073163413fa1c60b082178b8fc1d349d1c2f4c19060ea05c8c7ca842d116c8ba3ffdf0a7c020c1a4bc16764fdbce839c26eadab24a260419c077fbe8fa8e46b8368f6f20481ee60124cec354836099e2304f9626"

private def coins0Chars : List Char := chars_of_hex_ak coins0
private theorem coins0_eq_hex : coins0 = hexBytes (str_of_hex_ak coins0) := rfl
private theorem coins0Str_eq : (str_of_hex_ak coins0) = String.ofList coins0Chars := rfl
private def coins0Fast : HwBytes := hexBytes.go hexDigit coins0Chars

private theorem coins0_eq_fast : coins0 = coins0Fast := by
  change coins0 = hexBytes.go hexDigit coins0Chars
  rw [coins0_eq_hex, coins0Str_eq, hexBytes_ofList]

private theorem coins0_length : coins0.length = 192 := by
  rw [coins0_eq_fast]; rfl

private def initiateCharChunks (cs : List Char) : List (List Char) :=
  [cs.take 64] ++ (List.range 32).map (fun j => (cs.drop (64 + 8 * j)).take 8) ++ [(cs.drop 320).take 64]

private theorem map_rng_hexBytes_ofList (css : List (List Char)) :
    css.map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) =
    css.map (fun cs => MachineEvent.rng (hexBytes.go hexDigit cs)) := by
  induction css with
  | nil => rfl
  | cons cs css _ =>
    simp only [List.map_cons, hexBytes_ofList]

private theorem call0RngEvents_eq_ofList :
    call0RngEvents =
      (initiateCharChunks coins0Chars).map (fun cs => MachineEvent.rng (hexBytes (String.ofList cs))) := rfl

private theorem initiateDrawsOfCoins_coins0_eq :
    (CliCoinSplit.initiateDrawsOfCoins coins0).map MachineEvent.rng = call0RngEvents := by
  rw [coins0_eq_fast, call0RngEvents_eq_ofList, map_rng_hexBytes_ofList]
  rfl

private def pt1 : HwBytes :=
  match (AddrKeyLeakCli.trace[1]? : Option CliEvent) with
  | some (.run ev) => ev.input
  | _ => []

private def coins1 : HwBytes :=
  match (AddrKeyLeakCli.trace[1]? : Option CliEvent) with
  | some (.run ev) => ev.coins
  | _ => []

private def sentWire1 : HwBytes :=
  match (AddrKeyLeakCli.trace[1]? : Option CliEvent) with
  | some (.run ev) =>
    match ev.exit with
    | some (_, out) => out
    | none => []
  | _ => []

private def pt1Chars : List Char := chars_of_hex_ak pt1
private theorem pt1_eq_hex : pt1 = hexBytes (str_of_hex_ak pt1) := rfl
private theorem pt1Str_eq : (str_of_hex_ak pt1) = String.ofList pt1Chars := rfl

private theorem pt1_length : pt1.length = 14 := by
  have h : pt1 = hexBytes.go hexDigit pt1Chars := by
    rw [pt1_eq_hex, pt1Str_eq, hexBytes_ofList]
  rw [h]; rfl

end FastHex

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem nil_eq_hexBytes : ([] : HwBytes) = hexBytes "" := by
  unfold hexBytes hexBytes.go; rfl

/-- Call 0 (`init` Alice from Bob's honest bundle) structured `RunEvent`. -/
def evInitAk : RunEvent :=
  { party := "alice"
    cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle"
    input := bundleBytes
    coins := coins0
    exit := some (0, []) }

private def evSendAk : RunEvent :=
  { party := "alice"
    cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩
    input := pt1
    coins := coins1
    exit := some (0, sentWire1) }

theorem evInitAk_eq_rawRun0 :
    evInitAk = { (rawRunAt 0) with exit := some (0, []) } := by
  unfold evInitAk coins0 rawRunAt akTrace AddrKeyLeakCli.trace
  dsimp only [List.getElem?_cons_zero]
  rw [bundleBytes_eq_hex]

private theorem rawRun1_input_length : (rawRunAt 1).input.length = 14 := by
  show pt1.length = 14
  exact pt1_length

private theorem cliEventsAk_eq : [.run evInitAk, .run evSendAk] = AddrKeyLeakCli.trace := by
  unfold evInitAk evSendAk pt1 coins1 sentWire1 coins0 AddrKeyLeakCli.trace
  dsimp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
  rw [bundleBytes_eq_hex, nil_eq_hexBytes]

private theorem callsOf_evInitAk : callsOf [.run evInitAk] = [("alice", true)] := rfl

set_option linter.unnecessarySeqFocus false in
private theorem schedFits_evInitAk :
    SchedFits (callsOf [.run evInitAk])
      Witnesses.Cheval26SmallSubgroupHighBitComp.who
      Witnesses.Cheval26SmallSubgroupHighBitComp.ok := by
  rw [callsOf_evInitAk]
  refine ⟨by decide, fun k p b hget => ?_⟩
  rcases k with _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

private theorem list_eq_two_splits {α : Type} {a b x : α} {xs ys : List α}
    (h : [a, b] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b]) ∨
    (xs = [a] ∧ x = b ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, xs⟩⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr ⟨rfl, rfl, rfl⟩
  · simp at h

private theorem call0RngEvents_take_1_gt_14 :
    ∀ e ∈ call0RngEvents.take 1, 14 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he
  rw [call0RngEvents_take_1_eq, List.mem_singleton] at he
  subst he
  show 14 < rngEkBytes.length
  rw [rngEkBytes_length]
  decide

private theorem call0RngEvents_drop_33_gt_14 :
    ∀ e ∈ call0RngEvents.drop 33, 14 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he
  rw [call0RngEvents_drop_33_eq, List.mem_singleton] at he
  subst he
  show 14 < rngDhsBytes.length
  rw [rngDhsBytes_length]
  decide

/-- Post-Call-0 memo deadness for any 14-byte plaintext (`"attack-at-dawn"`). -/
theorem ptDead14_self {r : Records} {S : Sem} {who₀ : List Participant} {ok₀ : Nat → Bool}
    {g : Ghost} {ms : List Move} {pt : HwBytes}
    (hwf : RecordsWF r) (hnb : Common443.CompSetupSecrecy.NoBrk r ms)
    (hlen : pt.length = 14)
    (hexp : ExplainsMoves compI0 r S who₀ ok₀ g ms (.recv bundleBytes :: call0RngEvents))
    (hem : EventMatchesEntry compI0 r S g (.pt pt) (ptEntryOfNextEncrypt r ms)) :
    ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
  refine not_pt_collision_of_ne_bytes hem fun t ht x hx hinj hval_eq => ?_
  have hgt : 14 < x.2.2.length := memoInjGt_prefixTerms_of_matchedPrefix_ini_of hwf hexp.1
      (iniPrefixStateSecretsInv_call0 hwf hnb hexp)
      (by decide) call0RngEvents_kind call0RngEvents_take_1_gt_14 call0RngEvents_drop_33_gt_14
      t ht x hx hinj
  rw [hval_eq, hlen] at hgt
  exact Nat.lt_irrefl 14 hgt

/-- Refutes `CollisionAfterExplainedPrefix` on any 2-call trace `[.run ev0, .run ev1]` whose
first call equals `evInitAk` and whose second call is a `.send` of a 14-byte plaintext
(independent of `ev1.coins` and `ev1.exit`). -/
theorem not_collisionAfterExplainedPrefix_two_runs {r : Records} {S : Sem}
    {ev0 ev1 : RunEvent} {peer : CryptoVerification.SignalSession.Address}
    (hwf : ProtocolSetupWF r)
    (h0 : ev0 = evInitAk)
    (hcmd1 : ev1.cmd = .send peer)
    (hlen1 : ev1.input.length = 14) :
    ¬ CollisionAfterExplainedPrefix compI0 r S [.run ev0, .run ev1] := by
  subst h0
  have hbf : BreakFree [.run evInitAk, .run ev1] :=
    breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil)
  refine not_collisionAfterExplainedPrefix_of_splits hbf ?_
  intro evs₁ ev evs₂ g ss vis hevs hex
  rcases list_eq_two_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
  · injection hev with hev'; subst hev'
    exact not_nextEventCollidesClassical_init rfl
  · injection hev with hev'; subst hev'
    have hnrc₁ : ¬ ReadCollisionCliClassical compI0 r S g ss [.run evInitAk] := by
      refine not_readCollisionCliClassical_of_no_recv ?_
      intro ev' out' hev' ⟨p', hcmd'⟩ _
      simp only [List.mem_singleton] at hev'
      injection hev' with hev''; subst hev''; cases hcmd'
    refine not_nextEventCollidesClassical_send hwf schedFits_evInitAk hex hnrc₁ hcmd1 ?_
    intro τ ms hex_cli _ hnb hbme hmcol
    obtain ⟨hτ, hex_hw⟩ := CliCoinSplit.init_exit0_cut_eq (by decide) coins0_length hex_cli
    subst hτ
    dsimp only [evInitAk] at hex_hw
    rw [initiateDrawsOfCoins_coins0_eq] at hex_hw
    have hem : EventMatchesEntry compI0 r S g (.pt ev.input) (ptEntryOfNextEncrypt r ms) :=
      ⟨rfl, by simpa [EventMatchesEntry, BytesMatchEntry, ptEntryAt, ptEntryOfNextEncrypt, eventBytes] using hbme⟩
    have hmcol' : MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms))
        (runTraceMoves r ms) (runVis r ms)
        (ptEntryOfNextEncrypt r ms).terms (ptEntryOfNextEncrypt r ms).terms := by
      simpa [MemoCollisionOn, ptEntryAt, ptEntryOfNextEncrypt] using hmcol
    exact ptDead14_self hwf hnb hlen1 hex_hw hem hmcol'

/-- Refutation of `CollisionAfterExplainedPrefix` on `ImplTrace.akCarrierTrace` from
`ProtocolSetupWF r`. -/
theorem not_collisionAfterExplainedPrefix_carrier_of_wf {r : Records} {S : Sem}
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S akCarrierTrace :=
  not_collisionAfterExplainedPrefix_two_runs hwf evInitAk_eq_rawRun0.symm rfl rawRun1_input_length

/-- Refutation of `CollisionAfterExplainedPrefix` on `ImplTrace.akCarrierTrace` assuming
`ProtocolSetupWF r` and `compFitsPinned AddrKeyLeakCli.setup compI0 r`. -/
theorem not_collisionAfterExplainedPrefix_carrier {r : Records} {S : Sem}
    (hwf : ProtocolSetupWF r) (_hfits : compFitsPinned AddrKeyLeakCli.setup compI0 r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S akCarrierTrace :=
  not_collisionAfterExplainedPrefix_carrier_of_wf hwf

/-- Refutation of `CollisionAfterExplainedPrefix` on `ImplTrace.akCarrierTrace` from
`compFitsPinned AddrKeyLeakCli.setup compI0 r`. -/
theorem not_collisionAfterExplainedPrefix_carrier_of_fits {r : Records} {S : Sem}
    (hfits : compFitsPinned AddrKeyLeakCli.setup compI0 r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S akCarrierTrace :=
  not_collisionAfterExplainedPrefix_carrier_of_wf hfits.1.1

/-- Refutation of `CollisionAfterExplainedPrefix` on `AddrKeyLeakCli.trace` from `ProtocolSetupWF r`. -/
theorem not_collisionAfterExplainedPrefix_of_wf {r : Records} {S : Sem}
    (hwf : ProtocolSetupWF r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S AddrKeyLeakCli.trace := by
  rw [← cliEventsAk_eq]
  exact not_collisionAfterExplainedPrefix_two_runs hwf rfl rfl pt1_length

/-- Refutation of `CollisionAfterExplainedPrefix` on `AddrKeyLeakCli.trace` assuming
`ProtocolSetupWF r` and `compFitsPinned AddrKeyLeakCli.setup compI0 r`. -/
theorem not_collisionAfterExplainedPrefix {r : Records} {S : Sem}
    (hwf : ProtocolSetupWF r) (_hfits : compFitsPinned AddrKeyLeakCli.setup compI0 r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S AddrKeyLeakCli.trace :=
  not_collisionAfterExplainedPrefix_of_wf hwf

/-- Refutation of `CollisionAfterExplainedPrefix` on `AddrKeyLeakCli.trace` from
`compFitsPinned AddrKeyLeakCli.setup compI0 r`. -/
theorem not_collisionAfterExplainedPrefix_of_fits {r : Records} {S : Sem}
    (hfits : compFitsPinned AddrKeyLeakCli.setup compI0 r) :
    ¬ CollisionAfterExplainedPrefix compI0 r S AddrKeyLeakCli.trace :=
  not_collisionAfterExplainedPrefix_of_wf hfits.1.1

end Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.NoSendCollision
