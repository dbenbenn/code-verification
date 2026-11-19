/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli
public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.NonVacuity.CliSatisfiable
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Specifications.Refinement.WireFormat
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Common.CoinsFresh
public import Symbolic.Proofs.SpecLemmas.ModelProofDefs
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.Proofs.SpecLemmas.Refinement.Composed.Steps
public import Symbolic.Proofs.Tests.CliNonvacuity.WitnessBase
public import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.ModelMono
public import Symbolic.Proofs.Swarm.CREF.GammaBridge
public import Symbolic.Proofs.Swarm.COMPOSED.CompInv
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil
public import Symbolic.Proofs.Swarm.UA.BI.Step
public import DY.Bytes.Basic
public import DY.ALaCarte.Basic
public import Comparse.Basic
public import DY.Comparse
public import Symbolic.DYBridge.Comparse.Basic
public import Symbolic.DYBridge.DY.Comparse
public import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.DYBridge.DY.Trace.Basic
public import Symbolic.DYBridge.DY.Trace.Monad
public import Symbolic.DYBridge.DY.Trace.Manipulation
public import Symbolic.DYBridge.DY.Actions.ProtocolEvent
public import Symbolic.DYBridge.DY.Actions.Random
public import Symbolic.DYBridge.DY.Actions.Network
public import Symbolic.DYBridge.DY.Actions.PersistentLocalState
public import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
public import Symbolic.BugInjection.Synthetic.Witnesses.ImplicitRejectMacCli

/-!
# Definitions and Handshake Memo Bounds for `synthetic-prekey-start-v3-accept`

Shared witness abbreviations, wire-format parsing lemmas on the outer `v3` (`0x33`)
`PreKeySignalMessage`, and `MemoInjGt9` subterm length bounds on `aliceStart` for
`Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Top`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

namespace Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (sha256CompressFunction)
open scoped DY.Libsignal.Composed
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (compI0 compLookupPub compLookupDh compKyberEncaps)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (CliSetupMatchesPinned)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
open Symbolic.Swarm.COMPOSED.CompTrace

@[expose] public section

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

elab "chars_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

elab "str_of_hex_def" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit


/-! ## 1. Recorded Witness (`synthetic-prekey-start-v3-accept-cli`) -/

/-- Witness setup from `Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli`. -/
abbrev setup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.setup

/-- Witness interpretations and records (`cliCompFits setup`). -/
abbrev fits :=
  Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.fits

/-- Recorded 3-call CLI witness trace. -/
abbrev trace : List DY.Libsignal.HwEvents.CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.trace

/-! ## 2. Non-Vacuity & `CoinsFresh` -/

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
  Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_unpinned_prekeyStartV3AcceptCli

/-- **`CoinsFresh`** holds for `(setup, trace)` under `CliSetupMatchesPinned setup`. -/
theorem coinsFresh_pinned : ∀ iw r, CliSetupMatchesPinned setup iw r → CoinsFresh r trace :=
  fun iw r hf => coinsFresh_unpinned iw r (cliCompFitsPinned_sub_fits hf)

/-! ## 3. Wire-Format Properties of Mutated `v3` PreKey Message -/

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .recv ⟨"", 0⟩, input := [], coins := [], exit := none }

def ev0 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.trace with
  | .run e :: _ => e | _ => dummyRunEvent
def ev1 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.trace with
  | _ :: .run e :: _ => e | _ => dummyRunEvent
def ev2 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli.trace with
  | _ :: _ :: .run e :: _ => e | _ => dummyRunEvent

theorem trace_eq_evs : trace = [.run ev0, .run ev1, .run ev2] := rfl

theorem ev1_input_len : ev1.input.length = 9 := by decide +kernel

attribute [local irreducible] Symbolic.BugInjection.hexBytes

def ev0Input : HwBytes := ev0.input
def ev0InputChars : List Char := chars_of_hex_def ev0Input
theorem ev0Input_eq_hex : ev0Input = hexBytes (str_of_hex_def ev0Input) := rfl
theorem ev0InputStr_eq : (str_of_hex_def ev0Input) = String.ofList ev0InputChars := rfl
def ev0InputFast : HwBytes := hexBytes.go hexDigit ev0InputChars
theorem ev0Input_eq_fast : ev0Input = ev0InputFast := by
  change ev0Input = hexBytes.go hexDigit ev0InputChars
  rw [ev0Input_eq_hex, ev0InputStr_eq, hexBytes_ofList]

theorem ev0InputFast_getElem4_ne_one : ev0InputFast[4]? ≠ some 1#8 := by decide +kernel
theorem ev0_input_getElem4_ne_one : ev0.input[4]? ≠ some 1#8 := by
  change ev0Input[4]? ≠ some 1#8
  rw [ev0Input_eq_fast]
  exact ev0InputFast_getElem4_ne_one

def ev0Coins : HwBytes := ev0.coins
def ev0CoinsChars : List Char := chars_of_hex_def ev0Coins
theorem ev0Coins_eq_hex : ev0Coins = hexBytes (str_of_hex_def ev0Coins) := rfl
theorem ev0CoinsStr_eq : (str_of_hex_def ev0Coins) = String.ofList ev0CoinsChars := rfl
def ev0CoinsFast : HwBytes := hexBytes.go hexDigit ev0CoinsChars
theorem ev0Coins_eq_fast : ev0Coins = ev0CoinsFast := by
  change ev0Coins = hexBytes.go hexDigit ev0CoinsChars
  rw [ev0Coins_eq_hex, ev0CoinsStr_eq, hexBytes_ofList]

theorem ev0_coins_len : ev0.coins.length = 192 := by
  change ev0Coins.length = 192
  rw [ev0Coins_eq_fast]; rfl

/-- Mutated Call-2 `PreKeySignalMessage` wire bytes (outer version `0x33` = version 3, retaining Kyber fields). -/
def wireMut : HwBytes := ev2.input

def wireMutChars : List Char := chars_of_hex_def wireMut
theorem wireMut_eq_hex : wireMut = hexBytes (str_of_hex_def wireMut) := rfl
theorem wireMutStr_eq : (str_of_hex_def wireMut) = String.ofList wireMutChars := rfl
def wireMutFast : HwBytes := hexBytes.go hexDigit wireMutChars

theorem wireMut_eq_fast : wireMut = wireMutFast := by
  change wireMut = hexBytes.go hexDigit wireMutChars
  rw [wireMut_eq_hex, wireMutStr_eq, hexBytes_ofList]

theorem wireMutFast_head? : wireMutFast.head? = some 0x03#8 := by decide +kernel

/-- `parsePreKey` accepts outer `version = 3` (`0x33`) when Kyber fields are present,
mirroring `PreKeySignalMessage::try_from` (`rust/protocol/src/protocol.rs:475-481`). -/
theorem wireMutFast_parse_version :
    (parsePreKeyWire wireMutFast).map PreKeyFields.version = some 3 := by decide +kernel

theorem wireMut_head? : wireMut.head? = some 0x03#8 := by
  rw [wireMut_eq_fast]; exact wireMutFast_head?

theorem wireMut_head_ne_whisper : wireMut.head? ≠ some wireWhisperTag := by
  rw [wireMut_head?]; decide

theorem wireMut_parse_version :
    (parsePreKeyWire wireMut).map PreKeyFields.version = some 3 := by
  rw [wireMut_eq_fast]; exact wireMutFast_parse_version

theorem wireMut_version_ne_four {p : PreKeyFields} (hp : parsePreKeyWire wireMut = some p) :
    p.version ≠ 4 := by
  have hv := wireMut_parse_version
  rw [hp] at hv
  injection hv with hv'
  omega

end

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-! ## 4. Refutation of `Explains` & `CollisionAfterExplainedPrefix` (`SpecHalf`) -/

theorem no_runRejected_ev0 : ¬ RunRejected ev0 := fun h => h _ rfl
theorem no_runRejected_ev1 : ¬ RunRejected ev1 := fun h => h _ rfl
theorem no_runRejected_ev2 : ¬ RunRejected ev2 := fun h => h _ rfl

theorem matchesEventsAt_run_of_not_rejected
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hNotRej : ¬ RunRejected ev)
    (hM : MatchesEventsAt interp r S g initIds tr ss (.run ev :: evs) vis) :
    ∃ pre s ss' v vs,
      ss = pre ++ s :: ss' ∧
      vis = v ++ vs ∧
      RunMatches interp r S g (runSteps pre tr) s ev v initIds ∧
      MatchesEventsAt interp r S g (nextBundleIds initIds ev) (s.next (runSteps pre tr)) ss' evs vs := by
  cases hM with
  | run1 _ hRun hRest => exact ⟨_, _, _, _, _, rfl, rfl, hRun, hRest⟩
  | run0 _ hRej _ => exact False.elim (hNotRej hRej)

theorem not_preKeyRecvMatches_wireMut {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ek ct msg : DY.Bytes} :
    ¬ PreKeyRecvMatches interp r S g wireMut [ek, ct, msg] := by
  rintro ⟨p, hp, _, _, _, hver, _⟩
  exact wireMut_version_ne_four hp hver

theorem not_preKeyRecvOpkMatches_wireMut {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {terms : List DY.Bytes} :
    ¬ PreKeyRecvOpkMatches interp r S g wireMut terms := by
  rcases terms with _ | ⟨ek, _ | ⟨ct, _ | ⟨msg, _ | ⟨opk, _ | _⟩⟩⟩⟩
  · exact id
  · exact id
  · exact id
  · exact fun h => not_preKeyRecvMatches_wireMut h.1
  · exact fun h => not_preKeyRecvMatches_wireMut h.1
  · exact id

theorem exposures_kind_ne_recv (tr tr' : ExecTrace) {e : VisEntry}
    (he : e ∈ exposures tr tr') : e.kind ≠ .recv := by
  unfold exposures at he
  rcases List.mem_append.mp he with h1 | h2
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h1
    unfold pqExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rintro ⟨⟩
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp h2
    unfold trExposureAt at hj
    split at hj <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj <;> rintro ⟨⟩

theorem not_decVis_wireMut {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr tr' : ExecTrace} {stateIdx msgIdx : Nat} {inp : VisEntry} {rest : List VisEntry}
    (hv : inp :: rest = decVis tr tr' stateIdx msgIdx true ++ exposures tr tr')
    (hinp : BytesMatchEntry interp r S g .recv wireMut inp) : False := by
  unfold decVis at hv
  cases hm : tr.getMessageSentAt msgIdx with
  | none =>
    simp only [hm, Option.map_none, Option.toList_none, List.nil_append] at hv
    have hmem : inp ∈ ((newRandoms tr tr').map fun r => rngEntry r.1) ++
        ((receivedPlaintext tr tr').map fun m => (⟨.accept, [m], .single, none⟩ : VisEntry)).toList ++
        exposures tr tr' := by
      rw [← hv]; exact List.mem_cons_self
    rcases List.mem_append.mp hmem with hmem1 | hmem2
    · rcases List.mem_append.mp hmem1 with hrng | hacc
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng
        have hk := hinp.1; cases hk
      · cases hpt : receivedPlaintext tr tr' with
        | none => simp [hpt] at hacc
        | some m =>
          simp only [hpt, Option.map_some, Option.toList_some, List.mem_singleton] at hacc
          subst hacc
          have hk := hinp.1; cases hk
    · exact exposures_kind_ne_recv tr tr' hmem2 hinp.1.symm
  | some b =>
    simp only [hm, Option.map_some, Option.toList_some, List.cons_append] at hv
    injection hv with hinp_eq _
    rw [hinp_eq] at hinp
    obtain ⟨_, p, _, hp, hver, _⟩ := hinp.2
    exact wireMut_version_ne_four hp hver

/-- Neither `.bobStart` (`PreKeyRecvMatches`) nor `.messageDecrypt` / `.messageDecryptSkipped`
(the `.preKeyInner` `p.version = 4` guard) can match `ev2`. -/
theorem not_runMatches_ev2 {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {v : List VisEntry} {initIds : Option BundlePreKeyIds} :
    ¬ RunMatches interp r S g tr s ev2 v initIds := by
  rintro ⟨_, _, hfits, _, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, _⟩
  have hinp_wire : ev2.input = wireMut := rfl
  have hwrap : runWrapped ev2 = true := by
    unfold runWrapped
    have hcmd : ev2.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    rw [hcmd, hinp_wire]
    dsimp only
    rw [wireMut_head?]
    decide
  have hkind : inputKind ev2 = .recv := rfl
  rw [hwrap, hv_split] at hv_eq
  rw [hinp_wire, hkind] at hinp
  cases hs : s with
  | bobStart b a kh regA mh pq spqr =>
    rw [hs] at hok hv_eq
    dsimp only [stepView] at hv_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hv_eq
    unfold bobVis at hv_eq
    simp only [List.cons_append] at hv_eq
    injection hv_eq with hinp_eq _
    rw [hinp_eq] at hinp
    exact not_preKeyRecvOpkMatches_wireMut hinp.2
  | messageDecrypt me stateIdx msgIdx pqIdx spqrIdx =>
    rw [hs] at hok hv_eq
    dsimp only [stepView] at hv_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hv_eq
    exact not_decVis_wireMut hv_eq hinp
  | messageDecryptSkipped me stateIdx msgIdx skIdx pqIdx spqrIdx =>
    rw [hs] at hok hv_eq
    dsimp only [stepView] at hv_eq
    rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hv_eq
    exact not_decVis_wireMut hv_eq hinp
  | _ =>
    rw [hs] at hfits
    cases hfits

/-- **No model run explains `trace`** (for ANY `interp`, `r`, `S`, `g`). -/
theorem not_explains_trace {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis trace := by
  intro hex
  have hme := hex.2.2.2
  rw [trace_eq_evs] at hme
  obtain ⟨_, _, _, _, _, _, _, _, hme₁⟩ := matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hme
  obtain ⟨_, _, _, _, _, _, _, _, hme₂⟩ := matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hme₁
  obtain ⟨_, _, _, _, _, _, _, hrm₂, _⟩ := matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hme₂
  exact not_runMatches_ev2 hrm₂

theorem list_eq_three_splits {α : Type} {a b c x : α} {xs ys : List α}
    (h : [a, b, c] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b, c]) ∨
    (xs = [a] ∧ x = b ∧ ys = [c]) ∨
    (xs = [a, b] ∧ x = c ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, xs⟩⟩⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · simp at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · simp at h


end
end Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept
