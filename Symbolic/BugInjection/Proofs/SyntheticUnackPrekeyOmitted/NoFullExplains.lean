/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.UA.PendingPreKey

/-!
# Refutation of Full-Trace Explanations for `synthetic-unack-prekey-omitted-cli`

Proves `not_explains_uo` (`0 sorry`): after Call 0 (`init` Alice, exit `0`, no decrypts),
the only stored `TRState` snapshot on `tr₂` is at `tr₁.length + 8` and carries unacknowledged
`pendingPreKey` items `some (o.ek, o.ct)`, whereas Call 1 (`send` Alice) emits a `0x02`
(`wireWhisperTag`) frame (`runWrapped evSend = false`), forcing `encSendEntry` to `[]` and
contradicting the required `.send` output entry of `RunMatches`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoFullExplains

open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant ExecTrace Traceful)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet (TRState)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   Move setupTrace runSteps StepsWF RunMatches OutputsMatch MatchesEventsClassicalAt
   Explains nextBundleIds encSendEntry pendingPreKey runWrapped)
open CryptoVerification.SignalSession (Address)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry NetE aliceOut run_bind_fst)
open Symbolic.Swarm.CREF (b5_run_bind_pure_val bks_stored_of_getLocalState iniAliceStartTr)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (explainsClassical_of breakFree_nil)
open Symbolic.Proofs.Swarm.UA.XlateSteps
  (invisible_eq_network stepIn_ok attackerSend_next_eq_network)
open Symbolic.Proofs.Swarm.UA.PendingPreKey
  (handshakeSessionValid_reachable stepsWF_reachable stepsWF_le
   pendingPreKey_mono trSt_iniAliceStartTr pendingPreKey_iniAliceStartTr
   aliceStart_ok_eq_iniAliceStartTr)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct (noTRState_setupTrace)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice (at?_append_other_eq)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge
  (breakFree_cons_run runMatches_filter_send_send)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (compI0)
open Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.Defs
  (uoEvents uoEvents_eq uoEvents_carrier_eq uoCarrierTrace
   uoSendOut uoCarrierSendOut evInit evSend runWrapped_evSend)

attribute [local instance 2000]
  _root_.DY.Libsignal.Composed.instBytesFunctor_symbolic
  _root_.DY.Libsignal.Composed.instBytesLength_symbolic
  _root_.DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  _root_.DY.Libsignal.Composed.instExecTraceTypes_symbolic
  _root_.DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  _root_.DY.Libsignal.Composed.instHasExecBytes
  _root_.DY.Libsignal.Composed.instHasExecEntryT
  _root_.DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasExecTrace
  _root_.DY.Libsignal.Composed.instHasSubF
  _root_.DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  _root_.DY.Libsignal.Composed.instHasSubFLength
  _root_.DY.Libsignal.Composed.toTripleRatchet
  _root_.DY.Libsignal.Composed.toPQXDHSpqr

private theorem matchesEventsClassical_run_exit0_inv {interp : ExternInterpretation}
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
  | run1 hinv hrm hmev => exact ⟨_, _, _, _, _, rfl, rfl, hinv, hrm, hmev⟩

private theorem stepsWF_split : ∀ (a b : List Step) {tr : ExecTrace},
    StepsWF (a ++ b) tr → StepsWF a tr ∧ StepsWF b (runSteps a tr)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: xs, b, _, ⟨hpre, hloc, hwf⟩ =>
    let ⟨ha, hb⟩ := stepsWF_split xs b hwf
    ⟨⟨hpre, hloc, ha⟩, hb⟩

private theorem network_next_eq (msg : DY.Bytes) (tr : ExecTrace) :
    (Step.network msg).next tr = tr.append (NetE msg) := by
  rw [← attackerSend_next_eq_network]
  dsimp only [Move.next, Move.act]
  rw [b5_run_bind_pure_val]
  exact (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr msg).2

private theorem at?_trSt_runSteps_invisible :
    ∀ (ss : List Step) (tr : ExecTrace),
      (∀ x ∈ ss, x.cls = .invisible) →
      ∀ (j : Nat), ((runSteps ss tr).at? j : Option TRStEntry) = (tr.at? j : Option TRStEntry)
  | [], _, _, _ => rfl
  | s :: ss, tr, hinv, j => by
    obtain ⟨msg, rfl⟩ := invisible_eq_network (hinv s List.mem_cons_self)
    rw [runSteps, at?_trSt_runSteps_invisible ss _ (fun x hx => hinv x (List.mem_cons_of_mem _ hx)),
      network_next_eq]
    exact at?_append_other_eq tr (NetE msg) rfl j

private theorem stored_of_messageEncrypt_ok {tr : ExecTrace} {me : Participant}
    {stateIdx coinsLen pqIdx : Nat}
    (hok : (Step.messageEncrypt me stateIdx coinsLen pqIdx).ok tr = true) :
    ∃ st : TRState, (tr.at? stateIdx : Option TRStEntry) = some ⟨⟨me, st⟩⟩ := by
  unfold Step.ok Step.toInput at hok
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    (me, stateIdx, coinsLen, pqIdx) tr] at hok
  dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability,
    DY.Libsignal.TripleRatchet.messageEncrypt] at hok
  rw [run_bind_fst] at hok
  rcases hget :
      ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | st
  · rw [hget] at hok; cases hok
  · exact ⟨st, bks_stored_of_getLocalState hget⟩

/-- Parametric full-trace `Explains` refutation on any 2-call `[.run ev₀, .run ev₁]` trace where
Call 0 is an exit-`0` `.init` call and Call 1 is an exit-`0` `.send` call with
`runWrapped ev₁ = false`. -/
theorem not_explains_init_send_unwrapped {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {ev₀ ev₁ : RunEvent} {peer₀ peer₁ : Address} {dir₀ : String} {out₀ out₁ : HwBytes}
    (hcmd₀ : ev₀.cmd = .init peer₀ dir₀)
    (hexit₀ : ev₀.exit = some (0, out₀))
    (hcmd₁ : ev₁.cmd = .send peer₁)
    (hexit₁ : ev₁.exit = some (0, out₁))
    (hunw₁ : runWrapped ev₁ = false) :
    ¬ Explains interp r S g ss vis [.run ev₀, .run ev₁] := by
  intro hex
  have hbf := breakFree_cons_run ev₀ (breakFree_cons_run ev₁ breakFree_nil)
  obtain ⟨_, _, hrun, hmev⟩ := explainsClassical_of hex hbf
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, _, hinv₀, hrm₀, hmev₁⟩ :=
    matchesEventsClassical_run_exit0_inv hexit₀ hmev
  obtain ⟨pre₁, s₁, ss₂, v₁, _, rfl, _, hinv₁, hrm₁, _⟩ :=
    matchesEventsClassical_run_exit0_inv hexit₁ hmev₁
  have ⟨hwf_pre₀, hwf_rest₀⟩ := stepsWF_split pre₀ (s₀ :: (pre₁ ++ s₁ :: ss₂)) hrun.2.2.1
  let tr₁ := runSteps pre₀ (setupTrace r)
  have hreach_tr₁ : tr₁.Reachable reachability :=
    stepsWF_reachable pre₀ hrun.2.1 hwf_pre₀
  have hreach_s₀ : (s₀.next tr₁).Reachable reachability :=
    DY.Trace.Reachable.Step s₀.toInput hwf_rest₀.1 hreach_tr₁
  have hfits₀ := hrm₀.2.2.1
  rw [hcmd₀] at hfits₀
  have hok₀ : s₀.ok tr₁ = true := hrm₀.2.2.2.2.1
  cases hs₀ : s₀ with
  | aliceStart a b idStateIdx regIdxB bh =>
    rw [hs₀] at hok₀ hreach_s₀
    obtain ⟨ikA, ikB, spk, pqpk, opk, _, hnext₀⟩ := aliceStart_ok_eq_iniAliceStartTr hok₀
    let o := aliceOut tr₁ ikA ikB spk pqpk opk
    have hnext₀' : (Step.aliceStart a b idStateIdx regIdxB bh).next tr₁ =
        iniAliceStartTr tr₁ a b o := hnext₀
    let tr₂ := runSteps pre₁ (s₀.next tr₁)
    obtain ⟨stateIdx, coinsLen, pqIdx, msg, hs₁, hls, _, hfilter⟩ :=
      runMatches_filter_send_send hcmd₁ hrm₁
    have hok₁ : s₁.ok tr₂ = true := hrm₁.2.2.2.2.1
    rw [hs₁] at hok₁
    obtain ⟨st, hat₂⟩ := stored_of_messageEncrypt_ok hok₁
    have hat₁ : ((iniAliceStartTr tr₁ a b o).at? stateIdx : Option TRStEntry) =
        some ⟨⟨ev₁.party, st⟩⟩ := by
      have h := (at?_trSt_runSteps_invisible pre₁ (s₀.next tr₁) hinv₁ stateIdx).symm.trans hat₂
      rwa [hs₀, hnext₀'] at h
    have hidx : stateIdx = tr₁.length + 8 := by
      by_cases hlt : stateIdx < tr₁.length
      · exfalso
        have hle₀ : tr₁ ≤ iniAliceStartTr tr₁ a b o := by
          rw [← hnext₀']
          exact ((reachability.step (Step.aliceStart a b idStateIdx regIdxB bh).toInput).2.run tr₁).2.property
        have hat₀ : (tr₁.at? stateIdx : Option TRStEntry) = some ⟨⟨ev₁.party, st⟩⟩ := by
          rwa [Symbolic.Swarm.CREF.XplSteps.xat?_le_eq hle₀ hlt] at hat₁
        rw [at?_trSt_runSteps_invisible pre₀ (setupTrace r) hinv₀ stateIdx,
          noTRState_setupTrace r stateIdx] at hat₀
        cases hat₀
      · exact (trSt_iniAliceStartTr (Nat.le_of_not_lt hlt) hat₁).1
    have hppk₀ : pendingPreKey (iniAliceStartTr tr₁ a b o) (tr₁.length + 8) = some (o.ek, o.ct) :=
      pendingPreKey_iniAliceStartTr (handshakeSessionValid_reachable hreach_tr₁) a b o
    have hreach_ini : (iniAliceStartTr tr₁ a b o).Reachable reachability := by
      rwa [← hnext₀']
    have hle₁ : iniAliceStartTr tr₁ a b o ≤ tr₂ := by
      dsimp only [tr₂]
      rw [hs₀, hnext₀']
      exact stepsWF_le pre₁ (iniAliceStartTr tr₁ a b o)
    have hppk₂ : pendingPreKey tr₂ stateIdx = some (o.ek, o.ct) := by
      rw [hidx]
      exact pendingPreKey_mono (handshakeSessionValid_reachable hreach_ini) hle₁ hppk₀
    obtain ⟨_, _, _, _, _, _, _, inp, drs, outs, hv_split, _, _, houts, _, _⟩ := hrm₁
    unfold OutputsMatch at houts
    rw [hexit₁, hcmd₁] at houts
    obtain ⟨vo, rfl, hvo⟩ := houts
    have hvo_mem : vo ∈ v₁.filter (·.kind == .send) := by
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hv_split]; simp
      · simp [← hvo.1]
    have hese_nil : encSendEntry tr₂ (s₁.next tr₂) stateIdx (runWrapped ev₁) = [] := by
      unfold encSendEntry
      rw [hls, hunw₁, hppk₂]
    rw [hfilter, hese_nil] at hvo_mem
    nomatch hvo_mem
  | _ =>
    rw [hs₀] at hfits₀
    cases hfits₀

/-- Parametric full-trace `Explains` refutation on any `[.run ev₀, .run ev₁]` trace where Call 0 is
an exit-`0` `.init` call and Call 1 is an exit-`0` `.send` call with `0x02` (`wireWhisperTag`)
leading wire tag (`out₁.head? = some 0x02#8`). -/
theorem not_explains_init_send_head02 {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {ev₀ ev₁ : RunEvent} {peer₀ peer₁ : Address} {dir₀ : String} {out₀ out₁ : HwBytes}
    (hcmd₀ : ev₀.cmd = .init peer₀ dir₀)
    (hexit₀ : ev₀.exit = some (0, out₀))
    (hcmd₁ : ev₁.cmd = .send peer₁)
    (hexit₁ : ev₁.exit = some (0, out₁))
    (hhead₁ : out₁.head? = some 0x02#8) :
    ¬ Explains interp r S g ss vis [.run ev₀, .run ev₁] := by
  refine not_explains_init_send_unwrapped hcmd₀ hexit₀ hcmd₁ hexit₁ ?_
  unfold runWrapped
  rw [hcmd₁, hexit₁]
  dsimp only
  rw [hhead₁]
  decide

/-- Parametric full-trace `Explains` refutation on `uoEvents out1` for any `out1` with
`out1.head? = some 0x02#8`. -/
theorem not_explains_uo_any {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {out1 : HwBytes} (hhead : out1.head? = some 0x02#8) :
    ¬ Explains interp r S g ss vis (uoEvents out1) :=
  not_explains_init_send_unwrapped (ev₀ := evInit) (ev₁ := evSend out1)
    rfl rfl rfl rfl (runWrapped_evSend hhead)

/-- Parametric full-trace `Explains` refutation on `uoEvents out1` at `compI0`. -/
theorem not_explains_uo {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {out1 : HwBytes} (_hwf : ProtocolSetupWF r) (hhead : out1.head? = some 0x02#8) :
    ¬ Explains compI0 r S g ss vis (uoEvents out1) :=
  not_explains_uo_any hhead

/-- Full-trace `Explains` refutation directly on `UnackPrekeyOmittedCli.trace`. -/
theorem not_explains_uo_trace {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis
        Symbolic.BugInjection.Synthetic.Witnesses.UnackPrekeyOmittedCli.trace :=
  uoEvents_eq ▸ not_explains_uo_any (out1 := uoSendOut) rfl

/-- Full-trace `Explains` refutation directly on `uoCarrierTrace` (`ImplTrace.uoCarrierTrace`). -/
theorem not_explains_uo_carrier {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry} :
    ¬ Explains interp r S g ss vis uoCarrierTrace :=
  uoEvents_carrier_eq ▸ not_explains_uo_any (out1 := uoCarrierSendOut) rfl

end Symbolic.BugInjection.Proofs.SyntheticUnackPrekeyOmitted.NoFullExplains
