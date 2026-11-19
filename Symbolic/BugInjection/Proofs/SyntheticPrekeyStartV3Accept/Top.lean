/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Memo

/-!
# Machine-Checked Spec-Half Disproof for `synthetic-prekey-start-v3-accept`

Proves `spec_half_pinned` and `not_signalSessionSecurePlaced_of_implHalf` for
`Symbolic.BugInjection.Synthetic.Witnesses.PrekeyStartV3AcceptCli`, where the mutant omits the
`process_prekey_impl` outer wire-version check (`message.message_version() == 3`) and accepts an
outer `0x33` (v3) `PreKeySignalMessage` carrying Kyber fields. Also includes standalone audit
theorems `protocolSetupWF_kyberSec_rejectionSeed_unconstrained` and
`implicitRejectMacCli_kyberCiphertext_unchanged`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped _root_.DY.Libsignal.Composed _root_.DY.Libsignal.Composed.Refinement
cref_hide_foreign_instances

namespace Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Top

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
open Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem stepsWF_split : ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
    StepsWF (ss₁ ++ ss₂) tr → StepsWF ss₁ tr ∧ StepsWF ss₂ (runSteps ss₁ tr)
  | [], _, _, h => ⟨trivial, h⟩
  | _ :: ss₁, ss₂, _, ⟨hp, hl, hrest⟩ =>
    let ⟨h1, h2⟩ := stepsWF_split ss₁ ss₂ _ hrest
    ⟨⟨hp, hl, h1⟩, h2⟩

theorem reachable_of_stepsWF : ∀ (xs : List Step) {tr : ExecTrace},
    tr.Reachable DY.Libsignal.Composed.reachability →
    StepsWF xs tr →
    (runSteps xs tr).Reachable DY.Libsignal.Composed.reachability
  | [], _, hr, _ => hr
  | x :: xs, _, hr, ⟨hp, _, hrest⟩ =>
    reachable_of_stepsWF xs (DY.Trace.Reachable.Step x.toInput hp hr) hrest

theorem step_eq_network_of_invisible {x : Step} (h : x.cls = .invisible) :
    ∃ m, x = .network m := by
  cases x <;> simp_all [Step.cls]

theorem at?_append_other_eq {E E' : Type}
    [DY.ExecTraceTypes.Has E] [DY.ExecTraceTypes.Has E']
    (tr : ExecTrace) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E') = none)
    (j : Nat) : ((tr.append e).at? j : Option E') = (tr.at? j : Option E') := by
  by_cases hj : j < tr.length
  · exact Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt tr e hj
  · by_cases hjeq : j = tr.length
    · subst hjeq
      rw [Symbolic.Swarm.CREF.at?_append_length, hnone,
        Symbolic.Swarm.CREF.at?_ge_length tr (Nat.le_refl _)]
    · have hlen : (tr.append e).length = tr.length + 1 := by
        simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      rw [Symbolic.Swarm.CREF.at?_ge_length (tr.append e) (by omega),
        Symbolic.Swarm.CREF.at?_ge_length tr (by omega)]

theorem at?_runSteps_invisible {E : Type} [DY.ExecTraceTypes.Has E]
    (hnone : ∀ m : DY.Bytes,
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (⟨m⟩ : DY.Network.ExecEntryT) : ExecTrace.Entry) :
        Option E) = none) :
    ∀ {xs : List Step} (tr : ExecTrace),
      (∀ x ∈ xs, x.cls = .invisible) →
      ∀ j : Nat, ((runSteps xs tr).at? j : Option E) = (tr.at? j : Option E)
  | [], _, _, _ => rfl
  | x :: xs, tr, hinv, j => by
    obtain ⟨m, rfl⟩ := step_eq_network_of_invisible (hinv x List.mem_cons_self)
    simp only [runSteps, Symbolic.Proofs.Swarm.UA.BI.Step.next_network]
    rw [at?_runSteps_invisible hnone _ (fun y hy => hinv y (List.mem_cons_of_mem _ hy)) j,
      at?_append_other_eq tr (⟨m⟩ : DY.Network.ExecEntryT) (hnone m) j]

def NoTRState (tr : ExecTrace) : Prop :=
  ∀ j : Nat, (tr.at? j : Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) = none

theorem noTRState_nil : NoTRState (DY.Trace.nil : ExecTrace) := by
  intro j
  exact Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
    (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])

theorem noTRState_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : NoTRState tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option Symbolic.Swarm.COMPOSED.CompTrace.TRStEntry) = none) :
    NoTRState (tr.append e) :=
  fun j => (at?_append_other_eq tr e hnone j).trans (h j)

theorem noTRState_genRand (n : Nat) : Preserves NoTRState (DY.Random.genRand n) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.genRand tr n).2.symm ▸ noTRState_append_other h (RndE n) rfl
theorem noTRState_sendMessage (msg : DY.Bytes) : Preserves NoTRState (DY.Network.sendMessage msg) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr msg).2.symm ▸ noTRState_append_other h (NetE msg) rfl
theorem noTRState_logEvent_pq (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves NoTRState (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.logEvent tr ev).2.symm ▸ noTRState_append_other h (PQEvE ev) rfl
theorem noTRState_storeLocalState_pq (me : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves NoTRState (DY.PersistentLocalState.storeLocalState me st) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.storeLocalState tr me st).2.symm ▸ noTRState_append_other h (PQStE me st) rfl
theorem noTRState_getKey (p : DY.Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves NoTRState (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
theorem noTRState_registerIdentity (p : DY.Participant) :
    Preserves NoTRState (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (noTRState_genRand 32) fun _ => ?_
  refine Preserves.bind (noTRState_logEvent_pq _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  exact noTRState_storeLocalState_pq p _
theorem noTRState_genSignedPrekey (b : DY.Participant) (idStateIdx : Nat) :
    Preserves NoTRState (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (noTRState_getKey b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (noTRState_genRand 32) fun _ => ?_
  refine Preserves.bind (noTRState_genRand 64) fun _ => ?_
  refine Preserves.bind (noTRState_logEvent_pq _) fun _ => ?_
  refine Preserves.bind (noTRState_storeLocalState_pq b _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  exact Preserves.pure _
theorem noTRState_genPQPrekey (b : DY.Participant) (idStateIdx : Nat) :
    Preserves NoTRState (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (noTRState_getKey b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (noTRState_genRand 64) fun _ => ?_
  refine Preserves.bind (noTRState_genRand 64) fun _ => ?_
  refine Preserves.bind (noTRState_logEvent_pq _) fun _ => ?_
  refine Preserves.bind (noTRState_storeLocalState_pq b _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  refine Preserves.bind (noTRState_sendMessage _) fun _ => ?_
  exact Preserves.pure _
theorem noTRState_genOneTimePrekey (b : DY.Participant) :
    Preserves NoTRState (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (noTRState_genRand 32) fun _ => ?_
  refine Preserves.bind (noTRState_logEvent_pq _) fun _ => ?_
  refine Preserves.bind (noTRState_storeLocalState_pq b _) fun _ => ?_
  exact Preserves.bind (noTRState_sendMessage _) fun _ => Preserves.pure _
theorem noTRState_setupTrace (r : ProtocolSetup) : NoTRState (setupTrace r) := by
  have hact : Preserves NoTRState (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct
    refine Preserves.bind (noTRState_registerIdentity r.alice) fun _ => ?_
    refine Preserves.bind (noTRState_registerIdentity r.bob) fun hB => ?_
    refine Preserves.bind (noTRState_genSignedPrekey r.bob hB) fun _ => ?_
    refine Preserves.bind (noTRState_genPQPrekey r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact Preserves.pure ()
    · simp only [↓reduceIte]
      exact Preserves.bind (noTRState_genOneTimePrekey r.bob) fun _ => Preserves.pure ()
  exact hact DY.Trace.nil noTRState_nil

local macro "at?_localAliceStartTr_tac" : tactic =>
  `(tactic| (dsimp only [localAliceStartTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))

theorem at?_trSt_localAliceStartTr_of_noTRState {tr : ExecTrace} (htr : NoTRState tr)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) :
    ((localAliceStartTr tr a b o).at? j : Option TRStEntry) =
      if j = tr.length + 8 then some (TRStE a (localAliceStartState tr b o)) else none := by
  by_cases hj : j = tr.length + 8
  · subst hj; simp only [↓reduceIte]; at?_localAliceStartTr_tac
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < tr.length + 8
    · dsimp only [localAliceStartTr]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
        at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, htr j]
    · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by dsimp only [localAliceStartTr]; simp only [length_append_entry]; omega)]

def NoCompOrBreak (tr : ExecTrace) : Prop :=
  ∀ j ev, (tr.at? j : Option Symbolic.Swarm.COMPOSED.CompTrace.PQXDHEntry) =
    some (Symbolic.Swarm.COMPOSED.CompTrace.PQEvE ev) →
    (∀ b ik, ev ≠ .CompromisedIK b ik) ∧ ev ≠ .BrokenDH

theorem noCompOrBreak_nil : NoCompOrBreak (DY.Trace.nil : ExecTrace) := by
  intro j ev h
  rw [Symbolic.Swarm.CREF.at?_ge_length DY.Trace.nil
    (by simp [Symbolic.DYBridge.DY.Trace.length_eq_1])] at h
  cases h

theorem noCompOrBreak_append_other {E : Type} [DY.ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : NoCompOrBreak tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option Symbolic.Swarm.COMPOSED.CompTrace.PQXDHEntry) = none) :
    NoCompOrBreak (tr.append e) := by
  intro j ev hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j ev h0
  · rw [hnone] at hp; cases hp

theorem noCompOrBreak_append_pqEv {tr : ExecTrace} (h : NoCompOrBreak tr)
    (ev₀ : DY.Libsignal.PQXDH.PQXDHEvent)
    (h₀ : (∀ b ik, ev₀ ≠ .CompromisedIK b ik) ∧ ev₀ ≠ .BrokenDH) :
    NoCompOrBreak (tr.append (Symbolic.Swarm.COMPOSED.CompTrace.PQEvE ev₀)) := by
  intro j ev hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, h0⟩ | ⟨_, hp⟩
  · exact h j ev h0
  · rw [Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq] at hp
    cases hp
    exact h₀

theorem noCompOrBreak_genRand (n : Nat) : Preserves NoCompOrBreak (DY.Random.genRand n) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.genRand tr n).2.symm ▸ noCompOrBreak_append_other h (RndE n) rfl
theorem noCompOrBreak_sendMessage (msg : DY.Bytes) : Preserves NoCompOrBreak (DY.Network.sendMessage msg) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr msg).2.symm ▸ noCompOrBreak_append_other h (NetE msg) rfl
theorem noCompOrBreak_storeLocalState_pq (me : DY.Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves NoCompOrBreak (DY.PersistentLocalState.storeLocalState me st) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.storeLocalState tr me st).2.symm ▸ noCompOrBreak_append_other h (PQStE me st) rfl
theorem noCompOrBreak_logEvent_pq (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hev : (∀ b ik, ev ≠ .CompromisedIK b ik) ∧ ev ≠ .BrokenDH) :
    Preserves NoCompOrBreak (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.logEvent tr ev).2.symm ▸ noCompOrBreak_append_pqEv h ev hev
theorem noCompOrBreak_getKey (p : DY.Participant) (stateIdx : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves NoCompOrBreak (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine Preserves.bind (Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
theorem noCompOrBreak_registerIdentity (p : DY.Participant) :
    Preserves NoCompOrBreak (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine Preserves.bind (Preserves.requireTracePredicate _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_genRand 32) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_logEvent_pq _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  exact noCompOrBreak_storeLocalState_pq p _
theorem noCompOrBreak_genSignedPrekey (b : DY.Participant) (idStateIdx : Nat) :
    Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genSignedPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine Preserves.bind (noCompOrBreak_getKey b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_genRand 32) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_genRand 64) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_logEvent_pq _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_storeLocalState_pq b _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  exact Preserves.pure _
theorem noCompOrBreak_genPQPrekey (b : DY.Participant) (idStateIdx : Nat) :
    Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genPQPrekey b idStateIdx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine Preserves.bind (noCompOrBreak_getKey b idStateIdx .identity) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_genRand 64) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_genRand 64) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_logEvent_pq _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_storeLocalState_pq b _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_sendMessage _) fun _ => ?_
  exact Preserves.pure _
theorem noCompOrBreak_genOneTimePrekey (b : DY.Participant) :
    Preserves NoCompOrBreak (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine Preserves.bind (noCompOrBreak_genRand 32) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_logEvent_pq _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩) fun _ => ?_
  refine Preserves.bind (noCompOrBreak_storeLocalState_pq b _) fun _ => ?_
  exact Preserves.bind (noCompOrBreak_sendMessage _) fun _ => Preserves.pure _
theorem noCompOrBreak_setupTrace (r : ProtocolSetup) : NoCompOrBreak (setupTrace r) := by
  have hact : Preserves NoCompOrBreak (setupAct r.alice r.bob r.withOpk) := by
    unfold setupAct
    refine Preserves.bind (noCompOrBreak_registerIdentity r.alice) fun _ => ?_
    refine Preserves.bind (noCompOrBreak_registerIdentity r.bob) fun hB => ?_
    refine Preserves.bind (noCompOrBreak_genSignedPrekey r.bob hB) fun _ => ?_
    refine Preserves.bind (noCompOrBreak_genPQPrekey r.bob hB) fun _ => ?_
    cases r.withOpk
    · exact Preserves.pure ()
    · simp only [↓reduceIte]
      exact Preserves.bind (noCompOrBreak_genOneTimePrekey r.bob) fun _ => Preserves.pure ()
  exact hact DY.Trace.nil noCompOrBreak_nil

theorem getMessageSentAt_of_netMsgAt {tr : ExecTrace} {idx : Nat} {m : DY.Bytes}
    (h : NetMsgAt m idx tr) : tr.getMessageSentAt idx = some m := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold NetMsgAt at h
  simp [h]

theorem at?_pqSt_localAliceStartTr (tr : ExecTrace) (a b : DY.Participant)
    (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (j : Nat) :
    ((localAliceStartTr tr a b o).at? j : Option PQXDHStEntry) = (tr.at? j : Option PQXDHStEntry) := by
  dsimp only [localAliceStartTr]
  rw [at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
    at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl,
    at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl, at?_append_other_eq _ _ rfl]

theorem memoInjGt9_of_setupRandAt
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hwf : ProtocolSetupWF r) (hcompat : GhostAndSemMatchSetup compI0 r S g)
    {idx sz : Nat} (hsz : sz = 32 ∨ sz = 64)
    (hrand : Symbolic.Swarm.COMPOSED.CompInv.RandAt (setupTrace r) idx sz) :
    MemoInjGt9 S g (randTerm idx sz) := by
  have hlt : idx < (setupTrace r).length :=
    Nat.lt_of_not_ge fun hge => by
      unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hrand
      rw [Symbolic.Swarm.CREF.at?_ge_length (setupTrace r) hge] at hrand
      cases hrand
  have hni : idx ∈ newIndices DY.Trace.nil (setupTrace r) := by
    unfold newIndices
    have h0 : (DY.Trace.nil : ExecTrace).length = 0 := by
      simp [Symbolic.DYBridge.DY.Trace.length_eq_1]
    rw [h0, Nat.sub_zero]
    exact List.mem_range'.mpr ⟨idx, hlt, by omega⟩
  have hmem_sr : (idx, sz) ∈ setupRandomsAt r := by
    unfold setupRandomsAt
    refine List.mem_filterMap.mpr ⟨idx, hni, ?_⟩
    unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hrand
    simp [hrand]
  have hσ_eq := hcompat.1 (idx, sz) hmem_sr
  have hfr_len := hwf.2.1 (idx, sz) hmem_sr
  have hgt9 : 9 < (g.σ idx sz).length := by
    rw [hσ_eq, hfr_len]
    rcases hsz with rfl | rfl <;> omega
  exact memoInjGt9_randTerm (.inr hgt9)

theorem pqEv_before_localAliceStartTr
    {tr₀ tr₁ : ExecTrace} {pre : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre tr₀)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    {ev : DY.Libsignal.PQXDH.PQXDHEvent} {k : Nat}
    (hev : (localAliceStartTr tr₁ a b o).EventLoggedAt ev k)
    (hne : ∀ a' b' ikA' ikB' spk' pq' opk' ek' ct' keys',
      ev ≠ .AliceDone a' b' ikA' ikB' spk' pq' opk' ek' ct' keys') :
    k < tr₀.length ∧ k < tr₁.length := by
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hev
  have hk_lt_tr₂ : k < (localAliceStartTr tr₁ a b o).length :=
    Nat.lt_of_not_ge fun hge => by
      rw [Symbolic.Swarm.CREF.at?_ge_length _ hge] at hev; cases hev
  have hlen₂ : (localAliceStartTr tr₁ a b o).length = tr₁.length + 9 := by
    dsimp only [localAliceStartTr]; simp only [length_append_entry]
  have hk_lt_tr₁ : k < tr₁.length := by
    by_contra hge₁
    have hge₁' : tr₁.length ≤ k := Nat.le_of_not_lt hge₁
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := getEventAt_pq_localAliceStartTr tr₁ a b o
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at p0 p1 p2 p3 p4 p5 p6 p7 p8
    have hd : k = tr₁.length ∨ k = tr₁.length + 1 ∨ k = tr₁.length + 2 ∨ k = tr₁.length + 3 ∨
        k = tr₁.length + 4 ∨ k = tr₁.length + 5 ∨ k = tr₁.length + 6 ∨ k = tr₁.length + 7 ∨
        k = tr₁.length + 8 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hev] at p0; cases p0
    · rw [hev] at p1; cases p1
    · rw [hev] at p2; cases p2
    · rw [hev] at p3; cases p3
    · rw [hev] at p4; cases p4
    · rw [hev] at p5; injection p5 with hp5; exact hne _ _ _ _ _ _ _ _ _ _ hp5
    · rw [hev] at p6; cases p6
    · rw [hev] at p7; cases p7
    · rw [hev] at p8; cases p8
  have hat₁ : (tr₁.at? k : Option PQXDHEntry) = some (PQEvE ev) := by
    dsimp only [localAliceStartTr] at hev
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
      Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by omega)] at hev
    exact hev
  have hat₀ : (tr₀.at? k : Option PQXDHEntry) = some (PQEvE ev) := by
    rw [htr₁, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv k] at hat₁
    exact hat₁
  have hk_lt_tr₀ : k < tr₀.length :=
    Nat.lt_of_not_ge fun hge => by
      rw [Symbolic.Swarm.CREF.at?_ge_length tr₀ hge] at hat₀; cases hat₀
  exact ⟨hk_lt_tr₀, hk_lt_tr₁⟩

theorem randAt_before_localAliceStartTr
    {tr₀ tr₁ : ExecTrace} {pre : List Step}
    (hpre_inv : ∀ x ∈ pre, x.cls = .invisible)
    (htr₁ : tr₁ = runSteps pre tr₀)
    (a b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut)
    {idx sz : Nat} (hlt₁ : idx < tr₁.length)
    (hr : Symbolic.Swarm.COMPOSED.CompInv.RandAt (localAliceStartTr tr₁ a b o) idx sz) :
    Symbolic.Swarm.COMPOSED.CompInv.RandAt tr₀ idx sz := by
  unfold Symbolic.Swarm.COMPOSED.CompInv.RandAt at hr ⊢
  dsimp only [localAliceStartTr] at hr
  rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega),
    Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by omega)] at hr
  rw [htr₁, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv idx] at hr
  exact hr

theorem matchesEvents_singleton_run
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr₀ : ExecTrace} {ss : List Step} {vis : List VisEntry}
    (hme : MatchesEvents compI0 r S g tr₀ ss [.run ev0] vis) :
    ∃ pre s post,
      ss = pre ++ s :: post ∧
      (∀ x ∈ pre, x.cls = .invisible) ∧
      (∀ x ∈ post, x.cls = .invisible) ∧
      RunMatches compI0 r S g (runSteps pre tr₀) s ev0 vis none := by
  cases hme with
  | run0 _ hRej _ => exact False.elim (no_runRejected_ev0 hRej)
  | run1 hpre_inv hRun hRest =>
    cases hRest with
    | nil hpost_inv =>
      rw [List.append_nil]
      exact ⟨_, _, _, rfl, hpre_inv, hpost_inv, hRun⟩

theorem prefixTerms_memoInjGt9_ev0
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hex : Explains compI0 r S g ss vis [.run ev0]) :
    ∀ t ∈ prefixTerms r (runTrace r ss) vis, MemoInjGt9 S g t := by
  obtain ⟨hcompat, hgwf, ⟨_, hreach₀, hswf, _⟩, hme⟩ := hex
  set tr₀ := setupTrace r
  obtain ⟨pre, s, post, rfl, hpre_inv, hpost_inv, hRun⟩ := matchesEvents_singleton_run hme
  set v := vis
  ·
    ·
      set tr₁ := runSteps pre tr₀ with htr₁_def
      obtain ⟨hswf_pre, hs_pre, _, _⟩ := stepsWF_split pre (s :: post) tr₀ hswf
      have hreach₁ : tr₁.Reachable reachability := reachable_of_stepsWF pre hreach₀ hswf_pre
      have hreach₂ : (s.next tr₁).Reachable reachability :=
        DY.Trace.Reachable.Step s.toInput hs_pre hreach₁
      obtain ⟨_, _, hfits, hpeer, hok, _, hv_eq, inp, drs, outs, hv_split, hinp, _⟩ := hRun
      have ⟨addr₀, pth₀, hcmd₀⟩ : ∃ addr pth, ev0.cmd = .init addr pth := ⟨_, _, rfl⟩
      rw [hcmd₀] at hfits
      cases hs_eq : s with
      | aliceStart a b idS regB hb =>
        rw [hs_eq] at hpeer hok hv_eq hreach₂
        have hb_eq : b = r.bob := hpeer
        subst hb_eq
        obtain ⟨ikA, ikB, spk, spkSig, pqpk, pqpkSig, opk,
          hspk, hspkSig, hpq, hpqSig, hopk, hnext⟩ := aliceStart_ok_eq_localAliceStartTr hok
        set o₀ := aliceOut tr₁ ikA ikB spk pqpk opk
        have hreach_la : (localAliceStartTr tr₁ a r.bob o₀).Reachable reachability := by
          rwa [← hnext]
        dsimp only [stepView] at hv_eq
        rw [ite_eq_left_iff.mpr (fun h => absurd hok h), hnext,
          exposures_localAliceStartTr, List.append_nil] at hv_eq
        have hopk_none : opk = none := by
          rcases hopk with ⟨_, hopk_n⟩ | ⟨idx, u, hhb_s, _, hu⟩
          · exact hopk_n
          · exfalso
            have hv_al := hv_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o₀ hb)
            rw [hv_split] at hv_al
            injection hv_al with hinp_eq _
            have hkind₀ : inputKind ev0 = .recv := rfl
            rw [hkind₀, hinp_eq] at hinp
            have hrec5 : received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) =
                [spk, spkSig, pqpk, pqpkSig, u] := by
              rw [hhb_s]
              change received tr₁ [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig, idx] = [spk, spkSig, pqpk, pqpkSig, u]
              simp only [received, List.filterMap_cons, List.filterMap_nil,
                getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
                getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig,
                getMessageSentAt_of_netMsgAt hu]
            have hbm := hinp.2
            dsimp only at hbm
            rw [hrec5] at hbm
            exact ev0_input_getElem4_ne_one hbm.2.1
        subst hopk_none
        set o := aliceOut tr₁ ikA ikB spk pqpk none
        have hv_al : v =
            { kind := .recv, terms := received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList),
              layout := .bundle, anchor := none } ::
            rngEntry (randTerm tr₁.length 32) ::
            (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
              [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }]) :=
          hv_eq.trans (aliceVis_localAliceStartTr tr₁ a r.bob o hb)
        -- Fresh draws of `aliceStart` have length 32 > 9 via `GhostWF`
        have hmem_ek : rngEntry (randTerm tr₁.length 32) ∈ v := by
          rw [hv_al]; exact List.mem_cons_of_mem _ List.mem_cons_self
        have hek_gt9 : MemoInjGt9 S g (randTerm tr₁.length 32) := by
          have hlen := hgwf.1 _ hmem_ek rfl tr₁.length 32 (by decide) (List.mem_singleton.mpr rfl)
          exact memoInjGt9_randTerm (.inr (by omega))
        have hmem_ent : (⟨.rng, [randTerm (tr₁.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ v := by
          rw [hv_al]
          refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
          unfold kyberCoinEntries
          exact List.mem_map.mpr ⟨0, by decide, rfl⟩
        have hent_gt9 : MemoInjGt9 S g (randTerm (tr₁.length + 1) 32) := by
          have hlen := hgwf.1 _ hmem_ent rfl (tr₁.length + 1) 32 (by decide) (List.mem_singleton.mpr rfl)
          exact memoInjGt9_randTerm (.inr (by omega))
        have hmem_dhs : ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry) ∈ v := by
          rw [hv_al]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
        have hdhs_gt9 : MemoInjGt9 S g (randTerm (tr₁.length + 2) 32) := by
          have hlen := hgwf.1 _ hmem_dhs rfl (tr₁.length + 2) 32 (by decide) (List.mem_singleton.mpr rfl)
          exact memoInjGt9_randTerm (.inr (by omega))
        -- `NoCompOrBreak` on `localAliceStartTr tr₁ a r.bob o`
        have hncb₁ : NoCompOrBreak tr₁ := by
          intro j ev hat
          rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv j] at hat
          exact noCompOrBreak_setupTrace r j ev hat
        have hncb₂ : NoCompOrBreak (localAliceStartTr tr₁ a r.bob o) := by
          dsimp only [localAliceStartTr]
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_pqEv ?_ _ ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_other ?_ _ rfl
          refine noCompOrBreak_append_other ?_ _ rfl
          exact noCompOrBreak_append_other hncb₁ _ rfl
        -- Positional secrets on `localAliceStartTr` come from `setupTrace r`
        have hik_gt9 : ∀ p s_ik,
            Symbolic.Swarm.COMPOSED.CompInv.IKAt (localAliceStartTr tr₁ a r.bob o) p s_ik →
            MemoInjGt9 S g s_ik := by
          rintro p _ ⟨idx, rfl, hr, hev⟩
          have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
            (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
          exact memoInjGt9_of_setupRandAt hwf hcompat (.inl rfl)
            (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
        have hspk_gt9 : ∀ p s_spk,
            Symbolic.Swarm.COMPOSED.CompInv.SPKAt (localAliceStartTr tr₁ a r.bob o) p s_spk →
            MemoInjGt9 S g s_spk := by
          rintro p _ ⟨idx, rfl, hr, _, hev⟩
          have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
            (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
          exact memoInjGt9_of_setupRandAt hwf hcompat (.inl rfl)
            (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
        have hpq_gt9 : ∀ p s_pq,
            Symbolic.Swarm.COMPOSED.CompInv.PQAt (localAliceStartTr tr₁ a r.bob o) p s_pq →
            MemoInjGt9 S g s_pq := by
          rintro p _ ⟨idx, rfl, hr, _, hev⟩
          have ⟨_, hk₁⟩ := pqEv_before_localAliceStartTr hpre_inv htr₁_def a r.bob o hev
            (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
          exact memoInjGt9_of_setupRandAt hwf hcompat (.inr rfl)
            (randAt_before_localAliceStartTr hpre_inv htr₁_def a r.bob o (by omega) hr)
        -- `SpqrInv.aliceDone` at `tr₁.length + 5`
        have had_ev : (localAliceStartTr tr₁ a r.bob o).EventLoggedAt
            (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone a r.bob o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) (tr₁.length + 5) := by
          have hp5 := (getEventAt_pq_localAliceStartTr tr₁ a r.bob o).2.2.2.2.2.1
          rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hp5
          rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
          cases hp : ((localAliceStartTr tr₁ a r.bob o).at? (tr₁.length + 5) : Option PQXDHEntry) with
          | none => rw [hp] at hp5; cases hp5
          | some e =>
            rcases e with ⟨ev'⟩
            rw [hp] at hp5; injection hp5 with hev'; subst hev'; rfl
        obtain ⟨_, sA, _, _, hsA_at, hikA_eq, _, _, hbun_ok⟩ :=
          (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach_la).aliceDone
            a r.bob o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys (tr₁.length + 5) had_ev
        have hsA_gt9 : MemoInjGt9 S g sA := hik_gt9 a sA hsA_at
        have ho_ikA_gt9 : MemoInjGt9 S g o.ikA := hikA_eq ▸ memoInjGt9_dhPk hsA_gt9
        have hikA_sk_gt9 : MemoInjGt9 S g ikA := memoInjGt9_of_dhPk ho_ikA_gt9
        have ⟨ho_ikB_gt9, ho_spk_gt9, ho_pqpk_gt9⟩ :
            MemoInjGt9 S g o.ikB ∧ MemoInjGt9 S g o.spk ∧ MemoInjGt9 S g o.pqpk := by
          rcases hbun_ok with ⟨sB, sS, sQ, hsB, hikB_eq, hsS, hspk_eq, hsQ, hpq_eq⟩ |
              ⟨j, hj, _⟩ | ⟨j, hj, _⟩
          · exact ⟨hikB_eq ▸ memoInjGt9_dhPk (hik_gt9 r.bob sB hsB),
              hspk_eq ▸ memoInjGt9_dhPk (hspk_gt9 r.bob sS hsS),
              hpq_eq ▸ memoInjGt9_kemPk (hpq_gt9 r.bob sQ hsQ)⟩
          · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
            exact False.elim ((hncb₂ j _ hj).1 r.bob o.ikB rfl)
          · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
            exact False.elim ((hncb₂ j _ hj).2 rfl)
        have hkeys_gt9 : MemoInjGt9 S g o.keys.rk ∧ MemoInjGt9 S g o.keys.ck ∧ MemoInjGt9 S g o.keys.pqr :=
          memoInjGt9_pqxdhKdf_none
            (memoInjGt9_agree ho_spk_gt9 hikA_sk_gt9)
            (memoInjGt9_agree ho_ikB_gt9 hek_gt9)
            (memoInjGt9_agree ho_spk_gt9 hek_gt9)
            (memoInjGt9_kemEncap_snd ho_pqpk_gt9 hent_gt9)
        -- Evaluate `runTrace r (pre ++ .aliceStart ... :: post)`
        have htr₃_eq : runTrace r (pre ++ Step.aliceStart a r.bob idS regB hb :: post) =
            runSteps post (localAliceStartTr tr₁ a r.bob o) := by
          unfold runTrace
          rw [DY.Libsignal.Composed.Refinement.runSteps_append]
          change runSteps (Step.aliceStart a r.bob idS regB hb :: post) tr₁ = _
          dsimp only [runSteps]
          rw [hnext]
        rw [htr₃_eq]
        set tr₃ := runSteps post (localAliceStartTr tr₁ a r.bob o) with htr₃_def
        -- Prove all 4 branches of `prefixTerms`
        have hv_not_send_pt : ∀ w ∈ v, w.kind ≠ .send ∧ w.kind ≠ .pt := by
          intro w hw
          rw [hv_al] at hw
          rcases List.mem_cons.mp hw with rfl | hw1
          · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
          · rcases List.mem_cons.mp hw1 with rfl | hw2
            · exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
            · rcases List.mem_append.mp hw2 with hkc | hdhs_w
              · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc
                exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
              · rw [List.mem_singleton] at hdhs_w; subst hdhs_w
                exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
        intro t ht
        unfold prefixTerms principalTerms at ht
        rcases List.mem_append.mp ht with hprin | hpt
        · rcases List.mem_append.mp hprin with h12 | hsec
          · rcases List.mem_append.mp h12 with hsend | hst
            · obtain ⟨w, hw_f, _⟩ := List.mem_flatMap.mp hsend
              obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
              simp only [beq_iff_eq] at hw_k
              exact False.elim ((hv_not_send_pt w hw_v).1 hw_k)
            · obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst
              unfold storedStates at hls_mem
              obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hls_mem
              unfold ExecTrace.getLocalStateAt at hj
              have hnoTR₁ : NoTRState tr₁ := fun k => by
                rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv k]
                exact noTRState_setupTrace r k
              have hat_tr : (tr₃.at? j : Option TRStEntry) =
                  if j = tr₁.length + 8 then some (TRStE a (localAliceStartState tr₁ r.bob o)) else none := by
                rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv j,
                  at?_trSt_localAliceStartTr_of_noTRState hnoTR₁ a r.bob o j]
              change ((tr₃.at? j : Option TRStEntry).map (·.st)) = some ls at hj
              rw [hat_tr] at hj
              by_cases hj8 : j = tr₁.length + 8
              · simp only [hj8, ↓reduceIte, Option.map_some, Option.some.injEq] at hj
                subst hj
                exact memoInjGt9_iniAliceStartState tr₁ a r.bob o
                  ho_ikA_gt9 ho_ikB_gt9 ho_spk_gt9 hkeys_gt9.1 hkeys_gt9.2.1 hkeys_gt9.2.2 hdhs_gt9
              · simp only [hj8, ↓reduceIte, Option.map_none] at hj; cases hj
          · unfold storedSecrets at hsec
            obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hsec
            unfold ExecTrace.getLocalStateAt at hi
            have hat_pq : (tr₃.at? i : Option PQXDHStEntry) = (tr₀.at? i : Option PQXDHStEntry) := by
              rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hpost_inv i,
                at?_pqSt_localAliceStartTr tr₁ a r.bob o i,
                htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hpre_inv i]
            change (((tr₃.at? i : Option PQXDHStEntry).map (·.st)).map DY.Comparse.serialize) = some t at hi
            rw [hat_pq] at hi
            rcases hat₀ : (tr₀.at? i : Option PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
            · simp [hat₀] at hi
            · simp only [hat₀, Option.map_some, Option.some.injEq] at hi
              subst hi
              have hkind := (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable tr₀ hreach₀).stOK
                p st i hat₀
              apply memoInjGt9_serialize_local_pqxdh
              rcases st with ⟨kind, sk⟩
              cases kind
              · obtain ⟨idx, rfl, hr, _⟩ := hkind
                exact memoInjGt9_of_setupRandAt hwf hcompat (.inl rfl) hr
              · obtain ⟨idx, rfl, hr, _⟩ := hkind
                exact memoInjGt9_of_setupRandAt hwf hcompat (.inl rfl) hr
              · obtain ⟨idx, rfl, hr, _⟩ := hkind
                exact memoInjGt9_of_setupRandAt hwf hcompat (.inr rfl) hr
              · obtain ⟨idx, rfl, hr, _⟩ := hkind
                exact memoInjGt9_of_setupRandAt hwf hcompat (.inl rfl) hr
        · unfold plaintextTerms at hpt
          obtain ⟨w, hw_f, _⟩ := List.mem_flatMap.mp hpt
          obtain ⟨hw_v, hw_k⟩ := List.mem_filter.mp hw_f
          simp only [beq_iff_eq] at hw_k
          exact False.elim ((hv_not_send_pt w hw_v).2 hw_k)
      | _ => rw [hs_eq] at hfits; cases hfits

/-- **No collision excuse applies to Call 1 (`ev1`, 9-byte `"hello bob"` `.send`)**. -/
theorem not_nextEventCollides_ev1
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hwf : ProtocolSetupWF r)
    (hex : Explains compI0 r S g ss vis [.run ev0]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0] ev1 := by
  intro hcol
  have hcmd : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  set tr := runTrace r ss
  have hrand : gamma' compI0 S g (randTerm tr.length 32) =
      { bytes := g.σ tr.length 32, shape := randTerm tr.length 32,
        memo := [(randTerm tr.length 32, randTerm tr.length 32, g.σ tr.length 32)] } :=
    gamma'_randTerm compI0 S g tr.length 32 (by decide)
  have hσ_ev1 : g.σ tr.length 32 = ev1.input := by
    have hbme := hcol.1.2
    dsimp only [ptEntryAt, List.map_cons, List.map_nil] at hbme
    change [ (gamma' compI0 S g (randTerm tr.length 32)).bytes ] = [ev1.input] at hbme
    rw [hrand] at hbme
    injection hbme with hhead _
  have hmc := hcol.2 g ⟨rfl, vis, hex⟩
  dsimp only [ptEntryAt] at hmc
  obtain ⟨x₁, hx₁, x₂, hx₂, hsh_ne, _, hpts₁, _, hbytes_eq⟩ := hmc
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrand, List.mem_singleton] at hx₁
  subst hx₁
  have hx₁_pts : randTerm tr.length 32 ∈ plaintextTerms vis ++ [randTerm tr.length 32] :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨_, hinj₂, _⟩ := hpts₁ hx₁_pts
  rcases List.mem_append.mp hx₂ with hx₂_pfx | hx₂_new
  · obtain ⟨t, ht_mem, hx₂_mem⟩ := List.mem_flatMap.mp hx₂_pfx
    have hgt : 9 < x₂.2.2.length := prefixTerms_memoInjGt9_ev0 hwf hex t ht_mem x₂ hx₂_mem hinj₂
    have hlen9 : x₂.2.2.length = 9 := by
      rw [← hbytes_eq, hσ_ev1, ev1_input_len]
    omega
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hrand, List.mem_singleton] at hx₂_new
    subst hx₂_new
    exact hsh_ne rfl

/-- **No collision excuse applies to Call 2 (`ev2`, `wireMut`)**:
- The whisper branch contradicts `wireMut.head? = some 0x03#8`.
- The promoted-session branch (`KnownBaseKeyOn`) requires `p.version = 4`.
- The fresh-session branch (`PreKeyStartCollidesOrRejects`) requires
  `∃ x ∈ preKeyRepresentationsOn ... wireMut`, whose `PreKeyRecvMatches` conjunct requires `p.version = 4`. -/
theorem not_nextEventCollides_ev2
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry} {evs₁ : List CliEvent} :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev2 := by
  intro hcol
  have hcmd : ev2.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  have hinp : ev2.input = wireMut := rfl
  unfold NextEventCollides at hcol
  rw [hcmd, hinp] at hcol
  dsimp only at hcol
  rcases hmsg : wireMut with _ | ⟨tag, body⟩
  · have hh := wireMut_head?; rw [hmsg] at hh; cases hh
  · rw [hmsg] at hcol
    rcases hcol.2 with ⟨htag, _⟩ | ⟨p, hp, ⟨_, hver, _⟩ | ⟨_, ⟨x, hx⟩, _⟩⟩
    · apply wireMut_head_ne_whisper
      rw [hmsg, htag]; rfl
    · rw [← hmsg] at hp
      exact wireMut_version_ne_four hp hver
    · rw [← hmsg] at hx
      exact not_preKeyRecvMatches_wireMut hx.2.2.2.1

/-- **SpecHalf disproof** for `synthetic-prekey-start-v3-accept`: every setup and
interpretation fitting `cliCompFitsPinned setup` satisfies `cliCompShape.SpecHalf`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf (CliSetupMatchesPinned setup) trace := by
  intro (iw : cliCompShape.Interp) (r : ProtocolSetup) hfits
  have hwf : ProtocolSetupWF r := hfits.1.1.1
  have hiw : iw.1 = compI0 := hfits.1.2.1
  refine ⟨hwf, fun (S : OpaqueSymbolSemantics) _ hdisj => ?_⟩
  change (∃ g ss vis, Explains iw.1 r S g ss vis trace) ∨
    CollisionAfterExplainedPrefix iw.1 r S trace at hdisj
  rw [hiw] at hdisj
  rcases hdisj with ⟨g, ss, vis, hex⟩ | ⟨evs₁, ev, evs₂, g, ss, vis, hevs, hex, hcol⟩
  · exact not_explains_trace hex
  · rw [trace_eq_evs] at hevs
    rcases list_eq_three_splits hevs with ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩ | ⟨rfl, hev, _⟩
    · injection hev with hev'; subst hev'
      exact hcol
    · injection hev with hev'; subst hev'
      exact not_nextEventCollides_ev1 hwf hex hcol
    · injection hev with hev'; subst hev'
      exact not_nextEventCollides_ev2 hcol

/-- **Non-vacuity** of `CliSetupMatchesPinned setup`. -/
theorem cliCompFitsPinned_satisfiable :
    ∃ iw r, CliSetupMatchesPinned setup iw r :=
  Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.cliCompFitsPinned_satisfiable

/-- **Top-level `SignalSessionSecurePlaced` regression disproof** for `synthetic-prekey-start-v3-accept`:
any ELF binary `bytes` whose execution produces `trace` (`hi`) violates
`SignalSessionSecurePlaced bytes`. -/
theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
        (cliCompShapePlaced mpl mmpl).ImplHalf (CliSetupMatchesPinned setup) elf trace) :
    ¬ SignalSessionSecurePlaced bytes :=
  not_signalSessionSecurePlaced_of_witness
    hls hmg
    spec_half_pinned
    hi
    coinsFresh_pinned

/-! ## 5. Implicit-Rejection Setup & Witness Invariance Theorems -/

/-- **`ProtocolSetupWF` ML-KEM implicit-rejection seed invariance:**
`ProtocolSetupWF` (`TraceExplanation.lean:111-119`) checks `r.kyberSecB.length = 3169` and the
embedded public key `slice r.kyberSecB 1537 1568 = r.opaqueBytes r.pqpkPubTerm`, leaving the
trailing 32-byte FO implicit-rejection seed `z = slice r.kyberSecB 3137 32` completely
unconstrained. Replacing `z` with any 32-byte `z'` preserves `ProtocolSetupWF` while setting
`slice _ 3137 32 = z'`. Because `ProtocolSetupWF r` is a *premise* of `SignalSessionSecure`,
this makes the top-level security theorem strictly stronger (quantifying over all 32-byte `z'`). -/
theorem protocolSetupWF_kyberSec_rejectionSeed_unconstrained
    (r : ProtocolSetup) (hwf : ProtocolSetupWF r)
    (z' : HwBytes) (hz' : z'.length = 32) :
    let r' : ProtocolSetup := { r with kyberSecB := r.kyberSecB.take 3137 ++ z' }
    ProtocolSetupWF r' ∧ slice r'.kyberSecB 3137 32 = z' := by
  intro r'
  have hlen : r.kyberSecB.length = 3169 := hwf.2.2.2.2.2.2.1
  have hpk : slice r.kyberSecB 1537 1568 = r.opaqueBytes r.pqpkPubTerm := hwf.2.2.2.2.2.2.2
  have htake_len : (r.kyberSecB.take 3137).length = 3137 := by simp [hlen]
  have hr'_len : r'.kyberSecB.length = 3169 := by
    show (r.kyberSecB.take 3137 ++ z').length = 3169
    rw [List.length_append, htake_len, hz']
  have hslice_pk : slice r'.kyberSecB 1537 1568 = r.opaqueBytes r.pqpkPubTerm := by
    show ((r.kyberSecB.take 3137 ++ z').drop 1537).take 1568 = _
    rw [List.drop_append_of_le_length (by omega), List.drop_take]
    have h1600 : (3137 - 1537 : Nat) = 1600 := rfl
    rw [h1600, List.take_append_of_le_length (by simp [hlen]), List.take_take]
    exact hpk
  have hslice_z : slice r'.kyberSecB 3137 32 = z' := by
    show ((r.kyberSecB.take 3137 ++ z').drop 3137).take 32 = z'
    rw [List.drop_left' htake_len, List.take_of_length_le (by omega)]
  exact ⟨⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, hwf.2.2.2.2.2.1,
    hr'_len, hslice_pk⟩, hslice_z⟩

section IrmAudit
set_option maxHeartbeats 2000000

def irmSendWire : HwBytes :=
  match Symbolic.BugInjection.Synthetic.Witnesses.ImplicitRejectMacCli.trace with
  | _ :: .run ev :: _ => match ev.exit with | some (_, out) => out | none => []
  | _ => []

def irmRecvWire : HwBytes :=
  match Symbolic.BugInjection.Synthetic.Witnesses.ImplicitRejectMacCli.trace with
  | _ :: _ :: .run ev :: _ => ev.input
  | _ => []

def irmSendChars : List Char := chars_of_hex_def irmSendWire
theorem irmSendWire_eq_hex : irmSendWire = hexBytes (str_of_hex_def irmSendWire) := rfl
theorem irmSendStr_eq : (str_of_hex_def irmSendWire) = String.ofList irmSendChars := rfl
def irmSendFast : HwBytes := hexBytes.go hexDigit irmSendChars
theorem irmSend_eq_fast : irmSendWire = irmSendFast := by
  change irmSendWire = hexBytes.go hexDigit irmSendChars
  rw [irmSendWire_eq_hex, irmSendStr_eq, hexBytes_ofList]

def irmRecvChars : List Char := chars_of_hex_def irmRecvWire
theorem irmRecvWire_eq_hex : irmRecvWire = hexBytes (str_of_hex_def irmRecvWire) := rfl
theorem irmRecvStr_eq : (str_of_hex_def irmRecvWire) = String.ofList irmRecvChars := rfl
def irmRecvFast : HwBytes := hexBytes.go hexDigit irmRecvChars
theorem irmRecv_eq_fast : irmRecvWire = irmRecvFast := by
  change irmRecvWire = hexBytes.go hexDigit irmRecvChars
  rw [irmRecvWire_eq_hex, irmRecvStr_eq, hexBytes_ofList]

theorem irmFast_kyberCt_eq :
    (parsePreKeyWire irmRecvFast).bind PreKeyFields.kyberCiphertext =
      (parsePreKeyWire irmSendFast).bind PreKeyFields.kyberCiphertext ∧
    ((parsePreKeyWire irmRecvFast).bind PreKeyFields.kyberCiphertext).isSome = true := by
  decide +kernel

end IrmAudit

/-- **`ImplicitRejectMacCli` Kyber ciphertext invariance:**
In `third_party/libsignal/bug-injection/synthetic/witnesses/implicit-reject-mac-cli.json`, the
intended Kyber ciphertext corruption `"or_at"` with `"mask": "80"` at `offset: 4` after
`"42a10c08"` targeted byte `0xb8`, which *already* had bit 7 (`0x80`) set (`0xb8 | 0x80 = 0xb8`).
Consequently, `ImplicitRejectMacCli`'s Call-2 `recv` wire carries the **exact, unmodified**
`kyberCiphertext` sent by Alice in Call 1 — the `synthetic-implicit-reject-mac` witness
never triggered ML-KEM / Kyber implicit rejection or exercised `RejKey`! -/
theorem implicitRejectMacCli_kyberCiphertext_unchanged :
    (parsePreKeyWire irmRecvWire).bind PreKeyFields.kyberCiphertext =
      (parsePreKeyWire irmSendWire).bind PreKeyFields.kyberCiphertext ∧
    ((parsePreKeyWire irmRecvWire).bind PreKeyFields.kyberCiphertext).isSome = true := by
  rw [irmRecv_eq_fast, irmSend_eq_fast]
  exact irmFast_kyberCt_eq


end
end Symbolic.BugInjection.Proofs.SyntheticPrekeyStartV3Accept.Top
