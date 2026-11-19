/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Defs

/-!
# Unconditional `¬ Explains` Proof for `synthetic-skipped-key-replay`
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Swarm.CREF
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4 compSha256Rows)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (cliSetupMatchesPinned_satisfiable_of_plausible compHooks0 compRecordsI0)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws (compI0_kyberCorrectOn)
open ByteSpecs
open Symbolic.BugInjection.Proofs.Common443.CompRTag
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
open Symbolic.Swarm.COMPOSED

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

/-! ## Symbolic Trace Execution & Invariant Lemmas for `not_explains_trace` -/

theorem p_c1_message_tryFrom_counter_zero :
    ∃ m, CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec p_c1.message = .ok m ∧
      m.counter = 0 := by
  have h : (match CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec p_c1.message with
    | .ok m => decide (m.counter = 0)
    | .error _ => false) = true := by decide +kernel
  cases htry : CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec p_c1.message with
  | error _ => rw [htry] at h; cases h
  | ok m => rw [htry] at h; exact ⟨m, rfl, of_decide_eq_true h⟩

theorem runWrapped_ev4 : runWrapped ev4 = true := by
  show (ev4.input.head? != some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) = true
  rw [ev4_input_eq_fast]; decide +kernel

theorem runWrapped_ev5 : runWrapped ev5 = true := by
  show (ev5.input.head? != some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) = true
  rw [← ev4_input_eq_ev5_input, ev4_input_eq_fast]; decide +kernel

theorem runWrapped_ev3 : runWrapped ev3 = true := by
  show (ev3.input.head? != some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag) = true
  rw [ev3_input_eq_fast]; decide +kernel

theorem run_bind_isSome {α β : Type} {x : Traceful α} {f : α → Traceful β} {tr : ExecTrace}
    (h : ((x >>= f).run tr).1.isSome = true) :
    ∃ a, (x.run tr).1 = some a ∧
      ((f a).run (x.run tr).2.val).1.isSome = true ∧
      ((x >>= f).run tr).2.val = ((f a).run (x.run tr).2.val).2.val := by
  rw [CompTrace.run_bind_fst] at h
  rcases hx : (x.run tr).1 with _ | a
  · rw [hx] at h; cases h
  · refine ⟨a, rfl, ?_, ?_⟩
    · rw [hx] at h; exact h
    · rw [CompTrace.run_bind_snd, hx]

theorem sendMessage_run (t : DY.Bytes) (tr : ExecTrace) :
    ((DY.Network.sendMessage t : Traceful Nat).run tr).1 = some tr.length ∧
    ((DY.Network.sendMessage t : Traceful Nat).run tr).2.val = tr.append (CompTrace.NetE t) := by
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩

theorem genRand_run (n : Nat) (tr : ExecTrace) :
    ((DY.Random.genRand n : Traceful DY.Bytes).run tr).1 = some (CompTrace.mkRand tr.length n) ∧
    ((DY.Random.genRand n : Traceful DY.Bytes).run tr).2.val = tr.append (CompTrace.RndE n) := by
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_fst, CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only
  rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem logEvent_tr_run (ev : DY.Libsignal.TripleRatchet.TREvent) (tr : ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).1 = some () ∧
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val = tr.append (CompTrace.TREvE ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_fst, CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem logEvent_pq_run (ev : DY.Libsignal.PQXDH.PQXDHEvent) (tr : ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).1 = some () ∧
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val = tr.append (CompTrace.PQEvE ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_fst, CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem logEvent_c_run (ev : ComposedEvent) (tr : ExecTrace) :
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).1 = some () ∧
    ((DY.ProtocolEvent.logEvent ev : Traceful Unit).run tr).2.val = tr.append (CompTrace.CEvE ev) := by
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [CompTrace.run_bind_fst, CompTrace.run_bind_snd, Traceful.run_mk]
  dsimp only; rw [Traceful.run_pure]; exact ⟨rfl, rfl⟩

theorem storeLocalState_tr_run (me : Participant) (st : DY.Libsignal.TripleRatchet.TRState)
    (tr : ExecTrace) :
    ((DY.PersistentLocalState.storeLocalState me st : Traceful Nat).run tr).1 = some tr.length ∧
    ((DY.PersistentLocalState.storeLocalState me st : Traceful Nat).run tr).2.val =
      tr.append (CompTrace.TRStE me st) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩

theorem storeLocalState_pq_run (me : Participant) (st : DY.Libsignal.PQXDH.PQXDHState)
    (tr : ExecTrace) :
    ((DY.PersistentLocalState.storeLocalState me st : Traceful Nat).run tr).1 = some tr.length ∧
    ((DY.PersistentLocalState.storeLocalState me st : Traceful Nat).run tr).2.val =
      tr.append (CompTrace.PQStE me st) := by
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩

def NoBobBefore3 (tr : ExecTrace) : Prop :=
  (∀ idx st, ¬ CompTrace.TRStateStoredAt "bob" st idx tr) ∧
  (∀ idx s pk n seed rIdx src,
    ¬ tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) idx) ∧
  (∀ idx b a ikB ikA spk pqpk opk ek ct keys,
    ¬ tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) idx)

theorem noBobBefore3_nil : NoBobBefore3 Trace.nil := by
  refine ⟨fun idx st h => ?_, fun idx _ _ _ _ _ _ h => ?_, fun idx _ _ _ _ _ _ _ _ _ _ h => ?_⟩
  · simp [CompTrace.TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    simp [Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h
  · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
    simp [Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at h

theorem noBobBefore3_append_net {tr : ExecTrace} (t : DY.Bytes) (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.NetE t)) :=
  ⟨fun i st hs => h.1 i st (CompTrace.trStateStoredAt_append_other rfl hs),
   fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
   fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩

theorem noBobBefore3_append_rnd {tr : ExecTrace} (n : Nat) (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.RndE n)) :=
  ⟨fun i st hs => h.1 i st (CompTrace.trStateStoredAt_append_other rfl hs),
   fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
   fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩

theorem noBobBefore3_append_pqSt {tr : ExecTrace} (p : Participant)
    (st : DY.Libsignal.PQXDH.PQXDHState) (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.PQStE p st)) :=
  ⟨fun i st' hs => h.1 i st' (CompTrace.trStateStoredAt_append_other rfl hs),
   fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
   fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩

theorem noBobBefore3_append_trSt_alice {tr : ExecTrace}
    (st : DY.Libsignal.TripleRatchet.TRState) (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.TRStE "alice" st)) := by
  refine ⟨fun i st' hs => ?_,
    fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
    fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩
  rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, hp, _⟩
  · exact h.1 i st' hs
  · exact absurd hp (by decide)

theorem noBobBefore3_append_cEv {tr : ExecTrace} (ev : ComposedEvent) (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.CEvE ev)) :=
  ⟨fun i st hs => h.1 i st (CompTrace.trStateStoredAt_append_other rfl hs),
   fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
   fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩

theorem noBobBefore3_append_trEv {tr : ExecTrace}
    (ev : DY.Libsignal.TripleRatchet.TREvent)
    (hnot : ∀ s pk n seed rIdx src,
      ev ≠ DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src)
    (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.TREvE ev)) := by
  refine ⟨fun i st hs => h.1 i st (CompTrace.trStateStoredAt_append_other rfl hs),
    fun i s pk n seed rIdx src he => ?_,
    fun i _ _ _ _ _ _ _ _ _ _ he => h.2.2 i _ _ _ _ _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)⟩
  rcases CompTrace.eventLoggedAt_append_same he with ⟨_, he⟩ | ⟨_, heq⟩
  · exact h.2.1 i s pk n seed rIdx src he
  · exact hnot s pk n seed rIdx src heq

theorem noBobBefore3_append_pqEv {tr : ExecTrace}
    (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hnot : ∀ b a ikB ikA spk pqpk opk ek ct keys,
      ev ≠ DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys)
    (h : NoBobBefore3 tr) :
    NoBobBefore3 (tr.append (CompTrace.PQEvE ev)) := by
  refine ⟨fun i st hs => h.1 i st (CompTrace.trStateStoredAt_append_other rfl hs),
    fun i _ _ _ _ _ _ he => h.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he),
    fun i b a ikB ikA spk pqpk opk ek ct keys he => ?_⟩
  rcases CompTrace.eventLoggedAt_append_same he with ⟨_, he⟩ | ⟨_, heq⟩
  · exact h.2.2 i b a ikB ikA spk pqpk opk ek ct keys he
  · exact hnot b a ikB ikA spk pqpk opk ek ct keys heq

theorem preserves_sendMessage (t : DY.Bytes) :
    CompTrace.Preserves NoBobBefore3 (DY.Network.sendMessage t) := by
  intro tr h; rw [(sendMessage_run t tr).2]; exact noBobBefore3_append_net t h

theorem preserves_genRand (n : Nat) :
    CompTrace.Preserves NoBobBefore3 (DY.Random.genRand n) := by
  intro tr h; rw [(genRand_run n tr).2]; exact noBobBefore3_append_rnd n h

theorem preserves_storePq (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    CompTrace.Preserves NoBobBefore3 (DY.PersistentLocalState.storeLocalState p st) := by
  intro tr h; rw [(storeLocalState_pq_run p st tr).2]; exact noBobBefore3_append_pqSt p st h

theorem preserves_storeTr_alice (st : DY.Libsignal.TripleRatchet.TRState) :
    CompTrace.Preserves NoBobBefore3 (DY.PersistentLocalState.storeLocalState "alice" st) := by
  intro tr h; rw [(storeLocalState_tr_run "alice" st tr).2]; exact noBobBefore3_append_trSt_alice st h

theorem preserves_logTr (ev : DY.Libsignal.TripleRatchet.TREvent)
    (hnot : ∀ s pk n seed rIdx src,
      ev ≠ DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) :
    CompTrace.Preserves NoBobBefore3 (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(logEvent_tr_run ev tr).2]; exact noBobBefore3_append_trEv ev hnot h

theorem preserves_logPq (ev : DY.Libsignal.PQXDH.PQXDHEvent)
    (hnot : ∀ b a ikB ikA spk pqpk opk ek ct keys,
      ev ≠ DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) :
    CompTrace.Preserves NoBobBefore3 (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(logEvent_pq_run ev tr).2]; exact noBobBefore3_append_pqEv ev hnot h

theorem preserves_logC (ev : ComposedEvent) :
    CompTrace.Preserves NoBobBefore3 (DY.ProtocolEvent.logEvent ev) := by
  intro tr h; rw [(logEvent_c_run ev tr).2]; exact noBobBefore3_append_cEv ev h

theorem preserves_getKey (p : Participant) (idx : Nat) (k : DY.Libsignal.PQXDH.KeyKind) :
    CompTrace.Preserves NoBobBefore3 (DY.Libsignal.PQXDH.getKey p idx k) := by
  unfold DY.Libsignal.PQXDH.getKey
  exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p idx) fun _ =>
    CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

theorem preserves_registerIdentity (p : Participant) :
    CompTrace.Preserves NoBobBefore3 (DY.Libsignal.PQXDH.registerIdentity p) := by
  unfold DY.Libsignal.PQXDH.registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_logPq _ fun _ _ _ _ _ _ _ _ _ _ h => by cases h) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact preserves_storePq _ _

theorem preserves_genSignedPrekey (b : Participant) (idx : Nat) :
    CompTrace.Preserves NoBobBefore3 (DY.Libsignal.PQXDH.genSignedPrekey b idx) := by
  unfold DY.Libsignal.PQXDH.genSignedPrekey
  refine CompTrace.Preserves.bind (preserves_getKey _ _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_logPq _ fun _ _ _ _ _ _ _ _ _ _ h => by cases h) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_storePq _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _

theorem preserves_genPQPrekey (b : Participant) (idx : Nat) :
    CompTrace.Preserves NoBobBefore3 (DY.Libsignal.PQXDH.genPQPrekey b idx) := by
  unfold DY.Libsignal.PQXDH.genPQPrekey
  refine CompTrace.Preserves.bind (preserves_getKey _ _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_logPq _ fun _ _ _ _ _ _ _ _ _ _ h => by cases h) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_storePq _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _

theorem preserves_genOneTimePrekey (b : Participant) :
    CompTrace.Preserves NoBobBefore3 (DY.Libsignal.PQXDH.genOneTimePrekey b) := by
  unfold DY.Libsignal.PQXDH.genOneTimePrekey
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_logPq _ fun _ _ _ _ _ _ _ _ _ _ h => by cases h) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_storePq _ _) fun _ => ?_
  exact CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => CompTrace.Preserves.pure _

theorem preserves_aliceStart (idIdx regIdxB : Nat) (bh : DY.Libsignal.PQXDH.BundleHandles) :
    CompTrace.Preserves NoBobBefore3 (aliceStart "alice" "bob" idIdx regIdxB bh) := by
  intro tr hInv
  unfold aliceStart
  exact CompTrace.bind_aliceHandshake_at "alice" "bob" idIdx regIdxB bh tr hInv
    (noBobBefore3_append_rnd 32 hInv)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by
      have hInv2 := noBobBefore3_append_rnd 32 (noBobBefore3_append_rnd 32 hInv)
      refine (CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_) _ hInv2
      refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
      refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
      refine CompTrace.Preserves.bind (preserves_logPq _ fun _ _ _ _ _ _ _ _ _ _ h => by cases h) fun _ => ?_
      refine CompTrace.Preserves.bind (preserves_logTr _ fun _ _ _ _ _ _ h => by cases h) fun _ => ?_
      refine CompTrace.Preserves.bind (preserves_logC _) fun _ => ?_
      exact preserves_storeTr_alice _)

theorem preserves_messageEncrypt_alice (stIdx coinsLen pqIdx : Nat) :
    CompTrace.Preserves NoBobBefore3
      (DY.Libsignal.TripleRatchet.messageEncrypt "alice" stIdx coinsLen pqIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncrypt
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genRand _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_logTr _ fun _ _ _ _ _ _ h => by cases h) fun _ => ?_
  refine CompTrace.Preserves.bind ?_ fun _ => preserves_sendMessage _
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact CompTrace.Preserves.bind (preserves_logTr _ fun _ _ _ _ _ _ h => by cases h) fun _ =>
    preserves_storeTr_alice _

theorem preserves_messageEncryptAbort_alice (stIdx : Nat) :
    CompTrace.Preserves NoBobBefore3
      (DY.Libsignal.TripleRatchet.messageEncryptAbort "alice" stIdx) := by
  unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
  exact CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr _ _) fun _ =>
    CompTrace.Preserves.bind (preserves_genRand _) fun _ => CompTrace.Preserves.failure

theorem noBobBefore3_step_invisible {s : Step} {tr : ExecTrace}
    (hInv : s.cls = .invisible) (h : NoBobBefore3 tr) : NoBobBefore3 (s.next tr) := by
  obtain ⟨t, rfl⟩ := invisible_step_eq_network hInv
  dsimp only [Step.next, Step.toInput]
  rw [stepIn_next DY.Network.reachability t tr]
  exact preserves_sendMessage t tr h

theorem noBobBefore3_runSteps_invisible {ss : List Step} {tr : ExecTrace}
    (hInv : ∀ x ∈ ss, x.cls = .invisible) (h : NoBobBefore3 tr) :
    NoBobBefore3 (runSteps ss tr) := by
  induction ss generalizing tr with
  | nil => exact h
  | cons s ss ih =>
    exact ih (fun x hx => hInv x (List.mem_cons_of_mem s hx))
      (noBobBefore3_step_invisible (hInv s List.mem_cons_self) h)

theorem noBobBefore3_setupTrace (r : ProtocolSetup) : NoBobBefore3 (setupTrace r) := by
  unfold setupTrace DY.Libsignal.Composed.Refinement.setupAct
  refine (CompTrace.Preserves.bind (preserves_registerIdentity _) fun _ => ?_) Trace.nil noBobBefore3_nil
  refine CompTrace.Preserves.bind (preserves_registerIdentity _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genSignedPrekey _ _) fun _ => ?_
  refine CompTrace.Preserves.bind (preserves_genPQPrekey _ _) fun _ => ?_
  split
  · exact CompTrace.Preserves.bind (preserves_genOneTimePrekey _) fun _ => CompTrace.Preserves.pure _
  · exact CompTrace.Preserves.pure _

theorem noBobBefore3_alice_step {s : Step} {tr : ExecTrace}
    (hstep : (∃ idStateIdx regIdxB h, s = .aliceStart "alice" "bob" idStateIdx regIdxB h) ∨
             (∃ stateIdx coinsLen pqIdx, s = .messageEncrypt "alice" stateIdx coinsLen pqIdx) ∨
             (∃ stateIdx, s = .messageEncryptAbort "alice" stateIdx))
    (h : NoBobBefore3 tr) : NoBobBefore3 (s.next tr) := by
  rcases hstep with ⟨i, j, bh, rfl⟩ | ⟨st, cl, pq, rfl⟩ | ⟨st, rfl⟩
  · rw [show (Step.aliceStart "alice" "bob" i j bh).next tr =
      ((aliceStart "alice" "bob" i j bh).run tr).2.val from
      stepIn_next aliceStart.reachability ("alice", "bob", i, j, bh) tr]
    exact preserves_aliceStart i j bh tr h
  · rw [show (Step.messageEncrypt "alice" st cl pq).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt "alice" st cl pq).run tr).2.val from
      stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability ("alice", st, cl, pq) tr]
    exact preserves_messageEncrypt_alice st cl pq tr h
  · rw [show (Step.messageEncryptAbort "alice" st).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncryptAbort "alice" st).run tr).2.val from
      stepIn_next DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability ("alice", st) tr]
    exact preserves_messageEncryptAbort_alice st tr h

theorem getMessageSentAt_eq_of_at? {tr : ExecTrace} {idx : Nat} {msg : DY.Bytes}
    (h : (tr.at? idx : Option CompTrace.NetEntry) = some ⟨msg⟩) :
    tr.getMessageSentAt idx = some msg := by
  simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, h]

theorem receiveMessage_some {idx : Nat} {tr : ExecTrace} {msg : DY.Bytes}
    (h : ((DY.Network.receiveMessage idx).run tr).1 = some msg) :
    (tr.at? idx : Option CompTrace.NetEntry) = some ⟨msg⟩ := by
  rw [CompTrace.receiveMessage_fst] at h
  cases he : (tr.at? idx : Option CompTrace.NetEntry) with
  | none => rw [he] at h; cases h
  | some e =>
    rcases e with ⟨m⟩
    rw [he] at h; injection h with h; subst h; rfl

theorem receiveSignalMsg_some {idx : Nat} {tr : ExecTrace}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (h : ((DY.Libsignal.TripleRatchet.receiveSignalMsg idx).run tr).1 = some msg) :
    ∃ raw, (tr.at? idx : Option CompTrace.NetEntry) = some ⟨raw⟩ ∧
      DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg ∧
      ((DY.Libsignal.TripleRatchet.receiveSignalMsg idx).run tr).2.val = tr := by
  have htr : ((DY.Libsignal.TripleRatchet.receiveSignalMsg idx).run tr).2.val = tr :=
    CompTrace.Preserves.receiveSignalMsg (Inv := fun t => t = tr) idx tr rfl
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg at h
  obtain ⟨raw, hraw, h2, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨msg, h⟩)
  rw [CompTrace.receiveMessage_snd] at h2
  have hat := receiveMessage_some hraw
  rcases hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw with _ | pm
  · rw [hp, Traceful.run_failure] at h2; cases h2
  · rw [CompTrace.run_bind_fst, hraw, CompTrace.receiveMessage_snd] at h
    dsimp only at h
    rw [hp] at h
    unfold _root_.guard at h
    by_cases hver : pm.version = DY.Libsignal.TripleRatchet.messageVersion
    · simp only [hver, ↓reduceIte, CompTrace.run_bind_fst, Traceful.run_pure] at h
      injection h with h; subst h
      exact ⟨raw, hat, hp, htr⟩
    · simp only [hver, ↓reduceIte, CompTrace.run_bind_fst, Traceful.run_failure] at h
      cases h

theorem getLocalState_tr_some {me : Participant} {idx : Nat} {tr : ExecTrace}
    {st : DY.Libsignal.TripleRatchet.TRState}
    (h : ((DY.PersistentLocalState.getLocalState me idx :
      Traceful DY.Libsignal.TripleRatchet.TRState).run tr).1 = some st) :
    CompTrace.TRStateStoredAt me st idx tr := by
  rw [CompTrace.getLocalState_tr_fst] at h
  rcases he : (tr.at? idx : Option CompTrace.TRStEntry) with _ | ⟨⟨p, st'⟩⟩
  · rw [he] at h; cases h
  · rw [he] at h; dsimp only at h
    split at h
    · next hp => subst hp; injection h with h; subst h; exact he
    · cases h

theorem getEntry_trEv_some {idx : Nat} {tr : ExecTrace}
    {e : DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent}
    (h : ((DY.getEntry idx :
      Traceful (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)).run tr).1 = some e) :
    tr.EventLoggedAt e.ev idx ∧
    ((DY.getEntry idx :
      Traceful (DY.ProtocolEvent.ExecEntryT DY.Libsignal.TripleRatchet.TREvent)).run tr).2.val = tr := by
  simp only [Symbolic.DYBridge.DY.getEntry_eq_1] at h ⊢
  rw [Traceful.run_mk] at h ⊢
  dsimp only at h ⊢
  refine ⟨?_, rfl⟩
  rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
  rcases e with ⟨ev⟩
  exact h

theorem guard_some {p : Prop} [Decidable p] {tr : ExecTrace}
    (h : ((_root_.guard p : Traceful Unit).run tr).1.isSome = true) :
    p ∧ ((_root_.guard p : Traceful Unit).run tr).2.val = tr := by
  unfold _root_.guard at h ⊢
  split at h
  · next hp => rw [ite_eq_left_iff.mpr fun hc => absurd hp hc, Traceful.run_pure]; exact ⟨hp, rfl⟩
  · rw [Traceful.run_failure] at h; cases h

theorem guardTrace_tr_some {p : ExecTrace → Bool} {tr : ExecTrace}
    (h : ((DY.Libsignal.TripleRatchet.guardTrace p).run tr).1.isSome = true) :
    p tr = true ∧ ((DY.Libsignal.TripleRatchet.guardTrace p).run tr).2.val = tr := by
  unfold DY.Libsignal.TripleRatchet.guardTrace at h ⊢
  rw [Traceful.run_mk] at h ⊢
  dsimp only at h ⊢
  split at h
  · next hp => exact ⟨hp, rfl⟩
  · cases h

theorem verifyMacAndDecrypt_some_mac {st : DY.Libsignal.TripleRatchet.TRState}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {pqSalt seed : DY.Bytes} {tr : ExecTrace}
    (h : ((DY.Libsignal.TripleRatchet.verifyMacAndDecrypt st msg pqSalt seed).run tr).1.isSome = true) :
    msg.mac = DY.Libsignal.TripleRatchet.computeMac
      (DY.Libsignal.TripleRatchet.trMsgKeys pqSalt seed).macKey st.peerIk st.myIk msg.wire := by
  unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at h
  obtain ⟨_, hg, _, _⟩ := run_bind_isSome h
  exact (guard_some (Option.isSome_iff_exists.mpr ⟨_, hg⟩)).1

structure BobStateShape (stB : DY.Libsignal.TripleRatchet.TRState) : Prop where
  hasChain : ∃ c', stB.recv = [c'] ∧ c'.index = 2
  hasRk : ∃ u v, stB.rk = DY.Libsignal.TripleRatchet.hkdfBlock1
    (DY.Libsignal.TripleRatchet.hmac u v) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet")

theorem not_decryptInMemory_c1
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {stB : DY.Libsignal.TripleRatchet.TRState} (hShape : BobStateShape stB)
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hcnt : msg.counter = 0)
    (hmac : gamma compI0 S g msg.mac = msgMac8' p_c1)
    {pqIdx : Nat} {spqrMsgIdx : UInt32} {tr : ExecTrace}
    (hok : ((DY.Libsignal.TripleRatchet.decryptInMemory stB msg pqIdx spqrMsgIdx).run tr).1.isSome = true) :
    False := by
  obtain ⟨c', hrecv, hcIdx⟩ := hShape.hasChain
  obtain ⟨u, v, hrk⟩ := hShape.hasRk
  unfold DY.Libsignal.TripleRatchet.decryptInMemory at hok
  obtain ⟨⟨st1, c, ratcheted⟩, hens, hrest1, _⟩ := run_bind_isSome hok
  unfold DY.Libsignal.TripleRatchet.ensureReceiverChain at hens
  rcases hfind : DY.Libsignal.TripleRatchet.findRecvChain stB.recv msg.ratchetKey with _ | c_found
  · rw [hfind] at hens
    obtain ⟨⟨st1', c_new⟩, hdhr, _, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨_, hens⟩)
    rw [CompTrace.run_bind_fst, hdhr] at hens
    dsimp only at hens
    rw [Traceful.run_pure] at hens
    injection hens with hens
    cases hens
    unfold DY.Libsignal.TripleRatchet.dhRatchetStep at hdhr
    rcases hrhs : DY.Libsignal.TripleRatchet.recvHalfStep stB.toDRState msg.ratchetKey with _ | ⟨rk1, cr⟩
    · rw [hrhs, Traceful.run_failure] at hdhr; cases hdhr
    · rw [hrhs] at hdhr
      obtain ⟨dhs, hdhs, _, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨_, hdhr⟩)
      rw [CompTrace.run_bind_fst, hdhs] at hdhr
      dsimp only at hdhr
      rw [Traceful.run_pure] at hdhr
      injection hdhr with hdhr
      cases hdhr
      unfold DY.Libsignal.TripleRatchet.recvHalfStep at hrhs
      split at hrhs
      · cases hrhs
      · injection hrhs with hrhs
        have hcr : c =
            ({ ratchetKey := msg.ratchetKey
               chainKey := (DY.Libsignal.TripleRatchet.createChain stB.rk msg.ratchetKey stB.dhs).2
               index := 0
               rIdx := stB.rIdx + 2 } : DY.Libsignal.TripleRatchet.RecvChain) :=
          (Prod.mk.inj hrhs).2.symm
        have hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c msg.counter =
            some ((DY.Libsignal.TripleRatchet.kdfCk c.chainKey).2,
              { c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk c.chainKey).1, index := 1 }) := by
          rw [hcnt, hcr]; rfl
        dsimp only at hrest1
        rw [hcons] at hrest1
        dsimp only at hrest1
        rcases hspqr : DY.Spqr.spqrRecv stB.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · simp [hspqr, Traceful.run_failure] at hrest1
        · rw [hspqr] at hrest1
          dsimp only at hrest1
          obtain ⟨_, _, hrest2, _⟩ := run_bind_isSome hrest1
          obtain ⟨pqSalt, _, hrest3, _⟩ := run_bind_isSome hrest2
          obtain ⟨pt, hvm, _, _⟩ := run_bind_isSome hrest3
          have hmacEq := verifyMacAndDecrypt_some_mac (Option.isSome_iff_exists.mpr ⟨pt, hvm⟩)
          have hmacGamma := congrArg (gamma compI0 S g) hmacEq
          rw [hmac, hcr] at hmacGamma
          dsimp only [DY.Libsignal.TripleRatchet.createChain, DY.Libsignal.TripleRatchet.kdfRk] at hmacGamma
          have hrkLen : (gamma compI0 S g stB.rk).length = 32 := by
            rw [hrk]; exact gamma_hmac_length S g _ _
          have hrk0 := c1_ratchet_mac_forces_rk0Bytes hmacGamma.symm hrkLen
          rw [hrk] at hrk0
          exact not_hkdfBlock1_whisperRatchet_eq_rk0Bytes u v hrk0
  · rw [hfind, Traceful.run_pure] at hens
    injection hens with hens
    cases hens
    rw [hrecv] at hfind
    unfold DY.Libsignal.TripleRatchet.findRecvChain at hfind
    simp only [List.find?_cons, List.find?_nil] at hfind
    split at hfind
    · injection hfind with hcf; subst hcf
      have hcons : DY.Libsignal.TripleRatchet.consumeMessageKey c' msg.counter = none := by
        unfold DY.Libsignal.TripleRatchet.consumeMessageKey
        rw [hcnt, hcIdx]; rfl
      dsimp only at hrest1
      rw [hcons, Traceful.run_failure] at hrest1
      cases hrest1
    · cases hfind

theorem msg_c1_of_decVis_runMatches
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {s : Step} {ev : RunEvent} {v : List VisEntry}
    {initIds : Option BundlePreKeyIds} {stateIdx msgIdx : Nat} {raw : DY.Bytes}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hRun : RunMatches compI0 r S g tr s ev v initIds)
    (heqEv : ev.input = ev4.input)
    (hWrap : runWrapped ev = true)
    (hView : stepView s tr true = decVis tr (s.next tr) stateIdx msgIdx true ++ exposures tr (s.next tr))
    (hat : (tr.at? msgIdx : Option CompTrace.NetEntry) = some ⟨raw⟩)
    (hp : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg) :
    msg.counter = 0 ∧ gamma compI0 S g msg.mac = msgMac8' p_c1 := by
  rcases hRun with ⟨_, _, _, _, _, _, hvEq, inp, drs, outs, hvCons, _, _, _, hRead, _⟩
  rw [hWrap, hView] at hvEq
  unfold decVis at hvEq
  rw [getMessageSentAt_eq_of_at? hat] at hvEq
  dsimp only [Option.map, Option.toList, List.cons_append] at hvEq
  rw [hvCons] at hvEq
  injection hvEq with hinp _
  subst hinp
  unfold ReadsFaithfully at hRead
  have hpWire : parsePreKeyWire ev.input = some p_c1 := by rw [heqEv]; exact parsePreKeyWire_ev4
  have hRep := hRead p_c1 hpWire
  rcases hRep with ⟨_, _, _, hFields⟩
  obtain ⟨_, hmac, _, hDecF⟩ := hFields msg hp
  obtain ⟨m, htry, hm0⟩ := p_c1_message_tryFrom_counter_zero
  have hDec := hDecF m htry
  have hcntNat : msg.counter.toNat = 0 := by rw [hDec.2.2.2.1, hm0]; rfl
  have hcnt : msg.counter = 0 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hcntNat)
  exact ⟨hcnt, hmac⟩

theorem bobHandshake_trace {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles}
    {regIdxA ekIdx ctIdx : Nat} {tr : ExecTrace} :
    ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).2.val = tr := by
  have h := CompTrace.bind_bobHandshake_at (Inv := fun t => t = tr) b a kh regIdxA ekIdx ctIdx
    (f := Pure.pure) tr rfl
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by rw [Traceful.run_pure])
  rw [CompTrace.run_bind_snd] at h
  rcases hfst : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).1 with _ | o
  · rw [hfst] at h; exact h
  · rw [hfst] at h; dsimp only at h; rw [Traceful.run_pure] at h; exact h

theorem bobHandshake_ek_at? {b a : Participant} {kh : DY.Libsignal.PQXDH.BobKeyHandles}
    {regIdxA ekIdx ctIdx : Nat} {tr : ExecTrace} {o : DY.Libsignal.PQXDH.BobHandshakeOut}
    (h : ((DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx).run tr).1 = some o) :
    (tr.at? ekIdx : Option CompTrace.NetEntry) = some ⟨o.ek⟩ ∧
    (tr.at? ctIdx : Option CompTrace.NetEntry) = some ⟨o.ct⟩ := by
  let Inv : ExecTrace → Prop := fun t =>
    t = tr ∨ ∃ ek ct, t = tr.append (CompTrace.NetE (DY.Concat.concat ek ct)) ∧
      (tr.at? ekIdx : Option CompTrace.NetEntry) = some ⟨ek⟩ ∧
      (tr.at? ctIdx : Option CompTrace.NetEntry) = some ⟨ct⟩
  have hInv := CompTrace.bind_bobHandshake_at (Inv := Inv) b a kh regIdxA ekIdx ctIdx
    (f := fun out => DY.Network.sendMessage (DY.Concat.concat out.ek out.ct)) tr (Or.inl rfl)
    (fun _ _ _ _ _ _ ek ct _ _ _ _ _ _ _ hek hct _ _ => by
      rw [(sendMessage_run (DY.Concat.concat ek ct) tr).2]
      exact Or.inr ⟨ek, ct, rfl, hek, hct⟩)
  rw [CompTrace.run_bind_snd, h, bobHandshake_trace] at hInv
  dsimp only at hInv
  rw [(sendMessage_run _ tr).2] at hInv
  rcases hInv with hlen | ⟨ek, ct, heq, hek, hct⟩
  · exfalso
    have hl := congrArg Trace.length hlen
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2] at hl
  · have hat : ((tr.append (CompTrace.NetE (DY.Concat.concat o.ek o.ct))).at? tr.length :
        Option CompTrace.NetEntry) = some ⟨DY.Concat.concat ek ct⟩ := by
      rw [heq]; exact CompTrace.at?_append_here tr _
    rw [CompTrace.at?_append_here] at hat
    injection hat with hat; injection hat with hat
    have hv := congrArg (fun x : DY.Bytes => x.view? DY.Concat.Concat.SubF) hat
    simp only [DY.Concat.concat, BytesView.view_pack, Option.some.injEq,
      DY.Concat.Concat.SubF.mk.injEq] at hv
    rw [hv.1, hv.2]
    exact ⟨hek, hct⟩

theorem mem_bobDoneBaseKeys_of_loggedAt {tr : ExecTrace}
    {b a : Participant} {ikB ikA spk pqpk : DY.Bytes} {opk : Option DY.Bytes}
    {ek ct : DY.Bytes} {keys : DY.Libsignal.PQXDH.HandshakeKeys} {i : Nat}
    (h : tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i) :
    ek ∈ bobDoneBaseKeys tr := by
  have hat : (tr.at? i : Option CompTrace.PQXDHEntry) =
      some ⟨DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys⟩ := by
    rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
  have hi : i < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.PQXDHEntry) tr i
    rw [hat] at this; exact this
  unfold bobDoneBaseKeys
  refine List.mem_filterMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

theorem skippedKeyUsedB_true_of_loggedAt {tr : ExecTrace}
    {s : DY.Libsignal.TripleRatchet.SessionInfo} {skIdx i : Nat}
    (h : tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s skIdx) i) :
    DY.Libsignal.TripleRatchet.skippedKeyUsedB tr skIdx = true := by
  have hat : (tr.at? i : Option CompTrace.TREntry) =
      some ⟨DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s skIdx⟩ := by
    rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at h
  have hi : i < tr.length := by
    have := Trace.at?_eq_some_implies_length_le (EntryT := CompTrace.TREntry) tr i
    rw [hat] at this; exact this
  unfold DY.Libsignal.TripleRatchet.skippedKeyUsedB DY.Libsignal.TripleRatchet.anyEventOnTrace
  refine List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat, beq_self_eq_true]

structure BobPost (S : OpaqueSymbolSemantics) (g : Ghost)
    (skIdx0 : Nat) (used : Bool) (tr : ExecTrace) : Prop where
  bobStates : ∀ idx st, CompTrace.TRStateStoredAt "bob" st idx tr → BobStateShape st
  onlySk0 : ∀ idx s pk n seed rIdx src,
    tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) idx →
      idx = skIdx0
  hasBobDone : ∃ b a ikB ikA spk pqpk opk ek ct keys i,
    tr.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i ∧
    ecKey (gamma compI0 S g ek) = p_c1.baseKey.take 33
  skUsed : used = true → ∃ s i,
    tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s skIdx0) i

theorem bobPost_append_net {S : OpaqueSymbolSemantics} {g : Ghost}
    {skIdx0 : Nat} {used : Bool} {tr : ExecTrace} (t : DY.Bytes)
    (h : BobPost S g skIdx0 used tr) : BobPost S g skIdx0 used (tr.append (CompTrace.NetE t)) where
  bobStates idx st hs := h.bobStates idx st (CompTrace.trStateStoredAt_append_other rfl hs)
  onlySk0 idx _ _ _ _ _ _ he := h.onlySk0 idx _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)
  hasBobDone :=
    let ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, hi, hek⟩ := h.hasBobDone
    ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i,
      CompTrace.eventLoggedAt_mono (Trace.append_le tr _) hi, hek⟩
  skUsed hu :=
    let ⟨s, i, hi⟩ := h.skUsed hu
    ⟨s, i, CompTrace.eventLoggedAt_mono (Trace.append_le tr _) hi⟩

theorem bobPost_runSteps_invisible {S : OpaqueSymbolSemantics} {g : Ghost}
    {skIdx0 : Nat} {used : Bool} {ss : List Step} {tr : ExecTrace}
    (hInv : ∀ x ∈ ss, x.cls = .invisible) (h : BobPost S g skIdx0 used tr) :
    BobPost S g skIdx0 used (runSteps ss tr) := by
  induction ss generalizing tr with
  | nil => exact h
  | cons s ss ih =>
    apply ih (fun x hx => hInv x (List.mem_cons_of_mem s hx))
    obtain ⟨t, rfl⟩ := invisible_step_eq_network (hInv s List.mem_cons_self)
    rw [show (Step.network t).next tr = ((DY.Network.sendMessage t).run tr).2.val from
      stepIn_next DY.Network.reachability t tr, (sendMessage_run t tr).2]
    exact bobPost_append_net t h

theorem bobStart_ev3_establishes_bobPost
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr3 : ExecTrace} {kh : DY.Libsignal.PQXDH.BobKeyHandles} {regIdxA : Nat}
    {mh : DY.Libsignal.PQXDH.PreKeyMsgHandles} {pqIdx3 : Nat} {spqrIdx3 : UInt32}
    {v3 : List VisEntry} {initIds3 : Option BundlePreKeyIds}
    (hNoBob : NoBobBefore3 tr3)
    (hRun : RunMatches compI0 r S g tr3
      (.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3) ev3 v3 initIds3) :
    ∃ skIdx0, BobPost S g skIdx0 false
      ((Step.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).next tr3) := by
  have hokStep := hRun.2.2.2.2.1
  have hok : ((bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).run tr3).1.isSome = true := by
    rwa [show (Step.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).ok tr3 =
      ((bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).run tr3).1.isSome from
      stepIn_ok bobStart.reachability ("bob", "alice", kh, regIdxA, mh, pqIdx3, spqrIdx3) tr3] at hokStep
  have hnext : (Step.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).next tr3 =
      ((bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).run tr3).2.val :=
    stepIn_next bobStart.reachability ("bob", "alice", kh, regIdxA, mh, pqIdx3, spqrIdx3) tr3
  unfold bobStart at hok hnext
  obtain ⟨o, ho, h1, htr1⟩ := run_bind_isSome hok
  rw [bobHandshake_trace] at h1 htr1
  obtain ⟨hekAt, hctAt⟩ := bobHandshake_ek_at? ho
  obtain ⟨msg3, hmsg3, h2, htr2⟩ := run_bind_isSome h1
  obtain ⟨raw3, hrawAt, hpMsg3, hmsgTr⟩ := receiveSignalMsg_some hmsg3
  rw [hmsgTr] at h2 htr2
  -- Extract `msg3.counter = 1` and `ecKey (gamma o.ek) = p_c1.baseKey.take 33` from `RunMatches`
  rcases hRun with ⟨_, _, _, _, hokS, _, hvEq, inp, drs, outs, hvCons, _, _, _, hRead, _⟩
  unfold stepView at hvEq
  simp only [hokS, ↓reduceIte] at hvEq
  unfold bobVis received at hvEq
  simp only [List.filterMap_cons, List.filterMap_nil,
    getMessageSentAt_eq_of_at? hekAt, getMessageSentAt_eq_of_at? hctAt,
    getMessageSentAt_eq_of_at? hrawAt, List.cons_append] at hvEq
  rw [hvCons] at hvEq
  injection hvEq with hinp _
  subst hinp
  unfold ReadsFaithfully at hRead
  rcases hRead with ⟨_, _, _, hPkr, p3, hp3, msg3', hpMsg3', hFaith3⟩
  rw [parsePreKeyWire_ev3] at hp3
  injection hp3 with hp3; subst hp3
  rw [hpMsg3] at hpMsg3'
  injection hpMsg3' with hpMsg3'; subst hpMsg3'
  have hcnt3Nat : msg3.counter.toNat = 1 := by
    rw [hFaith3.2.2.2.2.2.2.1, p_c2_counter_eq]; rfl
  have hcnt3 : msg3.counter = 1 := UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hcnt3Nat)
  rcases hPkr with ⟨p3', hp3', hbk3, _⟩
  rw [parsePreKeyWire_ev3] at hp3'
  injection hp3' with hp3'; subst hp3'
  have hekEq : ecKey (gamma compI0 S g o.ek) = p_c1.baseKey.take 33 := by
    rw [p_c1_baseKey_eq_p_c2_baseKey, hbk3]
  -- Unpack `decryptInMemory` on `st0 = initBobState ...`
  set st0 := DY.Libsignal.TripleRatchet.initBobState "alice"
    (DY.Libsignal.PQXDH.serializedIk o.ikB) (DY.Libsignal.PQXDH.serializedIk o.ikA)
    o.spkSk msg3.ratchetKey o.keys.rk o.keys.ck o.keys.pqr
  obtain ⟨pending, hpend, h3, htr3⟩ := run_bind_isSome h2
  set trDec := ((DY.Libsignal.TripleRatchet.decryptInMemory st0 msg3 pqIdx3 spqrIdx3).run tr3).2.val
  -- Show `NoBobBefore3 trDec` and extract `pending` fields
  unfold DY.Libsignal.TripleRatchet.decryptInMemory at hpend
  obtain ⟨⟨st1, c, ratcheted⟩, hens, hp1, ht_ens⟩ :=
    run_bind_isSome (Option.isSome_iff_exists.mpr ⟨pending, hpend⟩)
  have hfind0 : DY.Libsignal.TripleRatchet.findRecvChain st0.recv msg3.ratchetKey = none := rfl
  unfold DY.Libsignal.TripleRatchet.ensureReceiverChain at hens ht_ens
  rw [hfind0] at hens
  obtain ⟨⟨st1', c_new⟩, hdhr, _, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨_, hens⟩)
  rw [CompTrace.run_bind_fst, hdhr] at hens
  dsimp only at hens
  rw [Traceful.run_pure] at hens
  injection hens with hens; cases hens
  have ht_ens_eq : ((match DY.Libsignal.TripleRatchet.findRecvChain st0.recv msg3.ratchetKey with
      | some c => Pure.pure (st0, c, false)
      | none => do
        let p ← DY.Libsignal.TripleRatchet.dhRatchetStep st0 msg3.ratchetKey
        Pure.pure (p.1, p.2, true)).run tr3).2.val =
      ((DY.Libsignal.TripleRatchet.dhRatchetStep st0 msg3.ratchetKey).run tr3).2.val := by
    rw [hfind0, CompTrace.run_bind_snd, hdhr]; dsimp only; rw [Traceful.run_pure]
  unfold DY.Libsignal.TripleRatchet.dhRatchetStep at hdhr
  rcases hrhs : DY.Libsignal.TripleRatchet.recvHalfStep st0.toDRState msg3.ratchetKey with _ | ⟨rk1, cr⟩
  · rw [hrhs, Traceful.run_failure] at hdhr; cases hdhr
  rw [hrhs] at hdhr
  obtain ⟨dhs, hdhs, _, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨_, hdhr⟩)
  rw [CompTrace.run_bind_fst, hdhs] at hdhr
  dsimp only at hdhr
  rw [Traceful.run_pure] at hdhr
  injection hdhr with hdhr; cases hdhr
  have hdhr_tr : ((DY.Libsignal.TripleRatchet.dhRatchetStep st0 msg3.ratchetKey).run tr3).2.val =
      tr3.append (CompTrace.RndE 32) := by
    unfold DY.Libsignal.TripleRatchet.dhRatchetStep
    rw [hrhs, CompTrace.run_bind_snd, (genRand_run 32 tr3).1, (genRand_run 32 tr3).2]
    dsimp only; rw [Traceful.run_pure]
  have hrhsOrig := hrhs
  unfold DY.Libsignal.TripleRatchet.recvHalfStep at hrhs
  split at hrhs
  · cases hrhs
  injection hrhs with hrhs
  have hcr : c =
      ({ ratchetKey := msg3.ratchetKey
         chainKey := (DY.Libsignal.TripleRatchet.createChain st0.rk msg3.ratchetKey st0.dhs).2
         index := 0
         rIdx := st0.rIdx + 2 } : DY.Libsignal.TripleRatchet.RecvChain) :=
    (Prod.mk.inj hrhs).2.symm
  have hcons3 : DY.Libsignal.TripleRatchet.consumeMessageKey c msg3.counter =
      some ((DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey 1)).2,
        { c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk
            (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey 1)).1, index := 2 }) := by
    rw [hcnt3, hcr]; rfl
  set trEns := ((DY.Libsignal.TripleRatchet.ensureReceiverChain st0 msg3.ratchetKey).run tr3).2.val
  have htrEns : trEns = tr3.append (CompTrace.RndE 32) := ht_ens_eq.trans hdhr_tr
  dsimp only at hp1
  rw [hcons3] at hp1
  dsimp only at hp1
  rcases hspqr : DY.Spqr.spqrRecv st0.spqr msg3.pqRatchet spqrIdx3 with _ | ⟨spqr', key⟩
  · simp [hspqr, Traceful.run_failure] at hp1
  rw [hspqr] at hp1
  dsimp only at hp1
  -- Extract `pending` equality and `NoBobBefore3 trDec`
  have hNoBobDec : NoBobBefore3 trDec := by
    dsimp only [trDec]
    unfold DY.Libsignal.TripleRatchet.decryptInMemory
    refine (CompTrace.Preserves.bind ?_ fun p => ?_) tr3 hNoBob
    · intro t ht
      unfold DY.Libsignal.TripleRatchet.ensureReceiverChain
      split
      · exact CompTrace.Preserves.pure _ t ht
      · refine (CompTrace.Preserves.bind ?_ fun _ => CompTrace.Preserves.pure _) t ht
        unfold DY.Libsignal.TripleRatchet.dhRatchetStep
        split
        · exact CompTrace.Preserves.bind (preserves_genRand 32) (fun _ => CompTrace.Preserves.pure _)
        · exact CompTrace.Preserves.failure
    · rcases p with ⟨st_, c_, rat_⟩
      dsimp only
      split
      · split
        · refine CompTrace.Preserves.bind (preserves_sendMessage _) fun _ => ?_
          refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage _) fun _ => ?_
          exact CompTrace.Preserves.bind (CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _) fun _ =>
            CompTrace.Preserves.pure _
        · exact CompTrace.Preserves.failure
      · exact CompTrace.Preserves.failure
  -- Extract `pending` field values directly from `hpend`
  have hensSome : ((DY.Libsignal.TripleRatchet.ensureReceiverChain st0 msg3.ratchetKey).run tr3).1 =
      some ({ st0 with
              rk := (DY.Libsignal.TripleRatchet.createChain rk1 msg3.ratchetKey (CompTrace.mkRand tr3.length 32)).1,
              dhs := CompTrace.mkRand tr3.length 32,
              cks := (DY.Libsignal.TripleRatchet.createChain rk1 msg3.ratchetKey (CompTrace.mkRand tr3.length 32)).2,
              ns := 0, pn := 0, rIdx := st0.rIdx + 2,
              recv := DY.Libsignal.TripleRatchet.pushRecvChain st0.recv c }, c, true) := by
    unfold DY.Libsignal.TripleRatchet.ensureReceiverChain
    rw [hfind0, CompTrace.run_bind_fst]
    unfold DY.Libsignal.TripleRatchet.dhRatchetStep
    rw [hrhsOrig]
    dsimp only [st0, DY.Libsignal.TripleRatchet.initBobState]
    rw [CompTrace.run_bind_fst, (genRand_run 32 tr3).1, (genRand_run 32 tr3).2]
    dsimp only
    rw [Traceful.run_pure]
    dsimp only
    simp only [Traceful.run_pure, ↓reduceIte]
  rw [CompTrace.run_bind_fst, hensSome] at hpend
  dsimp only [st0] at hpend ⊢
  rw [hcons3] at hpend
  dsimp only at hpend
  rw [hspqr] at hpend
  dsimp only at hpend
  obtain ⟨_, hsendK, hp2, _⟩ := run_bind_isSome (Option.isSome_iff_exists.mpr ⟨pending, hpend⟩)
  obtain ⟨pqSalt, hpqS, hp3_vm, _⟩ := run_bind_isSome hp2
  obtain ⟨pt, hvm, _, _⟩ := run_bind_isSome hp3_vm
  rw [CompTrace.run_bind_fst, hsendK] at hpend
  dsimp only at hpend
  rw [CompTrace.run_bind_fst, hpqS] at hpend
  dsimp only at hpend
  rw [CompTrace.run_bind_fst, hvm] at hpend
  dsimp only at hpend
  rw [Traceful.run_pure] at hpend
  injection hpend with hpend
  -- Now trace after `decryptInMemory` in `bobStart`:
  -- 1) `match o.opk` join-point preserves `NoBobBefore3`
  have ⟨trOpk, hNoBobOpk, htr4⟩ :
      ∃ trOpk : ExecTrace, NoBobBefore3 trOpk ∧
        ((Step.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).next tr3) =
          ((do
              let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
              DY.ProtocolEvent.logEvent
                (DY.Libsignal.PQXDH.PQXDHEvent.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
              pending.logRatchet "bob"
              DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (pending.st.sessionInfo "bob") doneIdx)
              pending.commit "bob").run trOpk).2.val := by
    rw [hnext, htr1, htr2, htr3]
    cases hopk : o.opk with
    | none =>
      exact ⟨trDec, hNoBobDec, rfl⟩
    | some opk =>
      rw [hopk] at h3
      have h3' : ((do
          DY.Libsignal.TripleRatchet.guardTrace fun tr => !DY.Libsignal.PQXDH.opkUsedB tr "bob" opk
          let _ ← DY.ProtocolEvent.logEvent (DY.Libsignal.PQXDH.PQXDHEvent.OPKUsed "bob" opk)
          let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
          DY.ProtocolEvent.logEvent
            (DY.Libsignal.PQXDH.PQXDHEvent.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk (some opk) o.ek o.ct o.keys)
          pending.logRatchet "bob"
          DY.ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (pending.st.sessionInfo "bob") doneIdx)
          pending.commit "bob").run trDec).1.isSome = true := h3
      obtain ⟨_, hgO, _, htr3a⟩ := run_bind_isSome h3'
      have hgOTr := (guardTrace_tr_some (Option.isSome_iff_exists.mpr ⟨_, hgO⟩)).2
      rw [hgOTr] at htr3a
      conv_rhs at htr3a =>
        rw [CompTrace.run_bind_snd, (logEvent_pq_run _ trDec).1, (logEvent_pq_run _ trDec).2]
        dsimp only
      exact ⟨trDec.append (CompTrace.PQEvE (DY.Libsignal.PQXDH.PQXDHEvent.OPKUsed "bob" opk)),
        noBobBefore3_append_pqEv _ (fun _ _ _ _ _ _ _ _ _ _ hc => by cases hc) hNoBobDec,
        htr3a⟩
  subst hpend
  -- 2) `doneIdx ← traceLength` (trace stays `trOpk`)
  have htl : (DY.Libsignal.TripleRatchet.traceLength.run trOpk).1 = some trOpk.length ∧
      (DY.Libsignal.TripleRatchet.traceLength.run trOpk).2.val = trOpk := by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩
  rw [CompTrace.run_bind_snd, htl.1, htl.2] at htr4
  dsimp only at htr4
  -- 3) `logEvent (PQXDHEvent.BobDone ...)` at `trOpk.length`
  rw [CompTrace.run_bind_snd, (logEvent_pq_run _ trOpk).1, (logEvent_pq_run _ trOpk).2] at htr4
  dsimp only at htr4
  set trBD := trOpk.append (CompTrace.PQEvE
    (DY.Libsignal.PQXDH.PQXDHEvent.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))
  have hBDLogged : trBD.EventLoggedAt
      (DY.Libsignal.PQXDH.PQXDHEvent.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys)
      trOpk.length := CompTrace.eventLoggedAt_here trOpk _
  have hNoStBD : ∀ idx st, ¬ CompTrace.TRStateStoredAt "bob" st idx trBD :=
    fun i st hs => hNoBobOpk.1 i st (CompTrace.trStateStoredAt_append_other rfl hs)
  have hNoSkBD : ∀ idx s pk n seed rIdx src,
      ¬ trBD.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) idx :=
    fun i _ _ _ _ _ _ he => hNoBobOpk.2.1 i _ _ _ _ _ _ (CompTrace.eventLoggedAt_append_other rfl he)
  -- 4) `pending.logRatchet "bob"` (`ratcheted = true`, logs `DHRatchet` and `HonestDH`)
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.logRatchet at htr4
  simp only [↓reduceIte] at htr4
  rw [CompTrace.run_bind_assoc_snd] at htr4
  rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trBD).1, (logEvent_tr_run _ trBD).2] at htr4
  dsimp only at htr4
  set trR1 := trBD.append (CompTrace.TREvE _)
  rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trR1).1, (logEvent_tr_run _ trR1).2] at htr4
  dsimp only at htr4
  set trR2 := trR1.append (CompTrace.TREvE _)
  -- 5) `logEvent (ComposedEvent.HandshakeSession ...)`
  rw [CompTrace.run_bind_snd, (logEvent_c_run _ trR2).1, (logEvent_c_run _ trR2).2] at htr4
  dsimp only at htr4
  set trHS := trR2.append (CompTrace.CEvE _)
  -- 6) `pending.commit "bob"` (`parentStateIdx = none`, `skipped = 1 - 0 = 1`)
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.commit at htr4
  dsimp only at htr4
  have hskipEq : msg3.counter.toNat - c.index.toNat = 1 := by
    rw [hcnt3, hcr]; rfl
  rw [hskipEq] at htr4
  have htlHS : (DY.Libsignal.TripleRatchet.traceLength.run trHS).1 = some trHS.length ∧
      (DY.Libsignal.TripleRatchet.traceLength.run trHS).2.val = trHS := by
    unfold DY.Libsignal.TripleRatchet.traceLength; rw [Traceful.run_mk]; exact ⟨rfl, rfl⟩
  rw [CompTrace.run_bind_snd, htlHS.1, htlHS.2] at htr4
  dsimp only [DY.Libsignal.TripleRatchet.logSkippedKeys,
    DY.Libsignal.TripleRatchet.logMessageKeyAndStore] at htr4
  rw [CompTrace.run_bind_assoc_snd] at htr4
  rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trHS).1, (logEvent_tr_run _ trHS).2] at htr4
  dsimp only at htr4
  rw [CompTrace.run_pure_bind_snd] at htr4
  set trSk := trHS.append (CompTrace.TREvE _)
  rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trSk).1, (logEvent_tr_run _ trSk).2] at htr4
  dsimp only at htr4
  set trRcv := trSk.append (CompTrace.TREvE _)
  rw [CompTrace.run_bind_snd,
      (logEvent_tr_run _ trRcv).1, (logEvent_tr_run _ trRcv).2] at htr4
  dsimp only at htr4
  set trMk := trRcv.append (CompTrace.TREvE _)
  rw [(storeLocalState_tr_run "bob" _ trMk).2] at htr4
  set stB :=
    ({ peer := "alice"
       myIk := DY.Libsignal.PQXDH.serializedIk o.ikB
       peerIk := DY.Libsignal.PQXDH.serializedIk o.ikA
       rk := (DY.Libsignal.TripleRatchet.createChain rk1 msg3.ratchetKey (CompTrace.mkRand tr3.length 32)).1
       dhs := CompTrace.mkRand tr3.length 32
       cks := (DY.Libsignal.TripleRatchet.createChain rk1 msg3.ratchetKey (CompTrace.mkRand tr3.length 32)).2
       ns := 0
       pn := 0
       sid := DY.Concat.concat (DY.X25519.normalizeX25519Key msg3.ratchetKey) o.keys.rk
       initiator := false
       rIdx := 2
       recv := DY.Libsignal.TripleRatchet.setRecvChain
         (DY.Libsignal.TripleRatchet.pushRecvChain [] c)
         { c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk
             (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey 1)).1, index := 2 }
       spqr := spqr' } : DY.Libsignal.TripleRatchet.TRState)
  have hEnd : (Step.bobStart "bob" "alice" kh regIdxA mh pqIdx3 spqrIdx3).next tr3 =
      trMk.append (CompTrace.TRStE "bob" stB) := by
    rw [htr4]; rfl
  have hShapeB : BobStateShape stB := by
    refine ⟨⟨{ c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk
        (DY.Libsignal.TripleRatchet.chainKeyAt c.chainKey 1)).1, index := 2 }, ?_, rfl⟩,
      ⟨rk1, DY.Libsignal.PQXDH.agree msg3.ratchetKey (CompTrace.mkRand tr3.length 32), rfl⟩⟩
    simp [stB, DY.Libsignal.TripleRatchet.pushRecvChain, DY.Libsignal.TripleRatchet.maxReceiverChains,
      DY.Libsignal.TripleRatchet.setRecvChain]
  refine ⟨trHS.length, ?_⟩
  rw [hEnd]
  refine ⟨?_, ?_, ?_, fun hu => nomatch hu⟩
  · intro idx st hs
    rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, _, rfl⟩
    · exfalso
      have hs1 := CompTrace.trStateStoredAt_append_other rfl hs
      have hs2 := CompTrace.trStateStoredAt_append_other rfl hs1
      have hs3 := CompTrace.trStateStoredAt_append_other rfl hs2
      have hs4 := CompTrace.trStateStoredAt_append_other rfl hs3
      have hs5 := CompTrace.trStateStoredAt_append_other rfl hs4
      have hs6 := CompTrace.trStateStoredAt_append_other rfl hs5
      exact hNoStBD idx st hs6
    · exact hShapeB
  · intro idx s pk n seed rIdx src he
    have he1 := CompTrace.eventLoggedAt_append_other rfl he
    rcases CompTrace.eventLoggedAt_append_same he1 with ⟨_, he2⟩ | ⟨_, hEq⟩
    · rcases CompTrace.eventLoggedAt_append_same he2 with ⟨_, he3⟩ | ⟨_, hEq⟩
      · rcases CompTrace.eventLoggedAt_append_same he3 with ⟨_, he4⟩ | ⟨rfl, _⟩
        · exfalso
          have he5 := CompTrace.eventLoggedAt_append_other rfl he4
          rcases CompTrace.eventLoggedAt_append_same he5 with ⟨_, he6⟩ | ⟨_, hEq⟩
          · rcases CompTrace.eventLoggedAt_append_same he6 with ⟨_, he7⟩ | ⟨_, hEq⟩
            · exact hNoSkBD idx s pk n seed rIdx src he7
            · cases hEq
          · cases hEq
        · rfl
      · cases hEq
    · cases hEq
  · refine ⟨"bob", "alice", o.ikB, o.ikA, o.spk, o.pqpk, o.opk, o.ek, o.ct, o.keys, trOpk.length, ?_, hekEq⟩
    have hle : trBD ≤ trMk.append (CompTrace.TRStE "bob" stB) :=
      DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <| DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <|
      DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <| DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <|
      DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <| DY.Trace.le_trans _ _ _ (Trace.append_le _ _) <|
      Trace.append_le _ _
    exact CompTrace.eventLoggedAt_mono hle hBDLogged

theorem bobStep_c1_contradiction_or_advances
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {skIdx0 : Nat} {used : Bool} {tr : ExecTrace} {s : Step} {ev : RunEvent}
    {v : List VisEntry} {initIds : Option BundlePreKeyIds}
    (ha : r.alice = "alice")
    (hEvParty : ev.party = "bob")
    (hEvCmd : ev.cmd = ev3.cmd)
    (hEvInp : ev.input = ev4.input)
    (hWrap : runWrapped ev = true)
    (hPost : BobPost S g skIdx0 used tr)
    (hRun : RunMatches compI0 r S g tr s ev v initIds) :
    used = false ∧ BobPost S g skIdx0 true (s.next tr) := by
  have ⟨hCls, hParty, hCmd, hPeer, hokStep, _, _, _, _, _, _, _, _, _, _, hPath⟩ := hRun
  rw [hEvParty] at hParty
  rw [hEvCmd] at hCmd
  have hpWire : parsePreKeyWire ev.input = some p_c1 := by rw [hEvInp]; exact parsePreKeyWire_ev4
  rcases step_of_recv_bob ha hParty hCmd hPeer with
    ⟨kh, regIdxA, mh, pqIdx, spqrIdx, rfl⟩ |
    ⟨stIdx, msgIdx, pqIdx, spqrIdx, rfl⟩ |
    ⟨stIdx, msgIdx, skIdx, pqIdx, spqrIdx, rfl⟩
  · -- Case `.bobStart`: refuted by `PathFaithfulAt`.
    exfalso
    have hNotKnown := hPath p_c1 hpWire
    obtain ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, hi, hek⟩ := hPost.hasBobDone
    exact hNotKnown ⟨ek, mem_bobDoneBaseKeys_of_loggedAt hi, hek⟩
  · -- Case `.messageDecrypt`: refuted by `not_decryptInMemory_c1`.
    exfalso
    have hok : ((DY.Libsignal.TripleRatchet.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx).run tr).1.isSome = true := by
      rwa [show (Step.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx).ok tr =
        ((DY.Libsignal.TripleRatchet.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx).run tr).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecrypt.reachability
          ("bob", stIdx, msgIdx, pqIdx, spqrIdx) tr] at hokStep
    have hView : stepView (.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx) tr true =
        decVis tr ((Step.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx).next tr) stIdx msgIdx true ++
          exposures tr ((Step.messageDecrypt "bob" stIdx msgIdx pqIdx spqrIdx).next tr) := by
      unfold stepView; simp only [hokStep, ↓reduceIte]
    unfold DY.Libsignal.TripleRatchet.messageDecrypt at hok
    obtain ⟨st, hst, h1, _⟩ := run_bind_isSome hok
    rw [CompTrace.getLocalState_tr_snd] at h1
    have hShape := hPost.bobStates stIdx st (getLocalState_tr_some hst)
    obtain ⟨msg, hmsg, h2, _⟩ := run_bind_isSome h1
    obtain ⟨raw, hat, hp, hmsgTr⟩ := receiveSignalMsg_some hmsg
    rw [hmsgTr] at h2
    obtain ⟨pend, hdec, _, _⟩ := run_bind_isSome h2
    obtain ⟨hcnt, hmac⟩ := msg_c1_of_decVis_runMatches hRun hEvInp hWrap hView hat hp
    exact not_decryptInMemory_c1 hShape hcnt hmac (Option.isSome_iff_exists.mpr ⟨pend, hdec⟩)
  · -- Case `.messageDecryptSkipped`: forces `skIdx = skIdx0` and `used = false`, logs `SkippedKeyUsed`.
    have hok : ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
        "bob" stIdx msgIdx skIdx pqIdx spqrIdx).run tr).1.isSome = true := by
      rwa [show (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx pqIdx spqrIdx).ok tr =
        ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
          "bob" stIdx msgIdx skIdx pqIdx spqrIdx).run tr).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
          ("bob", stIdx, msgIdx, skIdx, pqIdx, spqrIdx) tr] at hokStep
    have hnext : (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx pqIdx spqrIdx).next tr =
        ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
          "bob" stIdx msgIdx skIdx pqIdx spqrIdx).run tr).2.val :=
      stepIn_next DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
        ("bob", stIdx, msgIdx, skIdx, pqIdx, spqrIdx) tr
    unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped at hok hnext
    obtain ⟨st, hst, h1, htr1⟩ := run_bind_isSome hok
    rw [CompTrace.getLocalState_tr_snd] at h1 htr1
    have hShape := hPost.bobStates stIdx st (getLocalState_tr_some hst)
    obtain ⟨msg, hmsg, h2, htr2⟩ := run_bind_isSome h1
    obtain ⟨_, _, _, hmsgTr⟩ := receiveSignalMsg_some hmsg
    rw [hmsgTr] at h2 htr2
    obtain ⟨e, he, h3, htr3⟩ := run_bind_isSome h2
    obtain ⟨heLog, heTr⟩ := getEntry_trEv_some he
    rw [heTr] at h3 htr3
    rcases hev : e.ev with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨s, pk, n, seed, rIdx, src⟩ | _
    all_goals try (rw [hev, Traceful.run_failure] at h3; cases h3)
    rw [hev] at heLog h3 htr3
    dsimp only at h3 htr3
    have hskEq : skIdx = skIdx0 := hPost.onlySk0 skIdx s pk n seed rIdx src heLog
    subst skIdx
    obtain ⟨_, hg1, h4, htr4⟩ := run_bind_isSome h3
    rw [(guard_some (Option.isSome_iff_exists.mpr ⟨_, hg1⟩)).2] at h4 htr4
    obtain ⟨_, hg2, h5, htr5⟩ := run_bind_isSome h4
    obtain ⟨hNotUsed, hg2Tr⟩ := guardTrace_tr_some (Option.isSome_iff_exists.mpr ⟨_, hg2⟩)
    rw [hg2Tr] at h5 htr5
    have hUsedFalse : used = false := by
      cases used with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨s', ui, hui⟩ := hPost.skUsed rfl
        have hTrue := skippedKeyUsedB_true_of_loggedAt hui
        rw [hTrue] at hNotUsed; cases hNotUsed
    rcases hspqr : DY.Spqr.spqrRecv st.spqr msg.pqRatchet spqrIdx with _ | ⟨spqr', key⟩
    · simp [hspqr, Traceful.run_failure] at h5
    rw [hspqr] at h5
    dsimp only at h5
    obtain ⟨_, hsend, h6, htr6⟩ := run_bind_isSome h5
    rw [(sendMessage_run key tr).2] at h6 htr6
    set trN : ExecTrace := tr.append (CompTrace.NetE key)
    obtain ⟨pqSalt, hpq, h7, htr7⟩ := run_bind_isSome h6
    rw [CompTrace.receiveMessage_snd] at h7 htr7
    obtain ⟨m, hvm, _, htr8⟩ := run_bind_isSome h7
    rw [CompTrace.verifyMacAndDecrypt_trace] at htr8
    set trU : ExecTrace := trN.append (CompTrace.TREvE (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s skIdx0))
    have hULogged : trU.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s skIdx0) trN.length :=
      CompTrace.eventLoggedAt_here trN _
    set trR : ExecTrace := trU.append (CompTrace.TREvE (DY.Libsignal.TripleRatchet.TREvent.Received "bob" st.peer pk n m))
    set trM : ExecTrace := trR.append (CompTrace.TREvE
      (DY.Libsignal.TripleRatchet.TREvent.MessageKey s DY.Libsignal.TripleRatchet.KeyDir.receiver seed pqSalt n rIdx stIdx))
    conv_rhs at htr8 =>
      dsimp only [DY.Libsignal.TripleRatchet.logMessageKeyAndStore]
      rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trN).1, (logEvent_tr_run _ trN).2]
      dsimp only
      rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trU).1, (logEvent_tr_run _ trU).2]
      dsimp only
      rw [CompTrace.run_bind_snd, (logEvent_tr_run _ trR).1, (logEvent_tr_run _ trR).2]
      dsimp only
      rw [(storeLocalState_tr_run "bob" _ trM).2]
    have hEnd : (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx0 pqIdx spqrIdx).next tr =
        trM.append (CompTrace.TRStE "bob" { st with spqr := spqr' }) := by
      rw [hnext, htr1, htr2, htr3, htr4, htr5, hspqr]
      dsimp only
      rw [htr6, htr7, htr8]
    refine ⟨hUsedFalse, ?_⟩
    rw [hEnd]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro idx st' hs
      rcases CompTrace.trStateStoredAt_append_same hs with ⟨_, hs⟩ | ⟨_, _, rfl⟩
      · have hs1 := CompTrace.trStateStoredAt_append_other rfl hs
        have hs2 := CompTrace.trStateStoredAt_append_other rfl hs1
        have hs3 := CompTrace.trStateStoredAt_append_other rfl hs2
        have hs4 := CompTrace.trStateStoredAt_append_other rfl hs3
        exact hPost.bobStates idx st' hs4
      · exact ⟨hShape.hasChain, hShape.hasRk⟩
    · intro idx s' pk' n' seed' rIdx' src' he'
      have he1 := CompTrace.eventLoggedAt_append_other rfl he'
      rcases CompTrace.eventLoggedAt_append_same he1 with ⟨_, he2⟩ | ⟨_, hEq⟩
      · rcases CompTrace.eventLoggedAt_append_same he2 with ⟨_, he3⟩ | ⟨_, hEq⟩
        · rcases CompTrace.eventLoggedAt_append_same he3 with ⟨_, he4⟩ | ⟨_, hEq⟩
          · exact hPost.onlySk0 idx s' pk' n' seed' rIdx' src'
              (CompTrace.eventLoggedAt_append_other rfl he4)
          · cases hEq
        · cases hEq
      · cases hEq
    · obtain ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, hi, hek⟩ := hPost.hasBobDone
      have hle : tr ≤ (trM.append (CompTrace.TRStE "bob" { st with spqr := spqr' }) : ExecTrace) :=
        DY.Trace.le_trans _ _ _ (Trace.append_le tr _) <| DY.Trace.le_trans _ _ _ (Trace.append_le trN _) <|
        DY.Trace.le_trans _ _ _ (Trace.append_le trU _) <| DY.Trace.le_trans _ _ _ (Trace.append_le trR _) <|
        Trace.append_le trM _
      exact ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, CompTrace.eventLoggedAt_mono hle hi, hek⟩
    · intro _
      have hle : trU ≤ (trM.append (CompTrace.TRStE "bob" { st with spqr := spqr' }) : ExecTrace) :=
        DY.Trace.le_trans _ _ _ (Trace.append_le trU _) <| DY.Trace.le_trans _ _ _ (Trace.append_le trR _) <|
        Trace.append_le trM _
      exact ⟨s, trN.length, CompTrace.eventLoggedAt_mono hle hULogged⟩

theorem not_explains_trace {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) :
    ∀ S g ss vis, ¬ Explains compI0 r S g ss vis trace := by
  intro S g ss vis hExp
  have ha : r.alice = "alice" := hf.1.2.2.2.1.1
  have hb : r.bob = "bob" := hf.1.2.2.2.1.2
  rcases hExp with ⟨_, _, _, hM⟩
  rw [trace_eq] at hM
  -- Step 0 (`ev0`: `alice init`)
  obtain ⟨pre0, s0, ss1, v0, vs1, _, _, hInv0, hRun0, hM1⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hM
  have hNoBob0 := noBobBefore3_runSteps_invisible hInv0 (noBobBefore3_setupTrace r)
  have hs0 := step_of_init_alice hb hRun0.2.1 (fun _ _ h => h ▸ hRun0.2.2.1) hRun0.2.2.2.1
  have hNoBob0' := noBobBefore3_alice_step (.inl hs0) hNoBob0
  -- Step 1 (`ev1`: `alice send "first"`)
  obtain ⟨pre1, s1, ss2, v1, vs2, _, _, hInv1, hRun1, hM2⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM1
  have hNoBob1 := noBobBefore3_runSteps_invisible hInv1 hNoBob0'
  have hs1 := step_of_send_alice hRun1.2.1 hRun1.2.2.1
  have hNoBob1' := noBobBefore3_alice_step (.inr hs1) hNoBob1
  -- Step 2 (`ev2`: `alice send "second"`)
  obtain ⟨pre2, s2, ss3, v2, vs3, _, _, hInv2, hRun2, hM3⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hM2
  have hNoBob2 := noBobBefore3_runSteps_invisible hInv2 hNoBob1'
  have hs2 := step_of_send_alice hRun2.2.1 hRun2.2.2.1
  have hNoBob2' := noBobBefore3_alice_step (.inr hs2) hNoBob2
  -- Step 3 (`ev3`: `bob recv c2`)
  obtain ⟨pre3, s3, ss4, v3, vs4, _, _, hInv3, hRun3, hM4⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev3 hM3
  set tr3 := runSteps pre3 (s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r)))))))
  have hNoBob3 : NoBobBefore3 tr3 := noBobBefore3_runSteps_invisible hInv3 hNoBob2'
  have hs3Cases := step_of_recv_bob ha hRun3.2.1 hRun3.2.2.1 hRun3.2.2.2.1
  have hPost3' : ∃ skIdx0, BobPost S g skIdx0 false (s3.next tr3) := by
    rcases hs3Cases with ⟨kh, regIdxA, mh, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3, rfl⟩
    · exact bobStart_ev3_establishes_bobPost hNoBob3 hRun3
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecrypt.reachability
          ("bob", stIdx, msgIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecrypt at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
          "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
          ("bob", stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
  obtain ⟨skIdx0, hPost3⟩ := hPost3'
  -- Step 4 (`ev4`: `bob recv c1`, first delivery; consumes `skIdx0`)
  obtain ⟨pre4, s4, ss5, v4, vs5, _, _, hInv4, hRun4, hM5⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev4 hM4
  have hPost4 := bobPost_runSteps_invisible hInv4 hPost3
  have ⟨_, hPost4'⟩ :=
    bobStep_c1_contradiction_or_advances (ev := ev4) ha rfl rfl rfl runWrapped_ev4 hPost4 hRun4
  -- Step 5 (`ev5`: `bob recv c1`, replay; contradicts `used = true`)
  obtain ⟨pre5, s5, _, v5, _, _, _, hInv5, hRun5, _⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev5 hM5
  have hPost5 := bobPost_runSteps_invisible hInv5 hPost4'
  have ⟨hTrueEqFalse, _⟩ :=
    bobStep_c1_contradiction_or_advances (ev := ev5) ha rfl rfl ev4_input_eq_ev5_input.symm runWrapped_ev5 hPost5 hRun5
  cases hTrueEqFalse


end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
