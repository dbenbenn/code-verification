/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.AuxA
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-! # `NoSkippedKeyStored`, `ActivePartySt`, & Step-View Helpers (`Calls0to4PrefixAux.lean`) -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes Participant Trace Traceful ExecTrace ExecTraceTypes TraceEntryHas)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.HwEvents (RunEvent)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind AliceHandshakeOut)
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg TREvent RecvChain findRecvChain
  consumeMessageKey computeMac trMsgKeys messageVersion x25519LowOrder isCurrentSnapshot
  receiveSignalMsg verifyMacAndDecrypt ensureReceiverChain messageDecrypt messageDecryptSkipped)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
  BundlePreKeyIds gamma clamp randTerm rngEntry setupTrace runSteps lastSent newIndices newRandoms
  pendingPreKey encDraws encSendEntry pqExposureAt trExposureAt exposures stepView
  GhostAndSemMatchSetup OutputsMatch)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves TRStEntry RndE NetE TRStE PQStE PQEvE CEvE TREvE
  at?_append_cases proj_inj_eq at?_le_some run_bind_fst receiveMessage_snd)
open Symbolic.Swarm.CREF (bks_stored_of_getLocalState bks_lt_length_of_at?
  isCurrentSnapshot_false_of_later rpkT_receiveMessage_fst rpkT_at?_of_getMessageSentAt
  rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some rpkT_verifyMacAndDecrypt_some
  bobRatchetedChain bobStartPreSkipTr bobStartTr)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.Swarm.CREF.TR.RecvDec (getLocalState_snd receiveSignalMsg_run
  ensureReceiverChain_run_ratchet trDhRatchetState decRatchetPreTr decTailTr logSkippedKeysTr
  getEventAt_append_non_entry getEventAt_eq_none_of_le)
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (traceStatesP_setupTrace traceStatesP_at?_st)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSt encMsg StT EvT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (pqskB t1 t2 t3 t4)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice (iniAliceStartTr)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprI0 rcprHooks0 rcprCompFitsPinned rcprPubOfIdx rcprSecretIdx)

attribute [local irreducible] ev

/-! ## 3. `NoSkippedKeyStored` and Preservation Across Honest Prefix Steps -/

/-- No `TREvent.SkippedKeyStored` entry exists anywhere on `tr`. -/
def NoSkippedKeyStored (tr : ExecTrace) : Prop :=
  ∀ idx s pk n seed rIdx src,
    tr.getEventAt TREvent idx ≠ some (.SkippedKeyStored s pk n seed rIdx src)

theorem noSkippedKeyStored_nil : NoSkippedKeyStored Trace.nil := by
  intro idx s pk n seed rIdx src
  rw [getEventAt_eq_none_of_le TREvent Trace.nil
    (by rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega)]
  rintro ⟨⟩

theorem noSkippedKeyStored_append_non_tr {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : NoSkippedKeyStored tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none) :
    NoSkippedKeyStored (tr.append e) := by
  intro idx s pk n seed rIdx src
  rw [getEventAt_append_non_entry TREvent tr e hnone idx]
  exact h idx s pk n seed rIdx src

theorem noSkippedKeyStored_append_trEv {tr : ExecTrace} (h : NoSkippedKeyStored tr)
    (ev : TREvent)
    (hnskip : ∀ s pk n seed rIdx src, ev ≠ .SkippedKeyStored s pk n seed rIdx src) :
    NoSkippedKeyStored (tr.append (TREvE ev)) := by
  intro idx s pk n seed rIdx src hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append (TREvE ev)).at? idx : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with
    _ | ⟨⟨ev'⟩⟩
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; dsimp only at hget
    injection hget with hget'
    subst hget'
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h idx s pk n seed rIdx src
        (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0])
    · simp only [TREvE, proj_inj_eq, Option.some.injEq] at hproj
      injection hproj with hev; exact hnskip s pk n seed rIdx src hev

theorem noSkippedKeyStored_t4 : NoSkippedKeyStored t4 := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t1_t2_t3_t4_eq
  rw [ht4]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr]
  iterate 6 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  rw [ht3]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr]
  iterate 6 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  rw [ht2]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
  iterate 5 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  rw [ht1]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
  iterate 5 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  exact noSkippedKeyStored_nil

theorem noSkippedKeyStored_runSteps_network :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      NoSkippedKeyStored tr → NoSkippedKeyStored (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : NoSkippedKeyStored ((Step.network m).next tr) := by
      rw [next_network]; exact noSkippedKeyStored_append_non_tr h (NetE m) rfl
    exact noSkippedKeyStored_runSteps_network pre
      (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem noSkippedKeyStored_iniAliceStartTr {tr : ExecTrace} {a b : Participant}
    {o : AliceHandshakeOut} (h : NoSkippedKeyStored tr) :
    NoSkippedKeyStored (iniAliceStartTr tr a b o) := by
  unfold iniAliceStartTr; dsimp only
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
  iterate 6 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  exact h

theorem noSkippedKeyStored_encTrGen {tr : ExecTrace} {me : Participant} {stH cl : Nat}
    {st : TRState} {pq : Bytes} (h : NoSkippedKeyStored tr) :
    NoSkippedKeyStored (encTrGen tr me stH cl st pq) := by
  unfold encTrGen; dsimp only
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
  refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
  iterate 3 refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  exact h

theorem noSkippedKeyStored_bobStartTr {tr : ExecTrace} {b a : Participant}
    {o : DY.Libsignal.PQXDH.BobHandshakeOut} {msg : TRSignalMsg} {c' : RecvChain}
    {spqr' key seed pqSalt m : Bytes}
    (h : NoSkippedKeyStored tr) (hcnt : msg.counter.toNat = 0) :
    NoSkippedKeyStored (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) := by
  have hpre : NoSkippedKeyStored (bobStartPreSkipTr tr b a o msg key) := by
    unfold bobStartPreSkipTr; dsimp only
    refine noSkippedKeyStored_append_non_tr ?_ _ rfl
    refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
    refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
    refine noSkippedKeyStored_append_non_tr ?_ _ rfl
    cases o.opk with
    | none =>
      exact noSkippedKeyStored_append_non_tr
        (noSkippedKeyStored_append_non_tr h _ rfl) _ rfl
    | some _ =>
      exact noSkippedKeyStored_append_non_tr
        (noSkippedKeyStored_append_non_tr
          (noSkippedKeyStored_append_non_tr h _ rfl) _ rfl) _ rfl
  unfold bobStartTr; dsimp only
  have hskip0 : msg.counter.toNat - (bobRatchetedChain o.keys msg.ratchetKey o.spkSk).index.toNat = 0 := by
    rw [hcnt]; rfl
  rw [hskip0]
  simp only [DY.Libsignal.TripleRatchet.logSkippedKeys, DY.Traceful.run_pure]
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
  refine noSkippedKeyStored_append_trEv hpre _ (by intros; rintro ⟨⟩)

theorem noSkippedKeyStored_decRatchet {tr : ExecTrace} {me : Participant} {stateIdx : Nat}
    {st1 : TRState} {c c' : RecvChain} {pk key seed pqSalt ptTerm spqr' : Bytes} {n : UInt32}
    (h : NoSkippedKeyStored tr) (hcnt : n.toNat - c.index.toNat = 0) :
    NoSkippedKeyStored
      (decTailTr (decRatchetPreTr tr me st1 pk key) me stateIdx st1 c c'
        pk seed pqSalt ptTerm spqr' n) := by
  have hpre : NoSkippedKeyStored (decRatchetPreTr tr me st1 pk key) := by
    unfold decRatchetPreTr
    refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
    refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
    exact noSkippedKeyStored_append_non_tr (noSkippedKeyStored_append_non_tr h _ rfl) _ rfl
  unfold decTailTr; dsimp only
  rw [hcnt]; dsimp only [logSkippedKeysTr]
  refine noSkippedKeyStored_append_non_tr ?_ _ rfl
  refine noSkippedKeyStored_append_trEv ?_ _ (by intros; rintro ⟨⟩)
  exact noSkippedKeyStored_append_trEv hpre _ (by intros; rintro ⟨⟩)

/-! ## 4. `NoPartyState`, `NoNewPartyState`, and `ActivePartySt` (over `Fin 7`) -/

def NoPartyState (party : Participant) (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noPartyState_setupTrace (party : Participant) (r : ProtocolSetup) :
    NoPartyState party (setupTrace r) := by
  intro i st hat
  exact traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r) hat

def NoNewPartyState (party : Participant) (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ j st, tr₀.length ≤ j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩

theorem noNewPartyState_refl (party : Participant) (tr : ExecTrace) :
    NoNewPartyState party tr tr := by
  refine ⟨DY.Trace.le_refl tr, fun j st hj hat => ?_⟩
  exact absurd (bks_lt_length_of_at? hat) (by omega)

theorem noNewPartyState_trans {party : Participant} {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewPartyState party tr₀ tr₁) (h12 : NoNewPartyState party tr₁ tr₂) :
    NoNewPartyState party tr₀ tr₂ := by
  refine ⟨DY.Trace.le_trans _ _ _ h01.1 h12.1, fun j st hj hat => ?_⟩
  by_cases hlt : j < tr₁.length
  · rw [at?_of_le_lt h12.1 hlt] at hat; exact h01.2 j st hj hat
  · exact h12.2 j st (Nat.le_of_not_lt hlt) hat

theorem noPartyState_of_noNew {party : Participant} {tr tr' : ExecTrace}
    (hnew : NoNewPartyState party tr tr') (h0 : NoPartyState party tr) :
    NoPartyState party tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat; exact h0 i st hat
  · exact hnew.2 i st (Nat.le_of_not_lt hlt) hat

private theorem noNewPartyState_append_other {E : Type} [ExecTraceTypes.Has E]
    {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    NoNewPartyState party tr₀ (tr.append e) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr e, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · rw [hnone] at hproj; cases hproj

private theorem noNewPartyState_append_trSt_ne {party : Participant} {tr₀ tr : ExecTrace}
    (h : NoNewPartyState party tr₀ tr) (p : Participant) (hp : p ≠ party) (st₀ : TRState) :
    NoNewPartyState party tr₀ (tr.append (TRStE p st₀)) := by
  refine noNewPartyState_trans h ⟨DY.Trace.append_le tr _, fun j st hj hat => ?_⟩
  rcases at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · simp only [TRStE, proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1; injection h1 with hp_eq _; exact hp hp_eq

private theorem preserves_np_genRand {party : Participant} {tr₀ : ExecTrace} (n : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Symbolic.Swarm.CREF.TR.Runs.genRand tr n).2.symm ▸
    noNewPartyState_append_other hInv (RndE n) rfl

private theorem preserves_np_sendMessage {party : Participant} {tr₀ : ExecTrace} (m : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr m).2.symm ▸
    noNewPartyState_append_other hInv (NetE m) rfl

private theorem preserves_np_storeTR {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (hp : p ≠ party) (st : TRState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by
    rw [storeLocalState_tr_snd_eq]; exact noNewPartyState_append_trSt_ne hInv p hp st

private theorem preserves_np_storePQ {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (st : PQXDHState) :
    Preserves (NoNewPartyState party tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Symbolic.Swarm.CREF.TR.Runs.storeLocalState tr p st).2.symm ▸
    noNewPartyState_append_other hInv (PQStE p st) rfl

private theorem preserves_np_logPQ {party : Participant} {tr₀ : ExecTrace} (ev : PQXDHEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Symbolic.Swarm.CREF.TR.Runs.logEvent tr ev).2.symm ▸
    noNewPartyState_append_other hInv (PQEvE ev) rfl

private theorem preserves_np_logC {party : Participant} {tr₀ : ExecTrace} (ev : ComposedEvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (CEvE ev) rfl

private theorem preserves_np_logTR {party : Participant} {tr₀ : ExecTrace} (ev : TREvent) :
    Preserves (NoNewPartyState party tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewPartyState_append_other hInv (TREvE ev) rfl

private theorem preserves_np_getKey {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_np_lookupIdentity {party : Participant} {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_np_logMKAndStore {party : Participant} {tr₀ : ExecTrace}
    (me : Participant) (hme : me ≠ party) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_np_logTR _) fun _ => preserves_np_storeTR me hme st

private theorem preserves_np_dhRatchetStep {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  unfold DY.Libsignal.TripleRatchet.dhRatchetStep
  rcases DY.Libsignal.TripleRatchet.recvHalfStep st.toDRState pk with _ | ⟨_, _⟩
  · exact Preserves.failure
  · exact Preserves.bind (preserves_np_genRand 32) fun _ => Preserves.pure _

private theorem preserves_np_ensureReceiverChain {party : Participant} {tr₀ : ExecTrace}
    (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewPartyState party tr₀) (ensureReceiverChain st pk) := by
  unfold ensureReceiverChain; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_np_dhRatchetStep st pk) fun _ => Preserves.pure _

private theorem preserves_np_logSkippedKeys {party : Participant} {tr₀ : ExecTrace}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_np_logTR _) fun _ => ih _ _

local macro "noPartySt_tac" hne:ident : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_np_genRand
  | with_reducible apply preserves_np_storeTR _ $hne
  | with_reducible apply preserves_np_storePQ | with_reducible apply preserves_np_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_np_getKey | with_reducible apply preserves_np_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt
  | with_reducible apply preserves_np_dhRatchetStep
  | with_reducible apply preserves_np_ensureReceiverChain
  | with_reducible apply preserves_np_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_np_logMKAndStore _ $hne
  | with_reducible apply preserves_np_logPQ | with_reducible apply preserves_np_logC
  | with_reducible apply preserves_np_logTR | split | with_reducible intro))

private theorem preserves_np_decryptInMemory {party : Participant} {tr₀ : ExecTrace}
    {me : Participant} (_hme : me ≠ party)
    (st0 : TRState) (msg : TRSignalMsg) (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.TripleRatchet.decryptInMemory st0 msg pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.decryptInMemory; noPartySt_tac _hme

private theorem preserves_np_logRatchet {party : Participant} {tr₀ : ExecTrace}
    {me : Participant} (_hme : me ≠ party)
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) :
    Preserves (NoNewPartyState party tr₀) (p.logRatchet me) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.logRatchet; noPartySt_tac _hme

private theorem preserves_np_commit {party : Participant} {tr₀ : ExecTrace}
    {me : Participant} (hme : me ≠ party)
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) (par : Option Nat := none) :
    Preserves (NoNewPartyState party tr₀) (p.commit me par) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.commit
  cases par <;> (dsimp only; noPartySt_tac hme)

private theorem preserves_np_bobHandshake {party : Participant} {tr₀ : ExecTrace}
    {b : Participant} (_hb : b ≠ party) (a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (NoNewPartyState party tr₀)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; noPartySt_tac _hb

theorem noNewPartyState_runSteps_network {party : Participant} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) → NoNewPartyState party tr (runSteps pre tr)
  | [], tr, _ => noNewPartyState_refl party tr
  | s :: pre, tr, hnet => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : NoNewPartyState party tr ((Step.network m).next tr) := by
      rw [next_network]; exact noNewPartyState_append_other (noNewPartyState_refl party tr) (NetE m) rfl
    exact noNewPartyState_trans hm
      (noNewPartyState_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)))

theorem noNewPartyState_step_other {party : Participant} {s : Step} (tr : ExecTrace)
    (hcls : s.cls = .party) (hne : s.party? ≠ some party) :
    NoNewPartyState party tr (s.next tr) := by
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
    have hne' : a ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
      unfold DY.Libsignal.Composed.aliceStart DY.Libsignal.PQXDH.aliceHandshake
      noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    have hne' : b ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqr) := by
      unfold DY.Libsignal.Composed.bobStart
      refine Preserves.bind (preserves_np_bobHandshake hne' a kh regIdxA mh.ek mh.ct) fun o => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
      refine Preserves.bind (preserves_np_decryptInMemory hne' _ msg pqIdx spqr) fun pending => ?_
      cases o.opk with
      | none =>
        dsimp only
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_np_logPQ _) fun _ => ?_
        refine Preserves.bind (preserves_np_logRatchet hne' pending) fun _ => ?_
        refine Preserves.bind (preserves_np_logC _) fun _ => ?_
        exact preserves_np_commit hne' pending
      | some _ =>
        dsimp only
        refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
        refine Preserves.bind (preserves_np_logPQ _) fun _ => ?_
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_np_logPQ _) fun _ => ?_
        refine Preserves.bind (preserves_np_logRatchet hne' pending) fun _ => ?_
        refine Preserves.bind (preserves_np_logC _) fun _ => ?_
        exact preserves_np_commit hne' pending
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncrypt me stateIdx cl pq =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageEncryptAbort me stateIdx =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr) (messageDecrypt me stateIdx mIdx pq spqr) := by
      unfold messageDecrypt
      refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mIdx) fun msg => ?_
      refine Preserves.bind (preserves_np_decryptInMemory hne' st msg pq spqr) fun pending => ?_
      refine Preserves.bind (preserves_np_logRatchet hne' pending) fun _ => ?_
      exact preserves_np_commit hne' pending (some stateIdx)
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hne' : me ≠ party := fun h => hne (by simp [Step.party?, h])
    have hact : Preserves (NoNewPartyState party tr)
        (messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold messageDecryptSkipped; noPartySt_tac hne'
    dsimp only [Step.next, Step.toInput]; erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    exact hact tr (noNewPartyState_refl party tr)
  | _ => simp [Step.cls] at hcls

def ActivePartySt (party : Participant) (initRole : Bool)
    (S : OpaqueSymbolSemantics) (g g' : Ghost)
    (recvIdxs : List (Fin 7)) (skIdx : Fin 7)
    (stClean : TRState) (tr : ExecTrace) : Prop :=
  (∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → st.initiator = initRole) ∧
  ∃ idxP stP,
    (tr.at? idxP : Option TRStEntry) = some ⟨⟨party, stP⟩⟩ ∧
    (∀ j st, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩) ∧
    StateBytesAgree S g g' stP stClean ∧
    stP.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs.map rcprPubOfIdx ∧
    rcprSecretIdx (clamp (gamma rcprI0 S g stP.dhs)) = some skIdx

theorem noNewPartyState_preserves_active {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 7)} {skIdx : Fin 7} {stClean : TRState} {tr tr' : ExecTrace}
    (hnew : NoNewPartyState party tr tr')
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr) :
    ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr' := by
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hrecv, hdhs⟩ := hinv
  refine ⟨?_, idxP, stP, at?_le_some hnew.1 hatP, ?_, hagree, hrecv, hdhs⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat; exact hrole i st hat
    · exact False.elim (hnew.2 i st (Nat.le_of_not_lt hlt) hat)
  · intro j st hj hat
    by_cases hlt : j < tr.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat; exact hmaxP j st hj hat
    · exact hnew.2 j st (Nat.le_of_not_lt hlt) hat

theorem activePartySt_unique_current {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 7)} {skIdx : Fin 7} {stClean : TRState} {tr : ExecTrace}
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr) :
    ∃ idxP stP,
      (tr.at? idxP : Option TRStEntry) = some ⟨⟨party, stP⟩⟩ ∧
      (∀ j st, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨party, st⟩⟩) ∧
      StateBytesAgree S g g' stP stClean ∧
      stP.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs.map rcprPubOfIdx ∧
      rcprSecretIdx (clamp (gamma rcprI0 S g stP.dhs)) = some skIdx ∧
      (∀ stateIdx st,
        ((DY.PersistentLocalState.getLocalState party stateIdx : Traceful TRState).run tr).1 =
          some st →
        isCurrentSnapshot tr stateIdx = true →
        stateIdx = idxP ∧ st = stP) := by
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, hrecv, hdhs⟩ := hinv
  refine ⟨idxP, stP, hatP, hmaxP, hagree, hrecv, hdhs, ?_⟩
  intro stateIdx st hst hcur
  have hat := bks_stored_of_getLocalState hst
  have hle : stateIdx ≤ idxP := by
    by_contra hgt; exact hmaxP stateIdx st (by omega) hat
  by_cases hlt : stateIdx < idxP
  · exfalso
    have hfalse := isCurrentSnapshot_false_of_later hat hatP hlt
      (by rw [hrole _ _ hatP, hrole _ _ hat])
    rw [hfalse] at hcur; cases hcur
  · have hidx : stateIdx = idxP := by omega
    subst hidx; rw [hatP] at hat; cases hat
    exact ⟨rfl, rfl⟩

theorem activePartySt_pin_state {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 7)} {skIdx : Fin 7} {stClean : TRState}
    {tr : ExecTrace} {stateIdx : Nat} {st : TRState}
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr)
    (hst : ((DY.PersistentLocalState.getLocalState party stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    st.initiator = initRole ∧
    StateBytesAgree S g g' st stClean ∧
    st.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs.map rcprPubOfIdx ∧
    rcprSecretIdx (clamp (gamma rcprI0 S g st.dhs)) = some skIdx := by
  obtain ⟨idxP, stP, hatP, _, hagree, hrecv, hdhs, huniq⟩ := activePartySt_unique_current hinv
  obtain ⟨rfl, rfl⟩ := huniq stateIdx st hst hcur
  exact ⟨hinv.1 _ _ hatP, hagree, hrecv, hdhs⟩

theorem activePartySt_init {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs : List (Fin 7)} {skIdx : Fin 7} {stClean : TRState} {tr tr' : ExecTrace}
    (hnone : NoPartyState party tr) (hle : tr ≤ tr')
    {idxP' : Nat} {stP' : TRState}
    (hat' : (tr'.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → j = idxP' ∧ st = stP')
    (hinit' : stP'.initiator = initRole)
    (hagree' : StateBytesAgree S g g' stP' stClean)
    (hrecv' : stP'.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs.map rcprPubOfIdx)
    (hdhs' : rcprSecretIdx (clamp (gamma rcprI0 S g stP'.dhs)) = some skIdx) :
    ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr' := by
  have hge : tr.length ≤ idxP' := by
    by_contra hlt
    have hat0 : (tr.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩ := by
      rw [← at?_of_le_lt hle (by omega)]; exact hat'
    exact hnone idxP' stP' hat0
  refine ⟨?_, idxP', stP', hat', ?_, hagree', hrecv', hdhs'⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat; exact False.elim (hnone i st hat)
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat; exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat; omega

theorem activePartySt_of_unique_new {party : Participant} {initRole : Bool}
    {S : OpaqueSymbolSemantics} {g g' : Ghost}
    {recvIdxs recvIdxs' : List (Fin 7)} {skIdx skIdx' : Fin 7}
    {stClean stClean' : TRState} {tr tr' : ExecTrace}
    (hinv : ActivePartySt party initRole S g g' recvIdxs skIdx stClean tr) (hle : tr ≤ tr')
    {idxP' : Nat} {stP' : TRState} (hge : tr.length ≤ idxP')
    (hat' : (tr'.at? idxP' : Option TRStEntry) = some ⟨⟨party, stP'⟩⟩)
    (huniq : ∀ j st, tr.length ≤ j →
      (tr'.at? j : Option TRStEntry) = some ⟨⟨party, st⟩⟩ → j = idxP' ∧ st = stP')
    (hinit' : stP'.initiator = initRole)
    (hagree' : StateBytesAgree S g g' stP' stClean')
    (hrecv' : stP'.recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs'.map rcprPubOfIdx)
    (hdhs' : rcprSecretIdx (clamp (gamma rcprI0 S g stP'.dhs)) = some skIdx') :
    ActivePartySt party initRole S g g' recvIdxs' skIdx' stClean' tr' := by
  obtain ⟨hrole, _⟩ := hinv
  refine ⟨?_, idxP', stP', hat', ?_, hagree', hrecv', hdhs'⟩
  · intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hle hlt] at hat; exact hrole i st hat
    · obtain ⟨_, rfl⟩ := huniq i st (Nat.le_of_not_lt hlt) hat; exact hinit'
  · intro j st hj hat
    obtain ⟨hj_eq, _⟩ := huniq j st (by omega) hat; omega

/-! ## 5. `encTrGen_stepView_ok`, Decrypt Unpacking, & Visible-Entry Helpers -/

private theorem encTrGen_newIndices (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    newIndices tr (encTrGen tr me stH cl st pq) =
      [tr.length, tr.length + 1, tr.length + 2, tr.length + 3,
       tr.length + 4, tr.length + 5, tr.length + 6] := by
  unfold newIndices; rw [encTrGen_length, Nat.add_sub_cancel_left]; simp [List.range', Nat.add_assoc]

private theorem at?_append_proj_at {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E2) =
      TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) := by
  subst hi; exact at?_append_self_proj tr e

private theorem encTrGen_newRandoms (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    newRandoms tr (encTrGen tr me stH cl st pq) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
  unfold newRandoms; rw [encTrGen_newIndices]
  let tr' := encTrGen tr me stH cl st pq
  have h0 : (tr'.at? tr.length : Option DY.Random.ExecEntryT) = some (RndE 32) := by
    dsimp only [tr', encTrGen]; iterate 6 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    exact at?_append_at _ _ rfl
  have h1 : (tr'.at? (tr.length + 1) : Option DY.Random.ExecEntryT) = some (RndE cl) := by
    dsimp only [tr', encTrGen]; iterate 5 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    exact at?_append_at _ _ (by simp only [append_len])
  have h2 : (tr'.at? (tr.length + 2) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]; iterate 4 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h3 : (tr'.at? (tr.length + 3) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]; iterate 3 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h4 : (tr'.at? (tr.length + 4) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]; iterate 2 rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h5 : (tr'.at? (tr.length + 5) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]; rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
    rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  have h6 : (tr'.at? (tr.length + 6) : Option DY.Random.ExecEntryT) = none := by
    dsimp only [tr', encTrGen]; rw [at?_append_proj_at _ _ (by simp only [append_len])]; rfl
  change List.filterMap (fun i => (tr'.at? i : Option DY.Random.ExecEntryT).map _) _ = _
  simp [h0, h1, h2, h3, h4, h5, h6, RndE]

private theorem encTrGen_lastSent (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    lastSent tr (encTrGen tr me stH cl st pq) =
      some (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32)) := by
  unfold lastSent; rw [encTrGen_length]
  have hlt : tr.length < tr.length + 7 := by omega
  have hsub : tr.length + 7 - 1 = tr.length + 6 := by omega
  simp only [hlt, ↓reduceIte, hsub, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  have hat : ((encTrGen tr me stH cl st pq).at? (tr.length + 6) : Option DY.Network.ExecEntryT) =
      some (NetE (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
    dsimp only [encTrGen]; exact at?_append_at _ _ (by simp only [append_len])
  rw [hat]

private theorem pqExposureAt_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr.append e ≤ tr') (hj : j = tr.length)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntry) = none) :
    pqExposureAt tr' j = none := by
  subst hj; unfold pqExposureAt
  have hat : (tr'.at? tr.length : Option PQEvEntry) = none := by
    rw [at?_of_le_lt hle (by simp), at?_append_self_proj, hnone]
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

private theorem trExposureAt_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr tr' : ExecTrace} {e : E} (j : Nat)
    (hle : tr.append e ≤ tr') (hj : j = tr.length)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none) :
    trExposureAt tr' j = none := by
  subst hj; unfold trExposureAt
  have hat : (tr'.at? tr.length : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
    rw [at?_of_le_lt hle (by simp), at?_append_self_proj, hnone]
  simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat]

theorem encTrGen_exposures (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    exposures tr (encTrGen tr me stH cl st pq) = [] := by
  unfold exposures; rw [encTrGen_newIndices]
  let t0 := tr
  let t1 := t0.append (RndE 32)
  let t2 := t1.append (RndE cl)
  let t3 := t2.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.NetE
    (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1)
  let t4' := t3.append (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32)))
  let t5' := t4'.append (EvT (.MessageKey (st.sessionInfo me) .sender
    (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pq st.ns st.rIdx stH))
  let t6 := t5'.append (StT me (encSt st (rnd (tr.length + 1) cl)))
  let t7 := encTrGen tr me stH cl st pq
  have h67 : t6 ≤ t7 := DY.Trace.append_le _ _
  have h57 : t5' ≤ t7 := le_append_of_le (DY.Trace.append_le _ _) _
  have h47' : t4' ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h57
  have h37 : t3 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h47'
  have h27 : t2 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h37
  have h17 : t1 ≤ t7 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) h27
  have hp0 := pqExposureAt_append_non tr.length h17 rfl rfl
  have hp1 := pqExposureAt_append_non (tr.length + 1) h27 (by simp only [t1, t0, append_len]) rfl
  have hp2 := pqExposureAt_append_non (tr.length + 2) h37 (by simp only [t2, t1, t0, append_len]) rfl
  have hp3 := pqExposureAt_append_non (tr.length + 3) h47' (by simp only [t3, t2, t1, t0, append_len]) rfl
  have hp4 := pqExposureAt_append_non (tr.length + 4) h57 (by simp only [t4', t3, t2, t1, t0, append_len]) rfl
  have hp5 := pqExposureAt_append_non (tr.length + 5) h67 (by simp only [t5', t4', t3, t2, t1, t0, append_len]) rfl
  have hp6 := pqExposureAt_append_non (tr.length + 6) (DY.Trace.le_refl t7) (by simp only [append_len]) rfl
  have ht0 := trExposureAt_append_non tr.length h17 rfl rfl
  have ht1 := trExposureAt_append_non (tr.length + 1) h27 (by simp only [t1, t0, append_len]) rfl
  have ht2 := trExposureAt_append_non (tr.length + 2) h37 (by simp only [t2, t1, t0, append_len]) rfl
  have ht5 := trExposureAt_append_non (tr.length + 5) h67 (by simp only [t5', t4', t3, t2, t1, t0, append_len]) rfl
  have ht6 := trExposureAt_append_non (tr.length + 6) (DY.Trace.le_refl t7) (by simp only [append_len]) rfl
  have ht3 : trExposureAt t7 (tr.length + 3) = none := by
    unfold trExposureAt
    have hat : (t7.at? (tr.length + 3) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Sent me st.peer (dhPk st.dhs) st.ns (rnd tr.length 32))) :=
      at?_mono h47' (at?_append_at t3 _ (by simp only [t3, t2, t1, t0, append_len]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat, EvT]
  have ht4 : trExposureAt t7 (tr.length + 4) = none := by
    unfold trExposureAt
    have hat : (t7.at? (tr.length + 4) : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.MessageKey (st.sessionInfo me) .sender
          (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pq st.ns st.rIdx stH)) :=
      at?_mono h57 (at?_append_at t4' _ (by simp only [t4', t3, t2, t1, t0, append_len]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat, EvT]
  change List.filterMap (pqExposureAt t7) _ ++ List.filterMap (trExposureAt t7) _ = []
  simp [hp0, hp1, hp2, hp3, hp4, hp5, hp6, ht0, ht1, ht2, ht3, ht4, ht5, ht6]

def encSendList (wrapped : Bool) (ppk : Option (Bytes × Bytes)) (m : Bytes) : List VisEntry :=
  match wrapped, ppk with
  | true, some (ek, ct) => [⟨.send, [ek, ct, m], .preKeySend, none⟩]
  | false, none => [⟨.send, [m], .whisper, none⟩]
  | _, _ => []

theorem encTrGen_stepView_ok {tr : ExecTrace} {me : Participant} {stH cl pqH : Nat}
    {st : TRState} {pq : Bytes} {wrapped : Bool}
    (hok : (Step.messageEncrypt me stH cl pqH).ok tr = true)
    (hnext : (Step.messageEncrypt me stH cl pqH).next tr = encTrGen tr me stH cl st pq) :
    stepView (.messageEncrypt me stH cl pqH) tr wrapped =
      ⟨.pt, [randTerm tr.length 32], .single, none⟩ ::
      ((if cl != 0 then [rngEntry (randTerm (tr.length + 1) cl)] else []) ++
       encSendList wrapped (pendingPreKey tr stH)
         (encMsg st (rnd (tr.length + 1) cl) pq (rnd tr.length 32))) := by
  unfold stepView; simp only [hok, ↓reduceIte]
  rw [hnext, encTrGen_newRandoms, encTrGen_exposures, List.append_nil]
  unfold encDraws encSendEntry encSendList
  rw [encTrGen_lastSent]
  by_cases hcl : cl = 0 <;> simp [hcl, List.cons_append] <;>
    (rcases wrapped with _ | _ <;> rcases pendingPreKey tr stH with _ | ⟨_, _⟩ <;> rfl)

theorem append_singleton_inj {α : Type} {xs₁ xs₂ : List α} {y₁ y₂ : α}
    (h : xs₁ ++ [y₁] = xs₂ ++ [y₂]) : xs₁ = xs₂ ∧ y₁ = y₂ := by
  induction xs₁ generalizing xs₂ with
  | nil => cases xs₂ with | nil => simp at h; exact ⟨rfl, h⟩ | cons _ _ => simp at h
  | cons x xs₁ ih =>
    cases xs₂ with
    | nil => simp at h
    | cons a as =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxs, hy⟩ := ih h.2; exact ⟨congrArg₂ List.cons h.1 hxs, hy⟩

theorem findRecvChain_none_of_not_mem {S : OpaqueSymbolSemantics} {g : Ghost}
    {recv : List RecvChain} {recvIdxs : List (Fin 7)} {pk : DY.Bytes} {pkIdx : Fin 7}
    (hrecv : recv.map (fun c => gamma rcprI0 S g c.ratchetKey) = recvIdxs.map rcprPubOfIdx)
    (hpk : gamma rcprI0 S g pk = rcprPubOfIdx pkIdx)
    (hnotMem : pkIdx ∉ recvIdxs) :
    findRecvChain recv pk = none := by
  unfold findRecvChain
  cases hf : recv.find? (fun x => x.ratchetKey == pk) with
  | none => rfl
  | some c =>
    exfalso
    have hmem : c ∈ recv := List.mem_of_find?_eq_some hf
    have heq : c.ratchetKey = pk :=
      beq_iff_eq.mp (List.find?_some (p := fun (x : RecvChain) => x.ratchetKey == pk) hf)
    have hmem_map : gamma rcprI0 S g c.ratchetKey ∈
        recv.map (fun x => gamma rcprI0 S g x.ratchetKey) := List.mem_map_of_mem hmem
    rw [heq, hpk, hrecv, List.mem_map] at hmem_map
    obtain ⟨idx, hidx_mem, hidx_eq⟩ := hmem_map
    exact hnotMem (rcprPubOfIdx_inj hidx_eq ▸ hidx_mem)

theorem not_decryptSkipped_of_find_none {me : Participant} {stateIdx msgIdx sk pq : Nat}
    {spqr : UInt32} {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg}
    (hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hmsg : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hfind : findRecvChain st.recv msg.ratchetKey = none) :
    (Step.messageDecryptSkipped me stateIdx msgIdx sk pq spqr).ok tr = false := by
  rw [step_ok_decryptSkipped]
  obtain ⟨t, hat, hparse, hver⟩ := rpkT_receiveSignalMsg_some hmsg
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run (rpkT_getMessageSentAt_of_at? hat) hparse hver
  unfold messageDecryptSkipped
  rw [run_bind_fst, hst, getLocalState_snd]; dsimp only
  rw [run_bind_fst, hrcv1, hrcv2]; dsimp only
  rw [run_bind_fst]
  rcases ((DY.getEntry sk : Traceful (DY.ProtocolEvent.ExecEntryT TREvent)).run tr).1 with
    _ | ⟨⟨ev_sk⟩⟩
  · rfl
  · dsimp only
    cases ev_sk with
    | SkippedKeyStored s pk n seed rIdx src =>
      dsimp only
      have hguard_false : ¬ (s = st.sessionInfo me ∧ pk = msg.ratchetKey ∧ n = msg.counter ∧
          (findRecvChain st.toDRState.recv pk).isSome = true) := by
        rintro ⟨_, rfl, _, his⟩
        change (findRecvChain st.recv msg.ratchetKey).isSome = true at his
        rw [hfind] at his; cases his
      simp only [_root_.guard, hguard_false, ↓reduceIte, run_bind_fst, DY.Traceful.run_failure]
      rfl
    | _ => dsimp only; rw [DY.Traceful.run_failure]; rfl

structure DecryptRatchetWitness (me : Participant) (stateIdx msgIdx pqIdx : Nat)
    (spqr : UInt32) (tr : ExecTrace) (st : TRState) where
  t : DY.Bytes
  msg : TRSignalMsg
  seed : DY.Bytes
  c' : RecvChain
  spqr' : DY.Bytes
  key : DY.Bytes
  pqSalt : DY.Bytes
  ptTerm : DY.Bytes
  hmsg : tr.getMessageSentAt msgIdx = some t
  hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg t = some msg
  hver : msg.version = messageVersion
  hlow : x25519LowOrder msg.ratchetKey = false
  hcons : consumeMessageKey (trDhRatchetState st msg.ratchetKey tr.length).2 msg.counter =
    some (seed, c')
  hspqr : DY.Spqr.spqrRecv (trDhRatchetState st msg.ratchetKey tr.length).1.spqr
    msg.pqRatchet spqr = some (spqr', key)
  hpqSalt : (((tr.append (⟨32⟩ : DY.Random.ExecEntryT)).append
    (⟨key⟩ : DY.Network.ExecEntryT)).at? pqIdx : Option DY.Network.ExecEntryT) = some ⟨pqSalt⟩
  hmac_eq : msg.mac = computeMac (trMsgKeys pqSalt seed).macKey
    (trDhRatchetState st msg.ratchetKey tr.length).1.peerIk
    (trDhRatchetState st msg.ratchetKey tr.length).1.myIk msg.wire
  hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey (trMsgKeys pqSalt seed).iv
    msg.ciphertext = some ptTerm

theorem decrypt_ratchet_inv {me : Participant} {stateIdx msgIdx pqIdx : Nat}
    {spqr : UInt32} {tr : ExecTrace} {st : TRState} {msg : TRSignalMsg}
    (hok : (Step.messageDecrypt me stateIdx msgIdx pqIdx spqr).ok tr = true)
    (hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hmsg_run : ((receiveSignalMsg msgIdx).run tr).1 = some msg)
    (hfind : findRecvChain st.recv msg.ratchetKey = none) :
    ∃ w : DecryptRatchetWitness me stateIdx msgIdx pqIdx spqr tr st, w.msg = msg := by
  rw [step_ok_decrypt] at hok
  obtain ⟨t, hat, hparse, hver⟩ := rpkT_receiveSignalMsg_some hmsg_run
  have hmsg_at := rpkT_getMessageSentAt_of_at? hat
  obtain ⟨hrcv1, hrcv2⟩ := receiveSignalMsg_run hmsg_at hparse hver
  unfold messageDecrypt at hok
  rw [run_bind_fst, hst, getLocalState_snd] at hok; dsimp only at hok
  rw [run_bind_fst, hrcv1, hrcv2] at hok; dsimp only at hok
  have hdim : ((DY.Libsignal.TripleRatchet.decryptInMemory st msg pqIdx spqr).run tr).1.isSome = true := by
    rw [run_bind_fst] at hok
    cases hd : ((DY.Libsignal.TripleRatchet.decryptInMemory st msg pqIdx spqr).run tr).1
    · rw [hd] at hok; cases hok
    · rfl
  clear hok
  have hok := hdim
  unfold DY.Libsignal.TripleRatchet.decryptInMemory at hok
  have hlow : x25519LowOrder msg.ratchetKey = false := by
    cases hl : x25519LowOrder msg.ratchetKey with
    | false => rfl
    | true =>
      exfalso
      unfold ensureReceiverChain DY.Libsignal.TripleRatchet.dhRatchetStep
        DY.Libsignal.TripleRatchet.recvHalfStep TRState.toDRState at hok
      dsimp only at hok; rw [hfind, hl] at hok
      simp only [↓reduceIte, run_bind_fst, DY.Traceful.run_failure] at hok; cases hok
  obtain ⟨hens1, hens2⟩ := ensureReceiverChain_run_ratchet tr hfind hlow
  rw [run_bind_fst, hens1, hens2] at hok; dsimp only at hok
  let st1 := (trDhRatchetState st msg.ratchetKey tr.length).1
  let c := (trDhRatchetState st msg.ratchetKey tr.length).2
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩
  · rw [hcons, DY.Traceful.run_failure] at hok; cases hok
  · rw [hcons] at hok; dsimp only at hok
    rcases hspqr : DY.Spqr.spqrRecv st1.spqr msg.pqRatchet spqr with _ | ⟨spqr', key⟩
    · rw [hspqr, DY.Traceful.run_failure] at hok; cases hok
    · rw [hspqr] at hok; dsimp only at hok
      let tr_r := tr.append (⟨32⟩ : DY.Random.ExecEntryT)
      let tr_k := tr_r.append (⟨key⟩ : DY.Network.ExecEntryT)
      rw [run_bind_fst, (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r key).1,
          (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr_r key).2] at hok; dsimp only at hok
      rw [run_bind_fst, rpkT_receiveMessage_fst, receiveMessage_snd] at hok
      rcases hpq : tr_k.getMessageSentAt pqIdx with _ | pqSalt
      · rw [hpq] at hok; cases hok
      · rw [hpq] at hok; dsimp only at hok; rw [run_bind_fst] at hok
        rcases hv : ((verifyMacAndDecrypt st1 msg pqSalt seed).run tr_k).1 with _ | ptTerm
        · rw [hv] at hok; cases hok
        · have ⟨hmac_eq, _⟩ := rpkT_verifyMacAndDecrypt_some hv
          have hdec : DY.SymEnc.symDec (trMsgKeys pqSalt seed).cipherKey
              (trMsgKeys pqSalt seed).iv msg.ciphertext = some ptTerm := by
            unfold verifyMacAndDecrypt at hv
            simp only [_root_.guard, hmac_eq, ↓reduceIte, run_bind_fst, DY.Traceful.run_pure] at hv
            dsimp only [liftM, monadLift, MonadLift.monadLift] at hv
            rw [DY.Traceful.run_mk] at hv; exact hv
          exact ⟨⟨t, msg, seed, c', spqr', key, pqSalt, ptTerm,
            hmsg_at, hparse, hver, hlow, hcons, hspqr,
            rpkT_at?_of_getMessageSentAt hpq, hmac_eq, hdec⟩, rfl⟩

theorem exposures_kind_leak {tr tr' : ExecTrace} {w : VisEntry}
    (hw : w ∈ exposures tr tr') : w.kind = .leak := by
  unfold exposures at hw; rw [List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw; unfold pqExposureAt at hj
    rcases h : tr'.getEventAt PQXDHEvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw; unfold trExposureAt at hj
    rcases h : tr'.getEventAt TREvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl

theorem recv_outputs_accept {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {e : RunEvent} {outs : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hexit : ∃ out, e.exit = some (0, out)) (hcmd : ∃ peer, e.cmd = .recv peer)
    (hout : OutputsMatch rcprI0 r S g e outs initIds) :
    ∃ w_out, outs = [w_out] ∧ w_out.kind = .accept := by
  obtain ⟨out, he⟩ := hexit; obtain ⟨peer, hc⟩ := hcmd
  unfold OutputsMatch at hout; rw [he, hc] at hout
  obtain ⟨w_out, rfl, hbm⟩ := hout; exact ⟨w_out, rfl, hbm.1.symm⟩

theorem split_vis_recv_rng {inp v₀ v₂ w_out : VisEntry} {drs rest : List VisEntry} {ts : Nat}
    (hvis : inp :: (drs ++ [w_out]) = v₀ :: rngEntry (randTerm ts 32) :: v₂ :: rest)
    (hkind : w_out.kind = .accept) :
    inp = v₀ ∧ ∃ drs_rest, drs = rngEntry (randTerm ts 32) :: drs_rest := by
  injection hvis with hinp htail; refine ⟨hinp, ?_⟩
  cases drs with
  | nil =>
    dsimp only [List.nil_append] at htail; injection htail with hw _
    rw [hw] at hkind; cases hkind
  | cons d drs_rest =>
    dsimp only [List.cons_append] at htail; injection htail with hd _
    exact ⟨drs_rest, congrArg (· :: drs_rest) hd⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
