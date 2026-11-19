/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Trace State Lookup, `NoSkippedKeys`, and `messageDecrypt` Inversion for Seed 7003

Provides shared trace-state preservation lemmas across `b1_setupTr4`, invisible `runSteps`,
`aliceTr`, `encTrCl`, and `bobTr0`, plus monadic inversion for `messageDecryptSkipped` and
`messageDecrypt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003

open DY
open scoped DY.Libsignal.Composed
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent HandshakeKeys)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg RecvChain parseTrSignalMsg computeMac trMsgKeys
   findRecvChain consumeMessageKey recvChainFor)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.CREF (b1_setupTr4)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_ok)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd RndE NetE EvP EvT EvC StP StT aliceOut aliceSt aliceTr aliceTrOpt
   bobOut encSt ratchetState)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 hiding
  rk0Bytes seedA0Bytes cksA1Bytes seedB0Bytes cksA0Bytes cksB1Bytes cksB0Bytes
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

/-! ## 1. `bobDoneBaseKeys` Membership After `bobTr0` -/

theorem bobTr0_bobDone_mem (tr : ExecTrace) (ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (seed pq m key : DY.Bytes) (st' stOut : TRState) (c : RecvChain) :
    ek ∈ bobDoneBaseKeys (bobTr0 tr ek ct keys msg seed pq m key st' stOut c) := by
  unfold bobDoneBaseKeys
  set tr' := bobTr0 tr ek ct keys msg seed pq m key st' stOut c
  rw [List.mem_filterMap]
  refine ⟨tr.length + 2, ?_, ?_⟩
  · rw [List.mem_range]
    simp only [tr', bobTr0, length_append_eq, Nat.add_assoc]
    omega
  · rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    dsimp only [tr', bobTr0]
    repeat first
      | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
      | rw [at?_append_same_eq (fun _ => rfl)]
    simp only [length_append_eq, Nat.add_assoc, ↓reduceIte]
    rfl

/-! ## 2. `NoSkippedKeys` Invariant Across Setup and Honest Steps -/

def NoSkippedKeys (tr : ExecTrace) : Prop :=
  ∀ i s pk n seed rIdx child,
    tr.getEventAt TREvent i ≠ some (.SkippedKeyStored s pk n seed rIdx child)

theorem noSkippedKeys_setupTr4 : NoSkippedKeys (b1_setupTr4 "alice" "bob") := by
  intro i s pk n seed rIdx child
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, setupTr4_trEvent_none]
  simp

theorem noSkippedKeys_runSteps_invisible {pre : List Step} {tr : ExecTrace}
    (hinv : ∀ x ∈ pre, x.cls = .invisible) (hno : NoSkippedKeys tr) :
    NoSkippedKeys (runSteps pre tr) := by
  intro i s pk n seed rIdx child
  rw [runSteps_invisible_getEventAt_tr hinv]
  exact hno i s pk n seed rIdx child

theorem noSkippedKeys_aliceTr {tr : ExecTrace} {a b : Participant} {ikA ikB spk pqpk : DY.Bytes}
    (hno : NoSkippedKeys tr) :
    NoSkippedKeys (aliceTr tr a b ikA ikB spk pqpk) := by
  intro i s pk n seed rIdx child
  have h1 := hno i s pk n seed rIdx child
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h1 ⊢
  dsimp only [aliceTr, aliceTrOpt]
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  by_cases h6 : i = tr.length + 6
  · subst h6; simp [EvT]
  · rw [if_neg' h6]; exact h1

theorem noSkippedKeys_encTrCl {tr : ExecTrace} {me : Participant} {stH : Nat} {st : TRState} {cl : Nat}
    (hno : NoSkippedKeys tr) :
    NoSkippedKeys (encTrCl tr me stH st cl) := by
  intro i s pk n seed rIdx child
  have h1 := hno i s pk n seed rIdx child
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h1 ⊢
  dsimp only [encTrCl]
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  by_cases h4 : i = tr.length + 4
  · subst h4; simp [EvT]
  · rw [if_neg' h4]
    by_cases h3 : i = tr.length + 3
    · subst h3; simp [EvT]
    · rw [if_neg' h3]; exact h1

theorem noSkippedKeys_bobTr0 {tr : ExecTrace} {ek ct : DY.Bytes} {keys : HandshakeKeys}
    {msg : TRSignalMsg} {seed pq m key : DY.Bytes} {st' stOut : TRState} {c : RecvChain}
    (hno : NoSkippedKeys tr) :
    NoSkippedKeys (bobTr0 tr ek ct keys msg seed pq m key st' stOut c) := by
  intro i s pk n seed' rIdx child
  have h1 := hno i s pk n seed' rIdx child
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h1 ⊢
  dsimp only [bobTr0]
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT TREvent) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  by_cases h7 : i = tr.length + 7
  · subst h7; simp [EvT]
  · rw [if_neg' h7]
    by_cases h6 : i = tr.length + 6
    · subst h6; simp [EvT]
    · rw [if_neg' h6]
      by_cases h4 : i = tr.length + 4
      · subst h4; simp [EvT]
      · rw [if_neg' h4]
        by_cases h3 : i = tr.length + 3
        · subst h3; simp [EvT]
        · rw [if_neg' h3]; exact h1

/-! ## 3. `TRState`, `PQXDHEvent`, and `ComposedEvent` Lookup Helpers -/

theorem aliceTr_trState_eq (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) (i : Nat) :
    ((aliceTr tr a b ikA ikB spk pqpk).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) =
    if i = tr.length + 8 then
      some (StT a (aliceSt b (aliceOut tr ikA ikB spk pqpk) (rnd (tr.length + 2) 32)))
    else tr.at? i := by
  unfold aliceTr aliceTrOpt
  rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState)) rfl]

theorem encTrCl_trState_eq (tr : ExecTrace) (me : Participant) (stH : Nat) (st : TRState) (cl i : Nat) :
    ((encTrCl tr me stH st cl).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) =
    if i = tr.length + 5 then
      some (StT me (encSt st (randTerm (tr.length + 1) cl)))
    else tr.at? i := by
  unfold encTrCl
  rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
    (DY.PersistentLocalState.LocalState TRState)) rfl,
    at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState)) rfl]

theorem bobTr0_trState_eq (tr : ExecTrace) (ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (seed pq m key : DY.Bytes) (st' stOut : TRState) (c : RecvChain) (i : Nat) :
    ((bobTr0 tr ek ct keys msg seed pq m key st' stOut c).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) =
    if i = tr.length + 8 then some (StT "bob" stOut) else tr.at? i := by
  unfold bobTr0
  rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState)) rfl]

theorem aliceTr_pqxdhEvent_eq (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) (i : Nat) :
    ((aliceTr tr a b ikA ikB spk pqpk).at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
    if i = tr.length + 5 then
      let o := aliceOut tr ikA ikB spk pqpk
      some (EvP (.AliceDone a b o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys))
    else tr.at? i := by
  unfold aliceTr aliceTrOpt
  rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
      at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
      at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl,
      at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]

theorem bobTr0_pqxdhEvent_eq (tr : ExecTrace) (ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (seed pq m key : DY.Bytes) (st' stOut : TRState) (c : RecvChain) (i : Nat) :
    ((bobTr0 tr ek ct keys msg seed pq m key st' stOut c).at? i :
      Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
    if i = tr.length + 2 then
      let o := bobOut (randTerm 5 32) (randTerm 10 32) (randTerm 16 64)
        (DY.DiffieHellman.dhPk (randTerm 0 32)) ek ct keys
      some (EvP (.BobDone "bob" "alice" o.ikB o.ikA o.spk o.pqpk o.opk o.ek o.ct o.keys))
    else tr.at? i := by
  unfold bobTr0
  repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]
  rw [at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT PQXDHEvent) rfl]

theorem aliceTr_compEvent_eq (tr : ExecTrace) (a b : Participant) (ikA ikB spk pqpk : DY.Bytes) (i : Nat) :
    ((aliceTr tr a b ikA ikB spk pqpk).at? i : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) =
    if i = tr.length + 7 then
      let o := aliceOut tr ikA ikB spk pqpk
      some (EvC (.HandshakeSession ((aliceSt b o (rnd (tr.length + 2) 32)).sessionInfo a) (tr.length + 5)))
    else tr.at? i := by
  unfold aliceTr aliceTrOpt
  rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl,
      at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl]

theorem bobTr0_compEvent_eq (tr : ExecTrace) (ek ct : DY.Bytes) (keys : HandshakeKeys)
    (msg : TRSignalMsg) (seed pq m key : DY.Bytes) (st' stOut : TRState) (c : RecvChain) (i : Nat) :
    ((bobTr0 tr ek ct keys msg seed pq m key st' stOut c).at? i :
      Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) =
    if i = tr.length + 5 then
      some (EvC (.HandshakeSession (st'.sessionInfo "bob") (tr.length + 2)))
    else tr.at? i := by
  unfold bobTr0
  rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl,
      at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl,
      at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl,
      at?_append_same_eq (fun _ => rfl)]
  simp only [length_append_eq, Nat.add_assoc]
  split
  · rfl
  · repeat rw [at?_append_other_eq (E₂ := DY.ProtocolEvent.ExecEntryT ComposedEvent) rfl]

/-! ## 4. Inversion of `messageDecryptSkipped` and `messageDecrypt` -/

theorem not_messageDecryptSkipped_of_noSkippedKeys {tr : ExecTrace}
    {me : Participant} {stH msgH skH pqH : Nat} {idx : UInt32}
    (hno : NoSkippedKeys tr)
    (hok : (Step.messageDecryptSkipped me stH msgH skH pqH idx).ok tr = true) : False := by
  have hok' : ((DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH msgH skH pqH idx).run tr).1.isSome = true := by
    dsimp only [Step.ok, Step.toInput] at hok; erw [stepIn_ok] at hok; exact hok
  obtain ⟨_, hrun⟩ := isSome_iff_exists.mp hok'
  unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped at hrun
  obtain ⟨_, tr₁, hst, htr₁, hr1, _⟩ := bind_some_inv hrun
  obtain ⟨_, htr₁'⟩ := getLocalState_tr_some_inv hst; rw [htr₁'] at htr₁; subst tr₁
  obtain ⟨_, tr₂, hmsg, htr₂, hr2, _⟩ := bind_some_inv hr1
  obtain ⟨_, _, _, _, htr₂'⟩ := receiveSignalMsg_some_inv hmsg; rw [htr₂'] at htr₂; subst tr₂
  obtain ⟨⟨ev⟩, tr₃, he, htr₃, hr3, _⟩ := bind_some_inv hr2
  obtain ⟨hat_sk, htr₃'⟩ := getEntry_some_inv he; rw [htr₃'] at htr₃; subst tr₃
  cases ev with
  | SkippedKeyStored s pk n seed rIdx child =>
    have hget : tr.getEventAt TREvent skH = some (.SkippedKeyStored s pk n seed rIdx child) := by
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat_sk]
    exact hno skH s pk n seed rIdx child hget
  | _ => simp [Traceful.run_failure] at hr3

theorem messageDecrypt_inv
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {me : Participant} {stH msgH pqH : Nat} {idx : UInt32}
    {ev : RunEvent} {vis : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hrm : RunMatches compI7003 r S g tr (Step.messageDecrypt me stH msgH pqH idx) ev vis initIds) :
    ∃ st raw msg,
      me = ev.party ∧
      tr.at? stH = some (StT me st) ∧
      tr.at? msgH = some (NetE raw) ∧
      parseTrSignalMsg raw = some msg ∧
      ReadsFaithfully compI7003 r S g tr
        ⟨.recv, [raw], if runWrapped ev then .preKeyInner (sessionBaseKeys tr stH) else .whisper, none⟩
        ev.input ∧
      ((∃ c seed c' pq,
          findRecvChain st.recv msg.ratchetKey = some c ∧
          consumeMessageKey c msg.counter = some (seed, c') ∧
          msg.mac = computeMac (trMsgKeys pq seed).macKey st.peerIk st.myIk msg.wire) ∨
       (∃ st' c seed c' pq,
          findRecvChain st.recv msg.ratchetKey = none ∧
          ratchetState st msg.ratchetKey (rnd tr.length 32) = (st', c) ∧
          consumeMessageKey c msg.counter = some (seed, c') ∧
          msg.mac = computeMac (trMsgKeys pq seed).macKey st'.peerIk st'.myIk msg.wire)) := by
  obtain ⟨_, hparty, _, _, hok, _, hv_eq, inp, drs, outs, hv_split, _, _, _, hrf, _⟩ := hrm
  have hme : me = ev.party := Option.some.inj hparty
  have hok' : ((DY.Libsignal.TripleRatchet.messageDecrypt me stH msgH pqH idx).run tr).1.isSome = true := by
    dsimp only [Step.ok, Step.toInput] at hok; erw [stepIn_ok] at hok; exact hok
  obtain ⟨_, hrun⟩ := isSome_iff_exists.mp hok'
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline] at hrun
  obtain ⟨st, tr₁, hst, htr₁, hr1, _⟩ := bind_some_inv hrun
  obtain ⟨hat_st, htr₁'⟩ := getLocalState_tr_some_inv hst; rw [htr₁'] at htr₁; subst tr₁
  obtain ⟨msg, tr₂, hmsg, htr₂, hr2, _⟩ := bind_some_inv hr1
  obtain ⟨raw, hat_msg, hparse, _, htr₂'⟩ := receiveSignalMsg_some_inv hmsg; rw [htr₂'] at htr₂; subst tr₂
  -- Identify inp in stepView
  dsimp only [stepView] at hv_eq
  rw [ite_eq_left_iff.mpr (fun h => absurd hok h)] at hv_eq
  dsimp only [decVis] at hv_eq
  rw [getMessageSentAt_of_at?_net hat_msg] at hv_eq
  dsimp only [Option.map, Option.toList] at hv_eq
  simp only [List.cons_append] at hv_eq
  have hinp_eq : inp = ⟨.recv, [raw],
      if runWrapped ev then .preKeyInner (sessionBaseKeys tr stH) else .whisper, none⟩ :=
    (List.cons.inj (hv_split.symm.trans hv_eq)).1
  subst hinp_eq
  -- Invert ensureReceiverChain + consumeMessageKey + spqrRecv + verifyMacAndDecrypt
  obtain ⟨⟨st', c, ratcheted⟩, tr₃, herc, _, hr3, _⟩ := bind_some_inv hr2
  dsimp only at hr3
  rcases hcons : consumeMessageKey c msg.counter with _ | ⟨seed, c'⟩ <;> rw [hcons] at hr3
  · simp [Traceful.run_failure] at hr3
  · dsimp only at hr3
    rcases hrecv : DY.Spqr.spqrRecv st'.spqr msg.pqRatchet idx with _ | ⟨spqr', key⟩ <;> rw [hrecv] at hr3
    · simp [Traceful.run_failure] at hr3
    · dsimp only at hr3
      obtain ⟨_, _, _, _, hr4, _⟩ := bind_some_inv hr3
      obtain ⟨pq, _, _, _, hr5, _⟩ := bind_some_inv hr4
      obtain ⟨_, _, hvmd, _, _, _⟩ := bind_some_inv hr5
      unfold DY.Libsignal.TripleRatchet.verifyMacAndDecrypt at hvmd
      obtain ⟨_, _, hgd_mac, _, _, _⟩ := bind_some_inv hvmd
      have hmac : msg.mac = computeMac (trMsgKeys pq seed).macKey st'.peerIk st'.myIk msg.wire :=
        guard_some_inv hgd_mac
      refine ⟨st, raw, msg, hme, hat_st, hat_msg, hparse, hrf, ?_⟩
      rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at herc
      unfold recvChainFor at herc
      rcases hfind : findRecvChain st.recv msg.ratchetKey with _ | c0 <;> rw [hfind] at herc
      · dsimp only at herc
        by_cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey
        · rw [if_pos' hlo] at herc; simp [Traceful.run_failure] at herc
        · have hlo_f : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey = false := by
            cases hx : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;> simp [hx] at hlo ⊢
          have herc_rat := (Runs.ensureReceiverChain_ratchet (tr := tr) hfind hlo_f).1
          rw [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor] at herc_rat
          unfold recvChainFor at herc_rat
          rw [hfind] at herc_rat; dsimp only at herc_rat
          have hpair := Option.some.inj (herc.symm.trans herc_rat)
          have hrs_eq : ratchetState st msg.ratchetKey (rnd tr.length 32) = (st', c) := by
            injection hpair with hst' hp2
            injection hp2 with hc _
            exact Prod.ext hst'.symm hc.symm
          exact Or.inr ⟨st', c, seed, c', pq, rfl, hrs_eq, hcons, hmac⟩
      · dsimp only at herc
        rw [Traceful.run_pure] at herc
        injection herc with hpair
        injection hpair with hst' hp2
        injection hp2 with hc _
        subst hst'; subst hc
        exact Or.inl ⟨c0, seed, c', pq, rfl, hcons, hmac⟩

/-! ## 5. Shared 3-Step Prefix (`[ev0, ev1, ev2]`) Unpacker -/

structure ThreeStepsOut (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (restEvs : List CliEvent)
    (tr₂ trB : ExecTrace) (cl₁ : Nat)
    (ek₂ ct₂ : DY.Bytes) (keys₂ : HandshakeKeys) (msg₂ : TRSignalMsg)
    (seed₂ pq₂ m₂ key₂ : DY.Bytes) (st'₂ stB₁ : TRState) (c₂ c'₂ : RecvChain)
    (ss₃ : List Step) (vs₃ : List VisEntry) : Prop where
  trB_def : trB = bobTr0 tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂
  run_eq : runTrace r ss = runSteps ss₃ trB
  hm₃ : MatchesEventsAt compI7003 r S g (some (bundlePreKeyIds bun0Raw)) trB ss₃ restEvs vs₃
  swf₃ : StepsWF ss₃ trB
  gwf₃ : GhostWF g vs₃
  sem₂ : SemPinned2 S cl₁
  pinB : BobPin2 S g tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂
  noSk : NoSkippedKeys trB
  ek_mem : ek₂ ∈ bobDoneBaseKeys trB
  bob_st : ∀ i st, trB.at? i = some (StT "bob" st) → i = tr₂.length + 8 ∧ st = stB₁
  alice_st : ∀ i st, trB.at? i = some (StT "alice" st) →
    gamma compI7003 S g st.myIk = ecKey (compPubOfIdx 0) ∧
    gamma compI7003 S g st.peerIk = ecKey (compPubOfIdx 1)
  ppk_bob : ∀ pre₃, (∀ x ∈ pre₃, x.cls = .invisible) →
    pendingPreKey (runSteps pre₃ trB) (tr₂.length + 8) = none

theorem unpack_3_steps
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    {ev1 ev2 : RunEvent} {restEvs : List CliEvent}
    {pt1Bytes out1Bytes pt2Bytes ct1Bytes wire1Bytes mac1Bytes msg1Bytes : HwBytes}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hev1_party : ev1.party = "alice")
    (hev1_cmd : ev1.cmd = .send peerAddrBob)
    (hev1_inp : ev1.input = pt1Bytes)
    (hev1_coins : ev1.coins = coins1Bytes)
    (hev1_exit : ev1.exit = some (0, out1Bytes))
    (hwrap1 : runWrapped ev1 = true)
    (hout1_wire : out1Bytes = preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0))
      (compPubOfIdx 3) kyberCt0Bytes msg1Bytes)
    (hmsg1_len : msg1Bytes.length = 159)
    (hmsg1_split : msg1Bytes = wire1Bytes ++ mac1Bytes)
    (hmac1_len : mac1Bytes.length = 8)
    (hmac1_eq : (ByteSpecs.hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wire1Bytes)).take 8 = mac1Bytes)
    (hmac1_untag : (ByteSpecs.hmacWith F7 macKey1Bytes
      (ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wire1Bytes)).take 4 ≠ compTag4)
    (haes1_eq : compAesPerm encKey1Bytes iv1Bytes pt1Bytes = ct1Bytes)
    (htr1_wire : trWireBytes addr1Bytes DY.Libsignal.Refinement.canonicalVariation
      (DY.Libsignal.Refinement.WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ct1Bytes)
      pqMsg1Bytes = wire1Bytes)
    (hev2_party : ev2.party = "bob")
    (hev2_cmd : ev2.cmd = .recv peerAddrAlice)
    (hev2_inp : ev2.input = out1Bytes)
    (hev2_coins : ev2.coins = coins2Bytes)
    (hev2_exit : ev2.exit = some (0, pt2Bytes))
    (hchk2 : Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.checkPreKey7003
      out1Bytes msg1Bytes wire1Bytes mac1Bytes ct1Bytes pqMsg1Bytes = true)
    (hex : Explains compI7003 r S g ss vis (.run ev0 :: .run ev1 :: .run ev2 :: restEvs)) :
    ∃ tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂ c'₂ ss₃ vs₃,
      ThreeStepsOut r S g ss restEvs tr₂ trB cl₁ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂
        st'₂ stB₁ c₂ c'₂ ss₃ vs₃ := by
  obtain ⟨hgs, hgwf, ⟨_, _, hswf, _⟩, hm⟩ := hex
  have hrun_split : ∀ (a b : List Step) (t : ExecTrace), runSteps (a ++ b) t = runSteps b (runSteps a t) := by
    intro a b t; induction a generalizing t with
    | nil => rfl
    | cons x xs ih => exact ih (x.next t)
  -- Step 0 (ev0)
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, rfl, rfl, hinv₀, hrm₀, hm₁⟩ :=
    matchesEventsAt_run_exit0_inv (rfl : Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.ev0.exit =
      some (0, Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.out0Raw)) hm
  obtain ⟨hgwf₀, hgwf_rest₁⟩ := ghostWF_append hgwf
  obtain ⟨_, _, _, hswf₁⟩ := (stepsWF_append pre₀ (s₀ :: ss₁) (setupTrace r)).mp hswf
  obtain ⟨spkPk, pqPk, hnext₀, hpin₀⟩ := pin_step0_init hf hgs hgwf₀ hinv₀ hrm₀
  -- Step 1 (ev1)
  obtain ⟨pre₁, s₁, ss₂, v₁, vs₂, rfl, rfl, hinv₁, hrm₁, hm₂⟩ :=
    matchesEventsAt_run_exit0_inv hev1_exit hm₁
  obtain ⟨hgwf₁, hgwf_rest₂⟩ := ghostWF_append hgwf_rest₁
  rw [hnext₀] at hswf₁ hrm₁ hm₂
  obtain ⟨_, _, hs₁_lok, hswf₂⟩ := (stepsWF_append pre₁ (s₁ :: ss₂) _).mp hswf₁
  have htr₀_trNone : ∀ i, ((runSteps pre₀ (setupTrace r)).at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState TRState))) = none := by
    intro i; rw [runSteps_invisible_at?_trState hinv₀, setupTrace_eq_7003 hf, setupTr4_trState_none]
  have htr₀_compNone : ∀ i, ((runSteps pre₀ (setupTrace r)).at? i :
      Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none := by
    intro i; rw [runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₀, setupTrace_eq_7003 hf, setupTr4_compEvent_none]
  obtain ⟨cl₁, hsem₂, hnext₁⟩ := pin_step1_encrypt hf hpin₀ htr₀_trNone htr₀_compNone
    hgwf₁ hinv₁ hs₁_lok hev1_party hev1_cmd hev1_inp hev1_coins hev1_exit hwrap1 hout1_wire
    hmsg1_len hmsg1_split hmac1_len hmac1_eq hmac1_untag haes1_eq htr1_wire hrm₁
  -- Step 2 (ev2)
  have hnb₁ : nextBundleIds (nextBundleIds none Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.ev0) ev1 =
      some (bundlePreKeyIds Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.bun0Raw) := by
    dsimp only [nextBundleIds]; rw [hev1_cmd]; rfl
  rw [hnb₁, hnext₁] at hm₂
  rw [hnext₁] at hswf₂
  obtain ⟨pre₂, s₂, ss₃, v₂, vs₃, rfl, rfl, hinv₂, hrm₂, hm₃⟩ :=
    matchesEventsAt_run_exit0_inv hev2_exit hm₂
  obtain ⟨hgwf₂, hgwf₃⟩ := ghostWF_append hgwf_rest₂
  obtain ⟨_, _, _, hswf₃⟩ := (stepsWF_append pre₂ (s₂ :: ss₃) _).mp hswf₂
  set tr₀ := runSteps pre₀ (setupTrace r)
  set trA := aliceTr tr₀ "alice" "bob" (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk
  set oA := aliceOut tr₀ (randTerm 0 32) (DY.DiffieHellman.dhPk (randTerm 5 32)) spkPk pqPk
  set stA₀ := aliceSt "bob" oA (randTerm (tr₀.length + 2) 32)
  set tr₁ := runSteps pre₁ trA
  set trE := encTrCl tr₁ "alice" (tr₀.length + 8) stA₀ cl₁
  set tr₂ := runSteps pre₂ trE
  have htr₂_bobDone : bobDoneBaseKeys tr₂ = [] := by
    rw [runSteps_invisible_bobDoneBaseKeys hinv₂, encTrCl_bobDone_eq,
        runSteps_invisible_bobDoneBaseKeys hinv₁, aliceTr_bobDone_eq,
        runSteps_invisible_bobDoneBaseKeys hinv₀, setupTrace_eq_7003 hf, setupTr4_bobDone_nil]
  have htr₂_pqState : ∀ i, (tr₂.at? i :
      Option (DY.PersistentGlobalState.State.ExecEntryT
        (DY.PersistentLocalState.LocalState PQXDHState))) =
      (b1_setupTr4 "alice" "bob").at? i := by
    intro i
    rw [runSteps_invisible_at?_pqxdhState hinv₂, encTrCl_pqxdhState_eq,
        runSteps_invisible_at?_pqxdhState hinv₁, aliceTr_pqxdhState_eq,
        runSteps_invisible_at?_pqxdhState hinv₀, setupTrace_eq_7003 hf]
  have htr₂_regA : ∀ i ik vk hon,
      (tr₂.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some (EvP (.IdentityRegistered "alice" ik vk hon)) →
      ik = DY.DiffieHellman.dhPk (randTerm 0 32) := by
    intro i ik vk hon hat
    rw [runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₂, encTrCl_pqxdhEvent_eq,
        runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₁, aliceTr_pqxdhEvent_eq] at hat
    split at hat
    · simp [EvP] at hat
    · rw [runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₀, setupTrace_eq_7003 hf, setupTr4_pqxdhEvent_eq] at hat
      by_cases h18 : i = 18 <;> simp [h18, EvP] at hat
      by_cases h12 : i = 12 <;> simp [h12, EvP] at hat
      by_cases h6 : i = 6 <;> simp [h6, EvP] at hat
      by_cases h1 : i = 1 <;> simp [h1, EvP] at hat
      exact hat.1.symm
  obtain ⟨ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂, hnext₂, hpinB⟩ :=
    pin_step2_bobStart hf hgs hgwf₂ htr₂_bobDone htr₂_pqState htr₂_regA
      hev2_party hev2_cmd hev2_inp hev2_coins hev2_exit hchk2 hrm₂
  have hnb₂ : nextBundleIds (some (bundlePreKeyIds Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.bun0Raw)) ev2 =
      some (bundlePreKeyIds Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003.bun0Raw) := by
    dsimp only [nextBundleIds]; rw [hev2_cmd]
  rw [hnb₂, hnext₂] at hm₃
  rw [hnext₂] at hswf₃
  set trB := bobTr0 tr₂ ek₂ ct₂ keys₂ msg₂ seed₂ pq₂ m₂ key₂ st'₂ stB₁ c₂
  refine ⟨tr₂, trB, cl₁, ek₂, ct₂, keys₂, msg₂, seed₂, pq₂, m₂, key₂, st'₂, stB₁, c₂, c'₂, ss₃, vs₃,
    ⟨rfl, ?_, hm₃, hswf₃, hgwf₃, hsem₂, hpinB, ?_, bobTr0_bobDone_mem .., ?_, ?_, ?_⟩⟩
  · unfold runTrace
    rw [hrun_split pre₀, runSteps, hnext₀, hrun_split pre₁, runSteps, hnext₁,
        hrun_split pre₂, runSteps, hnext₂]
  · refine noSkippedKeys_bobTr0 (noSkippedKeys_runSteps_invisible hinv₂
      (noSkippedKeys_encTrCl (noSkippedKeys_runSteps_invisible hinv₁
        (noSkippedKeys_aliceTr (noSkippedKeys_runSteps_invisible hinv₀ ?_)))))
    rw [setupTrace_eq_7003 hf]; exact noSkippedKeys_setupTr4
  · intro i st hat
    rw [bobTr0_trState_eq] at hat
    split at hat
    · next heq =>
      injection hat with h1; injection h1 with h2; injection h2 with _ hst
      exact ⟨heq, hst.symm⟩
    · rw [runSteps_invisible_at?_trState hinv₂, encTrCl_trState_eq] at hat
      split at hat
      · simp [StT] at hat
      · rw [runSteps_invisible_at?_trState hinv₁, aliceTr_trState_eq] at hat
        split at hat
        · simp [StT] at hat
        · rw [htr₀_trNone] at hat; cases hat
  · intro i st hat
    rw [bobTr0_trState_eq] at hat
    split at hat
    · simp [StT] at hat
    · rw [runSteps_invisible_at?_trState hinv₂, encTrCl_trState_eq] at hat
      split at hat
      · injection hat with h1; injection h1 with h2; injection h2 with _ hst
        subst st
        exact ⟨hpin₀.myIk_eq, hpin₀.peerIk_eq⟩
      · rw [runSteps_invisible_at?_trState hinv₁, aliceTr_trState_eq] at hat
        split at hat
        · injection hat with h1; injection h1 with h2; injection h2 with _ hst
          subst st
          exact ⟨hpin₀.myIk_eq, hpin₀.peerIk_eq⟩
        · rw [htr₀_trNone] at hat; cases hat
  · intro pre₃ hinv₃
    unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    rw [runSteps_invisible_at?_trState hinv₃, bobTr0_trState_eq, if_pos' rfl]
    dsimp only [Option.map, StT]
    split
    · rfl
    · unfold sessionHandshakeEvents
      rw [List.findSome?_eq_none_iff]
      intro ev_pq hmem_pq
      obtain ⟨j, _, hj_eq⟩ := List.mem_filterMap.mp hmem_pq
      rw [runSteps_invisible_getEventAt_comp hinv₃, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
          bobTr0_compEvent_eq] at hj_eq
      by_cases hj5 : j = tr₂.length + 5
      · subst hj5
        simp only [↓reduceIte, hpinB.sid_eq] at hj_eq
        rw [runSteps_invisible_getEventAt_pqxdh hinv₃, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
            bobTr0_pqxdhEvent_eq, if_pos' rfl] at hj_eq
        dsimp only [Option.map, EvP] at hj_eq
        cases hj_eq
        rfl
      · rw [if_neg' hj5, runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₂, encTrCl_compEvent_eq,
            runSteps_invisible_at?_nonNet (fun _ => rfl) hinv₁, aliceTr_compEvent_eq] at hj_eq
        by_cases hj7 : j = tr₀.length + 7
        · subst hj7
          simp only [↓reduceIte] at hj_eq
          have hme_ne : ((aliceSt "bob" oA (rnd (tr₀.length + 2) 32)).sessionInfo "alice") ≠
              stB₁.sessionInfo "bob" := by
            intro heq
            have h := congrArg DY.Libsignal.TripleRatchet.SessionInfo.me heq
            dsimp [DY.Libsignal.TripleRatchet.DRState.sessionInfo] at h
            exact absurd h (by decide)
          rw [if_neg' hme_ne] at hj_eq
          cases hj_eq
        · rw [if_neg' hj7, htr₀_compNone] at hj_eq
          cases hj_eq

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
