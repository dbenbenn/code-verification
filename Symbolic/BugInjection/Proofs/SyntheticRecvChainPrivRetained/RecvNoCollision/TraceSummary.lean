/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Parse
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Schedule
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

/-!
# Closed-Form Clean Prefix Summaries (`TraceSummary.lean`)

Evaluates `runTrace r0 (ssClean cls k)`, `storedStates`, `availableStates`, `storedSecrets`,
`skippedStoredEvents`, `honestSaltsOf`, `bobTrials`, `storedRatchetKeys`, and `whisperTrials`
at `k = 2` (Call 2 PreKey `recv`) and `k = 4` (Call 4 Whisper `recv`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes Participant Trace ExecTrace ExecTraceTypes TraceEntryHas)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk kemEncap kemDecap)
open DY.Libsignal.PQXDH (PQXDHEvent errToOption agree serializedIk pqxdhIkm pqxdhKdf)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg TREvent RecvChain SessionInfo messageVersion u32Max spqrB2A
   kdfCk createChain recvChainFor findRecvChain consumeMessageKey skippedSeeds parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry PreKeyFields PreKeyRep TrialCtx
   preKeySpqrIndex setupTrace setupPublic setupSecret runTrace runSteps newIndices
   storedStates availableStates storedSecrets honestKeysOf honestSaltsOf
   ownKeys bobTrials whisperTrials storedRatchetKeys ReselectCollisionOn gamma)
open Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber (kemDecap_kemEncap)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs RndE NetE EvP EvT StT rnd encMsg encSt encSig parse_encMsg
   bobSt0 ratchetState agree_comm createChain_comm)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB bh1 kh1 o1 keys1 dhsA stA0
   t1 t2 t3 t4 t5 t1_length t2_length t3_length t4_length t5_length)
open Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
  (setupPublic_0 setupPublic_2 setupSecret_1 setupSecret_2)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprHooks0 rcprCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (encTrGen encTrGen_length
   pt0Clean coins0Clean key0Clean pqm0Clean stA1Clean m0Clean trClean2 trClean2_length
   dhsB1Clean stB20Clean stB20'Clean cBClean cB'Clean stB2Clean trClean3 trClean3_length
   pt1Clean coins1Clean key1Clean stB3Clean m1Clean trClean4
   cA0Clean s0Clean s1Clean s2Clean s3Clean ssClean
   s0_next_ok s1_next_ok s2_next_ok s3_next_ok runSteps_ssClean)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
  (r0 setupTrace_r0_eq_t4 storedStates_eq_r0 availableStates_eq_r0
   setupSecret_r0_4 pqSecretsList)

/-! ## 1. Generic `ExecTrace` Append Combinators -/

private theorem length_append {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (e : E) :
    (tr.append e).length = tr.length + 1 := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]

private theorem at?_append_of_lt {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append]; omega
  simp only [Trace.at?, hi, hi', ↓reduceDIte]
  rw [← Trace.at_le tr (tr.append e) i hi (Trace.append_le tr e)]

private theorem at?_append_self {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem at?_append_eq {E1 E2 : Type} [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E2) =
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  subst hi; exact at?_append_self tr e

private theorem range_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [length_append, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

private theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
    [ExecTraceTypes.Has E1] [ExecTraceTypes.Has E2]
    (tr₀ tr : ExecTrace) (e : E1) (f : Nat → Option E2 → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((newIndices tr₀ (tr.append e)).filterMap fun i => f i ((tr.append e).at? i)) =
      ((newIndices tr₀ tr).filterMap fun i => f i (tr.at? i)) ++
      (f tr.length (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  unfold newIndices
  rw [length_append, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hilt : i < tr.length := by
    have hm := List.mem_range'.mp hi
    omega
  rw [at?_append_of_lt tr e hilt]

def skippedStoredEvents (tr : ExecTrace) : List (SessionInfo × Bytes × UInt32 × Bytes) :=
  (List.range tr.length).filterMap fun i =>
    match tr.getEventAt TREvent i with
    | some (.SkippedKeyStored s pk n seed _ _) => some (s, pk, n, seed)
    | _ => none

private def isNotSkippedEvent (o : Option (DY.ProtocolEvent.ExecEntryT TREvent)) : Bool :=
  match o with
  | none => true
  | some x =>
    match x.ev with
    | .SkippedKeyStored .. => false
    | _ => true

private theorem skippedStoredEvents_nil : skippedStoredEvents Trace.nil = [] := by
  rw [skippedStoredEvents, Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem skippedStoredEvents_append {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    skippedStoredEvents (tr.append e) =
      skippedStoredEvents tr ++
      (match (tr.append e).getEventAt TREvent tr.length with
       | some (.SkippedKeyStored s pk n seed _ _) => [(s, pk, n, seed)]
       | _ => []) := by
  unfold skippedStoredEvents
  rw [length_append, List.range_succ, List.filterMap_append]
  congr 1
  · apply List.filterMap_congr
    intro i hi
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1,
      at?_append_of_lt tr e (List.mem_range.mp hi)]
  · cases hge : (tr.append e).getEventAt TREvent tr.length with
    | none => simp [hge]
    | some ev => cases ev <;> simp [hge]

private theorem skippedStoredEvents_append_non {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1)
    (h : isNotSkippedEvent
           (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
             Option (DY.ProtocolEvent.ExecEntryT TREvent)) = true) :
    skippedStoredEvents (tr.append e) = skippedStoredEvents tr := by
  rw [skippedStoredEvents_append, Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, at?_append_self]
  cases hproj : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option (DY.ProtocolEvent.ExecEntryT TREvent)) with
  | none => simp only [List.append_nil]
  | some x =>
    rw [hproj] at h
    unfold isNotSkippedEvent at h
    dsimp only at h ⊢
    generalize x.ev = ev at h ⊢
    cases ev <;> first | (dsimp only; exact List.append_nil _) | cases h

private theorem storedSecrets_nil : storedSecrets Trace.nil = [] := by
  unfold storedSecrets
  simp [Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem storedSecrets_append_pub {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    storedSecrets (tr.append e) =
      storedSecrets tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)))).map
        fun x => DY.Comparse.serialize x.st).toList := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map]
  exact range_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))
    tr e (fun o => o.map (DY.Comparse.serialize ∘ (·.st)))

private theorem storedStates_append_pub {E1 : Type} [ExecTraceTypes.Has E1]
    (tr : ExecTrace) (r : ProtocolSetup) (e : E1)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) =
      storedStates r tr ++
      (((TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState TRState)))).map (·.st)).toList := by
  unfold storedStates
  exact newIndices_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState))
    (setupTrace r) tr e (fun _ o => o.map (·.st)) hle

private theorem storedSecrets_encTrGen (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    storedSecrets (encTrGen tr me stH cl st pq) = storedSecrets tr := by
  simp only [encTrGen, storedSecrets_append_pub]
  repeat erw [List.append_nil]

private theorem skippedStoredEvents_encTrGen (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    skippedStoredEvents (encTrGen tr me stH cl st pq) = skippedStoredEvents tr := by
  unfold encTrGen; dsimp only
  repeat rw [skippedStoredEvents_append_non _ _ rfl]

private theorem storedStates_encTrGen (r : ProtocolSetup) (tr : ExecTrace) (me : Participant)
    (stH cl : Nat) (st : TRState) (pq : Bytes)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (encTrGen tr me stH cl st pq) =
      storedStates r tr ++ [⟨me, encSt st (rnd (tr.length + 1) cl)⟩] := by
  unfold encTrGen; dsimp only
  repeat rw [storedStates_append_pub _ r _ (by simp -failIfUnchanged only [length_append]; omega)]
  repeat erw [List.append_nil]
  rfl

private theorem encTrGen_getMessageSentAt_pq (tr : ExecTrace) (me : Participant) (stH cl : Nat)
    (st : TRState) (pq : Bytes) :
    (encTrGen tr me stH cl st pq).getMessageSentAt (tr.length + 2) =
      some (DY.Spqr.spqrSend st.spqr (rnd (tr.length + 1) cl)).2.1 := by
  rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
  unfold encTrGen; dsimp only
  repeat rw [at?_append_of_lt _ _ (by simp only [length_append]; omega)]
  rw [at?_append_eq _ _ (by simp only [length_append])]; rfl

/-! ## 2. Closed-Form `t4`, `t5`, `trClean2`, and `trClean4` Evaluations -/

private theorem t1_t2_t3_t4_closed :
    t1 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr Trace.nil "alice" ∧
    t2 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr t1 "bob" ∧
    t3 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr t2 "bob" ikB ∧
    t4 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr t3 "bob" ikB := by
  have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have someEventB_nil : ∀ p : PQXDHEvent → Bool,
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent Trace.nil p = false := fun p => by
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?, nil_len]; rfl
  have someEventB_non : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
      (p : PQXDHEvent → Bool),
      (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) = none →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent (tr.append x) p = false := by
    intro E _ tr x p hnone h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [length_append, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr x (List.mem_range.mp hi)]
      exact h i hi
    · rw [at?_append_self, hnone]
  have someEventB_ev : ∀ (tr : ExecTrace) (ev : PQXDHEvent)
      (p : PQXDHEvent → Bool), p ev = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent (tr.append (EvP ev)) p = false := by
    intro tr ev p hp h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [length_append, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr (EvP ev) (List.mem_range.mp hi)]
      exact h i hi
    · rw [Trace.at?_append]; exact hp
  have ht1 : t1 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr Trace.nil "alice" :=
    (Runs.registerIdentity (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2
  have ht2 : t2 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr t1 "bob" := by
    refine (Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_nil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [t1_length]
    exact at?_append_eq _ _ (by simp only [length_append, t1_length])
  have ht3 : t3 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr t2 "bob" ikB :=
    (Runs.genSignedPrekey hb2).2
  have hb3 : t3.at? 9 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .identity, sk := ikB }) := by
    rw [ht3]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr]
    repeat rw [at?_append_of_lt _ _ (by simp only [length_append, t2_length]; omega)]
    exact hb2
  have ht4 : t4 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr t3 "bob" ikB :=
    (Runs.genPQPrekey hb3).2
  exact ⟨ht1, ht2, ht3, ht4⟩

theorem storedSecrets_t5 : storedSecrets t5 = pqSecretsList := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t1_t2_t3_t4_closed
  have hs4 : storedSecrets t4 = pqSecretsList := by
    rw [ht4, ht3, ht2, ht1]
    simp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr,
      storedSecrets_append_pub, storedSecrets_nil, length_append,
      Symbolic.DYBridge.DY.Trace.length_eq_1]
    rfl
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat rw [storedSecrets_append_pub]
  rw [hs4]
  repeat erw [List.append_nil]

theorem storedStates_t5 : storedStates r0 t5 = [⟨"alice", stA0⟩] := by
  have h0 : storedStates r0 t4 = [] := by
    rw [← setupTrace_r0_eq_t4]
    simp [storedStates]
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  have hdhs : rnd (t4.length + 2) 32 = rnd 24 32 := by rw [t4_length]
  rw [hdhs]
  repeat rw [storedStates_append_pub _ r0 _
    (by simp -failIfUnchanged only [setupTrace_r0_eq_t4, length_append, t4_length]; omega)]
  rw [h0]
  repeat erw [List.append_nil]
  rfl

theorem skippedStoredEvents_t5 : skippedStoredEvents t5 = [] := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t1_t2_t3_t4_closed
  have hs1 : skippedStoredEvents t1 = [] := by
    rw [ht1]; unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact skippedStoredEvents_nil
  have hs2 : skippedStoredEvents t2 = [] := by
    rw [ht2]; unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact hs1
  have hs3 : skippedStoredEvents t3 = [] := by
    rw [ht3]; unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact hs2
  have hs4 : skippedStoredEvents t4 = [] := by
    rw [ht4]; unfold Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact hs3
  dsimp only [t5, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt]
  repeat rw [skippedStoredEvents_append_non _ _ rfl]
  exact hs4

theorem summary_at_2 (cls : Nat → Nat) :
    runTrace r0 (ssClean cls 2) = trClean2 cls ∧
    storedStates r0 (trClean2 cls) = [⟨"alice", stA0⟩, ⟨"alice", stA1Clean cls⟩] ∧
    storedSecrets (trClean2 cls) = pqSecretsList ∧
    honestSaltsOf r0 (ssClean cls 2) = [DY.Spqr.zeroKey, key0Clean cls] := by
  have htr : runTrace r0 (ssClean cls 2) = trClean2 cls := by
    unfold runTrace; rw [setupTrace_r0_eq_t4, (runSteps_ssClean cls).2.2.1]
  have hmin0 : (setupTrace r0).length ≤ t5.length := by
    rw [setupTrace_r0_eq_t4, t4_length, t5_length]; omega
  have hst : storedStates r0 (trClean2 cls) = [⟨"alice", stA0⟩, ⟨"alice", stA1Clean cls⟩] := by
    unfold trClean2
    rw [storedStates_encTrGen r0 t5 "alice" 30 (cls 0) stA0 _ hmin0, storedStates_t5, t5_length]
    rfl
  have hsec : storedSecrets (trClean2 cls) = pqSecretsList := by
    unfold trClean2
    rw [storedSecrets_encTrGen, storedSecrets_t5]
  have hsalts : honestSaltsOf r0 (ssClean cls 2) = [DY.Spqr.zeroKey, key0Clean cls] := by
    have hss : ssClean cls 2 = [s0Clean, s1Clean cls] := rfl
    rw [hss]; unfold honestSaltsOf
    rw [setupTrace_r0_eq_t4]
    have hk0 : honestKeysOf t4 [s0Clean, s1Clean cls] =
        honestKeysOf (s0Clean.next t4) [s1Clean cls] := rfl
    rw [hk0, (s0_next_ok).1]
    have hk1 : honestKeysOf t5 [s1Clean cls] = [key0Clean cls] := by
      have hk1_nil : honestKeysOf t5 [s1Clean cls] = ((s1Clean cls).publishedSpqrKey? t5).toList := by
        change ((s1Clean cls).publishedSpqrKey? t5).toList ++ [] = _
        exact List.append_nil _
      rw [hk1_nil]
      unfold Step.publishedSpqrKey?
        DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx
        DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx
      have hs1_def : s1Clean cls = .messageEncrypt "alice" 30 (cls 0) 33 := rfl
      rw [hs1_def]; dsimp only
      rw [← hs1_def, (s1_next_ok cls).1]
      have hne : ¬ (33 = t5.length + 3) := by rw [t5_length]; omega
      simp only [hne, ↓reduceIte]
      have hpq0 := encTrGen_getMessageSentAt_pq t5 "alice" 30 (cls 0) stA0 (key0Clean cls)
      rw [t5_length] at hpq0 ⊢
      unfold trClean2; rw [hpq0]; rfl
    rw [hk1]
  exact ⟨htr, hst, hsec, hsalts⟩

theorem summary_at_4 (cls : Nat → Nat) :
    runTrace r0 (ssClean cls 4) = trClean4 cls ∧
    storedStates r0 (trClean4 cls) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1Clean cls⟩, ⟨"bob", stB2Clean cls⟩, ⟨"bob", stB3Clean cls⟩] ∧
    storedSecrets (trClean4 cls) = pqSecretsList ∧
    skippedStoredEvents (trClean4 cls) = [] ∧
    honestSaltsOf r0 (ssClean cls 4) = [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls] := by
  obtain ⟨_, hst2, hsec2, _⟩ := summary_at_2 cls
  have htr : runTrace r0 (ssClean cls 4) = trClean4 cls := by
    unfold runTrace; rw [setupTrace_r0_eq_t4, (runSteps_ssClean cls).2.2.2.2.1]
  have hst3 : storedStates r0 (trClean3 cls) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1Clean cls⟩, ⟨"bob", stB2Clean cls⟩] := by
    unfold trClean3; dsimp only
    repeat rw [storedStates_append_pub _ r0 _
      (by simp -failIfUnchanged only [setupTrace_r0_eq_t4, length_append,
            trClean2_length, t4_length]; omega)]
    rw [hst2]
    repeat erw [List.append_nil]
    rfl
  have hmin3 : (setupTrace r0).length ≤ (trClean3 cls).length := by
    rw [setupTrace_r0_eq_t4, t4_length, trClean3_length]; omega
  have hst4 : storedStates r0 (trClean4 cls) =
      [⟨"alice", stA0⟩, ⟨"alice", stA1Clean cls⟩, ⟨"bob", stB2Clean cls⟩, ⟨"bob", stB3Clean cls⟩] := by
    unfold trClean4
    rw [storedStates_encTrGen r0 (trClean3 cls) "bob" 46 (cls 1) (stB2Clean cls) _ hmin3,
        hst3, trClean3_length]
    rfl
  have hsec3 : storedSecrets (trClean3 cls) = pqSecretsList := by
    unfold trClean3; dsimp only
    repeat rw [storedSecrets_append_pub]
    rw [hsec2]
    repeat erw [List.append_nil]
  have hsec4 : storedSecrets (trClean4 cls) = pqSecretsList := by
    unfold trClean4; rw [storedSecrets_encTrGen, hsec3]
  have hskip2 : skippedStoredEvents (trClean2 cls) = [] := by
    unfold trClean2; rw [skippedStoredEvents_encTrGen, skippedStoredEvents_t5]
  have hskip3 : skippedStoredEvents (trClean3 cls) = [] := by
    unfold trClean3; dsimp only
    repeat rw [skippedStoredEvents_append_non _ _ rfl]
    exact hskip2
  have hskip4 : skippedStoredEvents (trClean4 cls) = [] := by
    unfold trClean4; rw [skippedStoredEvents_encTrGen, hskip3]
  have hsalts : honestSaltsOf r0 (ssClean cls 4) =
      [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls] := by
    have hss : ssClean cls 4 = [s0Clean, s1Clean cls, s2Clean, s3Clean cls] := rfl
    rw [hss]; unfold honestSaltsOf
    rw [setupTrace_r0_eq_t4]
    have hk0 : honestKeysOf t4 [s0Clean, s1Clean cls, s2Clean, s3Clean cls] =
        honestKeysOf (s0Clean.next t4) [s1Clean cls, s2Clean, s3Clean cls] := rfl
    rw [hk0, (s0_next_ok).1]
    have hk1 : honestKeysOf t5 [s1Clean cls, s2Clean, s3Clean cls] =
        ((s1Clean cls).publishedSpqrKey? t5).toList ++
        honestKeysOf ((s1Clean cls).next t5) [s2Clean, s3Clean cls] := rfl
    have hp1 : ((s1Clean cls).publishedSpqrKey? t5).toList = [key0Clean cls] := by
      unfold Step.publishedSpqrKey?
        DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx
        DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx
      have hs1_def : s1Clean cls = .messageEncrypt "alice" 30 (cls 0) 33 := rfl
      rw [hs1_def]; dsimp only
      rw [← hs1_def, (s1_next_ok cls).1]
      have hne1 : ¬ (33 = t5.length + 3) := by rw [t5_length]; omega
      simp only [hne1, ↓reduceIte]
      have hpq0 := encTrGen_getMessageSentAt_pq t5 "alice" 30 (cls 0) stA0 (key0Clean cls)
      rw [t5_length] at hpq0 ⊢
      unfold trClean2; rw [hpq0]; rfl
    rw [hk1, hp1, (s1_next_ok cls).1]
    have hk2 : honestKeysOf (trClean2 cls) [s2Clean, s3Clean cls] =
        honestKeysOf (s2Clean.next (trClean2 cls)) [s3Clean cls] := rfl
    rw [hk2, (s2_next_ok cls).1]
    have hk3 : honestKeysOf (trClean3 cls) [s3Clean cls] = [key1Clean cls] := by
      have hk3_nil : honestKeysOf (trClean3 cls) [s3Clean cls] =
          ((s3Clean cls).publishedSpqrKey? (trClean3 cls)).toList := by
        change ((s3Clean cls).publishedSpqrKey? (trClean3 cls)).toList ++ [] = _
        exact List.append_nil _
      rw [hk3_nil]
      unfold Step.publishedSpqrKey?
        DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx
        DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx
      have hs3_def : s3Clean cls = .messageEncrypt "bob" 46 (cls 1) 49 := rfl
      rw [hs3_def]; dsimp only
      rw [← hs3_def, (s3_next_ok cls).1]
      have hne2 : ¬ (49 = (trClean3 cls).length + 3) := by rw [trClean3_length]; omega
      simp only [hne2, ↓reduceIte]
      have hpq1 := encTrGen_getMessageSentAt_pq (trClean3 cls) "bob" 46 (cls 1) (stB2Clean cls) (key1Clean cls)
      rw [trClean3_length] at hpq1 ⊢
      unfold trClean4; rw [hpq1]; rfl
    rw [hk3]; rfl
  exact ⟨htr, hst4, hsec4, hskip4, hsalts⟩

/-! ## 3. `bobTrials` at `k = 2`, `storedRatchetKeys`, and `whisperTrials` at `k = 4` -/

def bobCtx2 (cls : Nat → Nat) (p : PreKeyFields) : TrialCtx :=
  let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys1.pqr spqrB2A)
    (pqm0Clean cls) (preKeySpqrIndex p)).map (·.2)).toList
  { peerIk := serializedIk (dhPk ikA)
    myIk := serializedIk (dhPk ikB)
    extra := [keys1.rk, keys1.ck, keys1.pqr, stA0.cks, (stA1Clean cls).cks]
    ownSalts := own
    seed? := some (kdfCk stA0.cks).2 }

theorem bobTrials_at_2 (cls : Nat → Nat) (tr : ExecTrace) (p : PreKeyFields)
    (hpId : p.preKeyId = none) :
    bobTrials r0 tr p ⟨o1.ek, o1.ct, m0Clean cls⟩
        (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean) = [] ∨
      bobTrials r0 tr p ⟨o1.ek, o1.ct, m0Clean cls⟩
        (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean) = [bobCtx2 cls p] := by
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm ProtocolSetup.ikBSecTerm ProtocolSetup.spkSecTerm ProtocolSetup.pqskSecTerm
  rw [hpId]
  dsimp only
  split
  · exact .inl rfl
  · right
    have hp0 : setupPublic r0 0 = dhPk ikA := setupPublic_0 (r := r0) (by decide)
    have hp2 : setupPublic r0 2 = dhPk ikB := setupPublic_2 (r := r0) (by decide)
    have hs1 : setupSecret r0 1 = ikB := setupSecret_1 (r := r0) (by decide)
    have hs2 : setupSecret r0 2 = spkB := setupSecret_2 (r := r0) (by decide)
    have hs4 : setupSecret r0 4 = pqskB := setupSecret_r0_4
    rw [hp0, hp2, hs1, hs2, hs4]
    have hct_eq : o1.ct = (kemEncap (kemPk pqskB) (rnd 23 32)).1 := by
      dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement]
      rw [t4_length]; rfl
    have hek_eq : o1.ek = dhPk (rnd 22 32) := by
      dsimp only [o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt]
      rw [t4_length]; rfl
    have hss : (errToOption (kemDecap pqskB o1.ct)).getD (DY.PQKem.kemRejKey pqskB o1.ct) =
        (kemEncap (kemPk pqskB) (rnd 23 32)).2 := by
      rw [hct_eq, kemDecap_kemEncap]; rfl
    rw [hss]
    have hkeys : pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB) (agree o1.ek ikB)
        (agree o1.ek spkB) (Option.map (agree o1.ek) none)
        (kemEncap (kemPk pqskB) (rnd 23 32)).2) = keys1 := by
      rw [hek_eq]
      dsimp only [Option.map, keys1, o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOutOpt,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
        DY.Libsignal.PQXDH.aliceAgreement]
      rw [t4_length]
      rw [agree_comm ikA spkB, agree_comm (rnd 22 32) ikB, agree_comm (rnd 22 32) spkB]
      rfl
    rw [hkeys]
    have hrk : (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).ratchetKey = dhPk dhsA := rfl
    have hcnt : (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).counter = 0 := rfl
    have hpqm : (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean).pqRatchet = pqm0Clean cls := rfl
    rw [hrk, hcnt, hpqm]
    have hcc : (createChain keys1.rk (dhPk dhsA) spkB).2 = stA0.cks := by
      change (createChain keys1.rk (dhPk dhsA) spkB).2 = (createChain keys1.rk (dhPk spkB) dhsA).2
      rw [createChain_comm keys1.rk dhsA spkB]
    rw [hcc]
    rfl

theorem storedRatchetKeys_trClean4 {r : ProtocolSetup} {cls : Nat → Nat} {msg : TRSignalMsg}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    {rk : Bytes} (hrk : rk ∈ storedRatchetKeys r (trClean4 cls) msg) :
    rk = dhPk spkB ∨ rk = dhPk dhsA := by
  obtain ⟨_, hst4, _, hskip4, _⟩ := summary_at_4 cls
  unfold storedRatchetKeys at hrk
  rcases List.mem_append.mp hrk with hrk1 | hrk2
  · rw [availableStates_eq_r0 hfit, availableStates, hst4] at hrk1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hrk1
    have h1 : stA0.toDRState.recv = [cA0Clean] := rfl
    have h2 : (stA1Clean cls).toDRState.recv = [cA0Clean] := rfl
    have h3 : (stB2Clean cls).toDRState.recv = [cB'Clean] := rfl
    have h4 : (stB3Clean cls).toDRState.recv = [cB'Clean] := rfl
    rw [h1, h2, h3, h4] at hrk1
    simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hrk1
    rcases hrk1 with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · obtain ⟨i, hi, hge⟩ := List.mem_filterMap.mp hrk2
    have hnone := List.filterMap_eq_nil_iff.mp hskip4 i hi
    cases hev : (trClean4 cls).getEventAt TREvent i with
    | none => rw [hev] at hge; cases hge
    | some ev => rw [hev] at hnone hge; cases ev <;> first | cases hge | cases hnone

theorem not_reselectCollisionOn_trClean4
    {r : ProtocolSetup} {cls : Nat → Nat}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis : List VisEntry} {salts : List Bytes}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hne29 : gamma rcprI0 S g (dhPk spkB) ≠ gamma rcprI0 S g (dhPk dhsB1Clean))
    (hne69 : gamma rcprI0 S g (dhPk dhsA) ≠ gamma rcprI0 S g (dhPk dhsB1Clean)) :
    ¬ ReselectCollisionOn rcprI0 r S g (trClean4 cls) vis salts (m1Clean cls) := by
  rintro ⟨msg, hparse, rk, hrk, hgamEq, _⟩
  have hp0 := parse_encMsg (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean
  change parseTrSignalMsg (m1Clean cls) = some _ at hp0
  rw [hp0] at hparse
  injection hparse with hmsg
  subst hmsg
  have hm_rk : (encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean).ratchetKey =
      dhPk dhsB1Clean := rfl
  rw [hm_rk] at hgamEq
  rcases storedRatchetKeys_trClean4 hfit hrk with rfl | rfl
  · exact hne29 hgamEq
  · exact hne69 hgamEq

private theorem consumeMessageKey_zero_zero {c : RecvChain} (h0 : c.index = 0) :
    consumeMessageKey c 0 =
      some ((kdfCk c.chainKey).2, { c with chainKey := (kdfCk c.chainKey).1, index := 1 }) := by
  unfold consumeMessageKey
  rw [h0]
  have h1 : ¬ ((0 : UInt32) < 0) := by decide
  have h3 : ¬ ((0 : UInt32) = u32Max) := by decide
  simp only [h1, h3, ↓reduceIte, Nat.sub_self]
  rfl

theorem whisperTrials_trClean4_cases
    {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hne29 : gamma rcprI0 S g (dhPk spkB) ≠ gamma rcprI0 S g (dhPk dhsB1Clean))
    (hne69 : gamma rcprI0 S g (dhPk dhsA) ≠ gamma rcprI0 S g (dhPk dhsB1Clean))
    {ctx : TrialCtx}
    (hctx : ctx ∈ whisperTrials rcprI0 r0 S g (trClean4 cls)
      (encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean)) :
    (let ck := (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2
     ctx.peerIk = serializedIk (dhPk ikB) ∧
     ctx.myIk = serializedIk (dhPk ikA) ∧
     ctx.extra = [ck, (kdfCk ck).1] ∧
     ctx.seed? = some (kdfCk ck).2) ∨
    (let ck := (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2
     ctx.peerIk = serializedIk (dhPk ikA) ∧
     ctx.myIk = serializedIk (dhPk ikB) ∧
     ctx.extra = [ck, (kdfCk ck).1] ∧
     ctx.seed? = some (kdfCk ck).2) := by
  set msg := encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean
  obtain ⟨_, hst4, _, hskip4, _⟩ := summary_at_4 cls
  unfold whisperTrials at hctx
  have hver : msg.version = messageVersion := rfl
  have hmrk : msg.ratchetKey = dhPk dhsB1Clean := rfl
  have hmctr : msg.counter = 0 := rfl
  simp only [hver, ↓reduceIte] at hctx
  obtain ⟨st, hst_mem, hctx_st⟩ := List.mem_flatMap.mp hctx
  rcases List.mem_append.mp hctx_st with hctx_ch | hctx_sk
  swap
  · obtain ⟨i, hi, hge⟩ := List.mem_filterMap.mp hctx_sk
    have hnone := List.filterMap_eq_nil_iff.mp hskip4 i hi
    cases hev : (trClean4 cls).getEventAt TREvent i with
    | none => rw [hev] at hge; cases hge
    | some ev => rw [hev] at hnone hge; cases ev <;> first | cases hge | cases hnone
  obtain ⟨c, hc_mem, hctx_eq⟩ := List.mem_map.mp hctx_ch
  rw [availableStates, hst4] at hst_mem
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hst_mem
  have hchain_extract : ∀ (st₀ : TRState) (c₀ : RecvChain),
      st₀.recv = [c₀] →
      gamma rcprI0 S g c₀.ratchetKey ≠ gamma rcprI0 S g (dhPk dhsB1Clean) →
      c ∈ (st₀.recv.filter fun x =>
            decide (gamma rcprI0 S g x.ratchetKey = gamma rcprI0 S g msg.ratchetKey)) ++
          (match findRecvChain st₀.recv msg.ratchetKey,
              DY.Libsignal.TripleRatchet.recvHalfStep st₀.toDRState msg.ratchetKey with
           | none, some (_, x) => [x]
           | _, _ => []) →
      c = { ratchetKey := dhPk dhsB1Clean,
            chainKey := (createChain st₀.rk (dhPk dhsB1Clean) st₀.dhs).2,
            index := 0, rIdx := st₀.rIdx + 2 } := by
    intro st₀ c₀ hrecv hne hmem
    have hfilt : (st₀.recv.filter fun x =>
        decide (gamma rcprI0 S g x.ratchetKey = gamma rcprI0 S g msg.ratchetKey)) = [] := by
      rw [hrecv, hmrk]; simp [hne]
    rw [hfilt, List.nil_append, hmrk] at hmem
    unfold DY.Libsignal.TripleRatchet.recvHalfStep at hmem
    cases hfind : findRecvChain st₀.recv (dhPk dhsB1Clean) with
    | some _ => rw [hfind] at hmem; cases hmem
    | none =>
      rw [hfind] at hmem; dsimp only at hmem
      cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk dhsB1Clean) with
      | true => rw [hlo] at hmem; cases hmem
      | false =>
        rw [hlo] at hmem
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hmem
        exact hmem
  rcases hst_mem with rfl | rfl | rfl | rfl
  · have hc_eq := hchain_extract stA0 cA0Clean rfl hne29 hc_mem
    rw [hc_eq, hmctr, consumeMessageKey_zero_zero rfl] at hctx_eq
    rw [← hctx_eq]
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · have hc_eq := hchain_extract (stA1Clean cls) cA0Clean rfl hne29 hc_mem
    rw [hc_eq, hmctr, consumeMessageKey_zero_zero rfl] at hctx_eq
    rw [← hctx_eq]
    exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · have hc_eq := hchain_extract (stB2Clean cls) cB'Clean rfl hne69 hc_mem
    rw [hc_eq, hmctr, consumeMessageKey_zero_zero rfl] at hctx_eq
    rw [← hctx_eq]
    exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
  · have hc_eq := hchain_extract (stB3Clean cls) cB'Clean rfl hne69 hc_mem
    rw [hc_eq, hmctr, consumeMessageKey_zero_zero rfl] at hctx_eq
    rw [← hctx_eq]
    exact Or.inr ⟨rfl, rfl, rfl, rfl⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision
