/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.CleanStepViewA
import DY.Trace.Basic
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Network

/-!
# Clean Schedule `stepView` & `visClean` Formulas (`CleanStepView.lean`)

Proves explicit `stepView` equations for `s1Clean .. s4Clean` (building on `CleanStepViewA`),
evaluates `plaintextTerms` and `.send` terms on `visClean r cls 2` and `visClean r cls 4`, and
discharges `¬ ReadCollisionCli` vacuously on `ssClean cls k` for `k ≤ 4`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision

open scoped DY.Libsignal.Composed
open DY (Bytes ExecTrace ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TREvent)
open DY.Libsignal.Composed (ComposedEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost
   setupTrace runTrace stepView bobVis decVis bobOpkPk
   pendingPreKey sessionHasDecrypted
   newIndices newRandoms received receivedPlaintext eventIdx isBobDone
   exposures pqExposureAt trExposureAt rngEntry kyberCoinEntries randTerm
   plaintextTerms runWrapped)
open DY.Libsignal.Composed.Refinement.Cli (ReadCollisionCli)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (RndE NetE EvP EvT EvC StT recvKey registerIdentityTr genSignedPrekeyTr genPQPrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB dhsA t4 t5 t4_length t5_length kh1 mh1 o1 keys1 stA0)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprHooks0 rcprCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (ev ev1_runWrapped ev3_runWrapped
   append_len le_append_of_le at?_mono at?_append_at at?_append_self_proj at?_append_of_lt
   setupTrace_eq_t4 encTrGen encTrGen_le
   pt0Clean coins0Clean key0Clean stA1Clean m0Clean trClean2 trClean2_length
   dhsB1Clean stB20'Clean seedB0Clean stB2Clean trClean3 trClean3_length
   pt1Clean coins1Clean key1Clean pqm1Clean m1Clean trClean4 trClean4_length
   dhsA1Clean stA3'Clean seedA1Clean stA4Clean trClean5 trClean5_length
   s0Clean s1Clean s2Clean s3Clean s4Clean cleanCallSteps ssClean
   s0_next_ok s1_next_ok s2_next_ok s3_next_ok s4_next_ok runSteps_ssClean)

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.ev

/-! ## 3. Explicit `stepView` Equations for `s1Clean .. s4Clean` -/

private theorem no_cev_t4 {i : Nat} : t4.getEventAt ComposedEvent i = none := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t4_tr_eqs
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) = none →
      tr.getEventAt ComposedEvent i = none →
      (tr.append e).getEventAt ComposedEvent i = none := by
    intro E _ tr e hnone h0
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h0 ⊢
    by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt]; exact h0
    · by_cases heq : i = tr.length
      · subst heq; rw [at?_append_self_proj, hnone]
      · rcases hat : ((tr.append e).at? i : Option (DY.ProtocolEvent.ExecEntryT ComposedEvent)) with _ | _
        · rfl
        · have := DY.Trace.at?_eq_some_implies_length_le
            (EntryT := DY.ProtocolEvent.ExecEntryT ComposedEvent) (tr.append e) i
          rw [hat, append_len] at this; simp at this; omega
  have hnil : (DY.Trace.nil : ExecTrace).getEventAt ComposedEvent i = none := by
    have h0 : ¬ i < (DY.Trace.nil : ExecTrace).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?, h0]
  rw [ht4]; dsimp only [genPQPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht3]; dsimp only [genSignedPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht2]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  rw [ht1]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  exact hnil

private theorem no_trev_t4 {i : Nat} : t4.getEventAt TREvent i = none := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t4_tr_eqs
  have hpeel : ∀ {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {e : E},
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none →
      tr.getEventAt TREvent i = none →
      (tr.append e).getEventAt TREvent i = none := by
    intro E _ tr e hnone h0
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h0 ⊢
    by_cases hlt : i < tr.length
    · rw [at?_append_of_lt tr e hlt]; exact h0
    · by_cases heq : i = tr.length
      · subst heq; rw [at?_append_self_proj, hnone]
      · rcases hat : ((tr.append e).at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with _ | _
        · rfl
        · have := DY.Trace.at?_eq_some_implies_length_le
            (EntryT := DY.ProtocolEvent.ExecEntryT TREvent) (tr.append e) i
          rw [hat, append_len] at this; simp at this; omega
  have hnil : (DY.Trace.nil : ExecTrace).getEventAt TREvent i = none := by
    have h0 : ¬ i < (DY.Trace.nil : ExecTrace).length := by
      rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; omega
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, DY.Trace.at?, h0]
  rw [ht4]; dsimp only [genPQPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht3]; dsimp only [genSignedPrekeyTr]
  iterate 6 refine hpeel rfl ?_
  rw [ht2]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  rw [ht1]; dsimp only [registerIdentityTr]
  iterate 5 refine hpeel rfl ?_
  exact hnil

private theorem no_receiver_mk_t5 (s : DY.Libsignal.TripleRatchet.SessionInfo) :
    ∀ j < t5.length, ∀ seed pq' n rIdx pIdx,
      t5.getEventAt TREvent j ≠ some (.MessageKey s .receiver seed pq' n rIdx pIdx) := by
  intro j hj seed pq' n rIdx pIdx hget
  rw [t5_length] at hj
  by_cases hlt : j < 22
  · rw [getEventAt_of_le TREvent t4_le_t5 (by rw [t4_length]; exact hlt), no_trev_t4] at hget
    cases hget
  · let a0 := t4
    let a1 := a0.append (RndE 32)
    let a2 := a1.append (RndE 32)
    let a3 := a2.append (RndE 32)
    let a4 := a3.append (NetE o1.ek)
    let a5 := a4.append (NetE o1.ct)
    let a6 := a5.append (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))
    let a7 := a6.append (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))
    let a8 := a7.append (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))
    have ha8 : a8 ≤ t5 := by rw [t5_def_eq]; exact DY.Trace.append_le _ _
    have ha7 : a7 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha8
    have ha6 : a6 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha7
    have ha5 : a5 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha6
    have ha4 : a4 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha5
    have ha3 : a3 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha4
    have ha2 : a2 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha3
    have ha1 : a1 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha2
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
    have hd : j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [entry_proj_none 22 ha1 t4_length.symm rfl] at hget; cases hget
    · rw [entry_proj_none 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · rw [entry_proj_none 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget; cases hget
    · have t28 : (t5.at? 28 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk)) :=
        at?_mono ha7 (at?_append_at a6 _ (by simp +zetaDelta only [append_len, t4_length]))
      rw [t28] at hget; cases hget
    · rw [entry_proj_none 29 ha8 (by simp +zetaDelta only [append_len, t4_length]) rfl] at hget
      cases hget
    · have t30 : (t5.at? 30 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) = none := by
        refine entry_proj_none (tr₀ := a8) (e := StT "alice" stA0) 30 ?_
          (by simp +zetaDelta only [append_len, t4_length]) rfl
        rw [t5_def_eq]
      rw [t30] at hget; cases hget

private theorem no_cev_lt29 {i : Nat} (hi : i < 29) :
    t5.getEventAt ComposedEvent i = none := by
  by_cases h22 : i < 22
  · rw [getEventAt_of_le ComposedEvent t4_le_t5 (by rw [t4_length]; exact h22)]
    exact no_cev_t4
  · let a0 := t4
    let a1 := a0.append (RndE 32)
    let a2 := a1.append (RndE 32)
    let a3 := a2.append (RndE 32)
    let a4 := a3.append (NetE o1.ek)
    let a5 := a4.append (NetE o1.ct)
    let a6 := a5.append (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys))
    let a7 := a6.append (EvT (.InitSession "alice" "bob" (dhPk dhsA) o1.spk))
    let a8 := a7.append (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27))
    have ha8 : a8 ≤ t5 := by rw [t5_def_eq]; exact DY.Trace.append_le _ _
    have ha7 : a7 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha8
    have ha6 : a6 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha7
    have ha5 : a5 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha6
    have ha4 : a4 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha5
    have ha3 : a3 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha4
    have ha2 : a2 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha3
    have ha1 : a1 ≤ t5 := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) ha2
    simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    have hd : i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 := by omega
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [entry_proj_none 22 ha1 t4_length.symm rfl]
    · rw [entry_proj_none 23 ha2 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 24 ha3 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 25 ha4 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 26 ha5 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 27 ha6 (by simp +zetaDelta only [append_len, t4_length]) rfl]
    · rw [entry_proj_none 28 ha7 (by simp +zetaDelta only [append_len, t4_length]) rfl]

theorem pendingPreKey_t5_eq : pendingPreKey t5 30 = some (o1.ek, o1.ct) := by
  have hat : t5.at? 30 = some (StT "alice" stA0) := by
    rw [t5_def_eq]
    exact at?_append_at _ _ (by simp only [append_len, t4_length])
  have hdec : sessionHasDecrypted t5 (stA0.sessionInfo "alice") 30 = false := by
    unfold sessionHasDecrypted
    simp only [List.any_eq_false, Bool.not_eq_true]
    intro j hj
    have hj' : j < t5.length := by rw [t5_length]; exact Nat.lt_trans (List.mem_range.mp hj) (by decide)
    split
    · next s' mk pq n rIdx pIdx hget =>
      by_cases heq : s' = stA0.sessionInfo "alice"
      · subst heq; exact absurd hget (no_receiver_mk_t5 _ j hj' _ _ _ _ _)
      · exact decide_eq_false heq
    · rfl
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt
    DY.Libsignal.Composed.Refinement.sessionHandshakeEvents
  rw [hat]; dsimp only [StT, Option.map]
  simp only [hdec, Bool.false_eq_true, ↓reduceIte]
  have hsplit : List.range t5.length = List.range 29 ++ [29, 30] := by
    rw [t5_length]; decide
  rw [hsplit, List.filterMap_append,
    List.filterMap_eq_nil_iff.mpr fun i hi => by rw [no_cev_lt29 (List.mem_range.mp hi)],
    List.nil_append, List.filterMap_cons]
  have hhs : t5.getEventAt ComposedEvent 29 =
      some (.HandshakeSession (stA0.sessionInfo "alice") 27) := by
    have hat29 : t5.at? 29 = some (EvC (.HandshakeSession (stA0.sessionInfo "alice") 27)) := by
      rw [t5_def_eq]
      exact at?_mono (DY.Trace.append_le _ _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat29, EvC]
  have had : t5.getEventAt PQXDHEvent 27 =
      some (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys) := by
    have hat27 : t5.at? 27 =
        some (EvP (.AliceDone "alice" "bob" o1.ikA o1.ikB o1.spk o1.pqpk o1.opk o1.ek o1.ct o1.keys)) := by
      rw [t5_def_eq]
      exact at?_mono (le_append_of_le (le_append_of_le (DY.Trace.append_le _ _) _) _)
        (at?_append_at _ _ (by simp only [append_len, t4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat27, EvP]
  simp [hhs, had]

theorem stepView_s1 (cls : Nat → Nat) :
    stepView (s1Clean cls) t5 true =
      ⟨.pt, [randTerm 31 32], .single, none⟩ ::
      ((if cls 0 != 0 then [rngEntry (randTerm 32 (cls 0))] else []) ++
       [⟨.send, [o1.ek, o1.ct, m0Clean cls], .preKeySend, none⟩]) := by
  obtain ⟨hn1, hok1⟩ := s1_next_ok cls
  dsimp only [s1Clean] at hn1 hok1 ⊢
  have h := encTrGen_stepView_ok (wrapped := true) hok1 hn1
  rw [t5_length, pendingPreKey_t5_eq] at h
  exact h

theorem trClean2_sent_eqs (cls : Nat → Nat) :
    (trClean2 cls).getMessageSentAt 25 = some o1.ek ∧
    (trClean2 cls).getMessageSentAt 26 = some o1.ct ∧
    (trClean2 cls).getMessageSentAt 37 = some (m0Clean cls) := by
  have h52 : t5 ≤ trClean2 cls := encTrGen_le ..
  have hat25 : (trClean2 cls).at? 25 = some (NetE o1.ek) := by
    refine at?_mono h52 ?_
    rw [t5_def_eq]
    exact at?_mono (le_append_of_le (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le _ _) _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hat26 : (trClean2 cls).at? 26 = some (NetE o1.ct) := by
    refine at?_mono h52 ?_
    rw [t5_def_eq]
    exact at?_mono (le_append_of_le (le_append_of_le
      (le_append_of_le (DY.Trace.append_le _ _) _) _) _)
      (at?_append_at _ _ (by simp only [append_len, t4_length]))
  have hat37 : (trClean2 cls).at? 37 = some (NetE (m0Clean cls)) := by
    dsimp only [trClean2, encTrGen, m0Clean, pt0Clean, coins0Clean]
    rw [t5_length]
    exact at?_append_at _ _ (by simp only [append_len, t5_length])
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat25, hat26, hat37]

theorem stepView_s2 (cls : Nat → Nat) (w : Bool) :
    stepView s2Clean (trClean2 cls) w =
      ⟨.recv, [o1.ek, o1.ct, m0Clean cls], .preKeyRecv, none⟩ ::
      [rngEntry (randTerm 38 32), ⟨.accept, [pt0Clean], .single, some 40⟩] := by
  obtain ⟨hn2, hok2⟩ := s2_next_ok cls
  obtain ⟨hek, hct, hmsg⟩ := trClean2_sent_eqs cls
  have hni : newIndices (trClean2 cls) (trClean3 cls) =
      [38, 39, 40, 41, 42, 43, 44, 45, 46] := by
    unfold newIndices; rw [trClean2_length, trClean3_length]; decide
  let b0 := trClean2 cls
  let b1 := b0.append (RndE 32)
  let b2 := b1.append (NetE (key0Clean cls))
  let b3 := b2.append (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
    (kemPk pqskB) none o1.ek o1.ct keys1))
  let b4 := b3.append (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1Clean)))
  let b5 := b4.append (EvT (.HonestDH ((stB20'Clean cls).sessionInfo "bob") dhsB1Clean 0))
  let b6 := b5.append (EvC (.HandshakeSession ((stB20'Clean cls).sessionInfo "bob") 40))
  let b7 := b6.append (EvT (.Received "bob" "alice" (dhPk dhsA) 0 pt0Clean))
  let b8 := b7.append (EvT (.MessageKey ((stB20'Clean cls).sessionInfo "bob") .receiver
    seedB0Clean (key0Clean cls) 0 2 46))
  have hb8 : b8 ≤ trClean3 cls := by dsimp only [trClean3]; exact DY.Trace.append_le _ _
  have hb7 : b7 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb8
  have hb6 : b6 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb7
  have hb5 : b5 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb6
  have hb4 : b4 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb5
  have hb3 : b3 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb4
  have hb2 : b2 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb3
  have hb1 : b1 ≤ trClean3 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hb2
  have hnr : newRandoms (trClean2 cls) (trClean3 cls) = [(randTerm 38 32, 32)] := by
    unfold newRandoms; rw [hni]
    have r38 : ((trClean3 cls).at? 38 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono hb1 (at?_append_at b0 _ (trClean2_length cls))
    have r39 := entry_proj_none (E2 := DY.Random.ExecEntryT) 39 hb2 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r40 := entry_proj_none (E2 := DY.Random.ExecEntryT) 40 hb3 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r41 := entry_proj_none (E2 := DY.Random.ExecEntryT) 41 hb4 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r42 := entry_proj_none (E2 := DY.Random.ExecEntryT) 42 hb5 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r43 := entry_proj_none (E2 := DY.Random.ExecEntryT) 43 hb6 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r44 := entry_proj_none (E2 := DY.Random.ExecEntryT) 44 hb7 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r45 := entry_proj_none (E2 := DY.Random.ExecEntryT) 45 hb8 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have r46 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr₀ := b8) (tr' := trClean3 cls)
      (e := StT "bob" (stB2Clean cls)) 46 (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    change List.filterMap (fun i => ((trClean3 cls).at? i : Option DY.Random.ExecEntryT).map _) _ = _
    simp [r38, r39, r40, r41, r42, r43, r44, r45, r46, RndE]
  have hrpt : receivedPlaintext (trClean2 cls) (trClean3 cls) = some pt0Clean := by
    unfold receivedPlaintext; rw [hni]
    have t38 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 38 hb1 (trClean2_length cls).symm rfl
    have t39 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 39 hb2 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have t40 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 40 hb3 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have t41 : ((trClean3 cls).at? 41 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1Clean))) :=
      at?_mono hb4 (at?_append_at b3 _ (by simp +zetaDelta only [append_len, trClean2_length]))
    have t42 : ((trClean3 cls).at? 42 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.HonestDH ((stB20'Clean cls).sessionInfo "bob") dhsB1Clean 0)) :=
      at?_mono hb5 (at?_append_at b4 _ (by simp +zetaDelta only [append_len, trClean2_length]))
    have t43 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 43 hb6 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have t44 : ((trClean3 cls).at? 44 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Received "bob" "alice" (dhPk dhsA) 0 pt0Clean)) :=
      at?_mono hb7 (at?_append_at b6 _ (by simp +zetaDelta only [append_len, trClean2_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t38, t39, t40, t41, t42, t43, t44, EvT]
  have hev : eventIdx isBobDone (trClean2 cls) (trClean3 cls) = some 40 := by
    unfold eventIdx; rw [hni]
    have p38 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 38 hb1 (trClean2_length cls).symm rfl
    have p39 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT PQXDHEvent) 39 hb2 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have p40 : ((trClean3 cls).at? 40 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
        some (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
          (kemPk pqskB) none o1.ek o1.ct keys1)) :=
      at?_mono hb3 (at?_append_at b2 _ (by simp +zetaDelta only [append_len, trClean2_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p38, p39, p40, EvP, isBobDone]
  have hexp : exposures (trClean2 cls) (trClean3 cls) = [] := by
    unfold exposures; rw [hni]
    have hp38 := pqExp_non 38 hb1 (trClean2_length cls).symm rfl
    have hp39 := pqExp_non 39 hb2 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp40 : pqExposureAt (trClean3 cls) 40 = none := by
      unfold pqExposureAt
      have p40 : ((trClean3 cls).at? 40 : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some (EvP (.BobDone "bob" "alice" (dhPk ikB) (dhPk ikA) (dhPk spkB)
            (kemPk pqskB) none o1.ek o1.ct keys1)) :=
        at?_mono hb3 (at?_append_at b2 _ (by simp +zetaDelta only [append_len, trClean2_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, p40, EvP]
    have hp41 := pqExp_non 41 hb4 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp42 := pqExp_non 42 hb5 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp43 := pqExp_non 43 hb6 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp44 := pqExp_non 44 hb7 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp45 := pqExp_non 45 hb8 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have hp46 := pqExp_non (tr₀ := b8) (tr' := trClean3 cls) (e := StT "bob" (stB2Clean cls)) 46
      (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have ht38 := trExp_non 38 hb1 (trClean2_length cls).symm rfl
    have ht39 := trExp_non 39 hb2 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have ht40 := trExp_non 40 hb3 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have ht41 : trExposureAt (trClean3 cls) 41 = none := by
      unfold trExposureAt
      have t41 : ((trClean3 cls).at? 41 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.DHRatchet "bob" "alice" (dhPk dhsA) (dhPk dhsB1Clean))) :=
        at?_mono hb4 (at?_append_at b3 _ (by simp +zetaDelta only [append_len, trClean2_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t41, EvT]
    have ht42 : trExposureAt (trClean3 cls) 42 = none := by
      unfold trExposureAt
      have t42 : ((trClean3 cls).at? 42 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.HonestDH ((stB20'Clean cls).sessionInfo "bob") dhsB1Clean 0)) :=
        at?_mono hb5 (at?_append_at b4 _ (by simp +zetaDelta only [append_len, trClean2_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t42, EvT]
    have ht43 := trExp_non 43 hb6 (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    have ht44 : trExposureAt (trClean3 cls) 44 = none := by
      unfold trExposureAt
      have t44 : ((trClean3 cls).at? 44 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.Received "bob" "alice" (dhPk dhsA) 0 pt0Clean)) :=
        at?_mono hb7 (at?_append_at b6 _ (by simp +zetaDelta only [append_len, trClean2_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t44, EvT]
    have ht45 : trExposureAt (trClean3 cls) 45 = none := by
      unfold trExposureAt
      have t45 : ((trClean3 cls).at? 45 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.MessageKey ((stB20'Clean cls).sessionInfo "bob") .receiver
            seedB0Clean (key0Clean cls) 0 2 46)) :=
        at?_mono hb8 (at?_append_at b7 _ (by simp +zetaDelta only [append_len, trClean2_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t45, EvT]
    have ht46 := trExp_non (tr₀ := b8) (tr' := trClean3 cls) (e := StT "bob" (stB2Clean cls)) 46
      (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean2_length]) rfl
    change List.filterMap (pqExposureAt (trClean3 cls)) _ ++
      List.filterMap (trExposureAt (trClean3 cls)) _ = []
    simp [hp38, hp39, hp40, hp41, hp42, hp43, hp44, hp45, hp46,
      ht38, ht39, ht40, ht41, ht42, ht43, ht44, ht45, ht46]
  dsimp only [s2Clean] at hn2 hok2 ⊢
  unfold stepView bobVis
  simp only [hok2, ↓reduceIte, hn2, hexp, List.append_nil, hnr, hrpt, hev]
  dsimp only [bobOpkPk, kh1, Option.bind, Option.toList, List.append_nil, mh1,
    received, List.filterMap]
  simp [hek, hct, hmsg]

theorem pendingPreKey_trClean3_eq (cls : Nat → Nat) :
    pendingPreKey (trClean3 cls) 46 = none := by
  have hat_st : (trClean3 cls).at? 46 = some (StT "bob" (stB2Clean cls)) := by
    dsimp only [trClean3]
    exact at?_append_at _ _ (by simp only [append_len, trClean2_length])
  have hat_mk : (trClean3 cls).at? 45 =
      some (EvT (.MessageKey ((stB2Clean cls).sessionInfo "bob") .receiver
        seedB0Clean (key0Clean cls) 0 2 46)) := by
    dsimp only [trClean3]
    exact at?_mono (DY.Trace.append_le _ _)
      (at?_append_at _ _ (by simp only [append_len, trClean2_length]))
  exact pendingPreKey_eq_none_of_receiver_mk hat_st (by decide) hat_mk

theorem stepView_s3 (cls : Nat → Nat) :
    stepView (s3Clean cls) (trClean3 cls) false =
      ⟨.pt, [randTerm 47 32], .single, none⟩ ::
      ((if cls 1 != 0 then [rngEntry (randTerm 48 (cls 1))] else []) ++
       [⟨.send, [m1Clean cls], .whisper, none⟩]) := by
  obtain ⟨hn3, hok3⟩ := s3_next_ok cls
  dsimp only [s3Clean] at hn3 hok3 ⊢
  have h := encTrGen_stepView_ok (wrapped := false) hok3 hn3
  rw [trClean3_length, pendingPreKey_trClean3_eq] at h
  exact h

theorem trClean4_sent_53 (cls : Nat → Nat) :
    (trClean4 cls).getMessageSentAt 53 = some (m1Clean cls) := by
  have hat53 : (trClean4 cls).at? 53 = some (NetE (m1Clean cls)) := by
    dsimp only [trClean4, encTrGen, m1Clean, pt1Clean, coins1Clean]
    rw [trClean3_length]
    exact at?_append_at _ _ (by simp only [append_len, trClean3_length])
  simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat53]

theorem stepView_s4 (cls : Nat → Nat) :
    stepView s4Clean (trClean4 cls) false =
      ⟨.recv, [m1Clean cls], .whisper, none⟩ ::
      [rngEntry (randTerm 54 32), ⟨.accept, [pt1Clean], .single, none⟩] := by
  obtain ⟨hn4, hok4⟩ := s4_next_ok cls
  have hmsg := trClean4_sent_53 cls
  have hni : newIndices (trClean4 cls) (trClean5 cls) = [54, 55, 56, 57, 58, 59, 60] := by
    unfold newIndices; rw [trClean4_length, trClean5_length]; decide
  let d0 := trClean4 cls
  let d1 := d0.append (RndE 32)
  let d2 := d1.append (NetE (recvKey (stA1Clean cls).spqr (pqm1Clean cls)))
  let d3 := d2.append (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1Clean) (dhPk dhsA1Clean)))
  let d4 := d3.append (EvT (.HonestDH ((stA3'Clean cls).sessionInfo "alice") dhsA1Clean 1))
  let d5 := d4.append (EvT (.Received "alice" "bob" (dhPk dhsB1Clean) 0 pt1Clean))
  let d6 := d5.append (EvT (.MessageKey ((stA3'Clean cls).sessionInfo "alice") .receiver
    seedA1Clean (key1Clean cls) 0 3 36))
  have hd6 : d6 ≤ trClean5 cls := by dsimp only [trClean5]; exact DY.Trace.append_le _ _
  have hd5 : d5 ≤ trClean5 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd6
  have hd4 : d4 ≤ trClean5 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd5
  have hd3 : d3 ≤ trClean5 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd4
  have hd2 : d2 ≤ trClean5 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd3
  have hd1 : d1 ≤ trClean5 cls := DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) hd2
  have hnr : newRandoms (trClean4 cls) (trClean5 cls) = [(randTerm 54 32, 32)] := by
    unfold newRandoms; rw [hni]
    have r54 : ((trClean5 cls).at? 54 : Option DY.Random.ExecEntryT) = some (RndE 32) :=
      at?_mono hd1 (at?_append_at d0 _ (trClean4_length cls))
    have r55 := entry_proj_none (E2 := DY.Random.ExecEntryT) 55 hd2 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have r56 := entry_proj_none (E2 := DY.Random.ExecEntryT) 56 hd3 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have r57 := entry_proj_none (E2 := DY.Random.ExecEntryT) 57 hd4 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have r58 := entry_proj_none (E2 := DY.Random.ExecEntryT) 58 hd5 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have r59 := entry_proj_none (E2 := DY.Random.ExecEntryT) 59 hd6 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have r60 := entry_proj_none (E2 := DY.Random.ExecEntryT) (tr₀ := d6) (tr' := trClean5 cls)
      (e := StT "alice" (stA4Clean cls)) 60 (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    change List.filterMap (fun i => ((trClean5 cls).at? i : Option DY.Random.ExecEntryT).map _) _ = _
    simp [r54, r55, r56, r57, r58, r59, r60, RndE]
  have hrpt : receivedPlaintext (trClean4 cls) (trClean5 cls) = some pt1Clean := by
    unfold receivedPlaintext; rw [hni]
    have t54 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 54 hd1 (trClean4_length cls).symm rfl
    have t55 := entry_proj_none (E2 := DY.ProtocolEvent.ExecEntryT TREvent) 55 hd2 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have t56 : ((trClean5 cls).at? 56 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1Clean) (dhPk dhsA1Clean))) :=
      at?_mono hd3 (at?_append_at d2 _ (by simp +zetaDelta only [append_len, trClean4_length]))
    have t57 : ((trClean5 cls).at? 57 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.HonestDH ((stA3'Clean cls).sessionInfo "alice") dhsA1Clean 1)) :=
      at?_mono hd4 (at?_append_at d3 _ (by simp +zetaDelta only [append_len, trClean4_length]))
    have t58 : ((trClean5 cls).at? 58 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
        some (EvT (.Received "alice" "bob" (dhPk dhsB1Clean) 0 pt1Clean)) :=
      at?_mono hd5 (at?_append_at d4 _ (by simp +zetaDelta only [append_len, trClean4_length]))
    simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t54, t55, t56, t57, t58, EvT]
  have hexp : exposures (trClean4 cls) (trClean5 cls) = [] := by
    unfold exposures; rw [hni]
    have hp54 := pqExp_non 54 hd1 (trClean4_length cls).symm rfl
    have hp55 := pqExp_non 55 hd2 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have hp56 := pqExp_non 56 hd3 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have hp57 := pqExp_non 57 hd4 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have hp58 := pqExp_non 58 hd5 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have hp59 := pqExp_non 59 hd6 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have hp60 := pqExp_non (tr₀ := d6) (tr' := trClean5 cls) (e := StT "alice" (stA4Clean cls)) 60
      (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have ht54 := trExp_non 54 hd1 (trClean4_length cls).symm rfl
    have ht55 := trExp_non 55 hd2 (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    have ht56 : trExposureAt (trClean5 cls) 56 = none := by
      unfold trExposureAt
      have t56 : ((trClean5 cls).at? 56 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.DHRatchet "alice" "bob" (dhPk dhsB1Clean) (dhPk dhsA1Clean))) :=
        at?_mono hd3 (at?_append_at d2 _ (by simp +zetaDelta only [append_len, trClean4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t56, EvT]
    have ht57 : trExposureAt (trClean5 cls) 57 = none := by
      unfold trExposureAt
      have t57 : ((trClean5 cls).at? 57 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.HonestDH ((stA3'Clean cls).sessionInfo "alice") dhsA1Clean 1)) :=
        at?_mono hd4 (at?_append_at d3 _ (by simp +zetaDelta only [append_len, trClean4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t57, EvT]
    have ht58 : trExposureAt (trClean5 cls) 58 = none := by
      unfold trExposureAt
      have t58 : ((trClean5 cls).at? 58 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.Received "alice" "bob" (dhPk dhsB1Clean) 0 pt1Clean)) :=
        at?_mono hd5 (at?_append_at d4 _ (by simp +zetaDelta only [append_len, trClean4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t58, EvT]
    have ht59 : trExposureAt (trClean5 cls) 59 = none := by
      unfold trExposureAt
      have t59 : ((trClean5 cls).at? 59 : Option (DY.ProtocolEvent.ExecEntryT TREvent)) =
          some (EvT (.MessageKey ((stA3'Clean cls).sessionInfo "alice") .receiver
            seedA1Clean (key1Clean cls) 0 3 36)) :=
        at?_mono hd6 (at?_append_at d5 _ (by simp +zetaDelta only [append_len, trClean4_length]))
      simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, t59, EvT]
    have ht60 := trExp_non (tr₀ := d6) (tr' := trClean5 cls) (e := StT "alice" (stA4Clean cls)) 60
      (DY.Trace.le_refl _)
      (by simp +zetaDelta only [append_len, trClean4_length]) rfl
    change List.filterMap (pqExposureAt (trClean5 cls)) _ ++
      List.filterMap (trExposureAt (trClean5 cls)) _ = []
    simp [hp54, hp55, hp56, hp57, hp58, hp59, hp60, ht54, ht55, ht56, ht57, ht58, ht59, ht60]
  dsimp only [s4Clean] at hn4 hok4 ⊢
  unfold stepView
  rw [hok4]
  simp only [↓reduceIte, hn4]
  change decVis (trClean4 cls) (trClean5 cls) 36 53 false ++ exposures (trClean4 cls) (trClean5 cls) = _
  unfold decVis
  simp [hmsg, hnr, hrpt, hexp]

/-! ## 4. `plaintextTerms`, `.send` Terms, & Vacuous `¬ ReadCollisionCli` (`k ≤ 4`) -/

private theorem filter_pt_kyber (t : Bytes) :
    ((kyberCoinEntries t).filter (·.kind == .pt)) = [] := by
  unfold kyberCoinEntries
  refine List.filter_eq_nil_iff.mpr fun v hv => ?_
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  simp

private theorem filter_send_kyber (t : Bytes) :
    ((kyberCoinEntries t).filter (·.kind == .send)) = [] := by
  unfold kyberCoinEntries
  refine List.filter_eq_nil_iff.mpr fun v hv => ?_
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  simp

theorem visClean_2_terms {r : ProtocolSetup} (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    plaintextTerms (visClean r cls 2) = [randTerm 31 32] ∧
    ((visClean r cls 2).filter (·.kind == .send)).flatMap (·.terms) =
      [o1.ek, o1.ct, m0Clean cls] := by
  have hv2 : visClean r cls 2 =
      stepView s0Clean t4 (runWrapped (ev 0)) ++ stepView (s1Clean cls) t5 true := by
    unfold visClean ssClean cleanCallSteps
    rw [setupTrace_eq_t4 hfit]
    dsimp only [List.take, visOfSteps]
    rw [(s0_next_ok).1, ev1_runWrapped, List.append_nil]
  rw [hv2, stepView_s0, stepView_s1]
  unfold plaintextTerms
  by_cases hcl0 : cls 0 != 0 <;>
    simp [hcl0, rngEntry, filter_pt_kyber, filter_send_kyber, List.filter_append]

theorem visClean_4_terms {r : ProtocolSetup} (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    plaintextTerms (visClean r cls 4) = [randTerm 31 32, randTerm 47 32] ∧
    ((visClean r cls 4).filter (·.kind == .send)).flatMap (·.terms) =
      [o1.ek, o1.ct, m0Clean cls, m1Clean cls] := by
  obtain ⟨hpt2, hs2⟩ := visClean_2_terms cls hfit
  have hv3 : visClean r cls 3 =
      visClean r cls 2 ++ stepView s2Clean (trClean2 cls) (runWrapped (ev 2)) := by
    rw [visClean_succ (by decide) (s := s2Clean) rfl]
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.1]
  have hv4 : visClean r cls 4 =
      visClean r cls 3 ++ stepView (s3Clean cls) (trClean3 cls) false := by
    rw [visClean_succ (by decide) (s := s3Clean cls) rfl]
    unfold runTrace; rw [setupTrace_eq_t4 hfit, (runSteps_ssClean cls).2.2.2.1, ev3_runWrapped]
  rw [hv4, hv3, stepView_s2, stepView_s3]
  unfold plaintextTerms at hpt2 ⊢
  by_cases hcl1 : cls 1 != 0 <;>
    simp [hcl1, rngEntry, List.filter_append, hpt2, hs2]

theorem not_readCollisionCli_ssClean_le4 (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g' : Ghost) (cls : Nat → Nat) {k : Nat} (hk : k ≤ 4)
    (evs : List CliEvent) :
    ¬ ReadCollisionCli interp r S g' (ssClean cls k) evs := by
  rintro ⟨_, _, _, ss₁, ss₂, m, _, msgIdx, _, _, _, _, hss_eq, _, _, _, _, hdec, _, _⟩
  have hm_mem : m ∈ (cleanCallSteps cls).take k := by
    change m ∈ ssClean cls k
    rw [hss_eq]
    exact List.mem_append_right _ List.mem_cons_self
  have hm_4 : m ∈ [s0Clean, s1Clean cls, s2Clean, s3Clean cls] := by
    change m ∈ (cleanCallSteps cls).take 4
    rw [← Nat.min_eq_left hk, ← List.take_take] at hm_mem
    exact List.mem_of_mem_take hm_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm_4
  rcases hm_4 with rfl | rfl | rfl | rfl <;> cases hdec

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision
