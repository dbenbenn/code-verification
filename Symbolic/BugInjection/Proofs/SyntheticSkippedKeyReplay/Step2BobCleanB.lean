/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2BobCleanA

/-!
# Clean 4-Call & 5-Call Explanations, `RecvCollisionOn` Refutation, and `ReadCollisionCli` Discharge
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

noncomputable section Step2Part2D

open Symbolic.Swarm.COMPOSED
open DY.Libsignal.Composed
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
open ByteSpecs (hmacWith sha256With)
open _root_.Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
open _root_.Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

theorem stepView_s3Clean_eq (cl1 cl2 : Nat) :
    stepView s3Clean (tr3Clean cl1 cl2) (runWrapped ev3) =
      [{ kind := .recv, terms := [oClean.ek, oClean.ct, m2Clean cl1 cl2],
         layout := .preKeyRecv, anchor := none },
       rngEntry dhsBClean,
       { kind := .accept, terms := [randTerm 38 32], layout := .single, anchor := some 47 }] := by
  unfold stepView
  simp only [(s3Clean_runs cl1 cl2).1, ↓reduceIte, (s3Clean_runs cl1 cl2).2]
  dsimp only [s3Clean]
  rw [exposures_tr3_tr4_eq, List.append_nil]
  unfold bobVis bobOpkPk
  dsimp only [Option.bind, Option.toList]
  rw [List.append_nil]
  have hrec : received (tr3Clean cl1 cl2) [25, 26, 44] = [oClean.ek, oClean.ct, m2Clean cl1 cl2] := by
    have liftEnc : ∀ {tr : ExecTrace} {me : DY.Participant} {stIdx cl : Nat}
        {st : DY.Libsignal.TripleRatchet.TRState} {pqSalt : DY.Bytes}
        {i : Nat} {e : DY.Network.ExecEntryT},
        (tr.at? i : Option DY.Network.ExecEntryT) = some e →
        ((localEncTr tr me stIdx cl st pqSalt).at? i : Option DY.Network.ExecEntryT) = some e := by
      intro tr me stIdx cl st pqSalt i e h
      unfold localEncTr
      exact at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
          (at?_append_of_some_loc h))))))
    have hat25_1 : (tr1Clean.at? 25 : Option DY.Network.ExecEntryT) = some (CompTrace.NetE oClean.ek) := by
      unfold tr1Clean localAliceStartTr
      refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc (at?_append_of_some_loc ?_))))
      exact at?_append_eq_of_eq _ _ (by have h := setupTrace_r0_len; simp only [length_append_entry]; omega)
    have hat26_1 : (tr1Clean.at? 26 : Option DY.Network.ExecEntryT) = some (CompTrace.NetE oClean.ct) := by
      unfold tr1Clean localAliceStartTr
      refine at?_append_of_some_loc (at?_append_of_some_loc (at?_append_of_some_loc
        (at?_append_of_some_loc ?_)))
      exact at?_append_eq_of_eq _ _ (by have h := setupTrace_r0_len; simp only [length_append_entry]; omega)
    have hat25 : (tr3Clean cl1 cl2).getMessageSentAt 25 = some oClean.ek := by
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      unfold tr3Clean tr2Clean
      rw [liftEnc (liftEnc hat25_1)]
    have hat26 : (tr3Clean cl1 cl2).getMessageSentAt 26 = some oClean.ct := by
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      unfold tr3Clean tr2Clean
      rw [liftEnc (liftEnc hat26_1)]
    have hat44 : (tr3Clean cl1 cl2).getMessageSentAt 44 = some (m2Clean cl1 cl2) := by
      rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      have h44 : 44 = (tr2Clean cl1).length + 6 := by rw [tr2Clean_len]
      rw [h44]; unfold tr3Clean m2Clean coins2Clean
      have h39 : 39 = (tr2Clean cl1).length + 1 := by rw [tr2Clean_len]
      have h38 : 38 = (tr2Clean cl1).length := (tr2Clean_len cl1).symm
      rw [h39, h38]; unfold localEncTr
      rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]), proj_inj_netE]
    simp [received, hat25, hat26, hat44]
  have hrnd : newRandoms (tr3Clean cl1 cl2) (tr4Clean cl1 cl2) = [(dhsBClean, 32)] := by
    have hself : newRandoms (tr3Clean cl1 cl2) (tr3Clean cl1 cl2) = [] := by
      unfold newRandoms newIndices; simp
    have hle3 : (tr3Clean cl1 cl2).length ≤ (tr3Clean cl1 cl2).length := Nat.le_refl _
    unfold tr4Clean; dsimp only
    repeat rw [newRandoms_append_loc (tr3Clean cl1 cl2) _ _
      (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
    rw [hself, tr3Clean_len]
    rfl
  have hpt : receivedPlaintext (tr3Clean cl1 cl2) (tr4Clean cl1 cl2) = some (randTerm 38 32) := by
    have hself : receivedPlaintext (tr3Clean cl1 cl2) (tr3Clean cl1 cl2) = none := by
      unfold receivedPlaintext newIndices; simp
    have hle3 : (tr3Clean cl1 cl2).length ≤ (tr3Clean cl1 cl2).length := Nat.le_refl _
    unfold tr4Clean; dsimp only
    repeat rw [receivedPlaintext_append_loc (tr3Clean cl1 cl2) _ _
      (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
    rw [hself]
    rfl
  have hevIdx : eventIdx isBobDone (tr3Clean cl1 cl2) (tr4Clean cl1 cl2) = some 47 := by
    have hself : eventIdx isBobDone (tr3Clean cl1 cl2) (tr3Clean cl1 cl2) = none := by
      unfold eventIdx newIndices; simp
    unfold tr4Clean; dsimp only
    repeat (first
      | rw [eventIdx_isBobDone_append_other (tr3Clean cl1 cl2) _ _
            (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega) rfl]
      | rw [eventIdx_isBobDone_append_bobDone (tr3Clean cl1 cl2) _ _ _ _ _ _ _ _ _ _ _
            (by simp only [length_append_entry]; omega)])
    rw [hself]
    simp only [Option.or, length_append_entry, tr3Clean_len]
  rw [hrec, hrnd, hpt, hevIdx]
  rfl

theorem stepView_s4Clean_eq (cl1 cl2 : Nat) :
    stepView s4Clean (tr4Clean cl1 cl2) (runWrapped ev4) =
      [{ kind := .recv, terms := [m1Clean cl1],
         layout := .preKeyInner (sessionBaseKeys (tr4Clean cl1 cl2) 54), anchor := none },
       { kind := .accept, terms := [randTerm 31 32], layout := .single, anchor := none }] := by
  unfold stepView
  simp only [(s4Clean_runs cl1 cl2).1, ↓reduceIte, (s4Clean_runs cl1 cl2).2]
  dsimp only [s4Clean]
  rw [exposures_tr4_tr5_eq, List.append_nil]
  unfold decVis
  have hw4 : runWrapped ev4 = true := runWrapped_ev4
  have hm37 : (tr4Clean cl1 cl2).getMessageSentAt 37 = some (m1Clean cl1) := by
    rw [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat37_tr4Clean]
  have hrnd : newRandoms (tr4Clean cl1 cl2) (tr5Clean cl1 cl2) = [] := by
    have hself : newRandoms (tr4Clean cl1 cl2) (tr4Clean cl1 cl2) = [] := by
      unfold newRandoms newIndices; simp
    have hle4 : (tr4Clean cl1 cl2).length ≤ (tr4Clean cl1 cl2).length := Nat.le_refl _
    unfold tr5Clean; dsimp only
    repeat rw [newRandoms_append_loc (tr4Clean cl1 cl2) _ _
      (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
    rw [hself]
    rfl
  have hpt : receivedPlaintext (tr4Clean cl1 cl2) (tr5Clean cl1 cl2) = some (randTerm 31 32) := by
    have hself : receivedPlaintext (tr4Clean cl1 cl2) (tr4Clean cl1 cl2) = none := by
      unfold receivedPlaintext newIndices; simp
    have hle4 : (tr4Clean cl1 cl2).length ≤ (tr4Clean cl1 cl2).length := Nat.le_refl _
    unfold tr5Clean; dsimp only
    repeat rw [receivedPlaintext_append_loc (tr4Clean cl1 cl2) _ _
      (by simp (config := { failIfUnchanged := false }) only [length_append_entry]; omega)]
    rw [hself]
    rfl
  rw [hw4, hm37, hrnd, hpt]
  rfl

theorem getEventAt_bobDone47_tr4Clean (cl1 cl2 : Nat) :
    (tr4Clean cl1 cl2).getEventAt DY.Libsignal.PQXDH.PQXDHEvent 47 =
      some (.BobDone "bob" "alice"
        (DY.DiffieHellman.dhPk ikBSkClean) ikAPkClean
        (DY.DiffieHellman.dhPk spkBSkClean) (DY.PQKem.kemPk pqskBClean)
        none oClean.ek oClean.ct oClean.keys) := by
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
  unfold tr4Clean; dsimp only
  repeat rw [at?_append_other_eq _ _ rfl]
  rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len]),
      proj_inj_pqEvE, bobOut_eq]

theorem oClean_ek_mem_bobDoneBaseKeys_tr4Clean (cl1 cl2 : Nat) :
    oClean.ek ∈ bobDoneBaseKeys (tr4Clean cl1 cl2) := by
  unfold bobDoneBaseKeys
  rw [List.mem_filterMap]
  refine ⟨47, List.mem_range.mpr (by rw [tr4Clean_len]; decide), ?_⟩
  rw [getEventAt_bobDone47_tr4Clean]

theorem oClean_ek_mem_sessionBaseKeys_tr4Clean (cl1 cl2 : Nat) :
    oClean.ek ∈ sessionBaseKeys (tr4Clean cl1 cl2) 54 := by
  unfold sessionBaseKeys
  have hat54 : ((tr4Clean cl1 cl2).at? 54 : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE "bob" (stB3Clean cl1 cl2)) := by
    unfold tr4Clean; dsimp only
    rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len]), proj_inj_trStE]
  rw [getLocalStateAt_trStE hat54]
  dsimp only
  rw [List.mem_filterMap]
  refine ⟨.BobDone "bob" "alice" (DY.DiffieHellman.dhPk ikBSkClean) ikAPkClean
    (DY.DiffieHellman.dhPk spkBSkClean) (DY.PQKem.kemPk pqskBClean)
    none oClean.ek oClean.ct oClean.keys, ?_, rfl⟩
  unfold sessionHandshakeEvents
  rw [List.mem_filterMap]
  refine ⟨50, List.mem_range.mpr (by rw [tr4Clean_len]; decide), ?_⟩
  have hce50 : (tr4Clean cl1 cl2).getEventAt DY.Libsignal.Composed.ComposedEvent 50 =
      some (.HandshakeSession ((stB3Clean cl1 cl2).sessionInfo "bob") 47) := by
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1]
    unfold tr4Clean; dsimp only
    repeat rw [at?_append_other_eq _ _ rfl]
    rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry, tr3Clean_len]), proj_inj_cEvE]
  rw [hce50]; simp only [↓reduceIte, getEventAt_bobDone47_tr4Clean]

theorem plaintextTerms_vis4Clean (cl1 cl2 : Nat) :
    plaintextTerms (vis4Clean cl1 cl2) = [randTerm 31 32, randTerm 38 32] := by
  unfold plaintextTerms vis4Clean
  rw [List.filter_append, stepView_s3Clean_eq]
  have hf3 : ([⟨.recv, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeyRecv, none⟩,
      rngEntry dhsBClean,
      ⟨.accept, [randTerm 38 32], .single, some 47⟩] : List VisEntry).filter
      (·.kind == .pt) = [] := rfl
  rw [hf3, List.append_nil]
  exact plaintextTerms_vis3Clean cl1 cl2

theorem plaintextTerms_vis5Clean (cl1 cl2 : Nat) :
    plaintextTerms (vis5Clean cl1 cl2) = [randTerm 31 32, randTerm 38 32] := by
  unfold plaintextTerms vis5Clean
  rw [List.filter_append, stepView_s4Clean_eq]
  have hf4 : ([⟨.recv, [m1Clean cl1], .preKeyInner (sessionBaseKeys (tr4Clean cl1 cl2) 54), none⟩,
      ⟨.accept, [randTerm 31 32], .single, none⟩] : List VisEntry).filter
      (·.kind == .pt) = [] := rfl
  rw [hf4, List.append_nil]
  exact plaintextTerms_vis4Clean cl1 cl2

theorem sendTerms_vis4Clean (cl1 cl2 : Nat) :
    ((vis4Clean cl1 cl2).filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m1Clean cl1, oClean.ek, oClean.ct, m2Clean cl1 cl2] := by
  unfold vis4Clean
  rw [List.filter_append, stepView_s3Clean_eq]
  have hf3 : ([⟨.recv, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeyRecv, none⟩,
      rngEntry dhsBClean,
      ⟨.accept, [randTerm 38 32], .single, some 47⟩] : List VisEntry).filter
      (·.kind == .send) = [] := rfl
  rw [hf3, List.append_nil]
  exact sendTerms_vis3Clean cl1 cl2

theorem sendTerms_vis5Clean (cl1 cl2 : Nat) :
    ((vis5Clean cl1 cl2).filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m1Clean cl1, oClean.ek, oClean.ct, m2Clean cl1 cl2] := by
  unfold vis5Clean
  rw [List.filter_append, stepView_s4Clean_eq]
  have hf4 : ([⟨.recv, [m1Clean cl1], .preKeyInner (sessionBaseKeys (tr4Clean cl1 cl2) 54), none⟩,
      ⟨.accept, [randTerm 31 32], .single, none⟩] : List VisEntry).filter
      (·.kind == .send) = [] := rfl
  rw [hf4, List.append_nil]
  exact sendTerms_vis4Clean cl1 cl2

theorem ghostWF_gClean_vis4Clean (g : Ghost) {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    GhostWF (gClean g) (vis4Clean cl1 cl2) := by
  have hg3 := ghostWF_gClean_vis3Clean g hcl1 hcl2
  refine ⟨?_, fun _ => Or.inr cleanAddrBs_eq_serializeAddresses, ?_⟩
  · intro v hv hkind ts n hne hmem
    unfold vis4Clean at hv
    rcases List.mem_append.mp hv with hv3 | hv_s3
    · exact hg3.1 v hv3 hkind ts n hne hmem
    · rw [stepView_s3Clean_eq] at hv_s3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_s3
      rcases hv_s3 with rfl | rfl | rfl
      · cases hkind
      · simp only [rngEntry, dhsBClean, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
        change (dagBytes 127).length = 32; decide +kernel
      · cases hkind
  · intro v hv hkind
    unfold vis4Clean at hv
    rcases List.mem_append.mp hv with hv3 | hv_s3
    · exact hg3.2.2 v hv3 hkind
    · rw [stepView_s3Clean_eq] at hv_s3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_s3
      rcases hv_s3 with rfl | rfl | rfl <;> cases hkind

theorem ghostWF_gClean_vis5Clean (g : Ghost) {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    GhostWF (gClean g) (vis5Clean cl1 cl2) := by
  have hg4 := ghostWF_gClean_vis4Clean g hcl1 hcl2
  refine ⟨?_, fun _ => Or.inr cleanAddrBs_eq_serializeAddresses, ?_⟩
  · intro v hv hkind ts n hne hmem
    unfold vis5Clean at hv
    rcases List.mem_append.mp hv with hv4 | hv_s4
    · exact hg4.1 v hv4 hkind ts n hne hmem
    · rw [stepView_s4Clean_eq] at hv_s4
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_s4
      rcases hv_s4 with rfl | rfl <;> cases hkind
  · intro v hv hkind
    unfold vis5Clean at hv
    rcases List.mem_append.mp hv with hv4 | hv_s4
    · exact hg4.2.2 v hv4 hkind
    · rw [stepView_s4Clean_eq] at hv_s4
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_s4
      rcases hv_s4 with rfl | rfl <;> cases hkind

private theorem tryFrom_message_of_parsePreKeyWire {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p) :
    CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec p.message = .ok p.inner := by
  unfold parsePreKeyWire at hp
  split at hp
  · split at hp
    · unfold parsePreKey at hp
      split at hp
      · cases hp
      · dsimp only at hp
        split at hp
        · cases hp
        · split at hp
          · cases hp
          · split at hp
            · split at hp
              · split at hp
                · next inner htry' =>
                  injection hp with hp'; subst hp'; exact htry'
                · cases hp
              · cases hp
            · cases hp
    · cases hp
  · cases hp

theorem m1Clean_mem_recvReps_of_ak {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hc : GhostAndSemMatchSetup compI0 r S g)
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24)
    (hak : (m1Clean cl1).AttackerKnows tr) :
    m1Clean cl1 ∈ recvRepresentationsOn compI0 S (gClean g) tr p_c1.message := by
  let pts : List DY.Bytes := [randTerm 31 32, randTerm 38 32]
  have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hc hcl1 hcl2
    (by simp [pts]) (by simp [pts]) hsalt1 hpqm1 hsalt2 hpqm2
  obtain ⟨_, _, hcks0, _, _, hm1, _, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hdhsPk : DagTermAt S (gClean g) pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73 := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
  have hseed1 : DagTermAt S (gClean g) pts (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 97 :=
    termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0 (dagN_2 hw)
  obtain ⟨tck1, tmk1, tiv1⟩ := termAt_trMsgKeys
    (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
    dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (dagN_21 hw) hseed1
  have hct1 := termAt_symEncPt (id := 105) dag_nodes_ok (by decide)
    (congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel) : dagOp 105 = .symEncPt 100 104 31 ev1.input)
    tck1 tiv1 hw.hpt1_mem hw.hσ_pt1 (by decide +kernel)
  have hwire1 := termAt_trWire (id := 106) dag_nodes_ok (by decide)
    (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22) (by decide +kernel) :
      dagOp 106 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22 cleanAddrBs)
    hdhsPk hct1 (dagN_22 hw) (hw.haddr _)
  have hmac1 := termAt_computeMac
    (c1_id := 107) (c2_id := 108) (h_id := 109) (t_id := 110)
    dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    tmk1 (dagN_28 hw) (dagN_31 hw) hwire1
  have hm1_g : gamma compI0 S (gClean g) (m1Clean cl1) = dagBytes 111 := hm1.2.1
  have hw_g : gamma compI0 S (gClean g) (msg1Clean cl1).wire = dagBytes 106 := hwire1.2.1
  have hm_g : gamma compI0 S (gClean g) (msg1Clean cl1).mac = dagBytes 110 := hmac1.2.1
  have hc_g : gamma compI0 S (gClean g) (msg1Clean cl1).ciphertext = dagBytes 105 := hct1.2.1
  have hr_g : gamma compI0 S (gClean g) (msg1Clean cl1).ratchetKey = dagBytes 73 := hdhsPk.2.1
  have hp_g : gamma compI0 S (gClean g) (msg1Clean cl1).pqRatchet = dagBytes 22 := hpqm1
  refine ⟨hak, ?_, by rw [parse_m1Clean]; rfl, ?_⟩
  · rw [hm1_g]; decide +kernel
  · intro msg hparse
    rw [parse_m1Clean] at hparse
    injection hparse with hmsg; subst hmsg
    refine ⟨?_, ?_, spqrHeaded_computeMac_false _ _ _ _, ?_⟩
    · rw [hw_g]; decide +kernel
    · rw [hm_g]; decide +kernel
    · have htry := tryFrom_message_of_parsePreKeyWire parsePreKeyWire_ev4
      intro m hm
      rw [htry] at hm
      injection hm with hm_eq; subst hm_eq
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hc_g]; decide +kernel
      · rw [hr_g]; decide +kernel
      · rw [hp_g]; decide +kernel
      · change (0 : UInt32).toNat = p_c1.inner.counter.toNat; decide +kernel
      · change DY.Libsignal.TripleRatchet.messageVersion.toNat = p_c1.inner.messageVersion.toNat
        decide +kernel

theorem not_recvCollisionOn_c1_of_clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {tr : ExecTrace} {vis : List VisEntry} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hc : GhostAndSemMatchSetup compI0 r S g)
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24)
    (hpt : plaintextTerms vis = [randTerm 31 32, randTerm 38 32])
    (hsend : (vis.filter (·.kind == .send)).flatMap (·.terms) =
      [oClean.ek, oClean.ct, m1Clean cl1, oClean.ek, oClean.ct, m2Clean cl1 cl2])
    (hst : ∀ ls ∈ storedStates r0 tr,
      ls = ⟨"alice", stA0Clean⟩ ∨ ls = ⟨"alice", stA1Clean cl1⟩ ∨
      ls = ⟨"alice", stA2Clean cl1 cl2⟩ ∨ ls = ⟨"bob", stB3Clean cl1 cl2⟩ ∨
      ls = ⟨"bob", stB4Clean cl1 cl2⟩)
    (hsec_eq : storedSecrets tr = storedSecrets (tr3Clean cl1 cl2))
    (havail : ∀ st ∈ availableStates r0 tr,
      st = stA0Clean ∨ st = stA1Clean cl1 ∨ st = stA2Clean cl1 cl2 ∨
      st = stB3Clean cl1 cl2 ∨ st = stB4Clean cl1 cl2)
    (hsk : ∀ i, i < tr.length → ∀ s pk n seed rIdx srcIdx,
      tr.getEventAt DY.Libsignal.TripleRatchet.TREvent i =
        some (.SkippedKeyStored s pk n seed rIdx srcIdx) →
      pk = DY.DiffieHellman.dhPk stA0Clean.dhs ∧ n = 0 ∧
      seed = (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2) :
    ¬ RecvCollisionOn compI0 r S (gClean g) tr vis
        [DY.Spqr.zeroKey, salt1Clean cl1, salt2Clean cl1 cl2] (m1Clean cl1) := by
  unfold RecvCollisionOn
  dsimp only
  rw [parse_m1Clean]
  set pts := plaintextTerms vis ++ ([] : List DY.Bytes)
  have hpts_eq : pts = [randTerm 31 32, randTerm 38 32] := by simp [pts, hpt]
  have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hc hcl1 hcl2
    (by rw [hpts_eq]; simp) (by rw [hpts_eq]; simp) hsalt1 hpqm1 hsalt2 hpqm2
  obtain ⟨hek0, hct0, _, _, _⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, hcks0, _, _, hm1, _, hm2⟩ := dagTermAt_aliceRatchetAndMsgs hw
  obtain ⟨hsa0, hsa1, hsa2⟩ := safeMemo2_aliceStates hcl1 hcl2 hw
  obtain ⟨hsb3, hsb4⟩ := safeMemo2_bobStates hw
  have hsec := safeMemo2_storedSecrets_tr3Clean hw
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      unfold prefixTerms principalTerms at ht
      rcases List.mem_append.mp ht with hprin | hpt_mem
      · rcases List.mem_append.mp hprin with h12 | hs_mem
        · rcases List.mem_append.mp h12 with hsend_mem | hst_mem
          · rw [hsend] at hsend_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hsend_mem
            rcases hsend_mem with rfl | rfl | rfl | rfl | rfl | rfl
            · exact safeMemo_toSafeMemo2 hek0.safeMemo
            · exact safeMemo_toSafeMemo2 hct0.safeMemo
            · exact safeMemo_toSafeMemo2 hm1.safeMemo
            · exact safeMemo_toSafeMemo2 hek0.safeMemo
            · exact safeMemo_toSafeMemo2 hct0.safeMemo
            · exact safeMemo_toSafeMemo2 hm2.safeMemo
          · rw [storedStates_eq_of_parties hp.ha hp.hb hp.hopk] at hst_mem
            obtain ⟨ls, hls_mem, rfl⟩ := List.mem_map.mp hst_mem
            rcases hst ls hls_mem with rfl | rfl | rfl | rfl | rfl
            · exact hsa0
            · exact hsa1
            · exact hsa2
            · exact hsb3
            · exact hsb4
        · rw [hsec_eq] at hs_mem
          exact hsec t hs_mem
      · rw [hpt] at hpt_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt_mem
        rcases hpt_mem with rfl | rfl
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext (by change randTerm 31 32 ∈ pts; rw [hpts_eq]; simp)
            (by rw [hw.hσ_pt1]; decide +kernel))
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext (by change randTerm 38 32 ∈ pts; rw [hpts_eq]; simp)
            (by rw [hw.hσ_pt2]; decide +kernel))
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | htr_mem
      · exact safeMemo_toSafeMemo2 hm1.safeMemo
      · exact safeMemo_toSafeMemo2 (safeMemo_whisperTrials_c1 hp hw havail hsk t htr_mem)
  · have hseed1 : DagTermAt S (gClean g) pts (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 97 :=
      termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0 (dagN_2 hw)
    obtain ⟨tck1, tmk1, tiv1⟩ := termAt_trMsgKeys
      (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
      dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
      ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
      ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
      (dagN_21 hw) hseed1
    have hprk1 := termAt_kdf (id := 99) dag_nodes_ok (by decide) rfl (dagN_21 hw) hseed1
    have hdhsPk : DagTermAt S (gClean g) pts (msg1Clean cl1).ratchetKey 73 := by
      change DagTermAt S (gClean g) pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73
      unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
    have hct1 := termAt_symEncPt (id := 105) dag_nodes_ok (by decide)
      (congrArg (DagOp.symEncPt 100 104 31) (by decide +kernel) : dagOp 105 = .symEncPt 100 104 31 ev1.input)
      tck1 tiv1 hw.hpt1_mem hw.hσ_pt1 (by decide +kernel)
    have hwire1 : DagTermAt S (gClean g) pts (msg1Clean cl1).wire 106 :=
      termAt_trWire (id := 106) dag_nodes_ok (by decide)
        (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22) (by decide +kernel) :
          dagOp 106 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 0 0 105 22 cleanAddrBs)
        hdhsPk hct1 (dagN_22 hw) (hw.haddr _)
    have hmac1 : DagTermAt S (gClean g) pts (msg1Clean cl1).mac 110 :=
      termAt_computeMac (c1_id := 107) (c2_id := 108) (h_id := 109) (t_id := 110)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk1 (dagN_28 hw) (dagN_31 hw) hwire1
    refine not_macTagForgeryOrCollision_of_honest_mac
      (salt_h := salt1Clean cl1)
      (seed_h := (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2)
      (a_h := stA0Clean.myIk) (b_h := stA0Clean.peerIk) (w_h := (msg1Clean cl1).wire)
      (by simp) rfl ?_ ?_ ?_ hmac
    · unfold gamma; rw [hmac1.2.1]; decide +kernel
    · unfold gamma; rw [tmk1.2.1]; decide +kernel
    · unfold gamma msgPrk DY.Libsignal.TripleRatchet.hmac; rw [hprk1.2.1]; decide +kernel

theorem matchesEventsAt_snoc_run1 {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {evs : List CliEvent} {ev : RunEvent}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {s : Step} {vis v : List VisEntry}
    (hM : MatchesEventsAt interp r S g initIds tr ss evs vis)
    (hRun : ∀ ids, RunMatches interp r S g (runSteps ss tr) s ev v ids) :
    MatchesEventsAt interp r S g initIds tr (ss ++ [s]) (evs ++ [.run ev]) (vis ++ v) := by
  induction hM with
  | nil hinv =>
    simp only [List.nil_append]
    rw [show v = v ++ [] from (List.append_nil v).symm]
    exact MatchesEventsAt.run1 hinv (hRun _) (MatchesEventsAt.nil (fun _ h => nomatch h))
  | @run1 initIds tr pre s₀ ss₀ ev₀ evs₀ v₀ vis₀ hinv hrun₀ _ ih =>
    have hassoc_ss : (pre ++ s₀ :: ss₀) ++ [s] = pre ++ s₀ :: (ss₀ ++ [s]) := by simp [List.append_assoc]
    have hassoc_vis : (v₀ ++ vis₀) ++ v = v₀ ++ (vis₀ ++ v) := by simp [List.append_assoc]
    rw [hassoc_ss, List.cons_append, hassoc_vis]
    refine MatchesEventsAt.run1 hinv hrun₀ (ih fun ids => ?_)
    have hrs : runSteps (pre ++ s₀ :: ss₀) tr = runSteps ss₀ (s₀.next (runSteps pre tr)) := by
      rw [runSteps_append_local]; rfl
    rw [← hrs]; exact hRun ids
  | @run0 initIds tr pre ss₀ ev₀ evs₀ vis₀ hinv hrej₀ _ ih =>
    have hassoc_ss : (pre ++ ss₀) ++ [s] = pre ++ (ss₀ ++ [s]) := by simp [List.append_assoc]
    rw [hassoc_ss, List.cons_append]
    refine MatchesEventsAt.run0 hinv hrej₀ (ih fun ids => ?_)
    have hrs : runSteps (pre ++ ss₀) tr = runSteps ss₀ (runSteps pre tr) :=
      runSteps_append_local pre ss₀ tr
    rw [← hrs]; exact hRun ids
  | @env initIds tr pre s₀ ss₀ e₀ evs₀ v₀ vis₀ hinv henv₀ _ ih =>
    have hassoc_ss : (pre ++ s₀ :: ss₀) ++ [s] = pre ++ s₀ :: (ss₀ ++ [s]) := by simp [List.append_assoc]
    have hassoc_vis : (v₀ ++ vis₀) ++ v = v₀ ++ (vis₀ ++ v) := by simp [List.append_assoc]
    rw [hassoc_ss, List.cons_append, hassoc_vis]
    refine MatchesEventsAt.env hinv henv₀ (ih fun ids => ?_)
    have hrs : runSteps (pre ++ s₀ :: ss₀) tr = runSteps ss₀ (s₀.next (runSteps pre tr)) := by
      rw [runSteps_append_local]; rfl
    rw [← hrs]; exact hRun ids

theorem bobDoneBaseKeys_tr3Clean_nil (cl1 cl2 : Nat) :
    bobDoneBaseKeys (tr3Clean cl1 cl2) = [] := by
  refine bobDoneBaseKeys_nil_of_noBobBefore3 ?_
  have h0 : NoBobBefore3 (setupTrace r0) := noBobBefore3_setupTrace r0
  have h1 : NoBobBefore3 tr1Clean := by
    rw [← s0Clean_runs.2]
    dsimp only [s0Clean, Step.next, Step.toInput]
    rw [stepIn_next DY.Libsignal.Composed.aliceStart.reachability
      ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles))
      (setupTrace r0)]
    exact preserves_aliceStart 4 6 ⟨14, 15, 20, 21, none⟩ (setupTrace r0) h0
  have h2 : NoBobBefore3 (tr2Clean cl1) := by
    rw [← (s1Clean_runs cl1).2]
    dsimp only [s1Clean, Step.next, Step.toInput]
    rw [stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability
      ("alice", 30, cl1, 33) tr1Clean]
    exact preserves_messageEncrypt_alice 30 cl1 33 tr1Clean h1
  rw [← (s2Clean_runs cl1 cl2).2]
  dsimp only [s2Clean, Step.next, Step.toInput]
  rw [stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    ("alice", 36, cl2, 40) (tr2Clean cl1)]
  exact preserves_messageEncrypt_alice 36 cl2 40 (tr2Clean cl1) h2

theorem explains_clean_ev0123 {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2])
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24) :
    Explains compI0 r S (gClean g) (ss4Clean cl1 cl2) (vis4Clean cl1 cl2)
      [.run ev0, .run ev1, .run ev2, .run ev3] := by
  obtain ⟨hex3, hrep3⟩ := explains_clean_ev012 hp hex hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
  refine ⟨ghostAndSemMatchSetup_gClean hp hex.1,
          ghostWF_gClean_vis4Clean g hcl1 hcl2,
          ⟨hex.2.2.1.1, hex.2.2.1.2.1, stepsWF_ss4Clean hp hcl1 hcl2,
            stepsStateFaithful_ss4Clean r cl1 cl2⟩,
          ?_⟩
  have hss_eq : ss4Clean cl1 cl2 = ss3Clean cl1 cl2 ++ [s3Clean] := rfl
  have hvis_eq : vis4Clean cl1 cl2 = vis3Clean cl1 cl2 ++ stepView s3Clean (tr3Clean cl1 cl2) (runWrapped ev3) := rfl
  have hevs_eq : ([.run ev0, .run ev1, .run ev2, .run ev3] : List CliEvent) =
      [.run ev0, .run ev1, .run ev2] ++ [.run ev3] := rfl
  unfold MatchesEvents
  rw [hss_eq, hvis_eq, hevs_eq]
  refine matchesEventsAt_snoc_run1 hex3.2.2.2 fun ids => ?_
  have hrs3 : runSteps (ss3Clean cl1 cl2) (setupTrace r) = tr3Clean cl1 cl2 := runTrace_ss3Clean hp cl1 cl2
  rw [hrs3]
  rw [runTrace_ss3Clean hp] at hrep3
  refine ⟨rfl, rfl, trivial, hp.ha.symm, (s3Clean_runs cl1 cl2).1, ⟨ev2.input, rfl⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeyRecv, none⟩,
          [rngEntry dhsBClean],
          [⟨.accept, [randTerm 38 32], .single, some 47⟩],
          stepView_s3Clean_eq cl1 cl2,
          ⟨rfl, hrep3.2.2.2.1, opkNamed_ev3_false⟩,
          ?_, ?_, hrep3, ?_⟩
  · refine ⟨[ev3.coins.take 32], ?_, ⟨ev3.coins.drop 32, by simp [List.take_append_drop]⟩,
      List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp_mem; rcases List.mem_singleton.mp hp_mem with rfl; decide +kernel
    · simp only [rngEntry, dhsBClean, List.map_cons, List.map_nil]
      unfold gamma; rw [gamma'_randTerm compI0 S (gClean g) 45 32 (by decide)]
      dsimp only
      rw [show (gClean g).σ 45 32 = dagBytes 127 from rfl]
      decide +kernel
  · unfold OutputsMatch
    have hcmd3 : ev3.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    have hexit3 : ev3.exit = some (0, ev2.input) := ev3_exit_eq_ev2_input
    rw [hexit3, hcmd3]
    refine ⟨⟨.accept, [randTerm 38 32], .single, some 47⟩, rfl, rfl, ?_⟩
    dsimp only [List.map]
    unfold gamma
    rw [gamma'_randTerm compI0 S (gClean g) 38 32 (by decide)]
    rfl
  · unfold PathFaithfulAt s3Clean
    dsimp only
    rintro p _ ⟨ek, hek_mem, _⟩
    rw [bobDoneBaseKeys_tr3Clean_nil] at hek_mem
    cases hek_mem

theorem explains_clean_ev01234 {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2])
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24) :
    Explains compI0 r S (gClean g) (ss5Clean cl1 cl2) (vis5Clean cl1 cl2)
      [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] := by
  have hex4 := explains_clean_ev0123 hp hex hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
  let pts : List DY.Bytes := [randTerm 31 32, randTerm 38 32]
  have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hex.1 hcl1 hcl2
    (by simp [pts]) (by simp [pts]) hsalt1 hpqm1 hsalt2 hpqm2
  obtain ⟨hek0, _, _, _, _⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, _, _, _, hm1, _, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hek_g : gamma compI0 S (gClean g) oClean.ek = dagBytes 68 := hek0.2.1
  have hm1_g : gamma compI0 S (gClean g) (m1Clean cl1) = dagBytes 111 := hm1.2.1
  have hsec0 : secretBytes r 0 = setup.aliceId := hp.hsec0
  refine ⟨ghostAndSemMatchSetup_gClean hp hex.1,
          ghostWF_gClean_vis5Clean g hcl1 hcl2,
          ⟨hex.2.2.1.1, hex.2.2.1.2.1, stepsWF_ss5Clean hp hcl1 hcl2,
            stepsStateFaithful_ss5Clean r cl1 cl2⟩,
          ?_⟩
  have hss_eq : ss5Clean cl1 cl2 = ss4Clean cl1 cl2 ++ [s4Clean] := rfl
  have hvis_eq : vis5Clean cl1 cl2 = vis4Clean cl1 cl2 ++ stepView s4Clean (tr4Clean cl1 cl2) (runWrapped ev4) := rfl
  have hevs_eq : ([.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] : List CliEvent) =
      [.run ev0, .run ev1, .run ev2, .run ev3] ++ [.run ev4] := rfl
  unfold MatchesEvents
  rw [hss_eq, hvis_eq, hevs_eq]
  refine matchesEventsAt_snoc_run1 hex4.2.2.2 fun ids => ?_
  have hrs4 : runSteps (ss4Clean cl1 cl2) (setupTrace r) = tr4Clean cl1 cl2 := runTrace_ss4Clean hp cl1 cl2
  rw [hrs4]
  refine ⟨rfl, rfl, trivial, trivial, (s4Clean_runs cl1 cl2).1, ⟨ev1.input, ev4_exit_eq_ev1_input⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [m1Clean cl1], .preKeyInner (sessionBaseKeys (tr4Clean cl1 cl2) 54), none⟩,
          [],
          [⟨.accept, [randTerm 31 32], .single, none⟩],
          stepView_s4Clean_eq cl1 cl2,
          ?_,
          ⟨[], fun _ h => False.elim (List.not_mem_nil h), ⟨ev4.coins, rfl⟩, .nil⟩,
          ?_, ?_, ?_⟩
  · refine ⟨rfl, m1Clean cl1, p_c1, rfl, parsePreKeyWire_ev4, by decide +kernel, ?_,
      ⟨oClean.ek, oClean_ek_mem_sessionBaseKeys_tr4Clean cl1 cl2, ?_⟩, ?_⟩
    · rw [hsec0]; decide +kernel
    · rw [hek_g]; decide +kernel
    · rw [hm1_g]; decide +kernel
  · unfold OutputsMatch
    have hcmd4 : ev4.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
    have hexit4 : ev4.exit = some (0, ev1.input) := ev4_exit_eq_ev1_input
    rw [hexit4, hcmd4]
    refine ⟨⟨.accept, [randTerm 31 32], .single, none⟩, rfl, rfl, ?_⟩
    dsimp only [List.map]
    unfold gamma
    rw [gamma'_randTerm compI0 S (gClean g) 31 32 (by decide)]
    rfl
  · intro p hp_eq
    have hp_c1 : p = p_c1 := Option.some.inj (hp_eq.symm.trans parsePreKeyWire_ev4)
    subst hp_c1
    exact m1Clean_mem_recvReps_of_ak hp hex.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
      (attackerKnows_c1_tr4Clean cl1 cl2)
  · intro p hp_eq
    have hp_c1 : p = p_c1 := Option.some.inj (hp_eq.symm.trans parsePreKeyWire_ev4)
    subst hp_c1
    refine ⟨oClean.ek, oClean_ek_mem_bobDoneBaseKeys_tr4Clean cl1 cl2, ?_⟩
    rw [hek_g]; decide +kernel

theorem not_readCollisionCli_ss4Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g' : Ghost} {evs : List CliEvent} {cl1 cl2 : Nat} :
    ¬ ReadCollisionCli compI0 r S g' (ss4Clean cl1 cl2) evs := by
  rintro ⟨_, _, _, ss₁, ss₂, m, _, msgIdx, _, _, _, _, hss_eq, _, _, _, _, hm_dec, _⟩
  have hmem : m ∈ ss4Clean cl1 cl2 := by
    rw [hss_eq]; exact List.mem_append_right _ List.mem_cons_self
  unfold ss4Clean at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> cases hm_dec

theorem partyStep_matchesEventsAt_run1 {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {s : Step} {ss : List Step} {ev : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hs : s.cls = .party)
    (hnr : ¬ RunRejected ev)
    (hM : MatchesEventsAt interp r S g initIds tr (s :: ss) (.run ev :: evs) vis) :
    ∃ vis', vis = stepView s tr (runWrapped ev) ++ vis' ∧
      MatchesEventsAt interp r S g (nextBundleIds initIds ev) (s.next tr) ss evs vis' := by
  generalize hss_eq : (s :: ss : List Step) = ss_all at hM
  generalize hevs_eq : (CliEvent.run ev :: evs : List CliEvent) = evs_all at hM
  cases hM with
  | nil _ => cases hevs_eq
  | @run1 _ _ pre s₀ ss₀ ev₀ evs₀ v₀ vis₀ hinv hrun htail =>
    simp only [List.cons.injEq, CliEvent.run.injEq] at hevs_eq
    rcases hevs_eq with ⟨rfl, rfl⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hss_eq
      rcases hss_eq with ⟨rfl, rfl⟩
      dsimp only [runSteps] at hrun htail
      exact ⟨vis₀, by rw [hrun.2.2.2.2.2.2.1], htail⟩
    | cons x _ =>
      simp only [List.cons_append, List.cons.injEq] at hss_eq
      have hx := hinv x List.mem_cons_self
      rw [← hss_eq.1, hs] at hx; cases hx
  | run0 _ hrej _ =>
    simp only [List.cons.injEq, CliEvent.run.injEq] at hevs_eq
    rcases hevs_eq with ⟨rfl, _⟩
    exact False.elim (hnr hrej)
  | env _ _ _ => cases hevs_eq

theorem matchesEvents_ss4Clean_vis_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g' : Ghost} {evs₁ : List CliEvent} {ev : RunEvent} {evs₂ : List CliEvent}
    {vis₁ : List VisEntry} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hevs : ([.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] : List CliEvent) =
      evs₁ ++ .run ev :: evs₂)
    (hM : MatchesEvents compI0 r S g' (setupTrace r) (ss4Clean cl1 cl2) evs₁ vis₁) :
    vis₁ = vis4Clean cl1 cl2 := by
  have no_runRejected_ev0 : ¬ RunRejected ev0 := fun h => h _ rfl
  have no_runRejected_ev1 : ¬ RunRejected ev1 := fun h => h _ ev1_exit_eq_fast
  have no_runRejected_ev2 : ¬ RunRejected ev2 := fun h => h _ ev2_exit_eq_fast
  have hnil_false : ∀ {ids tr s' ss' v'}, s'.cls = .party →
      ¬ MatchesEventsAt compI0 r S g' ids tr (s' :: ss') [] v' := by
    intro ids tr s' ss' v' hs' hm
    generalize hss_eq : (s' :: ss' : List Step) = ss_all at hm
    generalize hevs_eq : ([] : List CliEvent) = evs_all at hm
    cases hm with
    | nil hinv =>
      subst hss_eq
      have := hinv s' List.mem_cons_self; rw [hs'] at this; cases this
    | run1 _ _ _ => cases hevs_eq
    | run0 _ _ _ => cases hevs_eq
    | env _ _ _ => cases hevs_eq
  unfold MatchesEvents ss4Clean at hM
  rw [setupTrace_eq_of_fits hp] at hM
  cases evs₁ with
  | nil => exact False.elim (hnil_false rfl hM)
  | cons e0 rest0 =>
    simp only [List.cons_append, List.cons.injEq] at hevs
    rcases hevs with ⟨rfl, hevs⟩
    obtain ⟨vis_a, rfl, hM1⟩ := partyStep_matchesEventsAt_run1 rfl no_runRejected_ev0 hM
    rw [s0Clean_runs.2] at hM1
    cases rest0 with
    | nil => exact False.elim (hnil_false rfl hM1)
    | cons e1 rest1 =>
      simp only [List.cons_append, List.cons.injEq] at hevs
      rcases hevs with ⟨rfl, hevs⟩
      obtain ⟨vis_b, rfl, hM2⟩ := partyStep_matchesEventsAt_run1 rfl no_runRejected_ev1 hM1
      rw [(s1Clean_runs cl1).2] at hM2
      cases rest1 with
      | nil => exact False.elim (hnil_false rfl hM2)
      | cons e2 rest2 =>
        simp only [List.cons_append, List.cons.injEq] at hevs
        rcases hevs with ⟨rfl, hevs⟩
        obtain ⟨vis_c, rfl, hM3⟩ := partyStep_matchesEventsAt_run1 rfl no_runRejected_ev2 hM2
        rw [(s2Clean_runs cl1 cl2).2] at hM3
        cases rest2 with
        | nil => exact False.elim (hnil_false rfl hM3)
        | cons e3 rest3 =>
          simp only [List.cons_append, List.cons.injEq] at hevs
          rcases hevs with ⟨rfl, hevs⟩
          obtain ⟨vis_d, rfl, hM4⟩ := partyStep_matchesEventsAt_run1 rfl no_runRejected_ev3 hM3
          cases rest3 with
          | nil =>
            generalize hss4 : ([] : List Step) = ss_all at hM4
            generalize hevs4 : ([] : List CliEvent) = evs_all at hM4
            cases hM4 with
            | nil _ => simp [vis4Clean, vis3Clean, List.append_assoc]
            | run1 _ _ _ => cases hevs4
            | run0 _ _ _ => cases hevs4
            | env _ _ _ => cases hevs4
          | cons e4 rest4 =>
            simp only [List.cons_append, List.cons.injEq] at hevs
            rcases hevs with ⟨rfl, hevs⟩
            cases rest4 <;> simp at hevs

theorem not_readCollisionCli_ss5Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cl1 cl2 : Nat}
    (hp : FitsPins r)
    (hc : GhostAndSemMatchSetup compI0 r S g)
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64)
    (hsalt1 : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21)
    (hpqm1 : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22)
    (hsalt2 : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23)
    (hpqm2 : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24) :
    ¬ ReadCollisionCli compI0 r S (gClean g) (ss5Clean cl1 cl2)
        [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] := by
  rintro ⟨evs₁, ev, evs₂, ss₁, ss₂, m, vis₁, msgIdx, out, b, t,
    hevs, hss, _, _, _, hM, hm_dec, hsent, hcol⟩
  unfold ss5Clean at hss
  cases ss₁ with
  | nil => simp only [List.nil_append, List.cons.injEq] at hss; rw [← hss.1] at hm_dec; cases hm_dec
  | cons a0 ss₁ =>
    simp only [List.cons_append, List.cons.injEq] at hss; rcases hss with ⟨rfl, hss⟩
    cases ss₁ with
    | nil => simp only [List.nil_append, List.cons.injEq] at hss; rw [← hss.1] at hm_dec; cases hm_dec
    | cons a1 ss₁ =>
      simp only [List.cons_append, List.cons.injEq] at hss; rcases hss with ⟨rfl, hss⟩
      cases ss₁ with
      | nil => simp only [List.nil_append, List.cons.injEq] at hss; rw [← hss.1] at hm_dec; cases hm_dec
      | cons a2 ss₁ =>
        simp only [List.cons_append, List.cons.injEq] at hss; rcases hss with ⟨rfl, hss⟩
        cases ss₁ with
        | nil => simp only [List.nil_append, List.cons.injEq] at hss; rw [← hss.1] at hm_dec; cases hm_dec
        | cons a3 ss₁ =>
          simp only [List.cons_append, List.cons.injEq] at hss; rcases hss with ⟨rfl, hss⟩
          cases ss₁ with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hss; rcases hss with ⟨rfl, _⟩
            dsimp only [s4Clean, Step.decryptMsgIdx?] at hm_dec
            injection hm_dec with hidx; subst hidx
            have hss4 : [s0Clean, s1Clean cl1, s2Clean cl2, s3Clean] = ss4Clean cl1 cl2 := rfl
            rw [hss4] at hM hsent hcol
            have hvis_eq := matchesEvents_ss4Clean_vis_eq hp hevs hM
            subst hvis_eq
            rw [runTrace_ss4Clean hp, Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat37_tr4Clean] at hsent
            injection hsent with ht; subst ht
            rw [runTrace_ss4Clean hp, honestSaltsOf_ss4Clean hp] at hcol
            exact not_recvCollisionOn_c1_of_clean hp hc hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
              (plaintextTerms_vis4Clean cl1 cl2) (sendTerms_vis4Clean cl1 cl2)
              (fun ls hls => by
                rw [storedStates_tr4Clean_eq] at hls
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
                rcases hls with rfl | rfl | rfl | rfl
                · exact Or.inl rfl
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr (Or.inl rfl))
                · exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
              (storedSecrets_tr4Clean_eq cl1 cl2)
              (availableStates_tr4Clean_mem cl1 cl2)
              (skippedKeyStored_tr4Clean_only cl1 cl2)
              hcol
          | cons _ _ => simp at hss


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
