/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2BobCleanB

/-!
# Machine-Checked Spec-Half Disproof for `synthetic-skipped-key-replay`

Proves `spec_half_pinned`, `cliCompFitsPinned_satisfiable`, and `not_signalSessionSecurePlaced_of_implHalf`
for `Symbolic.BugInjection.Synthetic.Witnesses.SkippedKeyReplayCli`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Top

open Arm64.Process (ElfImage)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.Composed.Security (SignalSessionSecurePlaced)
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay

@[expose] public section

attribute [local irreducible] Symbolic.BugInjection.hexBytes

set_option linter.constructorNameAsVariable false

-- END STEP2 CLEAN RUN AND COLLISION DISPROOFS

private theorem matchesEventsAt_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {evs₁ evs₂ : List CliEvent} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss (evs₁ ++ evs₂) vis →
      ∃ ss₁ ss₂ vis₁ vis₂, ss = ss₁ ++ ss₂ ∧ vis = vis₁ ++ vis₂ ∧
        MatchesEventsAt interp r S g initIds tr ss₁ evs₁ vis₁ := by
  induction evs₁ with
  | nil =>
    intro initIds tr ss vis _
    exact ⟨[], ss, [], vis, rfl, rfl, MatchesEventsAt.nil (fun _ h => nomatch h)⟩
  | cons e evs₁ ih =>
    intro initIds tr ss vis hM
    simp only [List.cons_append] at hM
    cases hM with
    | run1 hinv hrun htail =>
      obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hM₁⟩ := ih htail
      refine ⟨_ ++ _ :: ss₁, ss₂, _ ++ vis₁, vis₂, ?_, ?_, MatchesEventsAt.run1 hinv hrun hM₁⟩
      · simp [List.append_assoc]
      · simp [List.append_assoc]
    | run0 hinv hrej htail =>
      obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hM₁⟩ := ih htail
      refine ⟨_ ++ ss₁, ss₂, vis₁, vis₂, ?_, rfl, MatchesEventsAt.run0 hinv hrej hM₁⟩
      simp [List.append_assoc]
    | env hinv henv htail =>
      obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hM₁⟩ := ih htail
      refine ⟨_ ++ _ :: ss₁, ss₂, _ ++ vis₁, vis₂, ?_, ?_, MatchesEventsAt.env hinv henv hM₁⟩
      · simp [List.append_assoc]
      · simp [List.append_assoc]

private theorem stepsWF_prefix :
    ∀ (ss₁ ss₂ : List Step) (tr : ExecTrace),
      StepsWF (ss₁ ++ ss₂) tr → StepsWF ss₁ tr
  | [], _, _, _ => trivial
  | s :: ss₁, ss₂, tr, ⟨hp, hl, hw⟩ => ⟨hp, hl, stepsWF_prefix ss₁ ss₂ (s.next tr) hw⟩

private theorem explains_prefix {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ evs₂ : List CliEvent}
    (hex : Explains interp r S g ss vis (evs₁ ++ evs₂)) :
    ∃ ss₁ vis₁, Explains interp r S g ss₁ vis₁ evs₁ := by
  obtain ⟨hc, hg, ⟨hrlen, hreach, hswf, hfaith⟩, hM⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, rfl, rfl, hM₁⟩ := matchesEventsAt_prefix hM
  refine ⟨ss₁, vis₁, hc, ?_, ⟨hrlen, hreach, stepsWF_prefix ss₁ ss₂ _ hswf, ?_⟩, hM₁⟩
  · refine ⟨fun v hv => hg.1 v (List.mem_append_left _ hv), hg.2.1,
      fun v hv => hg.2.2 v (List.mem_append_left _ hv)⟩
  · intro i j si sj p k b hij hi hj hli hoki hlj
    obtain ⟨hi_lt, _⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hj_lt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hi' : (ss₁ ++ ss₂)[i]? = some si := by rwa [List.getElem?_append_left hi_lt]
    have hj' : (ss₁ ++ ss₂)[j]? = some sj := by rwa [List.getElem?_append_left hj_lt]
    have htake : (ss₁ ++ ss₂).take i = ss₁.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hi_lt)
    exact hfaith i j si sj p k b hij hi' hj' hli (by rwa [htake]) hlj

private theorem not_nextEventCollides_ev3 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0, .run ev1, .run ev2] ev3 := by
  have hp := fitsPins_of_pinned hf
  intro hcol
  have hcmd : ev3.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  obtain ⟨_, hbody⟩ := hcol
  cases hin : ev3.input with
  | nil =>
    have hparse := parsePreKeyWire_ev3
    rw [hin] at hparse; cases hparse
  | cons tag body =>
    rw [hin] at hbody
    dsimp only at hbody
    rcases hbody with ⟨htag, _⟩ | ⟨p, hp_eq, hbranch⟩
    · have hne : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
        have hw := runWrapped_ev3
        unfold runWrapped at hw
        rw [hcmd, hin] at hw
        simpa [bne_iff_ne] using hw
      exact hne htag
    · have hp_c2 : p = p_c2 := by
        have hp3 := parsePreKeyWire_ev3
        rw [hin] at hp3
        exact Option.some.inj (hp_eq.symm.trans hp3)
      subst hp_c2
      have hnb := (noBobBefore3_of_explains_ev012 hp.hb hex).2
      rcases hbranch with ⟨hkb, _⟩ | ⟨_, hpre⟩
      · exact hnb hkb
      · rcases hpre.2 with hkyb | hall
        · exact not_kyberMismatch_p_c2 hp hkyb
        · obtain ⟨cl1, cl2, hcl1, hcl2, hsalt1, hpqm1, hsalt2, hpqm2⟩ :=
            extract_spqrPins_of_explains_ev012 hp hex
          obtain ⟨hexClean, hrepClean⟩ :=
            explains_clean_ev012 hp hex hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
          rw [← hin] at hall
          exact not_bobSessionStartCollides_c2 hp hex.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
            (hall (gClean g) (ss3Clean cl1 cl2) (vis3Clean cl1 cl2)
              hexClean not_readCollisionCli_ev012 _ hrepClean)

private theorem not_nextEventCollides_ev4 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3] ev4 := by
  have hp := fitsPins_of_pinned hf
  intro hcol
  have hcmd : ev4.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  obtain ⟨_, hbody⟩ := hcol
  cases hin : ev4.input with
  | nil =>
    have hparse := parsePreKeyWire_ev4
    rw [hin] at hparse; cases hparse
  | cons tag body =>
    rw [hin] at hbody
    dsimp only at hbody
    rcases hbody with ⟨htag, _⟩ | ⟨p, hp_eq, hbranch⟩
    · have hne : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
        have hw := runWrapped_ev4
        unfold runWrapped at hw
        rw [hcmd, hin] at hw
        simpa [bne_iff_ne] using hw
      exact hne htag
    · have hp_c1 : p = p_c1 := by
        have hp4 := parsePreKeyWire_ev4
        rw [hin] at hp4
        exact Option.some.inj (hp_eq.symm.trans hp4)
      subst hp_c1
      have hkb := knownBaseKeyOn_of_explains_ev0123 hp.ha hp.hb hex
      rcases hbranch with ⟨_, hsig⟩ | ⟨hnkb, _⟩
      · obtain ⟨ss₀, vis₀, hex₀⟩ := explains_prefix
          (evs₁ := [.run ev0, .run ev1, .run ev2]) (evs₂ := [.run ev3]) hex
        obtain ⟨cl1, cl2, hcl1, hcl2, hsalt1, hpqm1, hsalt2, hpqm2⟩ :=
          extract_spqrPins_of_explains_ev012 hp hex₀
        have hex4 := explains_clean_ev0123 hp hex₀ hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
        have hex5 := explains_clean_ev01234 hp hex₀ hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
        have hrep4 : m1Clean cl1 ∈ recvRepresentationsOn compI0 S (gClean g)
            (runTrace r (ss4Clean cl1 cl2)) p_c1.message := by
          rw [runTrace_ss4Clean hp]
          exact m1Clean_mem_recvReps_of_ak hp hex₀.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
            (attackerKnows_c1_tr4Clean cl1 cl2)
        have hno_recv : ¬ RecvCollisionOn compI0 r S (gClean g)
            (runTrace r (ss4Clean cl1 cl2)) (vis4Clean cl1 cl2)
            (honestSaltsOf r (ss4Clean cl1 cl2)) (m1Clean cl1) := by
          rw [runTrace_ss4Clean hp, honestSaltsOf_ss4Clean hp]
          exact not_recvCollisionOn_c1_of_clean hp hex₀.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
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
        have ⟨_, hsig_all⟩ := hsig.2.2
        rcases hsig_all (gClean g) (ss4Clean cl1 cl2) (vis4Clean cl1 cl2)
            hex4 not_readCollisionCli_ss4Clean with hall | ⟨_, himp⟩
        · rcases hall (m1Clean cl1) hrep4 with hrc | hrsc
          · exact hno_recv hrc
          · rw [runTrace_ss4Clean hp] at hrsc
            let pts : List DY.Bytes := [randTerm 31 32, randTerm 38 32]
            have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hex₀.1 hcl1 hcl2
              (by simp [pts]) (by simp [pts]) hsalt1 hpqm1 hsalt2 hpqm2
            exact not_reselectCollisionOn_c1 hp hw
              (availableStates_tr4Clean_mem cl1 cl2)
              (skippedKeyStored_tr4Clean_only cl1 cl2) hrsc
        · refine hno_recv (himp (m1Clean cl1) hrep4 ?_)
          refine ⟨[], s4Clean, 37, gClean g, vis5Clean cl1 cl2,
            fun _ h => False.elim (List.not_mem_nil h), rfl, rfl, fun _ _ => rfl, ?_, ?_⟩
          · rw [List.map_nil, List.append_nil, runTrace_ss4Clean hp,
              Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1, hat37_tr4Clean]
          · have hss5 : ss4Clean cl1 cl2 ++ [].map Step.network ++ [s4Clean] = ss5Clean cl1 cl2 := rfl
            have hev4 : ([.run ev0, .run ev1, .run ev2, .run ev3] : List CliEvent) ++ [.run ev4] =
                [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] := rfl
            rw [hss5, hev4]
            exact hex5
      · exact hnkb hkb

private theorem not_nextEventCollides_ev5 {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4]) :
    ¬ NextEventCollides compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] ev5 := by
  have hp := fitsPins_of_pinned hf
  intro hcol
  have hcmd : ev5.cmd = .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  unfold NextEventCollides at hcol
  rw [hcmd] at hcol
  dsimp only at hcol
  obtain ⟨_, hbody⟩ := hcol
  cases hin : ev5.input with
  | nil =>
    have hparse := parsePreKeyWire_ev5
    rw [hin] at hparse; cases hparse
  | cons tag body =>
    rw [hin] at hbody
    dsimp only at hbody
    rcases hbody with ⟨htag, _⟩ | ⟨p, hp_eq, hbranch⟩
    · have hne : tag ≠ DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
        have hw := runWrapped_ev5
        unfold runWrapped at hw
        rw [hcmd, hin] at hw
        simpa [bne_iff_ne] using hw
      exact hne htag
    · have hp_c1 : p = p_c1 := by
        have hp5 := parsePreKeyWire_ev5
        rw [hin] at hp5
        exact Option.some.inj (hp_eq.symm.trans hp5)
      subst hp_c1
      have hkb := knownBaseKeyOn_of_explains_ev01234 hp.ha hp.hb hex
      rcases hbranch with ⟨_, hsig⟩ | ⟨hnkb, _⟩
      · obtain ⟨ss₀, vis₀, hex₀⟩ := explains_prefix
          (evs₁ := [.run ev0, .run ev1, .run ev2]) (evs₂ := [.run ev3, .run ev4]) hex
        obtain ⟨cl1, cl2, hcl1, hcl2, hsalt1, hpqm1, hsalt2, hpqm2⟩ :=
          extract_spqrPins_of_explains_ev012 hp hex₀
        have hex5 := explains_clean_ev01234 hp hex₀ hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
        have hrep5 : m1Clean cl1 ∈ recvRepresentationsOn compI0 S (gClean g)
            (runTrace r (ss5Clean cl1 cl2)) p_c1.message := by
          rw [runTrace_ss5Clean hp]
          exact m1Clean_mem_recvReps_of_ak hp hex₀.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
            (attackerKnows_c1_tr5Clean cl1 cl2)
        have hno_recv : ¬ RecvCollisionOn compI0 r S (gClean g)
            (runTrace r (ss5Clean cl1 cl2)) (vis5Clean cl1 cl2)
            (honestSaltsOf r (ss5Clean cl1 cl2)) (m1Clean cl1) := by
          rw [runTrace_ss5Clean hp, honestSaltsOf_ss5Clean hp]
          exact not_recvCollisionOn_c1_of_clean hp hex₀.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
            (plaintextTerms_vis5Clean cl1 cl2) (sendTerms_vis5Clean cl1 cl2)
            (fun ls hls => by
              rw [storedStates_tr5Clean_eq] at hls
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
              exact hls)
            (storedSecrets_tr5Clean_eq cl1 cl2)
            (availableStates_tr5Clean_mem cl1 cl2)
            (skippedKeyStored_tr5Clean_only cl1 cl2)
        have hno_read := not_readCollisionCli_ss5Clean hp hex₀.1 hcl1 hcl2 hsalt1 hpqm1 hsalt2 hpqm2
        have ⟨_, hsig_all⟩ := hsig.2.2
        rcases hsig_all (gClean g) (ss5Clean cl1 cl2) (vis5Clean cl1 cl2) hex5 hno_read
            with hall | ⟨⟨_, _, hAcc⟩, _⟩
        · rcases hall (m1Clean cl1) hrep5 with hrc | hrsc
          · exact hno_recv hrc
          · rw [runTrace_ss5Clean hp] at hrsc
            let pts : List DY.Bytes := [randTerm 31 32, randTerm 38 32]
            have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hex₀.1 hcl1 hcl2
              (by simp [pts]) (by simp [pts]) hsalt1 hpqm1 hsalt2 hpqm2
            exact not_reselectCollisionOn_c1 hp hw
              (availableStates_tr5Clean_mem cl1 cl2)
              (skippedKeyStored_tr5Clean_only cl1 cl2) hrsc
        · obtain ⟨_, _, _, g₁, vis₁, _, _, _, _, _, hex_full⟩ := hAcc
          have htr_eq : ([.run ev0, .run ev1, .run ev2, .run ev3, .run ev4] : List CliEvent) ++ [.run ev5] =
              trace := rfl
          rw [htr_eq] at hex_full
          exact not_explains_trace hf S g₁ _ vis₁ hex_full
      · exact hnkb hkb

private def NoCollisionFrom (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (evs₁ rest : List CliEvent) : Prop :=
  ∀ δ ev evs₂ g ss vis,
    rest = δ ++ (.run ev :: evs₂) →
    Explains interp r S g ss vis (evs₁ ++ δ) →
    ¬ NextEventCollides interp r S g ss vis (evs₁ ++ δ) ev

private theorem not_collisionAfterExplainedPrefix_of_from {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {evs : List CliEvent}
    (h : NoCollisionFrom interp r S [] evs) :
    ¬ CollisionAfterExplainedPrefix interp r S evs := by
  rintro ⟨evs₁, ev, evs₂, g, ss, vis, rfl, hExp, hCol⟩
  exact h evs₁ ev evs₂ g ss vis rfl (by simpa using hExp) (by simpa using hCol)

private theorem not_collision_nil {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} :
    NoCollisionFrom interp r S evs₁ [] := by
  intro δ _ _ _ _ _ heq
  cases δ <;> cases heq

private theorem not_collision_step_env {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {e : DY.Libsignal.HwEvents.EnvEvent}
    {rest : List CliEvent}
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [.env e]) rest) :
    NoCollisionFrom interp r S evs₁ (.env e :: rest) := by
  intro δ ev evs₂ g ss vis heq hExp
  cases δ with
  | nil => cases heq
  | cons d δ' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hassoc : evs₁ ++ (.env e :: δ') = (evs₁ ++ [.env e]) ++ δ' := by simp [List.append_assoc]
    rw [hassoc] at hExp ⊢
    exact h_tail δ' ev evs₂ g ss vis rfl hExp

private theorem not_collision_step_run {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {ev : RunEvent} {rest : List CliEvent}
    (h_here : ∀ g ss vis, Explains interp r S g ss vis evs₁ →
      ¬ NextEventCollides interp r S g ss vis evs₁ ev)
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [.run ev]) rest) :
    NoCollisionFrom interp r S evs₁ (.run ev :: rest) := by
  intro δ ev' evs₂ g ss vis heq hExp
  cases δ with
  | nil =>
    simp only [List.nil_append, List.cons.injEq, CliEvent.run.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rw [List.append_nil] at hExp ⊢
    exact h_here g ss vis hExp
  | cons d δ' =>
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hassoc : evs₁ ++ (.run ev :: δ') = (evs₁ ++ [.run ev]) ++ δ' := by simp [List.append_assoc]
    rw [hassoc] at hExp ⊢
    exact h_tail δ' ev' evs₂ g ss vis rfl hExp

private def isIrrelevantCliEvent : CliEvent → Bool
  | .env _ => true
  | .run ev =>
    match ev.cmd with
    | .init _ _ => true
    | .recv _ =>
      match ev.exit with
      | some (0, _) => ev.input.isEmpty
      | _ => true
    | .send _ => false

private theorem nextEventCollides_AutoFalse {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ : List CliEvent} {ev : RunEvent}
    (hirr : isIrrelevantCliEvent (.run ev) = true := by rfl) :
    ¬ NextEventCollides interp r S g ss vis evs₁ ev := by
  dsimp only [isIrrelevantCliEvent] at hirr
  unfold NextEventCollides
  cases hcmd : ev.cmd with
  | init _ _ => simp
  | send _ => simp [hcmd] at hirr
  | recv _ =>
    rw [hcmd] at hirr
    dsimp only at hirr ⊢
    rintro ⟨⟨out, hexit⟩, hbody⟩
    rw [hexit] at hirr
    cases hin : ev.input with
    | nil => rw [hin] at hbody; exact hbody
    | cons _ _ => rw [hin] at hirr; cases hirr

private theorem not_collision_step_irrelevant {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {evs₁ : List CliEvent} {e : CliEvent} {rest : List CliEvent}
    (hirr : isIrrelevantCliEvent e = true := by rfl)
    (h_tail : NoCollisionFrom interp r S (evs₁ ++ [e]) rest) :
    NoCollisionFrom interp r S evs₁ (e :: rest) := by
  cases e with
  | env _ => exact not_collision_step_env h_tail
  | run _ => exact not_collision_step_run (fun _ _ _ _ => nextEventCollides_AutoFalse hirr) h_tail

theorem not_collisionAfterExplainedPrefix_trace {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (hf : cliCompFitsPinned iw r) :
    ∀ S, ¬ CollisionAfterExplainedPrefix compI0 r S trace := by
  intro S
  rw [trace_eq]
  apply not_collisionAfterExplainedPrefix_of_from
  apply not_collision_step_irrelevant rfl
  apply not_collision_step_run
  · intro g ss vis hex; exact not_nextEventCollides_ev1 hf.1.1.1 hex
  apply not_collision_step_run
  · intro g ss vis hex; exact not_nextEventCollides_ev2 hf hex
  apply not_collision_step_run
  · intro g ss vis hex; exact not_nextEventCollides_ev3 hf hex
  apply not_collision_step_run
  · intro g ss vis hex; exact not_nextEventCollides_ev4 hf hex
  apply not_collision_step_run
  · intro g ss vis hex; exact not_nextEventCollides_ev5 hf hex
  exact not_collision_nil


/-- **SpecHalf disproof** for `synthetic-skipped-key-replay`. -/
theorem spec_half_pinned :
    cliCompShape.SpecHalf
      (Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.CliSetupMatchesPinned Witnesses.SkippedKeyReplayCli.setup)
      Witnesses.SkippedKeyReplayCli.trace := by
  intro iw r hf
  have hFits : fits iw r := cliCompFitsPinned_sub_fits iw r hf
  refine ⟨hFits.1.1, ?_⟩
  intro S _ hOr
  dsimp [cliCompShape] at hOr
  have hiw : iw.1 = compI0 := hf.1.2.1
  rw [hiw] at hOr
  rcases hOr with ⟨g, ss, vis, hExp⟩ | hCol
  · exact not_explains_trace hf S g ss vis hExp
  · exact not_collisionAfterExplainedPrefix_trace hf S hCol

/-- **Non-vacuity** of `cliCompFitsPinned` on `SkippedKeyReplayCli.setup`. -/
theorem cliCompFitsPinned_satisfiable :
    ∃ iw r,
      Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.CliSetupMatchesPinned
        Witnesses.SkippedKeyReplayCli.setup iw r :=
  Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.cliCompFitsPinned_satisfiable

/-- **Top-level `SignalSessionSecurePlaced` regression disproof** for `synthetic-skipped-key-replay`. -/
theorem not_signalSessionSecurePlaced_of_implHalf {bytes : List (BitVec 8)}
    {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hi : ∀ elf : ElfImage, ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf
        (Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable.CliSetupMatchesPinned Witnesses.SkippedKeyReplayCli.setup)
        elf Witnesses.SkippedKeyReplayCli.trace) :
    ¬ SignalSessionSecurePlaced bytes :=
  Symbolic.BugInjection.not_signalSessionSecurePlaced_of_witness
    hls hmg
    spec_half_pinned
    hi
    Symbolic.BugInjection.Proofs.Common.CoinsFresh.coinsFresh_skippedKeyReplayCli

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Top
