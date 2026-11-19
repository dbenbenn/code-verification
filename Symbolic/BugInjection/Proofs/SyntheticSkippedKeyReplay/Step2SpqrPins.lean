/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2SpqrHelpers

/-!
# Prefix Extraction of Alice SPQR Coins & Concrete Evaluations (`extract_spqrPins_of_explains_ev012`)
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

local macro "at?_localEncTr_tac" : tactic =>
  `(tactic| (dsimp only [localEncTr]
             repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [length_append_entry]; omega)])
             rw [at?_append_eq_of_eq _ _ (by simp only [length_append_entry]; try omega)]
             rfl))


set_option maxHeartbeats 1600000 in
theorem extract_spqrPins_of_explains_ev012 {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hp : FitsPins r)
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2]) :
    ∃ cl1 cl2,
      (cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64) ∧
      (cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) ∧
      gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21 ∧
      gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22 ∧
      gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23 ∧
      gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24 := by
  obtain ⟨hcompat, hgwf, ⟨_, hreach₀, hswf, hfaith⟩, hme⟩ := hex
  set tr₀ := setupTrace r
  have htr₀_eq : tr₀ = setupTrace r0 := setupTrace_eq_of_fits hp
  obtain ⟨pre0, s0, ss1, v0, vs1, hss0, hvis0, hinv0, hRun0, hM1⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hme
  obtain ⟨pre1, s1, ss2, v1, vs2, hss1, hvis1, hinv1, hRun1, hM2⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM1
  obtain ⟨pre2, s2, post, v2, vs3, hss2, hvis2, hinv2, hRun2, hM3⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hM2
  have ⟨_, hvs3_nil⟩ : (∀ x ∈ post, x.cls = .invisible) ∧ vs3 = [] := by
    cases hM3 with
    | nil h => exact ⟨h, rfl⟩
  subst hvs3_nil
  rw [List.append_nil] at hvis2
  subst hvis2 hss2 hvis1 hss1 hvis0 hss0
  set tr₁ := runSteps pre0 tr₀ with htr₁_def
  obtain ⟨hswf0, hs0_pre, _, hswf_after0⟩ :=
    stepsWF_split pre0 (s0 :: (pre1 ++ s1 :: (pre2 ++ s2 :: post))) tr₀ hswf
  obtain ⟨_, _, hs1_lok, hswf_after1⟩ :=
    stepsWF_split pre1 (s1 :: (pre2 ++ s2 :: post)) (s0.next tr₁) hswf_after0
  obtain ⟨_, _, hs2_lok, _⟩ :=
    stepsWF_split pre2 (s2 :: post) (s1.next (runSteps pre1 (s0.next tr₁))) hswf_after1
  have hreach₁ : tr₁.Reachable reachability := reachable_of_stepsWF pre0 hreach₀ hswf0
  have hreach_s0 : (s0.next tr₁).Reachable reachability :=
    DY.Trace.Reachable.Step s0.toInput hs0_pre hreach₁
  obtain ⟨_, hparty0, hfits0, hpeer0, hok0, _, hv0_eq, inp0, drs0, outs0, hv0_split, hinp0, hdrs0, houts0, _, _⟩ := hRun0
  have hcmd0 : ev0.cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" := rfl
  rw [hcmd0] at hfits0
  obtain ⟨a, b, idS, regB, hb, hs0_eq⟩ := step_of_fitsCmd_init hfits0
  rw [hs0_eq] at hparty0 hpeer0 hok0 hv0_eq hreach_s0 hs1_lok hs2_lok hRun1 hRun2 hfaith
  have ha_eq : a = "alice" := Option.some.inj hparty0
  have hb_eq : b = "bob" := hpeer0.trans hp.hb
  subst ha_eq hb_eq
  obtain ⟨ikA, ikB, spk, spkSig, pqpk, pqpkSig, opk,
    hspk, hspkSig, hpq, hpqSig, hopk, hnext0⟩ := aliceStart_ok_eq_localAliceStartTr hok0
  set o₀ := CompTrace.aliceOut tr₁ ikA ikB spk pqpk opk
  have hreach_la : (localAliceStartTr tr₁ "alice" "bob" o₀).Reachable reachability := by
    rwa [← hnext0]
  dsimp only [stepView] at hv0_eq
  rw [ite_eq_left_iff.mpr (fun h => absurd hok0 h), hnext0,
    exposures_localAliceStartTr, List.append_nil] at hv0_eq
  have hopk_none : opk = none := by
    rcases hopk with ⟨_, hopk_n⟩ | ⟨idx, u, hhb_s, _, hu⟩
    · exact hopk_n
    · exfalso
      have hv_al := hv0_eq.trans (aliceVis_localAliceStartTr tr₁ "alice" "bob" o₀ hb)
      rw [hv0_split] at hv_al
      injection hv_al with hinp_eq _
      have hkind0 : inputKind ev0 = .recv := rfl
      rw [hkind0, hinp_eq] at hinp0
      have hrec5 : received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig, u] := by
        rw [hhb_s]
        change received tr₁ [hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig, idx] = [spk, spkSig, pqpk, pqpkSig, u]
        simp only [received, List.filterMap_cons, List.filterMap_nil,
          getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
          getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig,
          getMessageSentAt_of_netMsgAt hu]
      have hbm := hinp0.2; dsimp only at hbm; rw [hrec5] at hbm
      exact ev0_input_getElem4_ne_one hbm.2.1
  subst hopk_none
  set o := CompTrace.aliceOut tr₁ ikA ikB spk pqpk none
  have hv0_al : v0 =
      { kind := .recv, terms := received tr₁ ([hb.spk, hb.spkSig, hb.pqpk, hb.pqpkSig] ++ hb.opk.toList),
        layout := .bundle, anchor := none } ::
      rngEntry (randTerm tr₁.length 32) ::
      (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
        [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }]) :=
    hv0_eq.trans (aliceVis_localAliceStartTr tr₁ "alice" "bob" o hb)
  have houts0_nil : outs0 = [] := houts0
  subst houts0_nil
  rw [List.append_nil] at hv0_split
  have hdrs0_eq : drs0 =
      rngEntry (randTerm tr₁.length 32) ::
      (kyberCoinEntries (randTerm (tr₁.length + 1) 32) ++
        [{ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) }]) :=
    (List.cons.inj (hv0_split.symm.trans hv0_al)).2
  rw [hdrs0_eq] at hdrs0
  have hl_ek : (g.σ tr₁.length 32).length = 32 := by
    refine hgwf.1 (rngEntry (randTerm tr₁.length 32)) ?_ rfl tr₁.length 32 (by decide) (by simp [rngEntry])
    apply List.mem_append_left; rw [hv0_al]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hl_ent : (g.σ (tr₁.length + 1) 32).length = 32 := by
    refine hgwf.1 ⟨.rng, [randTerm (tr₁.length + 1) 32], .kyberCoin 0, none⟩ ?_ rfl (tr₁.length + 1) 32 (by decide) (by simp)
    apply List.mem_append_left; rw [hv0_al]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
    unfold kyberCoinEntries; exact List.mem_map.mpr ⟨0, by decide, rfl⟩
  have hl_dhs : (g.σ (tr₁.length + 2) 32).length = 32 := by
    refine hgwf.1 { rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } ?_ rfl (tr₁.length + 2) 32 (by decide) (by simp [rngEntry])
    apply List.mem_append_left; rw [hv0_al]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  obtain ⟨hσ_ek, hσ_ent, hσ_dhs⟩ := extract_aliceStart_draws hl_ek hl_ent hl_dhs hdrs0
  -- Extract exact symbolic setup keys via spqrInv
  have hncb₁ : NoCompOrBreak tr₁ := by
    intro j ev hat
    rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hinv0 j] at hat
    exact noCompOrBreak_setupTrace r j ev hat
  have hncb₂ : NoCompOrBreak (localAliceStartTr tr₁ "alice" "bob" o) := by
    intro j ev hat
    dsimp only [localAliceStartTr] at hat
    have hat := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl hat))
    rcases pqEv_append_same_loc hat with hat | ⟨_, hev⟩
    · have hat := pqEv_append_other_loc rfl (pqEv_append_other_loc rfl
        (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl (pqEv_append_other_loc rfl hat))))
      exact hncb₁ j ev hat
    · subst hev; exact ⟨(fun _ _ h => nomatch h), (fun h => nomatch h)⟩
  have had_ev : (localAliceStartTr tr₁ "alice" "bob" o).EventLoggedAt
      (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone "alice" "bob" o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys) (tr₁.length + 5) := by
    have hp5 := (getEventAt_pq_localAliceStartTr tr₁ "alice" "bob" o).2.2.2.2.2.1
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hp5
    rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
    cases hp : ((localAliceStartTr tr₁ "alice" "bob" o).at? (tr₁.length + 5) : Option CompTrace.PQXDHEntry) with
    | none => rw [hp] at hp5; cases hp5
    | some e => rcases e with ⟨ev'⟩; rw [hp] at hp5; injection hp5 with hev'; subst hev'; rfl
  obtain ⟨_, sA, _, _, hsA_at, hikA_eq, _, _, hbun_ok⟩ :=
    (Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable _ hreach_la).aliceDone
      "alice" "bob" o.ikA o.ikB o.spk o.pqpk o.opk o.ek o.ct o.keys (tr₁.length + 5) had_ev
  have hikA_clean : ikA = ikASkClean := by
    obtain ⟨idxA, rfl, _, hevA⟩ := hsA_at
    have hkA := pqEv_tr0_of_localAliceStartTr hinv0 htr₁_def "alice" "bob" o hevA
      (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
    rw [htr₀_eq] at hkA
    rcases pqEv_setupTrace_r0 hkA with ⟨hidx, _⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
    · have h0 : idxA = 0 := by omega
      subst h0
      change DY.DiffieHellman.dhPk ikA = DY.DiffieHellman.dhPk ikASkClean at hikA_eq
      exact dhPk_inj_loc hikA_eq
    · injection h2 with hparty; exact absurd hparty (by decide)
    · exact False.elim h3
    · exact False.elim h4
  have ⟨hikB_clean, hspk_clean, hpqpk_clean⟩ :
      ikB = ikBPkClean ∧ spk = spkBPkClean ∧ pqpk = pqpkBClean := by
    rcases hbun_ok with ⟨sB, sS, sQ, hsB, hikB_eq, hsS, hspk_eq, hsQ, hpq_eq⟩ |
        ⟨j, hj⟩ | ⟨j, hj⟩
    · have hsB_clean : sB = ikBSkClean := by
        obtain ⟨idxB, rfl, _, hevB⟩ := hsB
        have hkB := pqEv_tr0_of_localAliceStartTr hinv0 htr₁_def "alice" "bob" o hevB
          (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
        rw [htr₀_eq] at hkB
        rcases pqEv_setupTrace_r0 hkB with ⟨_, h1⟩ | ⟨hidx, _⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
        · injection h1 with hparty; exact absurd hparty (by decide)
        · have h5 : idxB = 5 := by omega
          subst h5; rfl
        · exact False.elim h3
        · exact False.elim h4
      have hsS_clean : sS = spkBSkClean := by
        obtain ⟨idxS, rfl, _, _, hevS⟩ := hsS
        have hkS := pqEv_tr0_of_localAliceStartTr hinv0 htr₁_def "alice" "bob" o hevS
          (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
        rw [htr₀_eq] at hkS
        rcases pqEv_setupTrace_r0 hkS with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨hidx, _⟩ | ⟨_, h4⟩
        · cases h1
        · cases h2
        · have h10 : idxS = 10 := by omega
          subst h10; rfl
        · exact False.elim h4
      have hsQ_clean : sQ = pqskBClean := by
        obtain ⟨idxQ, rfl, _, _, hevQ⟩ := hsQ
        have hkQ := pqEv_tr0_of_localAliceStartTr hinv0 htr₁_def "alice" "bob" o hevQ
          (fun _ _ _ _ _ _ _ _ _ _ h => nomatch h)
        rw [htr₀_eq] at hkQ
        rcases pqEv_setupTrace_r0 hkQ with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨hidx, _⟩
        · cases h1
        · cases h2
        · exact False.elim h3
        · have h16 : idxQ = 16 := by omega
          subst h16; rfl
      change ikB = DY.DiffieHellman.dhPk sB at hikB_eq
      change spk = DY.DiffieHellman.dhPk sS at hspk_eq
      change pqpk = DY.PQKem.kemPk sQ at hpq_eq
      rw [hsB_clean] at hikB_eq
      rw [hsS_clean] at hspk_eq
      rw [hsQ_clean] at hpq_eq
      exact ⟨hikB_eq, hspk_eq, hpq_eq⟩
    · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
      exact False.elim ((hncb₂ j _ hj.1).1 "bob" o.ikB rfl)
    · rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hj
      exact False.elim ((hncb₂ j _ hj.1).2 rfl)
  subst hikA_clean hikB_clean hspk_clean hpqpk_clean
  -- Analyze s1 (ev1)
  rw [hnext0] at hs1_lok hs2_lok hRun1 hRun2
  set tr₂ := runSteps pre1 (localAliceStartTr tr₁ "alice" "bob" o) with htr₂_def
  obtain ⟨_, _, hfits1, _, hok1, _, hv1_eq, inp1, drs1, outs1, hv1_split, hinp1, hdrs1, houts1, _, _⟩ := hRun1
  have hcmd1 : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  rw [hcmd1] at hfits1
  rcases step_of_fitsCmd_send hfits1 with ⟨me1, stIdx1, cl1, pqIdx1, hs1_eq⟩ | ⟨me1, stIdx1, hs1_eq⟩
  · rw [hs1_eq] at hok1 hs1_lok hv1_eq hs2_lok hRun2 hfaith
    obtain ⟨st₁, hst₁_at, hcl1, hnext1⟩ := messageEncrypt_ok_eq_localEncTr hok1 hs1_lok
    have hnoTR₁ : NoTRState tr₁ := fun k => by
      rw [htr₁_def, at?_runSteps_invisible (fun _ => rfl) tr₀ hinv0 k]
      exact noTRState_setupTrace r k
    have hat_tr₂ : ∀ j, (tr₂.at? j : Option CompTrace.TRStEntry) =
        if j = tr₁.length + 8 then some (CompTrace.TRStE "alice" (localAliceStartState tr₁ "bob" o)) else none := by
      intro j
      rw [htr₂_def, at?_runSteps_invisible (fun _ => rfl) _ hinv1 j,
        at?_trSt_localAliceStartTr_of_noTRState hnoTR₁ "alice" "bob" o j]
    have hstIdx1_eq : stIdx1 = tr₁.length + 8 := by
      rw [hat_tr₂ stIdx1] at hst₁_at
      by_contra hne; simp [hne] at hst₁_at
    subst hstIdx1_eq
    rw [hat_tr₂ (tr₁.length + 8)] at hst₁_at
    simp only [↓reduceIte, Option.some.injEq] at hst₁_at
    cases hst₁_at
    set stA₀ := localAliceStartState tr₁ "bob" o
    set m₁ := randTerm tr₂.length 32
    set coins₁ := randTerm (tr₂.length + 1) cl1
    set pqSalt₁ := (DY.Spqr.spqrSend stA₀.spqr coins₁).2.1
    set pqm₁ := (DY.Spqr.spqrSend stA₀.spqr coins₁).2.2
    -- Analyze s2 (ev2)
    rw [hnext1] at hs2_lok hRun2
    set tr₃ := runSteps pre2 (localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁) with htr₃_def
    obtain ⟨_, _, hfits2, _, hok2, _, hv2_eq, inp2, drs2, outs2, hv2_split, hinp2, hdrs2, houts2, _, _⟩ := hRun2
    have hcmd2 : ev2.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
    rw [hcmd2] at hfits2
    rcases step_of_fitsCmd_send hfits2 with ⟨me2, stIdx2, cl2, pqIdx2, hs2_eq⟩ | ⟨me2, stIdx2, hs2_eq⟩
    · rw [hs2_eq] at hok2 hs2_lok hv2_eq hfaith
      obtain ⟨st₂, hst₂_at, hcl2, hnext2⟩ := messageEncrypt_ok_eq_localEncTr hok2 hs2_lok
      -- Rule out stIdx2 = tr₁.length + 8 via StepsStateFaithful
      have hstIdx2_ne : stIdx2 ≠ tr₁.length + 8 := by
        intro hst2_eq
        subst hst2_eq
        have hme2 : me2 = "alice" := by
          rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hinv2] at hst₂_at
          have hlt : tr₁.length + 8 < tr₂.length := by
            by_contra hge
            have hnone : (tr₂.at? (tr₁.length + 8) : Option CompTrace.TRStEntry) = none :=
              Symbolic.Swarm.CREF.at?_ge_length tr₂ (Nat.not_lt.mp hge)
            rw [hat_tr₂ (tr₁.length + 8)] at hnone
            simp at hnone
          dsimp only [localEncTr] at hst₂_at
          repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by first | exact hlt | (simp only [length_append_entry]; omega))] at hst₂_at)
          rw [hat_tr₂ (tr₁.length + 8)] at hst₂_at
          simp only [↓reduceIte, Option.some.injEq] at hst₂_at
          cases hst₂_at; rfl
        subst hme2
        let s0_step := Step.aliceStart "alice" "bob" idS regB hb
        let s1_step := Step.messageEncrypt "alice" (tr₁.length + 8) cl1 pqIdx1
        let s2_step := Step.messageEncrypt "alice" (tr₁.length + 8) cl2 pqIdx2
        let i1 := pre0.length + 1 + pre1.length
        let i2 := pre0.length + 1 + pre1.length + 1 + pre2.length
        have hi1 : (pre0 ++ s0_step :: (pre1 ++ s1_step :: (pre2 ++ s2_step :: post)))[i1]? = some s1_step := by
          rw [List.getElem?_append_right (by omega)]
          have hsub1 : i1 - pre0.length = pre1.length + 1 := by omega
          rw [hsub1, List.getElem?_cons_succ, List.getElem?_append_right (by omega), Nat.sub_self]
          rfl
        have hi2 : (pre0 ++ s0_step :: (pre1 ++ s1_step :: (pre2 ++ s2_step :: post)))[i2]? = some s2_step := by
          rw [List.getElem?_append_right (by omega)]
          have hsub1 : i2 - pre0.length = (pre1.length + 1 + pre2.length) + 1 := by omega
          rw [hsub1, List.getElem?_cons_succ, List.getElem?_append_right (by omega)]
          have hsub2 : pre1.length + 1 + pre2.length - pre1.length = pre2.length + 1 := by omega
          rw [hsub2, List.getElem?_cons_succ, List.getElem?_append_right (by omega), Nat.sub_self]
          rfl
        have htake1 : (pre0 ++ s0_step :: (pre1 ++ s1_step :: (pre2 ++ s2_step :: post))).take i1 =
            pre0 ++ s0_step :: pre1 := by
          have hassoc : pre0 ++ s0_step :: (pre1 ++ s1_step :: (pre2 ++ s2_step :: post)) =
              (pre0 ++ s0_step :: pre1) ++ (s1_step :: (pre2 ++ s2_step :: post)) := by
            simp [List.append_assoc]
          have hlen_p : (pre0 ++ s0_step :: pre1).length = i1 := by simp [i1]; omega
          rw [hassoc, ← hlen_p, List.take_left]
        have htr_take1 : runTrace r (pre0 ++ s0_step :: pre1) = tr₂ := by
          unfold runTrace
          rw [runSteps_append_local]; dsimp only [runSteps]
          change runSteps pre1 (s0_step.next tr₁) = tr₂
          rw [hnext0]
        exact hfaith i1 i2 s1_step s2_step "alice" (tr₁.length + 8) true (by omega)
          hi1 hi2 rfl (by rw [htake1, htr_take1]; exact hok1) rfl
      -- Identify stIdx2 = tr₂.length + 5 and st₂ = localEncState stA₀ coins₁
      rw [htr₃_def, at?_runSteps_invisible (fun _ => rfl) _ hinv2] at hst₂_at
      have hstIdx2_eq : stIdx2 = tr₂.length + 5 := by
        by_cases hlt : stIdx2 < tr₂.length
        · dsimp only [localEncTr] at hst₂_at
          repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by first | exact hlt | (simp only [length_append_entry]; omega))] at hst₂_at)
          rw [hat_tr₂ stIdx2] at hst₂_at
          simp [hstIdx2_ne] at hst₂_at
        · by_cases h5 : stIdx2 = tr₂.length + 5
          · exact h5
          · by_cases hge7 : tr₂.length + 7 ≤ stIdx2
            · rw [Symbolic.Swarm.CREF.at?_ge_length _ (by dsimp only [localEncTr]; simp only [length_append_entry]; omega)] at hst₂_at
              cases hst₂_at
            · have hcases : stIdx2 = tr₂.length ∨ stIdx2 = tr₂.length + 1 ∨ stIdx2 = tr₂.length + 2 ∨
                  stIdx2 = tr₂.length + 3 ∨ stIdx2 = tr₂.length + 4 ∨ stIdx2 = tr₂.length + 6 := by omega
              rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? tr₂.length : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 1) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 2) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 3) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 4) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
              · have hn : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 6) : Option CompTrace.TRStEntry) = none := by at?_localEncTr_tac
                rw [hn] at hst₂_at; cases hst₂_at
      subst hstIdx2_eq
      have hat5 : ((localEncTr tr₂ "alice" (tr₁.length + 8) cl1 stA₀ pqSalt₁).at? (tr₂.length + 5) : Option CompTrace.TRStEntry) =
          some (CompTrace.TRStE "alice" (localEncState stA₀ coins₁)) := by at?_localEncTr_tac
      rw [hat5] at hst₂_at
      simp only [Option.some.injEq] at hst₂_at
      cases hst₂_at
      set m₂ := randTerm tr₃.length 32
      set coins₂ := randTerm (tr₃.length + 1) cl2
      set pqSalt₂ := (DY.Spqr.spqrSend (localEncState stA₀ coins₁).spqr coins₂).2.1
      set pqm₂ := (DY.Spqr.spqrSend (localEncState stA₀ coins₁).spqr coins₂).2.2
      -- Unpack v1 and v2 splits for DrawsMatch and OutputsMatch
      dsimp only [stepView] at hv1_eq hv2_eq
      rw [ite_eq_left_iff.mpr (fun h => absurd hok1 h), hnext1,
        exposures_localEncTr, List.append_nil, newRandoms_localEncTr] at hv1_eq
      rw [ite_eq_left_iff.mpr (fun h => absurd hok2 h), hnext2,
        exposures_localEncTr, List.append_nil, newRandoms_localEncTr] at hv2_eq
      dsimp only [OutputsMatch] at houts1 houts2
      rw [ev1_exit_eq, hcmd1] at houts1
      rw [ev2_exit_eq, hcmd2] at houts2
      obtain ⟨vout1, houts1_eq, hbm_out1⟩ := houts1
      obtain ⟨vout2, houts2_eq, hbm_out2⟩ := houts2
      subst houts1_eq houts2_eq
      -- Extract pendingPreKey non-emptiness and exact drs1, vout1, drs2, vout2
      have hv1_tail := (List.cons.inj (hv1_split.symm.trans hv1_eq)).2
      unfold encDraws encSendEntry at hv1_tail
      rw [lastSent_localEncTr, runWrapped_ev1_fast] at hv1_tail
      rcases hpp1 : pendingPreKey tr₂ (tr₁.length + 8) with _ | ⟨ek1_p, ct1_p⟩
      · rw [hpp1] at hv1_tail
        change drs1 ++ [vout1] =
          ([(randTerm (tr₂.length + 1) cl1, cl1)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++ [] at hv1_tail
        rw [List.append_nil] at hv1_tail
        exfalso
        have hmem_v1 : vout1 ∈ ([(randTerm (tr₂.length + 1) cl1, cl1)].filter fun r => r.2 != 0).map fun r => rngEntry r.1 := by
          rw [← hv1_tail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmem_v1
        cases hbm_out1.1
      · rw [hpp1] at hv1_tail
        change drs1 ++ [vout1] =
          ([(randTerm (tr₂.length + 1) cl1, cl1)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++
          [⟨.send, [ek1_p, ct1_p, localEncMsg stA₀ coins₁ pqSalt₁ m₁], .preKeySend, none⟩] at hv1_tail
        have hlen1 : drs1.length = (([(randTerm (tr₂.length + 1) cl1, cl1)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1)).length := by
          have := congrArg List.length hv1_tail; simp only [List.length_append, List.length_singleton] at this; omega
        obtain ⟨hdrs1_eq, hvout1_cons⟩ := List.append_inj hv1_tail hlen1
        have hvout1_eq : vout1 = ⟨.send, [ek1_p, ct1_p, localEncMsg stA₀ coins₁ pqSalt₁ m₁], .preKeySend, none⟩ :=
          List.singleton_injective hvout1_cons
        have hv2_tail := (List.cons.inj (hv2_split.symm.trans hv2_eq)).2
        unfold encDraws encSendEntry at hv2_tail
        rw [lastSent_localEncTr, runWrapped_ev2_fast] at hv2_tail
        rcases hpp2 : pendingPreKey tr₃ (tr₂.length + 5) with _ | ⟨ek2_p, ct2_p⟩
        · rw [hpp2] at hv2_tail
          change drs2 ++ [vout2] =
            ([(randTerm (tr₃.length + 1) cl2, cl2)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++ [] at hv2_tail
          rw [List.append_nil] at hv2_tail
          exfalso
          have hmem_v2 : vout2 ∈ ([(randTerm (tr₃.length + 1) cl2, cl2)].filter fun r => r.2 != 0).map fun r => rngEntry r.1 := by
            rw [← hv2_tail]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
          obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmem_v2
          cases hbm_out2.1
        · rw [hpp2] at hv2_tail
          change drs2 ++ [vout2] =
            ([(randTerm (tr₃.length + 1) cl2, cl2)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++
            [⟨.send, [ek2_p, ct2_p, localEncMsg (localEncState stA₀ coins₁) coins₂ pqSalt₂ m₂], .preKeySend, none⟩] at hv2_tail
          have hlen2 : drs2.length = (([(randTerm (tr₃.length + 1) cl2, cl2)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1)).length := by
            have := congrArg List.length hv2_tail; simp only [List.length_append, List.length_singleton] at this; omega
          obtain ⟨hdrs2_eq, hvout2_cons⟩ := List.append_inj hv2_tail hlen2
          have hvout2_eq : vout2 = ⟨.send, [ek2_p, ct2_p, localEncMsg (localEncState stA₀ coins₁) coins₂ pqSalt₂ m₂], .preKeySend, none⟩ :=
            List.singleton_injective hvout2_cons
          -- Equate coins₁ and coins₂ under gamma
          rw [hdrs1_eq] at hdrs1
          rw [hdrs2_eq] at hdrs2
          have hg_c1 : cl1 ≠ 0 → (g.σ (tr₂.length + 1) cl1).length = cl1 := by
            intro hne
            refine hgwf.1 (rngEntry (randTerm (tr₂.length + 1) cl1)) ?_ rfl (tr₂.length + 1) cl1 hne (by simp [rngEntry])
            apply List.mem_append_right; apply List.mem_append_left
            rw [hv1_split, hdrs1_eq]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [bne_iff_ne.mpr hne]))
          have hg_c2 : cl2 ≠ 0 → (g.σ (tr₃.length + 1) cl2).length = cl2 := by
            intro hne
            refine hgwf.1 (rngEntry (randTerm (tr₃.length + 1) cl2)) ?_ rfl (tr₃.length + 1) cl2 hne (by simp [rngEntry])
            apply List.mem_append_right; apply List.mem_append_right
            rw [hv2_split, hdrs2_eq]
            exact List.mem_cons_of_mem _ (List.mem_append_left _ (by simp [bne_iff_ne.mpr hne]))
          have hcoins1_γ : gamma compI0 S g coins₁ = gamma compI0 S (gClean g) (coins1Clean cl1) :=
            extract_enc_coins hcl1 hg_c1 (fun _ => rfl) hdrs1
          have hcoins2_γ : gamma compI0 S g coins₂ = gamma compI0 S (gClean g) (coins2Clean cl2) :=
            extract_enc_coins hcl2 hg_c2 (fun _ => rfl) hdrs2
          -- Plaintext m₁ and m₂ under gamma
          have hm1_γ : gamma compI0 S g m₁ = ev1.input := by
            have hinp1_eq : inp1 = ⟨.pt, [m₁], .single, none⟩ :=
              (List.cons.inj (hv1_split.symm.trans hv1_eq)).1
            have hb := hinp1.2; rw [hinp1_eq] at hb; dsimp only [List.map_cons, List.map_nil] at hb
            injection hb with h
          have hm2_γ : gamma compI0 S g m₂ = ev2.input := by
            have hinp2_eq : inp2 = ⟨.pt, [m₂], .single, none⟩ :=
              (List.cons.inj (hv2_split.symm.trans hv2_eq)).1
            have hb := hinp2.2; rw [hinp2_eq] at hb; dsimp only [List.map_cons, List.map_nil] at hb
            injection hb with h
          -- Equate gamma compI0 S g on o.keys and SPQR outputs with gClean g on oClean
          have hr0_γ : gamma compI0 S g ikASkClean = gamma compI0 S (gClean g) ikASkClean :=
            congrArg ConcretizedTerm.bytes (gamma'_rand_lt22 S g (by decide)).symm
          have hr5_γ : gamma compI0 S g ikBSkClean = gamma compI0 S (gClean g) ikBSkClean :=
            congrArg ConcretizedTerm.bytes (gamma'_rand_lt22 S g (by decide)).symm
          have hr10_γ : gamma compI0 S g spkBSkClean = gamma compI0 S (gClean g) spkBSkClean :=
            congrArg ConcretizedTerm.bytes (gamma'_rand_lt22 S g (by decide)).symm
          have hpqpk_γ : gamma compI0 S g pqpkBClean = gamma compI0 S (gClean g) pqpkBClean :=
            congrArg ConcretizedTerm.bytes
              (gamma'_kemPk_eq_of_eq S (gClean g) g (gamma'_rand_lt22 S g (by decide))).symm
          have hek_sk_γ : gamma compI0 S g (randTerm tr₁.length 32) = gamma compI0 S (gClean g) (randTerm 22 32) := by
            unfold gamma
            rw [gamma'_randTerm compI0 S g tr₁.length 32 (by decide),
                gamma'_randTerm compI0 S (gClean g) 22 32 (by decide)]
            exact hσ_ek
          have hent_γ : gamma compI0 S g (randTerm (tr₁.length + 1) 32) = gamma compI0 S (gClean g) (randTerm 23 32) := by
            unfold gamma
            rw [gamma'_randTerm compI0 S g (tr₁.length + 1) 32 (by decide),
                gamma'_randTerm compI0 S (gClean g) 23 32 (by decide)]
            exact hσ_ent
          have hdhs_γ : gamma compI0 S g (randTerm (tr₁.length + 2) 32) = gamma compI0 S (gClean g) (randTerm 24 32) := by
            unfold gamma
            rw [gamma'_randTerm compI0 S g (tr₁.length + 2) 32 (by decide),
                gamma'_randTerm compI0 S (gClean g) 24 32 (by decide)]
            exact hσ_dhs
          have hlit_γ : ∀ ba : ByteArray,
              gamma compI0 S g (DY.Literal.literalToBytes ba) =
                gamma compI0 S (gClean g) (DY.Literal.literalToBytes ba) :=
            fun ba => congrArg ConcretizedTerm.bytes (gamma'_lit_eq_gClean S g ba).symm
          have hikm_γ :
              gamma compI0 S g (DY.Libsignal.PQXDH.pqxdhIkm
                (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean)
                (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm tr₁.length 32))
                (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm tr₁.length 32))
                none (DY.PQKem.kemEncap pqpkBClean (randTerm (tr₁.length + 1) 32)).2) =
              gamma compI0 S (gClean g) (DY.Libsignal.PQXDH.pqxdhIkm
                (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean)
                (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm 22 32))
                (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm 22 32))
                none (DY.PQKem.kemEncap pqpkBClean (randTerm 23 32)).2) := by
            unfold DY.Libsignal.PQXDH.pqxdhIkm DY.Libsignal.PQXDH.discontinuity
            simp only [agree_dhPk, gamma_concat_eq0, hlit_γ]
            rw [gamma_dh_dhPk_congr_loc hr10_γ hr0_γ,
                gamma_dh_dhPk_congr_loc hr5_γ hek_sk_γ,
                gamma_dh_dhPk_congr_loc hr10_γ hek_sk_γ,
                gamma_kemEncap_snd_congr_loc hpqpk_γ hent_γ]
          have hprk_pqxdh_γ :
              gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac
                (DY.Literal.literalToBytes ⟨Array.replicate 32 0⟩)
                (DY.Libsignal.PQXDH.pqxdhIkm
                  (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean)
                  (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm tr₁.length 32))
                  (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm tr₁.length 32))
                  none (DY.PQKem.kemEncap pqpkBClean (randTerm (tr₁.length + 1) 32)).2)) =
              gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.hmac
                (DY.Literal.literalToBytes ⟨Array.replicate 32 0⟩)
                (DY.Libsignal.PQXDH.pqxdhIkm
                  (DY.Libsignal.PQXDH.agree spkBPkClean ikASkClean)
                  (DY.Libsignal.PQXDH.agree ikBPkClean (randTerm 22 32))
                  (DY.Libsignal.PQXDH.agree spkBPkClean (randTerm 22 32))
                  none (DY.PQKem.kemEncap pqpkBClean (randTerm 23 32)).2)) :=
            gamma_hmac_congr_loc (hlit_γ _) hikm_γ
          have ho_rk_γ : gamma compI0 S g o.keys.rk = gamma compI0 S (gClean g) oClean.keys.rk := by
            unfold o oClean CompTrace.aliceOut DY.Libsignal.PQXDH.aliceAgreement DY.Libsignal.PQXDH.pqxdhKdf
              DY.Libsignal.TripleRatchet.hkdfBlock1 DY.Libsignal.PQXDH.pqxdhLabel
              DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
              DY.Libsignal.TripleRatchet.zeroSalt
            dsimp only; rw [setupTrace_r0_len]
            exact gamma_hmac_congr_loc hprk_pqxdh_γ (by simp only [gamma_concat_eq0, hlit_γ])
          have ho_ck_γ : gamma compI0 S g o.keys.ck = gamma compI0 S (gClean g) oClean.keys.ck := by
            have hrk := ho_rk_γ
            unfold o oClean CompTrace.aliceOut DY.Libsignal.PQXDH.aliceAgreement DY.Libsignal.PQXDH.pqxdhKdf
              DY.Libsignal.TripleRatchet.hkdfBlock2 DY.Libsignal.TripleRatchet.hkdfBlock1
              DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit
              DY.Libsignal.TripleRatchet.litByte DY.Libsignal.TripleRatchet.zeroSalt at hrk ⊢
            dsimp only at hrk ⊢; rw [setupTrace_r0_len] at hrk ⊢
            refine gamma_hmac_congr_loc hprk_pqxdh_γ ?_
            simp only [gamma_concat_eq0, hlit_γ]
            rw [hrk]
          have ho_pqr_γ : gamma compI0 S g o.keys.pqr = gamma compI0 S (gClean g) oClean.keys.pqr := by
            have hck := ho_ck_γ
            unfold o oClean CompTrace.aliceOut DY.Libsignal.PQXDH.aliceAgreement DY.Libsignal.PQXDH.pqxdhKdf
              DY.Libsignal.TripleRatchet.hkdfBlock3 DY.Libsignal.TripleRatchet.hkdfBlock2
              DY.Libsignal.TripleRatchet.hkdfBlock1 DY.Libsignal.PQXDH.pqxdhLabel
              DY.Libsignal.TripleRatchet.lit DY.Libsignal.TripleRatchet.litByte
              DY.Libsignal.TripleRatchet.zeroSalt at hck ⊢
            dsimp only at hck ⊢; rw [setupTrace_r0_len] at hck ⊢
            refine gamma_hmac_congr_loc hprk_pqxdh_γ ?_
            simp only [gamma_concat_eq0, hlit_γ]
            rw [hck]
          have hspqr0_γ : gamma compI0 S g stA₀.spqr = gamma compI0 S (gClean g) stA0Clean.spqr :=
            gamma_spqrInit_congr ho_pqr_γ (hlit_γ _)
          have hsalt1_γ : gamma compI0 S g pqSalt₁ = gamma compI0 S (gClean g) (salt1Clean cl1) :=
            gamma_spqrSend_key_init_congr ho_pqr_γ (hlit_γ _) (hlit_γ _)
          have hpqm1_γ : gamma compI0 S g pqm₁ = gamma compI0 S (gClean g) (pqm1Clean cl1) :=
            gamma_spqrSend_msg_congr hspqr0_γ hcoins1_γ
          have hspqr1_γ : gamma compI0 S g (DY.Spqr.spqrSend stA₀.spqr coins₁).1 =
              gamma compI0 S (gClean g) (spqrA1Clean cl1) :=
            gamma_spqrSend_fst_congr hspqr0_γ hcoins1_γ
          have hsalt2_γ : gamma compI0 S g pqSalt₂ = gamma compI0 S (gClean g) (salt2Clean cl1 cl2) :=
            gamma_spqrSend_key_step_congr hspqr1_γ hcoins2_γ
          have hpqm2_γ : gamma compI0 S g pqm₂ = gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) :=
            gamma_spqrSend_msg_congr hspqr1_γ hcoins2_γ
          -- Unpack SendMatches on vout1 (ev4.input) and vout2 (ev3.input)
          rw [hvout1_eq] at hbm_out1
          obtain ⟨_, _, _, _, hpw1⟩ := hbm_out1.2
          have hp_c1_inv := Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.parsePreKeyWire_preKeyWire_inv
            hpw1 ev4_input_len_lt parsePreKeyWire_ev4
          rw [hvout2_eq] at hbm_out2
          obtain ⟨_, _, _, _, hpw2⟩ := hbm_out2.2
          have hp_c2_inv := Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire.parsePreKeyWire_preKeyWire_inv
            hpw2 ev3_input_len_lt parsePreKeyWire_ev3
          -- Extract MACs and pin salt1 = dagBytes 21, salt2 = dagBytes 23
          clear hme hM1 hM2 hM3 hfaith
          let seed₁ := (DY.Libsignal.TripleRatchet.kdfCk stA₀.cks).2
          let keys₁ := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt₁ seed₁
          let wire₁ := DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk stA₀.dhs) stA₀.ns stA₀.pn
            (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁) pqm₁
          let mac₁ := DY.Libsignal.TripleRatchet.computeMac keys₁.macKey stA₀.myIk stA₀.peerIk wire₁
          have hmsg1_bytes : p_c1.message = gamma compI0 S g wire₁ ++ gamma compI0 S g mac₁ := by
            have h := hp_c1_inv.2.2.2
            unfold localEncMsg at h; dsimp only at h
            rwa [gamma_concat_eq0] at h
          have hmac1_len : (gamma compI0 S g mac₁).length = 8 :=
            gamma_computeMac_length _ _ _ _
          have hmac1_bytes : gamma compI0 S g mac₁ = msgMac8' p_c1 := by
            unfold msgMac8'
            rw [hmsg1_bytes, List.length_append, hmac1_len, Nat.add_sub_cancel, List.drop_left]
          have hwire1_bytes : gamma compI0 S g wire₁ = p_c1.message.take (p_c1.message.length - 8) := by
            rw [hmsg1_bytes, List.length_append, hmac1_len, Nat.add_sub_cancel,
              List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _)]
          have hsalt1_pin0 : gamma compI0 S g pqSalt₁ = dagBytes 21 :=
            c1_mac_forces_salt hmac1_bytes (gamma_spqrSend_key_length stA₀.spqr coins₁)
          have hsalt1_pin : gamma compI0 S (gClean g) (salt1Clean cl1) = dagBytes 21 :=
            hsalt1_γ.symm.trans hsalt1_pin0
          let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk (localEncState stA₀ coins₁).cks).2
          let keys₂ := DY.Libsignal.TripleRatchet.trMsgKeys pqSalt₂ seed₂
          let wire₂ := DY.Libsignal.TripleRatchet.trHonestWireMsg
            (DY.DiffieHellman.dhPk (localEncState stA₀ coins₁).dhs)
            (localEncState stA₀ coins₁).ns (localEncState stA₀ coins₁).pn
            (DY.SymEnc.symEnc keys₂.cipherKey keys₂.iv m₂) pqm₂
          let mac₂ := DY.Libsignal.TripleRatchet.computeMac keys₂.macKey
            (localEncState stA₀ coins₁).myIk (localEncState stA₀ coins₁).peerIk wire₂
          have hmsg2_bytes : p_c2.message = gamma compI0 S g wire₂ ++ gamma compI0 S g mac₂ := by
            have h := hp_c2_inv.2.2.2
            unfold localEncMsg at h; dsimp only at h
            rwa [gamma_concat_eq0] at h
          have hmac2_len : (gamma compI0 S g mac₂).length = 8 :=
            gamma_computeMac_length _ _ _ _
          have hmac2_bytes : gamma compI0 S g mac₂ = msgMac8' p_c2 := by
            unfold msgMac8'
            rw [hmsg2_bytes, List.length_append, hmac2_len, Nat.add_sub_cancel, List.drop_left]
          have hwire2_bytes : gamma compI0 S g wire₂ = p_c2.message.take (p_c2.message.length - 8) := by
            rw [hmsg2_bytes, List.length_append, hmac2_len, Nat.add_sub_cancel,
              List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _)]
          have hsalt2_pin0 : gamma compI0 S g pqSalt₂ = dagBytes 23 :=
            c2_mac_forces_salt hmac2_bytes (gamma_spqrSend_key_length (localEncState stA₀ coins₁).spqr coins₂)
          have hsalt2_pin : gamma compI0 S (gClean g) (salt2Clean cl1 cl2) = dagBytes 23 :=
            hsalt2_γ.symm.trans hsalt2_pin0
          -- Pin pqm1 = dagBytes 22 and pqm2 = dagBytes 24 via GhostWF + trWireBytes_pq_inj
          have hc' := ghostAndSemMatchSetup_gClean hp hcompat
          obtain ⟨hf0, hf5, hf10, hf11, hf16, hf17⟩ := secretBytes_at_of_fits hp
          have hmemR : ∀ p ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)],
              p ∈ setupRandomsAt r := by
            intro p hp0; rwa [setupRandomsAt_eq_of_fits hp, setupRandomsAt_r0_eq]
          have hpqpk_gamma : gamma compI0 S (gClean g) pqpkBClean = dagBytes 25 := by
            have hpub := hc'.2.1 r.pqpkPubTerm (by simp)
            unfold ProtocolSetup.pqpkPubTerm at hpub
            rw [hp.hpqpkPub, setupPublic_eq_of_fits hp 6, setupPublic_r0_6] at hpub
            exact hpub.trans kyberPk_eq_dag25
          have hσ_16 : (gClean g).σ 16 64 = dagBytes 35 := by
            rw [hc'.1 (16, 64) (hmemR _ (by simp)), hf16]; exact fillFresh_16_eq_dag35
          have hw_lit : CleanDagHyp S (gClean g) [randTerm 31 32, randTerm 38 32] pqpkBClean
              (litOf (dagBytes 21)) (litOf (dagBytes 22)) (litOf (dagBytes 23)) (litOf (dagBytes 24)) :=
            { hσ_0_32 := by rw [hc'.1 (0, 32) (hmemR _ (by simp)), hf0]; exact setup_aliceId_eq_dag26,
              hσ_5_32 := by rw [hc'.1 (5, 32) (hmemR _ (by simp)), hf5]; exact setup_bobId_eq_dag29,
              hσ_10_32 := by rw [hc'.1 (10, 32) (hmemR _ (by simp)), hf10]; exact setup_spk_eq_dag32,
              hσ_11_64 := by rw [hc'.1 (11, 64) (hmemR _ (by simp)), hf11]; exact fillFresh_11_eq_dag34,
              hσ_16_64 := hσ_16,
              hσ_17_64 := by rw [hc'.1 (17, 64) (hmemR _ (by simp)), hf17]; exact fillFresh_17_eq_dag36,
              hσ_22_32 := rfl, hσ_23_32 := rfl, hσ_24_32 := rfl,
              hσ_32_32 := by exact ev1_coins_take32,
              hσ_32_64 := by exact ev1_coins_take64,
              hσ_39_32 := by exact ev2_coins_take32,
              hσ_39_64 := by exact ev2_coins_take64,
              hσ_45_32 := rfl,
              hσ_pt1 := rfl, hpt1_mem := by simp,
              hσ_pt2 := rfl, hpt2_mem := by simp,
              haddr := fun _ => rfl,
              hzero := opaqueAt_zeroKey,
              hpqpk := opaqueAt_kemPk hpqpk_gamma (termAt_rand (id := 35) dag_nodes_ok (by decide) rfl hσ_16).safeMemo,
              hsalt1 := opaqueAt_litOf (by decide) dagOp_21_lit,
              hpqm1 := opaqueAt_litOf (by decide) dagOp_22_lit,
              hsalt2 := opaqueAt_litOf (by decide) dagOp_23_lit,
              hpqm2 := opaqueAt_litOf (by decide) dagOp_24_lit }
          obtain ⟨_, _, hrk0_d, _, _⟩ := dagTermAt_oClean hw_lit
          have hdhInit_d : DagTermAt S (gClean g) [randTerm 31 32, randTerm 38 32]
              (DY.Libsignal.PQXDH.agree oClean.spk stA0Clean.dhs) 87 := by
            unfold stA0Clean localAliceStartState oClean CompTrace.aliceOut
            dsimp only; rw [setupTrace_r0_len, agree_dhPk]
            exact dagN_87_symm hw_lit
          have hprk0_d := termAt_kdf (id := 88) dag_nodes_ok (by decide) rfl hrk0_d hdhInit_d
          have hrkA0_d := termAt_kdf (id := 89) dag_nodes_ok (by decide) rfl hprk0_d (dagN_13 hw_lit)
          have hc2_0_d := termAt_concat (id := 90) dag_nodes_ok (by decide) rfl hrkA0_d (dagN_14 hw_lit)
          have hcks0_d : DagTermAt S (gClean g) [randTerm 31 32, randTerm 38 32] stA0Clean.cks 91 :=
            termAt_kdf (id := 91) dag_nodes_ok (by decide) rfl hprk0_d hc2_0_d
          have hcks1_d : DagTermAt S (gClean g) [randTerm 31 32, randTerm 38 32] (stA1Clean cl1).cks 98 :=
            termAt_kdf (id := 98) dag_nodes_ok (by decide) rfl hcks0_d (dagN_3 hw_lit)
          have hdhsPk_clean : gamma compI0 S (gClean g) (DY.DiffieHellman.dhPk stA0Clean.dhs) = dagBytes 73 := by
            unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]
            exact (dagN_73 hw_lit).2.1
          have hdhsPk_g : gamma compI0 S g (DY.DiffieHellman.dhPk stA₀.dhs) = dagBytes 73 := by
            unfold stA₀ localAliceStartState; dsimp only
            exact (gamma_dhPk_congr_loc hdhs_γ).trans (by
              unfold stA0Clean localAliceStartState at hdhsPk_clean; dsimp only at hdhsPk_clean
              rwa [setupTrace_r0_len] at hdhsPk_clean)
          have hcks0_g : gamma compI0 S g stA₀.cks = gamma compI0 S (gClean g) stA0Clean.cks := by
            have hdh_init : gamma compI0 S g (DY.X25519.agree spkBPkClean (randTerm (tr₁.length + 2) 32)) =
                gamma compI0 S (gClean g) (DY.X25519.agree spkBPkClean (randTerm 24 32)) := by
              rw [agree_dhPk, agree_dhPk]
              exact gamma_dh_dhPk_congr_loc hr10_γ hdhs_γ
            change gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfRk o.keys.rk
                (DY.X25519.agree spkBPkClean (randTerm (tr₁.length + 2) 32))).2 =
              gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.kdfRk oClean.keys.rk
                (DY.X25519.agree spkBPkClean (randTerm ((setupTrace r0).length + 2) 32))).2
            rw [setupTrace_r0_len]
            exact gamma_kdfRk_snd_congr ho_rk_γ hdh_init
          have hseed1_g : gamma compI0 S g seed₁ = dagBytes 97 := by
            have hc : gamma compI0 S g seed₁ = gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.kdfCk stA0Clean.cks).2 :=
              gamma_hmac_congr_loc hcks0_g (hlit_γ ⟨#[1]⟩)
            exact hc.trans (termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0_d (dagN_2 hw_lit)).2.1
          have hcks1_g : gamma compI0 S g (localEncState stA₀ coins₁).cks =
              gamma compI0 S (gClean g) (stA1Clean cl1).cks :=
            gamma_hmac_congr_loc hcks0_g (hlit_γ ⟨#[2]⟩)
          have hseed2_g : gamma compI0 S g seed₂ = dagBytes 112 := by
            have hc : gamma compI0 S g seed₂ = gamma compI0 S (gClean g) (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 :=
              gamma_hmac_congr_loc hcks1_g (hlit_γ ⟨#[1]⟩)
            exact hc.trans (termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1_d (dagN_2 hw_lit)).2.1
          -- Evaluate ciphertexts for c1 (node 105) and c2 (node 120)
          have hseed1_d := termAt_kdf (id := 97) dag_nodes_ok (by decide) rfl hcks0_d (dagN_2 hw_lit)
          obtain ⟨tck1_d, _, tiv1_d⟩ := termAt_trMsgKeys
            (prk_id := 99) (ck_id := 100) (c2_id := 101) (mk_id := 102) (c3_id := 103) (iv_id := 104)
            dag_nodes_ok (dagN_15 hw_lit) (dagN_16 hw_lit) (dagN_17 hw_lit)
            ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
            ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
            (dagN_21 hw_lit) hseed1_d
          have hct1_d := termAt_symEncPt (id := 105) dag_nodes_ok (by decide)
            dagOp_105_eq_ev1 tck1_d tiv1_d (by simp) rfl ev1_input_len_lt8
          have hct1_g : gamma compI0 S g (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁) = dagBytes 105 := by
            obtain ⟨hck1, _, hiv1⟩ := gamma_trMsgKeys_congr
              (hsalt1_pin0.trans (dagN_21 hw_lit).2.1.symm)
              (hseed1_g.trans hseed1_d.2.1.symm)
            have hm1_clean : gamma compI0 S g m₁ = gamma compI0 S (gClean g) (randTerm 31 32) := by
              rw [hm1_γ]; unfold gamma; rw [gamma'_randTerm compI0 S (gClean g) 31 32 (by decide)]; rfl
            exact (gamma_symEnc_congr_loc hck1 hiv1 hm1_clean).trans hct1_d.2.1
          have hseed2_d := termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1_d (dagN_2 hw_lit)
          obtain ⟨tck2_d, _, tiv2_d⟩ := termAt_trMsgKeys
            (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
            dag_nodes_ok (dagN_15 hw_lit) (dagN_16 hw_lit) (dagN_17 hw_lit)
            ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
            ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
            (dagN_23 hw_lit) hseed2_d
          have hct2_d := termAt_symEncPt (id := 120) dag_nodes_ok (by decide)
            dagOp_120_eq_ev2 tck2_d tiv2_d (by simp) rfl ev2_input_len_lt8
          have hct2_g : gamma compI0 S g (DY.SymEnc.symEnc keys₂.cipherKey keys₂.iv m₂) = dagBytes 120 := by
            obtain ⟨hck2, _, hiv2⟩ := gamma_trMsgKeys_congr
              (hsalt2_pin0.trans (dagN_23 hw_lit).2.1.symm)
              (hseed2_g.trans hseed2_d.2.1.symm)
            have hm2_clean : gamma compI0 S g m₂ = gamma compI0 S (gClean g) (randTerm 38 32) := by
              rw [hm2_γ]; unfold gamma; rw [gamma'_randTerm compI0 S (gClean g) 38 32 (by decide)]; rfl
            exact (gamma_symEnc_congr_loc hck2 hiv2 hm2_clean).trans hct2_d.2.1
          -- GhostWF gives g.addr wire₁ = cleanAddrBs and g.addr wire₂ = cleanAddrBs
          have haddr_ser : Cli.serializeAddresses ⟨Cli.aliceUuid, 1⟩ ⟨Cli.bobUuid, 1⟩ = cleanAddrBs :=
            addr_ser_eq_cleanAddrBs
          have haddr1 : g.addr wire₁ = cleanAddrBs := by
            have hv_mem : vout1 ∈ v0 ++ (v1 ++ vs2) := by
              apply List.mem_append_right; apply List.mem_append_left
              rw [hv1_split]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
            have hparse1 := Runs.parse_honest (DY.DiffieHellman.dhPk stA₀.dhs)
              (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁) pqm₁ keys₁.macKey stA₀.myIk stA₀.peerIk
              stA₀.ns stA₀.pn
            have hg_a := (hgwf.2.2 vout1 hv_mem (by rw [hvout1_eq])).1 (by rw [hvout1_eq])
              ek1_p ct1_p (localEncMsg stA₀ coins₁ pqSalt₁ m₁) _ (by rw [hvout1_eq]) hparse1
            exact hg_a.trans haddr_ser
          have haddr2 : g.addr wire₂ = cleanAddrBs := by
            have hv_mem : vout2 ∈ v0 ++ (v1 ++ vs2) := by
              apply List.mem_append_right; apply List.mem_append_right
              rw [hv2_split]; exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
            have hparse2 := Runs.parse_honest (DY.DiffieHellman.dhPk (localEncState stA₀ coins₁).dhs)
              (DY.SymEnc.symEnc keys₂.cipherKey keys₂.iv m₂) pqm₂ keys₂.macKey
              (localEncState stA₀ coins₁).myIk (localEncState stA₀ coins₁).peerIk
              (localEncState stA₀ coins₁).ns (localEncState stA₀ coins₁).pn
            have hg_a := (hgwf.2.2 vout2 hv_mem (by rw [hvout2_eq])).1 (by rw [hvout2_eq])
              ek2_p ct2_p (localEncMsg (localEncState stA₀ coins₁) coins₂ pqSalt₂ m₂) _ (by rw [hvout2_eq]) hparse2
            exact hg_a.trans haddr_ser
          have hpqm1_pin : gamma compI0 S (gClean g) (pqm1Clean cl1) = dagBytes 22 := by
            have hw1 := gamma_trHonestWireMsg_eq (S := S) (g := g)
              (DY.DiffieHellman.dhPk stA₀.dhs) stA₀.ns stA₀.pn
              (DY.SymEnc.symEnc keys₁.cipherKey keys₁.iv m₁) pqm₁
            change gamma compI0 S g wire₁ = _ at hw1
            have hns0 : stA₀.ns.toNat = 0 := rfl
            have hpn0 : stA₀.pn.toNat = 0 := rfl
            rw [hwire1_bytes, haddr1, hdhsPk_g, hct1_g, hns0, hpn0] at hw1
            exact hpqm1_γ.symm.trans (trWireBytes_pq_inj dagBytes_22_ne_nil (hw1.symm.trans p_c1_wire_eq_dag22))
          have hpqm2_pin : gamma compI0 S (gClean g) (pqm2Clean cl1 cl2) = dagBytes 24 := by
            have hw2 := gamma_trHonestWireMsg_eq (S := S) (g := g)
              (DY.DiffieHellman.dhPk (localEncState stA₀ coins₁).dhs)
              (localEncState stA₀ coins₁).ns (localEncState stA₀ coins₁).pn
              (DY.SymEnc.symEnc keys₂.cipherKey keys₂.iv m₂) pqm₂
            change gamma compI0 S g wire₂ = _ at hw2
            have hdhs2 : (localEncState stA₀ coins₁).dhs = stA₀.dhs := rfl
            have hns1 : (localEncState stA₀ coins₁).ns.toNat = 1 := rfl
            have hpn1 : (localEncState stA₀ coins₁).pn.toNat = 0 := rfl
            rw [hwire2_bytes, haddr2, hdhs2, hdhsPk_g, hct2_g, hns1, hpn1] at hw2
            exact hpqm2_γ.symm.trans (trWireBytes_pq_inj dagBytes_24_ne_nil (hw2.symm.trans p_c2_wire_eq_dag24))
          exact ⟨cl1, cl2, hcl1, hcl2, hsalt1_pin, hpqm1_pin, hsalt2_pin, hpqm2_pin⟩
    · rw [hs2_eq] at hok2
      have hok_a : ((DY.Libsignal.TripleRatchet.messageEncryptAbort me2 stIdx2).run tr₃).1.isSome = true := by
        rwa [show (Step.messageEncryptAbort me2 stIdx2).ok tr₃ =
          ((DY.Libsignal.TripleRatchet.messageEncryptAbort me2 stIdx2).run tr₃).1.isSome from
          stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me2, stIdx2) tr₃] at hok2
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort at hok_a
      obtain ⟨_, _, h1, _⟩ := run_bind_isSome hok_a
      obtain ⟨_, _, h2, _⟩ := run_bind_isSome h1
      rw [DY.Traceful.run_failure] at h2; cases h2
  · rw [hs1_eq] at hok1
    have hok_a : ((DY.Libsignal.TripleRatchet.messageEncryptAbort me1 stIdx1).run tr₂).1.isSome = true := by
      rwa [show (Step.messageEncryptAbort me1 stIdx1).ok tr₂ =
        ((DY.Libsignal.TripleRatchet.messageEncryptAbort me1 stIdx1).run tr₂).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me1, stIdx1) tr₂] at hok1
    unfold DY.Libsignal.TripleRatchet.messageEncryptAbort at hok_a
    obtain ⟨_, _, h1, _⟩ := run_bind_isSome hok_a
    obtain ⟨_, _, h2, _⟩ := run_bind_isSome h1
    rw [DY.Traceful.run_failure] at h2; cases h2


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
