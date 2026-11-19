/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2SpqrPins

/-!
# Clean 3-Call Alice Prefix Explanation & `m2Clean` Representation Membership
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

theorem ev_parties_012 :
    ev0.party = "alice" ∧ ev1.party = "alice" ∧ ev2.party = "alice" :=
  ⟨rfl, rfl, rfl⟩

theorem stepsStateFaithful_ss3Clean (r : ProtocolSetup) (cl1 cl2 : Nat) :
    StepsStateFaithful r (ss3Clean cl1 cl2) := by
  intro i j si sj p k b hij hsi hsj hl1 _ hl2
  have hj_lt : j < 3 := by
    by_contra hge
    rw [List.getElem?_eq_none (by simp [ss3Clean]; omega)] at hsj
    cases hsj
  have hi_cases : i = 0 ∨ i = 1 := by omega
  rcases hi_cases with rfl | rfl
  · simp [ss3Clean, s0Clean, Step.stateLoad?] at hsi hl1; subst hsi; cases hl1
  · have hj2 : j = 2 := by omega
    subst hj2
    simp only [ss3Clean, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hsi hsj
    subst hsi hsj
    simp [s1Clean, s2Clean, Step.stateLoad?] at hl1 hl2
    omega

theorem cleanAddrBs_eq_serializeAddresses :
    cleanAddrBs = DY.Libsignal.Composed.Refinement.Cli.serializeAddresses
      ⟨DY.Libsignal.Composed.Refinement.Cli.aliceUuid, 1⟩
      ⟨DY.Libsignal.Composed.Refinement.Cli.bobUuid, 1⟩ := by
  decide +kernel

theorem stepView_s0Clean_eq :
    stepView s0Clean (setupTrace r0) (runWrapped ev0) =
      { kind := .recv,
        terms := [spkBPkClean, setupPublic r0 5, pqpkBClean, setupPublic r0 7],
        layout := .bundle, anchor := none } ::
      rngEntry (randTerm 22 32) ::
      (kyberCoinEntries (randTerm 23 32) ++
        [{ rngEntry (randTerm 24 32) with anchor := some 27 }]) := by
  unfold stepView
  simp only [s0Clean_runs.1, ↓reduceIte, s0Clean_runs.2]
  dsimp only [s0Clean]
  unfold tr1Clean
  rw [exposures_localAliceStartTr, List.append_nil, aliceVis_localAliceStartTr, setupTrace_r0_len]
  have hrec : received (setupTrace r0) [14, 15, 20, 21] =
      [spkBPkClean, setupPublic r0 5, pqpkBClean, setupPublic r0 7] := by
    have hl1 : setupTr1.length = 5 := by
      simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.length_eq_1]
    have hl2 : setupTr2.length = 10 := by
      unfold setupTr2 registerIdentityTr; simp [hl1]
    have hl3 : setupTr3.length = 16 := by
      unfold setupTr3 genSignedPrekeyTr; simp [hl2]
    have h14 : (setupTrace r0).getMessageSentAt 14 = some spkBPkClean := by
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr; dsimp only
      repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)])
      unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl2, length_append_entry]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [hl2, length_append_entry])]; rfl
    have h15 : (setupTrace r0).getMessageSentAt 15 = some (setupPublic r0 5) := by
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      rw [setupPublic_r0_5, setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr; dsimp only
      repeat (rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)])
      unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
      rw [at?_append_eq_of_eq _ _ (by simp only [hl2, length_append_entry])]; rfl
    have h20 : (setupTrace r0).getMessageSentAt 20 = some pqpkBClean := by
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      rw [setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_append_of_lt _ _ (by simp only [hl3, length_append_entry]; omega)]
      rw [at?_append_eq_of_eq _ _ (by simp only [hl3, length_append_entry])]; rfl
    have h21 : (setupTrace r0).getMessageSentAt 21 = some (setupPublic r0 7) := by
      simp only [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1]
      rw [setupPublic_r0_7, setupTrace_r0_eq]; unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
      rw [at?_append_eq_of_eq _ _ (by simp only [hl3, length_append_entry])]; rfl
    simp [received, h14, h15, h20, h21]
  change ({ kind := .recv, terms := received (setupTrace r0) [14, 15, 20, 21], layout := .bundle, anchor := none } : VisEntry) :: _ = _
  rw [hrec]

theorem stepView_s1Clean_eq (cl1 : Nat) :
    stepView (s1Clean cl1) tr1Clean (runWrapped ev1) =
      (⟨.pt, [randTerm 31 32], .single, none⟩ : VisEntry) ::
      (([(randTerm 32 cl1, cl1)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++
        [⟨.send, [oClean.ek, oClean.ct, m1Clean cl1], .preKeySend, none⟩]) := by
  unfold stepView
  simp only [(s1Clean_runs cl1).1, ↓reduceIte, (s1Clean_runs cl1).2]
  dsimp only [s1Clean]
  unfold tr2Clean
  rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr1Clean_len, runWrapped_ev1_fast]
  unfold encDraws encSendEntry
  rw [lastSent_localEncTr, tr1Clean_len, pendingPreKey_tr1Clean]
  rfl

theorem stepView_s2Clean_eq (cl1 cl2 : Nat) :
    stepView (s2Clean cl2) (tr2Clean cl1) (runWrapped ev2) =
      (⟨.pt, [randTerm 38 32], .single, none⟩ : VisEntry) ::
      (([(randTerm 39 cl2, cl2)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1) ++
        [⟨.send, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeySend, none⟩]) := by
  unfold stepView
  simp only [(s2Clean_runs cl1 cl2).1, ↓reduceIte, (s2Clean_runs cl1 cl2).2]
  dsimp only [s2Clean]
  unfold tr3Clean
  rw [exposures_localEncTr, List.append_nil, newRandoms_localEncTr, tr2Clean_len, runWrapped_ev2_fast]
  unfold encDraws encSendEntry
  rw [lastSent_localEncTr, tr2Clean_len, pendingPreKey_tr2Clean]
  rfl

theorem ghostWF_gClean_vis3Clean (g : Ghost) {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    GhostWF (gClean g) (vis3Clean cl1 cl2) := by
  refine ⟨?_, fun _ => Or.inr cleanAddrBs_eq_serializeAddresses, ?_⟩
  · intro v hv hkind ts n hne hmem
    unfold vis3Clean at hv
    rw [stepView_s0Clean_eq, stepView_s1Clean_eq, stepView_s2Clean_eq] at hv
    rcases List.mem_append.mp hv with hv01 | hv2
    · rcases List.mem_append.mp hv01 with hv0 | hv1
      · rcases List.mem_cons.mp hv0 with rfl | hv0'
        · cases hkind
        · rcases List.mem_cons.mp hv0' with rfl | hv0''
          · simp only [rngEntry, List.mem_singleton] at hmem
            obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
            change (dagBytes 67).length = 32; decide +kernel
          · rcases List.mem_append.mp hv0'' with hkc | hdhs
            · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hkc
              simp only [List.mem_singleton] at hmem
              obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
              change (dagBytes 69).length = 32; decide +kernel
            · rcases List.mem_singleton.mp hdhs with rfl
              simp only [rngEntry, List.mem_singleton] at hmem
              obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
              change (dagBytes 72).length = 32; decide +kernel
      · rcases List.mem_cons.mp hv1 with rfl | hv1'
        · cases hkind
        · rcases List.mem_append.mp hv1' with hrng1 | hsend1
          · obtain ⟨p, hp_mem, rfl⟩ := List.mem_map.mp hrng1
            have hp_eq : p = (randTerm 32 cl1, cl1) := by
              have := (List.mem_filter.mp hp_mem).1
              exact List.mem_singleton.mp this
            subst hp_eq
            simp only [rngEntry, List.mem_singleton] at hmem
            obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
            rcases hcl1 with rfl | rfl | rfl
            · exact absurd rfl hne
            · change (ev1.coins.take 32).length = 32; decide +kernel
            · change (ev1.coins.take 64).length = 64; decide +kernel
          · rcases List.mem_singleton.mp hsend1 with rfl; cases hkind
    · rcases List.mem_cons.mp hv2 with rfl | hv2'
      · cases hkind
      · rcases List.mem_append.mp hv2' with hrng2 | hsend2
        · obtain ⟨p, hp_mem, rfl⟩ := List.mem_map.mp hrng2
          have hp_eq : p = (randTerm 39 cl2, cl2) := by
            have := (List.mem_filter.mp hp_mem).1
            exact List.mem_singleton.mp this
          subst hp_eq
          simp only [rngEntry, List.mem_singleton] at hmem
          obtain ⟨rfl, rfl⟩ := randTerm_inj_loc hmem
          rcases hcl2 with rfl | rfl | rfl
          · exact absurd rfl hne
          · change (ev2.coins.take 32).length = 32; decide +kernel
          · change (ev2.coins.take 64).length = 64; decide +kernel
        · rcases List.mem_singleton.mp hsend2 with rfl; cases hkind
  · intro v hv hkind
    refine ⟨fun _ _ _ _ _ _ _ => cleanAddrBs_eq_serializeAddresses, fun hwh => ?_⟩
    exfalso
    unfold vis3Clean at hv
    rw [stepView_s0Clean_eq, stepView_s1Clean_eq, stepView_s2Clean_eq] at hv
    rcases List.mem_append.mp hv with hv01 | hv2
    · rcases List.mem_append.mp hv01 with hv0 | hv1
      · rcases List.mem_cons.mp hv0 with rfl | hv0'
        · cases hkind
        · rcases List.mem_cons.mp hv0' with rfl | hv0''
          · cases hkind
          · rcases List.mem_append.mp hv0'' with hkc | hdhs
            · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hkc; cases hkind
            · rcases List.mem_singleton.mp hdhs with rfl; cases hkind
      · rcases List.mem_cons.mp hv1 with rfl | hv1'
        · cases hkind
        · rcases List.mem_append.mp hv1' with hrng1 | hsend1
          · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng1; cases hkind
          · rcases List.mem_singleton.mp hsend1 with rfl; cases hwh
    · rcases List.mem_cons.mp hv2 with rfl | hv2'
      · cases hkind
      · rcases List.mem_append.mp hv2' with hrng2 | hsend2
        · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrng2; cases hkind
        · rcases List.mem_singleton.mp hsend2 with rfl; cases hwh

theorem forall2_append_loc {α β : Type _} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h1 : List.Forall₂ R xs₁ ys₁) (h2 : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h1 with
  | nil => exact h2
  | cons ha _ ih => exact .cons ha ih

theorem drawsMatch_s0Clean (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DrawsMatch compI0 r S (gClean g)
      (rngEntry (randTerm 22 32) ::
        (kyberCoinEntries (randTerm 23 32) ++
          [{ rngEntry (randTerm 24 32) with anchor := some 27 }]))
      ev0.coins := by
  let kcPieces : List HwBytes := (List.range 32).map fun j => (ev0CoinsLit.drop (32 + 4 * j)).take 4
  refine ⟨[dagBytes 67] ++ kcPieces ++ [dagBytes 72], ?_, ?_, ?_⟩
  · intro p hp
    have hne_all : ∀ q ∈ ([dagBytes 67] ++ kcPieces ++ [dagBytes 72] : List HwBytes), q ≠ [] := by
      decide +kernel
    exact hne_all p hp
  · rw [ev0_coins_eq_lit]
    refine ⟨[], ?_⟩
    rw [List.append_nil]
    decide +kernel
  · simp only [List.singleton_append]
    refine List.Forall₂.cons ?_ ?_
    · refine ⟨rfl, ?_⟩
      simp only [rngEntry, List.map_cons, List.map_nil]
      unfold gamma
      rw [gamma'_randTerm compI0 S (gClean g) 22 32 (by decide)]
      rfl
    · have hkc : List.Forall₂ (fun p v => BytesMatchEntry compI0 r S (gClean g) .rng p v)
          kcPieces (kyberCoinEntries (randTerm 23 32)) := by
        unfold kcPieces kyberCoinEntries
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.forall₂_same.mpr fun j hj => ?_
        have hj32 : j < 32 := List.mem_range.mp hj
        refine ⟨rfl, ?_, randTerm 23 32, rfl, ?_, ?_⟩
        · have hlen_all : ∀ k ∈ List.range 32, ((ev0CoinsLit.drop (32 + 4 * k)).take 4).length = 4 := by
            decide +kernel
          exact hlen_all j hj
        · unfold gamma; rw [gamma'_randTerm compI0 S (gClean g) 23 32 (by decide)]
          change (dagBytes 69).length = 32; decide +kernel
        · unfold gamma; rw [gamma'_randTerm compI0 S (gClean g) 23 32 (by decide)]
          change ((ev0CoinsLit.drop (32 + 4 * j)).take 4).head? = (dagBytes 69)[j]?
          have hhd_all : ∀ k ∈ List.range 32,
              ((ev0CoinsLit.drop (32 + 4 * k)).take 4).head? = (dagBytes 69)[k]? := by
            decide +kernel
          exact hhd_all j hj
      have hdhs : List.Forall₂ (fun p v => BytesMatchEntry compI0 r S (gClean g) .rng p v)
          [dagBytes 72] [{ rngEntry (randTerm 24 32) with anchor := some 27 }] := by
        refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
        simp only [rngEntry, List.map_cons, List.map_nil]
        unfold gamma
        rw [gamma'_randTerm compI0 S (gClean g) 24 32 (by decide)]
        rfl
      exact forall2_append_loc hkc hdhs

theorem drawsMatch_s1Clean (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    {cl1 : Nat} (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64) :
    DrawsMatch compI0 r S (gClean g)
      (([(randTerm 32 cl1, cl1)].filter fun r => r.2 != 0).map fun r => rngEntry r.1)
      ev1.coins := by
  rcases hcl1 with rfl | hcl_pos
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), ⟨ev1.coins, rfl⟩, .nil⟩
  · have hne0 : cl1 ≠ 0 := by rcases hcl_pos with rfl | rfl <;> decide
    have hbne : (cl1 != 0) = true := bne_iff_ne.mpr hne0
    simp only [List.filter_cons, List.filter_nil, hbne, ↓reduceIte, List.map_cons, List.map_nil]
    refine ⟨[ev1.coins.take cl1], ?_, ⟨ev1.coins.drop cl1, by simp [List.take_append_drop]⟩,
      List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp
      rcases List.mem_singleton.mp hp with rfl
      rcases hcl_pos with rfl | rfl <;> decide +kernel
    · simp only [rngEntry, List.map_cons, List.map_nil]
      unfold gamma
      rw [gamma'_randTerm compI0 S (gClean g) 32 cl1 hne0]
      rfl

theorem drawsMatch_s2Clean (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    {cl2 : Nat} (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    DrawsMatch compI0 r S (gClean g)
      (([(randTerm 39 cl2, cl2)].filter fun r => r.2 != 0).map fun r => rngEntry r.1)
      ev2.coins := by
  rcases hcl2 with rfl | hcl_pos
  · exact ⟨[], fun _ h => False.elim (List.not_mem_nil h), ⟨ev2.coins, rfl⟩, .nil⟩
  · have hne0 : cl2 ≠ 0 := by rcases hcl_pos with rfl | rfl <;> decide
    have hbne : (cl2 != 0) = true := bne_iff_ne.mpr hne0
    simp only [List.filter_cons, List.filter_nil, hbne, ↓reduceIte, List.map_cons, List.map_nil]
    refine ⟨[ev2.coins.take cl2], ?_, ⟨ev2.coins.drop cl2, by simp [List.take_append_drop]⟩,
      List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp
      rcases List.mem_singleton.mp hp with rfl
      rcases hcl_pos with rfl | rfl <;> decide +kernel
    · simp only [rngEntry, List.map_cons, List.map_nil]
      unfold gamma
      rw [gamma'_randTerm compI0 S (gClean g) 39 cl2 hne0]
      rfl

theorem spqrHeaded_computeMac_false (mk a b w : DY.Bytes) :
    spqrHeaded (DY.Libsignal.TripleRatchet.computeMac mk a b w) = false := by
  let sub : DY.Trunc.Trunc8.SubF DY.Bytes :=
    { input := DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat a (DY.Concat.concat b w)) }
  change spqrHeaded sub.pack = false
  unfold spqrHeaded
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.InitState.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendState.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendKey.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.SendMsg.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvState.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.RecvKey.SubF sub,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Spqr.ChainKey.SubF sub]
  rfl

theorem isCurrentSnapshot_tr1Clean :
    DY.Libsignal.TripleRatchet.isCurrentSnapshot tr1Clean 30 = true := by
  rw [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  have hst : (tr1Clean.at? 30 : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE "alice" stA0Clean) := by
    unfold tr1Clean localAliceStartTr stA0Clean
    exact at?_append_eq_of_eq _ _ (by simp [setupTrace_r0_len])
  rw [hst, tr1Clean_len]
  rfl

theorem isCurrentSnapshot_tr2Clean (cl1 : Nat) :
    DY.Libsignal.TripleRatchet.isCurrentSnapshot (tr2Clean cl1) 36 = true := by
  rw [DY.Libsignal.TripleRatchet.isCurrentSnapshot_eq_at?]
  have hst : ((tr2Clean cl1).at? 36 : Option CompTrace.TRStEntry) =
      some (CompTrace.TRStE "alice" (stA1Clean cl1)) := by
    have h36 : 36 = tr1Clean.length + 5 := by rw [tr1Clean_len]
    rw [h36]; unfold tr2Clean stA1Clean coins1Clean
    have h32 : 32 = tr1Clean.length + 1 := by rw [tr1Clean_len]
    rw [h32]; at?_localEncTr_tac
  have hat37 : ((tr2Clean cl1).at? 37 : Option CompTrace.TRStEntry) = none := by
    unfold tr2Clean localEncTr
    rw [at?_append_other_eq _ _ rfl]
    exact Symbolic.Swarm.CREF.at?_ge_length _
      (by have hlen1 := tr1Clean_len; simp only [length_append_entry]; omega)
  rw [hst, tr2Clean_len]
  have hrange : List.range' (36 + 1) (38 - (36 + 1)) = [37] := rfl
  rw [hrange]
  dsimp only [List.all_cons, List.all_nil]
  rw [hat37]
  rfl

theorem bobDoneBaseKeys_setupTrace (r : ProtocolSetup) :
    bobDoneBaseKeys (setupTrace r) = [] :=
  bobDoneBaseKeys_nil_of_noBobBefore3 (noBobBefore3_setupTrace r)

theorem fitsCmd_s012Clean (cl1 cl2 : Nat) :
    s0Clean.FitsCmd ev0.cmd ∧ (s1Clean cl1).FitsCmd ev1.cmd ∧ (s2Clean cl2).FitsCmd ev2.cmd :=
  ⟨trivial, trivial, trivial⟩

theorem matchesSetupPeer_s012Clean {r : ProtocolSetup} (hp : FitsPins r) (cl1 cl2 : Nat) :
    s0Clean.MatchesSetupPeer r ∧ (s1Clean cl1).MatchesSetupPeer r ∧ (s2Clean cl2).MatchesSetupPeer r :=
  ⟨hp.hb.symm, trivial, trivial⟩

theorem stepCls_s012Clean (cl1 cl2 : Nat) :
    s0Clean.cls = .party ∧ (s1Clean cl1).cls = .party ∧ (s2Clean cl2).cls = .party :=
  ⟨rfl, rfl, rfl⟩

theorem outputsMatch_s0Clean (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    OutputsMatch compI0 r S (gClean g) ev0 [] none := rfl

theorem spkSig_pqpk_gamma_of_fits {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (hp : FitsPins r) (hc : GhostAndSemMatchSetup compI0 r S g) :
    gamma compI0 S (gClean g) (setupPublic r0 5) = setup.spkSig ∧
    gamma compI0 S (gClean g) pqpkBClean = setup.kyberPk ∧
    gamma compI0 S (gClean g) (setupPublic r0 7) = setup.kyberPkSig := by
  have hc' := ghostAndSemMatchSetup_gClean hp hc
  have h5 := hc'.2.1 r.spkSigTerm (by simp)
  unfold ProtocolSetup.spkSigTerm at h5
  rw [hp.hspkSig, setupPublic_eq_of_fits hp 5] at h5
  have h6 := hc'.2.1 r.pqpkPubTerm (by simp)
  unfold ProtocolSetup.pqpkPubTerm at h6
  rw [hp.hpqpkPub, setupPublic_eq_of_fits hp 6, setupPublic_r0_6] at h6
  have h7 := hc'.2.1 r.pqpkSigTerm (by simp)
  unfold ProtocolSetup.pqpkSigTerm at h7
  rw [hp.hpqpkSig, setupPublic_eq_of_fits hp 7] at h7
  exact ⟨h5, h6, h7⟩

theorem ikASecBytes_eq_of_fits {r : ProtocolSetup} (hp : FitsPins r) :
    r.ikASecBytes = setup.aliceId :=
  hp.hsec0

theorem readsFaithfully_s012Clean (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    ReadsFaithfully compI0 r S (gClean g) (setupTrace r0)
      { kind := .recv, terms := [spkBPkClean, setupPublic r0 5, pqpkBClean, setupPublic r0 7],
        layout := .bundle, anchor := none } ev0.input ∧
    ReadsFaithfully compI0 r S (gClean g) tr1Clean
      { kind := .pt, terms := [randTerm 31 32], layout := .single, anchor := none } ev1.input ∧
    ∀ cl1, ReadsFaithfully compI0 r S (gClean g) (tr2Clean cl1)
      { kind := .pt, terms := [randTerm 38 32], layout := .single, anchor := none } ev2.input :=
  ⟨trivial, trivial, fun _ => trivial⟩

theorem pathFaithful_s012Clean (S : OpaqueSymbolSemantics) (g : Ghost) (cl1 cl2 : Nat) :
    PathFaithfulAt compI0 S (gClean g) (setupTrace r0) s0Clean ev0.input ∧
    PathFaithfulAt compI0 S (gClean g) tr1Clean (s1Clean cl1) ev1.input ∧
    PathFaithfulAt compI0 S (gClean g) (tr2Clean cl1) (s2Clean cl2) ev2.input :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem localOk_s1Clean {cl1 : Nat} (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64) :
    (s1Clean cl1).LocalOk tr1Clean := by
  refine ⟨hcl1, Or.inl ?_⟩
  unfold encryptOwnSpqrKeyIdx
  rw [tr1Clean_len]

theorem localOk_s2Clean (cl1 : Nat) {cl2 : Nat} (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    (s2Clean cl2).LocalOk (tr2Clean cl1) := by
  refine ⟨hcl2, Or.inl ?_⟩
  unfold encryptOwnSpqrKeyIdx
  rw [tr2Clean_len]

theorem opkNamed_ev3_false {r : ProtocolSetup} :
    OpkNamed r ev3.input false :=
  ⟨p_c2, parsePreKeyWire_ev3, by simp only [Bool.false_eq_true, ↓reduceIte]; decide +kernel⟩

theorem stepsWF_ss3Clean {r : ProtocolSetup} (hp : FitsPins r)
    {cl1 cl2 : Nat}
    (hcl1 : cl1 = 0 ∨ cl1 = 32 ∨ cl1 = 64)
    (hcl2 : cl2 = 0 ∨ cl2 = 32 ∨ cl2 = 64) :
    StepsWF (ss3Clean cl1 cl2) (setupTrace r) := by
  rw [setupTrace_eq_of_fits hp]
  unfold ss3Clean
  refine ⟨?_, trivial, ?_⟩
  · exact Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
      DY.Libsignal.Composed.aliceStart.reachability
      ("alice", "bob", 4, 6, (⟨14, 15, 20, 21, none⟩ : DY.Libsignal.PQXDH.BundleHandles))
      (setupTrace r0) trivial
  · rw [s0Clean_runs.2]
    refine ⟨?_, localOk_s1Clean hcl1, ?_⟩
    · exact Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
        DY.Libsignal.TripleRatchet.messageEncrypt.reachability
        ("alice", 30, cl1, 33) tr1Clean isCurrentSnapshot_tr1Clean
    · rw [(s1Clean_runs cl1).2]
      refine ⟨?_, localOk_s2Clean cl1 hcl2, trivial⟩
      exact Symbolic.Proofs.Swarm.UA.BI.Step.stepIn_preCond_of
        DY.Libsignal.TripleRatchet.messageEncrypt.reachability
        ("alice", 36, cl2, 40) (tr2Clean cl1) (isCurrentSnapshot_tr2Clean cl1)

theorem attackerKnows_c2_tr3Clean (cl1 cl2 : Nat) :
    oClean.ek.AttackerKnows (tr3Clean cl1 cl2) ∧
    oClean.ct.AttackerKnows (tr3Clean cl1 cl2) ∧
    (m2Clean cl1 cl2).AttackerKnows (tr3Clean cl1 cl2) := by
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
  have hat25_3 : ((tr3Clean cl1 cl2).at? 25 : Option DY.Network.ExecEntryT) =
      some (CompTrace.NetE oClean.ek) := liftEnc (liftEnc hat25_1)
  have hat26_3 : ((tr3Clean cl1 cl2).at? 26 : Option DY.Network.ExecEntryT) =
      some (CompTrace.NetE oClean.ct) := liftEnc (liftEnc hat26_1)
  have hat44_3 : ((tr3Clean cl1 cl2).at? 44 : Option DY.Network.ExecEntryT) =
      some (CompTrace.NetE (m2Clean cl1 cl2)) := by
    have h44 : 44 = (tr2Clean cl1).length + 6 := by rw [tr2Clean_len]
    rw [h44]
    unfold tr3Clean m2Clean coins2Clean
    have h39 : 39 = (tr2Clean cl1).length + 1 := by rw [tr2Clean_len]
    have h38 : 38 = (tr2Clean cl1).length := (tr2Clean_len cl1).symm
    rw [h39, h38]
    unfold localEncTr
    exact at?_append_eq_of_eq _ _ (by simp only [length_append_entry])
  refine ⟨DY.Trace.MessageSentAt_implies_AttackerKnows _ _ 25
            (by rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact hat25_3),
          DY.Trace.MessageSentAt_implies_AttackerKnows _ _ 26
            (by rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact hat26_3),
          DY.Trace.MessageSentAt_implies_AttackerKnows _ _ 44
            (by rw [Symbolic.DYBridge.DY.Trace.MessageSentAt_eq_1]; exact hat44_3)⟩

theorem explains_clean_ev012 {r : ProtocolSetup}
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
    Explains compI0 r S (gClean g) (ss3Clean cl1 cl2) (vis3Clean cl1 cl2)
      [.run ev0, .run ev1, .run ev2] ∧
    (⟨oClean.ek, oClean.ct, m2Clean cl1 cl2⟩ : PreKeyRep) ∈
      preKeyRepresentationsOn compI0 r S (gClean g) (runTrace r (ss3Clean cl1 cl2)) ev3.input := by
  let pts : List DY.Bytes := [randTerm 31 32, randTerm 38 32]
  have hw := cleanDagHyp_of_spqrPins (pts := pts) hp hex.1 hcl1 hcl2
    (by simp [pts]) (by simp [pts]) hsalt1 hpqm1 hsalt2 hpqm2
  obtain ⟨hek0, hct0, _, _, _⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, _, _, hcks1, hm1, _, hm2⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hek_g : gamma compI0 S (gClean g) oClean.ek = dagBytes 68 := hek0.2.1
  have hct_g : gamma compI0 S (gClean g) oClean.ct = dagBytes 70 := hct0.2.1
  have hm1_g : gamma compI0 S (gClean g) (m1Clean cl1) = dagBytes 111 := hm1.2.1
  have hm2_g : gamma compI0 S (gClean g) (m2Clean cl1 cl2) = dagBytes 126 := hm2.2.1
  obtain ⟨hspkSig_g, hpqpk_g, hpqpkSig_g⟩ := spkSig_pqpk_gamma_of_fits hp hex.1
  have hspk_g : gamma compI0 S (gClean g) spkBPkClean = dagBytes 33 := (dagN_33 hw).2.1
  have hikA_sec : r.ikASecBytes = setup.aliceId := ikASecBytes_eq_of_fits hp
  refine ⟨?_, ?_⟩
  · refine ⟨ghostAndSemMatchSetup_gClean hp hex.1,
            ghostWF_gClean_vis3Clean g hcl1 hcl2,
            ⟨hex.2.2.1.1, hex.2.2.1.2.1, stepsWF_ss3Clean hp hcl1 hcl2,
              stepsStateFaithful_ss3Clean r cl1 cl2⟩,
            ?_⟩
    unfold MatchesEvents
    rw [setupTrace_eq_of_fits hp]
    set v0 := stepView s0Clean (setupTrace r0) (runWrapped ev0)
    set v1 := stepView (s1Clean cl1) tr1Clean (runWrapped ev1)
    set v2 := stepView (s2Clean cl2) (tr2Clean cl1) (runWrapped ev2)
    have hvis_eq : vis3Clean cl1 cl2 = v0 ++ (v1 ++ (v2 ++ [])) := by
      simp [vis3Clean, v0, v1, v2, List.append_assoc]
    have hss_eq : ss3Clean cl1 cl2 =
        ([] : List Step) ++ s0Clean :: (([] : List Step) ++ s1Clean cl1 :: (([] : List Step) ++ s2Clean cl2 :: [])) := rfl
    rw [hvis_eq, hss_eq]
    have hRun0 : RunMatches compI0 r S (gClean g) (setupTrace r0) s0Clean ev0 v0 none := by
      refine ⟨rfl, rfl, (fitsCmd_s012Clean cl1 cl2).1, (matchesSetupPeer_s012Clean hp cl1 cl2).1,
              s0Clean_runs.1, ⟨Symbolic.BugInjection.hexBytes "", rfl⟩, rfl, ?_⟩
      refine ⟨{ kind := .recv, terms := [spkBPkClean, setupPublic r0 5, pqpkBClean, setupPublic r0 7],
                layout := .bundle, anchor := none },
              rngEntry (randTerm 22 32) :: (kyberCoinEntries (randTerm 23 32) ++
                [{ rngEntry (randTerm 24 32) with anchor := some 27 }]),
              [], ?_, ?_, drawsMatch_s0Clean r S g, outputsMatch_s0Clean r S g,
              (readsFaithfully_s012Clean r S g).1, (pathFaithful_s012Clean S g cl1 cl2).1⟩
      · rw [List.append_nil]; exact stepView_s0Clean_eq
      · refine ⟨rfl, ?_⟩
        dsimp only [PreKeyBundleLayoutMatches, BundleSignedKeysMatch]
        rw [ev0_input_eq_fast, hspk_g, hspkSig_g, hpqpk_g, hpqpkSig_g]
        decide +kernel
    refine MatchesEventsAt.run1 (fun _ h => nomatch h) hRun0 ?_
    dsimp only [runSteps, nextBundleIds]
    rw [s0Clean_runs.2]
    have hRun1 : RunMatches compI0 r S (gClean g) tr1Clean (s1Clean cl1) ev1 v1
        (some (bundlePreKeyIds ev0.input)) := by
      refine ⟨rfl, rfl, (fitsCmd_s012Clean cl1 cl2).2.1, (matchesSetupPeer_s012Clean hp cl1 cl2).2.1,
              (s1Clean_runs cl1).1, ⟨c1Fast, ev1_exit_eq_fast⟩, rfl, ?_⟩
      refine ⟨⟨.pt, [randTerm 31 32], .single, none⟩,
              ([(randTerm 32 cl1, cl1)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1),
              [⟨.send, [oClean.ek, oClean.ct, m1Clean cl1], .preKeySend, none⟩],
              stepView_s1Clean_eq cl1, ?_, drawsMatch_s1Clean r S g hcl1, ?_,
              (readsFaithfully_s012Clean r S g).2.1, (pathFaithful_s012Clean S g cl1 cl2).2.1⟩
      · refine ⟨rfl, ?_⟩
        dsimp only [List.map]
        unfold gamma
        rw [gamma'_randTerm compI0 S (gClean g) 31 32 (by decide)]
        rfl
      · unfold OutputsMatch
        have hcmd1 : ev1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
        rw [ev1_exit_eq_fast, hcmd1]
        refine ⟨⟨.send, [oClean.ek, oClean.ct, m1Clean cl1], .preKeySend, none⟩, rfl, rfl, ?_⟩
        dsimp only [SendMatches]
        refine ⟨(bundlePreKeyIds ev0InFast).1, (bundlePreKeyIds ev0InFast).2.1, (bundlePreKeyIds ev0InFast).2.2,
          by rw [bundlePreKeyIds_ev0], ?_⟩
        rw [hp.hregA, hikA_sec, hek_g, hct_g, hm1_g]
        decide +kernel
    refine MatchesEventsAt.run1 (fun _ h => nomatch h) hRun1 ?_
    dsimp only [runSteps, nextBundleIds]
    rw [(s1Clean_runs cl1).2]
    have hRun2 : RunMatches compI0 r S (gClean g) (tr2Clean cl1) (s2Clean cl2) ev2 v2
        (some (bundlePreKeyIds ev0.input)) := by
      refine ⟨rfl, rfl, (fitsCmd_s012Clean cl1 cl2).2.2, (matchesSetupPeer_s012Clean hp cl1 cl2).2.2,
              (s2Clean_runs cl1 cl2).1, ⟨c2Fast, ev2_exit_eq_fast⟩, rfl, ?_⟩
      refine ⟨⟨.pt, [randTerm 38 32], .single, none⟩,
              ([(randTerm 39 cl2, cl2)].filter fun r => r.2 != 0).map (fun r => rngEntry r.1),
              [⟨.send, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeySend, none⟩],
              stepView_s2Clean_eq cl1 cl2, ?_, drawsMatch_s2Clean r S g hcl2, ?_,
              (readsFaithfully_s012Clean r S g).2.2 cl1, (pathFaithful_s012Clean S g cl1 cl2).2.2⟩
      · refine ⟨rfl, ?_⟩
        dsimp only [List.map]
        unfold gamma
        rw [gamma'_randTerm compI0 S (gClean g) 38 32 (by decide)]
        rfl
      · unfold OutputsMatch
        have hcmd2 : ev2.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
        rw [ev2_exit_eq_fast, hcmd2]
        refine ⟨⟨.send, [oClean.ek, oClean.ct, m2Clean cl1 cl2], .preKeySend, none⟩, rfl, rfl, ?_⟩
        dsimp only [SendMatches]
        refine ⟨(bundlePreKeyIds ev0InFast).1, (bundlePreKeyIds ev0InFast).2.1, (bundlePreKeyIds ev0InFast).2.2,
          by rw [bundlePreKeyIds_ev0], ?_⟩
        rw [hp.hregA, hikA_sec, hek_g, hct_g, hm2_g]
        decide +kernel
    refine MatchesEventsAt.run1 (fun _ h => nomatch h) hRun2 ?_
    exact MatchesEventsAt.nil (fun _ h => nomatch h)
  · rw [runTrace_ss3Clean hp]
    obtain ⟨hak_ek, hak_ct, hak_m2⟩ := attackerKnows_c2_tr3Clean cl1 cl2
    refine ⟨hak_ek, hak_ct, hak_m2, ?_, p_c2, parsePreKeyWire_ev3, msg2Clean cl1 cl2,
            parse_m2Clean cl1 cl2, ?_⟩
    · refine ⟨p_c2, parsePreKeyWire_ev3, ?_, ?_, ?_, by decide +kernel, ?_, ?_, ?_,
              false, opkNamed_ev3_false⟩
      · dsimp only; rw [hek_g]; decide +kernel
      · dsimp only; rw [hct_g]; decide +kernel
      · dsimp only; rw [hm2_g]; decide +kernel
      · rw [hp.hspkId]; decide +kernel
      · rw [hp.hkpkId]; decide +kernel
      · rw [hikA_sec]; decide +kernel
    · have hdhsPk : DagTermAt S (gClean g) pts (DY.DiffieHellman.dhPk stA0Clean.dhs) 73 := by
        unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]; exact dagN_73 hw
      have hseed2 : DagTermAt S (gClean g) pts (DY.Libsignal.TripleRatchet.kdfCk (stA1Clean cl1).cks).2 112 :=
        termAt_kdf (id := 112) dag_nodes_ok (by decide) rfl hcks1 (dagN_2 hw)
      obtain ⟨tck2, tmk2, tiv2⟩ := termAt_trMsgKeys
        (prk_id := 114) (ck_id := 115) (c2_id := 116) (mk_id := 117) (c3_id := 118) (iv_id := 119)
        dag_nodes_ok (dagN_15 hw) (dagN_16 hw) (dagN_17 hw)
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        (dagN_23 hw) hseed2
      have hct2 := termAt_symEncPt (id := 120) dag_nodes_ok (by decide)
        (congrArg (DagOp.symEncPt 115 119 38) (by decide +kernel) : dagOp 120 = .symEncPt 115 119 38 ev2.input)
        tck2 tiv2 hw.hpt2_mem hw.hσ_pt2 (by decide +kernel)
      have hwire2 := termAt_trWire (id := 121) dag_nodes_ok (by decide)
        (congrArg (DagOp.trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24) (by decide +kernel) :
          dagOp 121 = .trWire DY.Libsignal.TripleRatchet.messageVersion 73 1 0 120 24 cleanAddrBs)
        hdhsPk hct2 (dagN_24 hw) (hw.haddr _)
      have hmac2 := termAt_computeMac
        (c1_id := 122) (c2_id := 123) (h_id := 124) (t_id := 125)
        dag_nodes_ok ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
        tmk2 (dagN_28 hw) (dagN_31 hw) hwire2
      have hw_g : gamma compI0 S (gClean g) (msg2Clean cl1 cl2).wire = dagBytes 121 := hwire2.2.1
      have hm_g : gamma compI0 S (gClean g) (msg2Clean cl1 cl2).mac = dagBytes 125 := hmac2.2.1
      have hc_g : gamma compI0 S (gClean g) (msg2Clean cl1 cl2).ciphertext = dagBytes 120 := hct2.2.1
      have hr_g : gamma compI0 S (gClean g) (msg2Clean cl1 cl2).ratchetKey = dagBytes 73 := hdhsPk.2.1
      have hp_g : gamma compI0 S (gClean g) (msg2Clean cl1 cl2).pqRatchet = dagBytes 24 := hpqm2
      refine ⟨?_, ?_, spqrHeaded_computeMac_false _ _ _ _, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hw_g]; decide +kernel
      · rw [hm_g]; decide +kernel
      · rw [hc_g]; decide +kernel
      · rw [hr_g]; decide +kernel
      · rw [hp_g]; decide +kernel
      · change (1 : UInt32).toNat = p_c2.inner.counter.toNat; decide +kernel
      · change DY.Libsignal.TripleRatchet.messageVersion.toNat = p_c2.inner.messageVersion.toNat
        decide +kernel


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
