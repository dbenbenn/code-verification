/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixC
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Clean-Prefix Extraction & `¬ KnownBaseKeyOn` (`CleanPrefix.lean`)

Exports the 3 clean-prefix theorems for `RecvNoCollision`:
1. `not_knownBaseKeyOn_5`
2. `extract_clean_2`
3. `extract_clean_5`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefix

open scoped DY.Libsignal.Composed
open DY (Bytes Participant Traceful ExecTrace ExecTraceTypes TraceEntryHas)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH
  (PQXDHEvent BundleHandles BobKeyHandles PreKeyMsgHandles)
open DY.Libsignal.TripleRatchet
  (TRState TREvent SessionInfo KeyDir logMessageKeyAndStore
   messageEncrypt messageEncryptAbort)
open DY.Libsignal.Composed (ComposedEvent aliceStart)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds Move PreKeyFields
   gamma ecKey pubBytes secretBytes received receivedPlaintext bobOpkPk bobVis
   pqExposureAt trExposureAt exposures stepView bobDoneBaseKeys setupTrace runTrace runSteps
   RunMatches OutputsMatch BytesMatchEntry PreKeyRecvOpkMatches KnownBaseKeyOn
   Explains runWrapped parsePreKeyWire preKeyRepresentationsOn)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
  (PQXDHEntry TRStEntry RndE NetE PQEvE TRStE TREvE CEvE at?_append_cases)
open Symbolic.Swarm.CREF
  (bobOpkPk_eq bobStartTr rpkT_bobStart_inv rpkT_bobDoneBaseKeys_append_other
   rpkT_bobDoneBaseKeys_append_pq rpkT_bobDoneBaseKeys_bobStartTr rpkT_getMessageSentAt_of_at?)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next run_bind_pure_snd)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (registerIdentityTr genSignedPrekeyTr genPQPrekeyTr genOneTimePrekeyTr)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (oOpk dhsAOpk stA0Opk t4Opk t7Opk t4Opk_length t7Opk_length)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (trace0 ev ev0_cmd_and_exit ev3_cmd_and_exit ev3_in_eq_ev0 ev0_bundle_base
   nextBundleIds_ev1 nextBundleIds_ev2 nextBundleIds_ev4
   ev0KyberEnt ev0_coins_base ev3KyberEnt ev3_coins_base
   ev1_facts ev2_facts ev4_facts ev1_to_ev2 ev4_to_ev5
   ev2In_eq ev5In_eq p2 p5 parse_ev2 parse_ev5 p2_ne_p5_baseKey)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (ValidCoinLens t4_entry_facts setupTrace_eq_t4Opk ssClean
   m0Clean o2Clean dhsA2Clean stA2_0Clean m1Clean cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis (visClean)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
  (r_facts_of_fit gClean gClean_sigma_26 gClean_sigma_27 gClean_sigma_28
   gClean_sigma_35 gClean_sigma_36 gClean_sigma_52 gClean_sigma_53 gClean_sigma_54
   gClean_sigma_61 gClean_sigma_62)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA
  (runSteps_append PeeledCall PeeledValid trace0_take_eq_evsRange peel_evsRange
   clsOfCalls validCoinLens_clsOfCalls stepCoinLen)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixB
  (pkiUnchanged_t4Opk hsSidBound_t4Opk)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixC
  (alice_init_agree alice_send_agree bob_call2_preserve
   explains_ssClean_2 explains_ssClean_5)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
  (cleanPreKeyRep_2_mem cleanPreKeyRep_5_mem)

attribute [local irreducible] WitnessParse.ev

/-! ## 1. `bobDoneBaseKeys` Tracking & `not_knownBaseKeyOn_5` -/

private def BksEq (L : List Bytes) (tr : ExecTrace) : Prop :=
  bobDoneBaseKeys tr = L

private theorem bksEq_append_non {E : Type} [ExecTraceTypes.Has E] {L : List Bytes}
    {tr : ExecTrace} (h : BksEq L tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none) :
    BksEq L (tr.append e) :=
  (rpkT_bobDoneBaseKeys_append_other tr e hnone).trans h

private theorem bksEq_t4Opk : BksEq [] t4Opk := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  unfold BksEq
  dsimp only [t4Opk, genOneTimePrekeyTr]
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      ht4]
  dsimp only [genPQPrekeyTr]
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      ht3]
  dsimp only [genSignedPrekeyTr]
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      ht2]
  dsimp only [registerIdentityTr]
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      ht1]
  dsimp only [registerIdentityTr]
  rw [rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl,
      rpkT_bobDoneBaseKeys_append_pq, List.append_nil,
      rpkT_bobDoneBaseKeys_append_other _ _ rfl]
  unfold bobDoneBaseKeys
  rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl

private theorem bksEq_runSteps_network {L : List Bytes} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) → BksEq L tr → BksEq L (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨msg, rfl⟩ := hnet s List.mem_cons_self
    have hs : BksEq L ((Step.network msg).next tr) := by
      rw [next_network]; exact bksEq_append_non h (NetE msg) rfl
    exact bksEq_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hs

private theorem bksEq_genRand (L : List Bytes) (n : Nat) :
    CompTrace.Preserves (BksEq L) (DY.Random.genRand n : Traceful Bytes) :=
  fun tr h => (Runs.genRand tr n).2.symm ▸ bksEq_append_non h (RndE n) rfl

private theorem bksEq_sendMessage (L : List Bytes) (msg : Bytes) :
    CompTrace.Preserves (BksEq L) (DY.Network.sendMessage msg) :=
  fun tr h => (Runs.sendMessage tr msg).2.symm ▸ bksEq_append_non h (NetE msg) rfl

private theorem bksEq_logTr (L : List Bytes) (ev0 : TREvent) :
    CompTrace.Preserves (BksEq L) (DY.ProtocolEvent.logEvent ev0) :=
  fun tr h => by rw [logEvent_snd_eq]; exact bksEq_append_non h (TREvE ev0) rfl

private theorem bksEq_logC (L : List Bytes) (ev0 : ComposedEvent) :
    CompTrace.Preserves (BksEq L) (DY.ProtocolEvent.logEvent ev0) :=
  fun tr h => by rw [logEvent_snd_eq]; exact bksEq_append_non h (CEvE ev0) rfl

private theorem bksEq_storeTr (L : List Bytes) (me : Participant) (st : TRState) :
    CompTrace.Preserves (BksEq L) (DY.PersistentLocalState.storeLocalState me st) :=
  fun tr h => by rw [storeLocalState_tr_snd_eq]; exact bksEq_append_non h (TRStE me st) rfl

private theorem bksEq_aliceStart (L : List Bytes)
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    CompTrace.Preserves (BksEq L) (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr h
  unfold aliceStart
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr h
    (bksEq_append_non h (RndE 32) rfl) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h2 : BksEq L ((tr.append (RndE 32)).append (RndE 32)) :=
    bksEq_append_non (bksEq_append_non h (RndE 32) rfl) (RndE 32) rfl
  refine (show CompTrace.Preserves (BksEq L) _ by
    refine CompTrace.Preserves.bind (bksEq_genRand L 32) fun _ => ?_
    refine CompTrace.Preserves.bind (bksEq_sendMessage L _) fun _ => ?_
    refine CompTrace.Preserves.bind (bksEq_sendMessage L _) fun _ => ?_
    refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
    refine CompTrace.Preserves.bind ?_ fun _ => ?_
    · intro t ht
      rw [(Runs.logEvent t _).2]
      unfold BksEq at ht ⊢
      rw [rpkT_bobDoneBaseKeys_append_pq, ht, List.append_nil]
    · refine CompTrace.Preserves.bind (bksEq_logTr L _) fun _ => ?_
      refine CompTrace.Preserves.bind (bksEq_logC L _) fun _ => ?_
      exact bksEq_storeTr L a _) _ h2

private theorem bksEq_messageEncrypt (L : List Bytes)
    (me : Participant) (stH coinsLen pqIdx : Nat) :
    CompTrace.Preserves (BksEq L) (messageEncrypt me stH coinsLen pqIdx) := by
  unfold messageEncrypt logMessageKeyAndStore
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (bksEq_genRand L 32) fun _ => ?_
  refine CompTrace.Preserves.bind (bksEq_genRand L coinsLen) fun _ => ?_
  refine CompTrace.Preserves.bind (bksEq_sendMessage L _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (bksEq_logTr L _) fun _ => ?_
  refine CompTrace.Preserves.bind
    (CompTrace.Preserves.bind (bksEq_logTr L _) fun _ => bksEq_storeTr L me _) fun _ => ?_
  exact bksEq_sendMessage L _

private theorem bksEq_messageEncryptAbort (L : List Bytes) (me : Participant) (stH : Nat) :
    CompTrace.Preserves (BksEq L) (messageEncryptAbort me stH) := by
  unfold messageEncryptAbort
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (bksEq_genRand L 32) fun _ => ?_
  exact CompTrace.Preserves.failure

private theorem bksEq_alice_step {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {L : List Bytes} {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {c : PeeledCall}
    {e : RunEvent}
    (h : BksEq L tr)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hcmd : (∃ peer bp, e.cmd = .init peer bp) ∨ (∃ peer, e.cmd = .send peer))
    (hrm : RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s e c.v initIds) :
    BksEq L (c.s.next (runSteps c.pre tr)) := by
  set tr₁ := runSteps c.pre tr
  have h₁ : BksEq L tr₁ := bksEq_runSteps_network c.pre hnet h
  have hfits := hrm.2.2.1
  rcases hcmd with ⟨peer, bp, hc⟩ | ⟨peer, hc⟩
  · rw [hc] at hfits
    cases hs : c.s <;> rw [hs] at hfits <;> try cases hfits
    rename_i a b idIdx regB bh
    dsimp only [Step.next, Step.toInput]
    erw [stepIn_next]
    exact bksEq_aliceStart L a b idIdx regB bh tr₁ h₁
  · rw [hc] at hfits
    cases hs : c.s <;> rw [hs] at hfits <;> try cases hfits
    · rename_i me stH cl pq
      dsimp only [Step.next, Step.toInput]
      erw [stepIn_next]
      exact bksEq_messageEncrypt L me stH cl pq tr₁ h₁
    · rename_i me stH
      dsimp only [Step.next, Step.toInput]
      erw [stepIn_next]
      exact bksEq_messageEncryptAbort L me stH tr₁ h₁

private theorem exposures_kind_leak {tr tr' : ExecTrace} {w : VisEntry}
    (hw : w ∈ exposures tr tr') : w.kind = .leak := by
  unfold exposures at hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold pqExposureAt at hj
    rcases h : tr'.getEventAt PQXDHEvent j with _ | ev_pq <;> rw [h] at hj
    · cases hj
    · cases ev_pq <;> simp at hj <;> subst hj <;> rfl
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold trExposureAt at hj
    rcases h : tr'.getEventAt TREvent j with _ | ev_tr <;> rw [h] at hj
    · cases hj
    · cases ev_tr <;> simp at hj <;> subst hj <;> rfl

private theorem bksEq_bob_call2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {c : PeeledCall}
    (hnil : BksEq [] tr)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s (ev 2) c.v initIds) :
    ∃ ek₂, ecKey (gamma keepOpkI0 S g ek₂) = p2.baseKey.take 33 ∧
      BksEq [ek₂] (c.s.next (runSteps c.pre tr)) := by
  set tr₁ := runSteps c.pre tr
  have hnil₁ : BksEq [] tr₁ := bksEq_runSteps_network c.pre hnet hnil
  obtain ⟨hp_bob, hcmd2, _, _⟩ := ev2_facts
  obtain ⟨_, hparty, hfits, _, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, _, hout, _, hpf⟩ := hrm
  have hnot_known : ¬ ∃ ek ∈ bobDoneBaseKeys tr₁,
      ecKey (gamma keepOpkI0 S g ek) = p2.baseKey.take 33 := by
    rw [hnil₁]; rintro ⟨_, ⟨⟩, _⟩
  have hpath := hpf p2 parse_ev2
  rw [hcmd2] at hfits
  cases hs : c.s <;> rw [hs] at hfits hparty hok hvis_eq hpath <;> try cases hfits
  case messageDecrypt => exact False.elim (hnot_known hpath)
  case messageDecryptSkipped => exact False.elim (hnot_known hpath)
  case bobStart b a kh regA mh pqIdx spqr =>
    rw [hp_bob] at hparty
    rcases Option.some.inj hparty with rfl
    obtain ⟨out, hex2⟩ := hexit
    unfold OutputsMatch at hout; rw [hex2, hcmd2] at hout
    obtain ⟨w_out, rfl, hbm_out⟩ := hout
    have hw_accept : w_out.kind = .accept := hbm_out.1.symm
    have hnext_mv : (Step.bobStart "bob" a kh regA mh pqIdx spqr).next tr₁ =
        (Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr₁ := by
      dsimp only [Move.next, Move.act, Step.next, Step.toInput]
      erw [stepIn_next]; exact (run_bind_pure_snd _ tr₁).symm
    have hview : stepView (.bobStart "bob" a kh regA mh pqIdx spqr) tr₁ (runWrapped (ev 2)) =
        bobVis tr₁ ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr₁)
          mh (bobOpkPk "bob" kh tr₁) ++
        exposures tr₁ ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr₁) := by
      unfold stepView; simp only [hok, ↓reduceIte]; rw [hnext_mv]
    have hpt_some : ∃ pt,
        receivedPlaintext tr₁ ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr₁) =
          some pt := by
      rcases hpt : receivedPlaintext tr₁
          ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr₁) with _ | pt
      · exfalso
        have hw_mem : w_out ∈ c.v := by rw [hv_split]; simp
        rw [hvis_eq, hview, List.mem_append] at hw_mem
        rcases hw_mem with hw_bob | hw_exp
        · simp only [bobVis, hpt, Option.map_none, Option.toList_none, List.append_nil,
            List.mem_cons, List.mem_map] at hw_bob
          rcases hw_bob with rfl | ⟨_, _, rfl⟩ <;>
            simp [DY.Libsignal.Composed.Refinement.rngEntry] at hw_accept
        · rw [exposures_kind_leak hw_exp] at hw_accept; cases hw_accept
      · exact ⟨pt, rfl⟩
    obtain ⟨pt, hpt⟩ := hpt_some
    obtain ⟨w⟩ := rpkT_bobStart_inv hpt
    have htr' : (Step.bobStart "bob" a kh regA mh pqIdx spqr).next tr₁ =
        bobStartTr tr₁ "bob" a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m :=
      hnext_mv.trans (w.next_eq 0)
    have hrec_terms : received tr₁ [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hinp_eq : inp = ⟨.recv, [w.ek, w.ct, w.raw] ++ (w.opk.map DY.DiffieHellman.dhPk).toList,
        .preKeyRecv, none⟩ := by
      have hcons := hv_split.symm.trans (hvis_eq.trans hview)
      unfold bobVis at hcons
      rw [hrec_terms, bobOpkPk_eq tr₁ "bob" kh w.opk w.hopk] at hcons
      exact List.head_eq_of_cons_eq hcons
    have hbm_opk : PreKeyRecvOpkMatches keepOpkI0 r S g (ev 2).input
        ([w.ek, w.ct, w.raw] ++ (w.opk.map DY.DiffieHellman.dhPk).toList) := by
      unfold BytesMatchEntry at hbm_in; rw [hinp_eq] at hbm_in; exact hbm_in.2
    have hprm : DY.Libsignal.Composed.Refinement.PreKeyRecvMatches keepOpkI0 r S g (ev 2).input
        [w.ek, w.ct, w.raw] := by
      rcases hw : w.opk with _ | o <;> (rw [hw] at hbm_opk; exact hbm_opk.1)
    obtain ⟨p', hp', hbk_eq, _⟩ := hprm
    rw [parse_ev2] at hp'; cases hp'
    refine ⟨w.ek, hbk_eq.symm, ?_⟩
    unfold BksEq at hnil₁ ⊢
    rw [htr', rpkT_bobDoneBaseKeys_bobStartTr, hnil₁]; rfl

theorem not_knownBaseKeyOn_5
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hex : Explains keepOpkI0 r S g ss vis (trace0.take 5)) :
    ¬ KnownBaseKeyOn keepOpkI0 S g (runTrace r ss) p5 := by
  have hf := r_facts_of_fit hfit
  obtain ⟨_, _, hwf_run, hme⟩ := hex
  have hm_ev := hme
  rw [trace0_take_eq_evsRange (by decide)] at hm_ev
  obtain ⟨cs, hlen, hpv⟩ := peel_evsRange 5 0 (by decide) hwf_run.2.2.1 hm_ev (fun _ hw => hw)
  cases hpv with
  | nil _ => cases hlen
  | @cons _ _ _ c0 _ _ hnet0 _ _ hrm0 _ hpv1 =>
    cases hpv1 with
    | nil _ => simp at hlen
    | @cons _ _ _ c1 _ _ hnet1 _ _ hrm1 _ hpv2 =>
      cases hpv2 with
      | nil _ => simp at hlen
      | @cons _ _ _ c2 _ _ hnet2 _ _ hrm2 _ hpv3 =>
        cases hpv3 with
        | nil _ => simp at hlen
        | @cons _ _ _ c3 _ _ hnet3 _ _ hrm3 _ hpv4 =>
          cases hpv4 with
          | nil _ => simp at hlen
          | @cons _ _ _ c4 _ tail hnet4 _ _ hrm4 _ hpv5 =>
            cases hpv5 with
            | cons _ _ _ _ _ _ => simp at hlen
            | nil hnet_tail =>
              have hbks0 : BksEq [] (setupTrace r) := by
                rw [setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq]; exact bksEq_t4Opk
              have hbks1 := bksEq_alice_step hbks0 hnet0
                (Or.inl ⟨_, _, ev0_cmd_and_exit.2.1⟩) hrm0
              have hbks2 := bksEq_alice_step hbks1 hnet1
                (Or.inr ⟨_, ev1_facts.2.1⟩) hrm1
              obtain ⟨ek₂, hek₂, hbks3⟩ := bksEq_bob_call2 hbks2 hnet2 hrm2
              have hbks4 := bksEq_alice_step hbks3 hnet3
                (Or.inl ⟨_, _, ev3_cmd_and_exit.2.1⟩) hrm3
              have hbks5 := bksEq_alice_step hbks4 hnet4
                (Or.inr ⟨_, ev4_facts.2.1⟩) hrm4
              have hbks_end := bksEq_runSteps_network tail hnet_tail hbks5
              have hrun_eq : runTrace r
                  (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s ::
                    (c3.pre ++ c3.s :: (c4.pre ++ c4.s :: tail))))) =
                  runSteps tail (c4.s.next (runSteps c4.pre
                    (c3.s.next (runSteps c3.pre
                      (c2.s.next (runSteps c2.pre
                        (c1.s.next (runSteps c1.pre
                          (c0.s.next (runSteps c0.pre (setupTrace r))))))))))) := by
                unfold runTrace
                simp only [runSteps_append, runSteps]
              rintro ⟨ek, hek_mem, hbk5⟩
              rw [hrun_eq, hbks_end] at hek_mem
              rcases List.mem_singleton.mp hek_mem with rfl
              exact p2_ne_p5_baseKey (hek₂.symm.trans hbk5.symm)

/-! ## 2. Clean-Prefix Extraction (`extract_clean_2` and `extract_clean_5`) -/

private theorem t4Opk_alice_role :
    ∀ i st, (t4Opk.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true := by
  obtain ⟨ht1, ht2, ht3, ht4, _⟩ := t4_entry_facts
  intro i st hat
  exfalso
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option TRStEntry) = none →
      ((tr0.append e).at? j : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ →
      (tr0.at? j : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  dsimp only [t4Opk, genOneTimePrekeyTr] at hat
  iterate 4 replace hat := peel_non rfl hat
  rw [ht4] at hat; dsimp only [genPQPrekeyTr] at hat
  iterate 6 replace hat := peel_non rfl hat
  rw [ht3] at hat; dsimp only [genSignedPrekeyTr] at hat
  iterate 6 replace hat := peel_non rfl hat
  rw [ht2] at hat; dsimp only [registerIdentityTr] at hat
  iterate 5 replace hat := peel_non rfl hat
  rw [ht1] at hat; dsimp only [registerIdentityTr] at hat
  iterate 5 replace hat := peel_non rfl hat
  have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) (DY.Trace.nil : ExecTrace) i
  rw [hat, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt

theorem extract_clean_2
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hex : Explains keepOpkI0 r S g ss vis (trace0.take 2)) :
    ∃ cls : Nat → Nat,
      ValidCoinLens cls ∧
      Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2) (visClean r cls 2) (trace0.take 2) ∧
      cleanPreKeyRep cls 2 ∈
        preKeyRepresentationsOn keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 2))
          (WitnessParse.ev 2).input ∧
      gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hCompat, hgwf, hwf_run, hme⟩ := hex
  rw [trace0_take_eq_evsRange (by decide)] at hme
  obtain ⟨cs, hlen, hpv⟩ := peel_evsRange 2 0 (by decide) hwf_run.2.2.1 hme (fun _ hw => hw)
  have hv := validCoinLens_clsOfCalls hpv
  set cls := clsOfCalls cs with hcls_def
  cases hpv with
  | nil _ => cases hlen
  | @cons _ _ _ c0 _ _ hnet0 _ _ hrm0 hsub0 hpv1 =>
    cases hpv1 with
    | nil _ => simp at hlen
    | @cons _ _ _ c1 _ _ hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
      cases hpv2 with
      | cons _ _ _ _ _ _ => simp at hlen
      | nil _ =>
        have htr0 := setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq
        obtain ⟨ek0, ct0, hek0, hct0, hpki1, hSid1, hAct1, hids1⟩ :=
          alice_init_agree cls (callIdx := 0) (trClean := t4Opk) (dhsClean := dhsAOpk)
            (kyberEnt := ev0KyberEnt) hfit hCompat hgwf
            (htr0 ▸ pkiUnchanged_t4Opk) (htr0 ▸ hsSidBound_t4Opk) (htr0 ▸ t4Opk_alice_role)
            ⟨ev0_cmd_and_exit.1, ev0_cmd_and_exit.2.1, ev0_cmd_and_exit.2.2.1⟩
            rfl ev0_bundle_base.2.2.1
            ⟨ev0_coins_base.1, ev0_coins_base.2.1, ev0_coins_base.2.2.2⟩
            (by rw [t4Opk_length]; exact gClean_sigma_26 r cls 32)
            (by rw [t4Opk_length]; exact gClean_sigma_27 r cls 32)
            (by rw [t4Opk_length])
            (by rw [t4Opk_length]; exact gClean_sigma_28 r cls 32)
            hnet0 hrm0 hsub0
        rw [hids1] at hrm1
        obtain ⟨_, _, _, hev1_out⟩ :=
          alice_send_agree cls (oClean := oOpk) (stClean := stA0Opk)
            (sIdx := 0) (tsPt := 35) (tsCoins := 36)
            hgwf hpki1 hSid1 hek0 hct0 hAct1
            ⟨ev1_facts.1, ⟨_, ev1_facts.2.1⟩, ev1_facts.2.2.2.2⟩
            rfl (gClean_sigma_35 r cls 32) (gClean_sigma_36 r cls)
            hnet1 hpre1 hlok1 hrm1 hsub1
        have hexClean2 := explains_ssClean_2 hfit hv hCompat hev1_out
        have hb2 : (ev 2).input = _ := Option.some.inj (ev1_to_ev2.symm.trans hev1_out) |> Prod.mk.inj |>.2
        have hlen2 : (ev 2).input.length < 2 ^ 63 := by rw [ev2In_eq]; decide +kernel
        have hm0 : gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message :=
          (parsePreKeyWire_preKeyWire_inv hb2 hlen2 parse_ev2).2.2.2.symm
        exact ⟨cls, hv, hexClean2, cleanPreKeyRep_2_mem hfit hv hexClean2, hm0⟩

theorem extract_clean_5
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hex : Explains keepOpkI0 r S g ss vis (trace0.take 5)) :
    ∃ cls : Nat → Nat,
      ValidCoinLens cls ∧
      Explains keepOpkI0 r S (gClean r cls) (ssClean cls 5) (visClean r cls 5) (trace0.take 5) ∧
      cleanPreKeyRep cls 5 ∈
        preKeyRepresentationsOn keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 5))
          (WitnessParse.ev 5).input ∧
      gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message ∧
      gamma keepOpkI0 S (gClean r cls) (m1Clean cls) = p5.message := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hCompat, hgwf, hwf_run, hme⟩ := hex
  rw [trace0_take_eq_evsRange (by decide)] at hme
  obtain ⟨cs, hlen, hpv⟩ := peel_evsRange 5 0 (by decide) hwf_run.2.2.1 hme (fun _ hw => hw)
  have hv := validCoinLens_clsOfCalls hpv
  set cls := clsOfCalls cs with hcls_def
  cases hpv with
  | nil _ => cases hlen
  | @cons _ _ _ c0 _ _ hnet0 _ _ hrm0 hsub0 hpv1 =>
    cases hpv1 with
    | nil _ => simp at hlen
    | @cons _ _ _ c1 _ _ hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
      cases hpv2 with
      | nil _ => simp at hlen
      | @cons _ _ _ c2 _ _ hnet2 _ _ hrm2 _ hpv3 =>
        cases hpv3 with
        | nil _ => simp at hlen
        | @cons _ _ _ c3 _ _ hnet3 _ _ hrm3 hsub3 hpv4 =>
          cases hpv4 with
          | nil _ => simp at hlen
          | @cons _ _ _ c4 _ _ hnet4 hpre4 hlok4 hrm4 hsub4 hpv5 =>
            cases hpv5 with
            | cons _ _ _ _ _ _ => simp at hlen
            | nil _ =>
              have htr0 := setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq
              obtain ⟨ek0, ct0, hek0, hct0, hpki1, hSid1, hAct1, hids1⟩ :=
                alice_init_agree cls (callIdx := 0) (trClean := t4Opk) (dhsClean := dhsAOpk)
                  (kyberEnt := ev0KyberEnt) hfit hCompat hgwf
                  (htr0 ▸ pkiUnchanged_t4Opk) (htr0 ▸ hsSidBound_t4Opk) (htr0 ▸ t4Opk_alice_role)
                  ⟨ev0_cmd_and_exit.1, ev0_cmd_and_exit.2.1, ev0_cmd_and_exit.2.2.1⟩
                  rfl ev0_bundle_base.2.2.1
                  ⟨ev0_coins_base.1, ev0_coins_base.2.1, ev0_coins_base.2.2.2⟩
                  (by rw [t4Opk_length]; exact gClean_sigma_26 r cls 32)
                  (by rw [t4Opk_length]; exact gClean_sigma_27 r cls 32)
                  (by rw [t4Opk_length])
                  (by rw [t4Opk_length]; exact gClean_sigma_28 r cls 32)
                  hnet0 hrm0 hsub0
              rw [hids1] at hrm1 hrm2 hrm3 hrm4
              obtain ⟨hpki2, hSid2, hrole2, hev1_out⟩ :=
                alice_send_agree cls (oClean := oOpk) (stClean := stA0Opk)
                  (sIdx := 0) (tsPt := 35) (tsCoins := 36)
                  hgwf hpki1 hSid1 hek0 hct0 hAct1
                  ⟨ev1_facts.1, ⟨_, ev1_facts.2.1⟩, ev1_facts.2.2.2.2⟩
                  rfl (gClean_sigma_35 r cls 32) (gClean_sigma_36 r cls)
                  hnet1 hpre1 hlok1 hrm1 hsub1
              obtain ⟨hpki3, hSid3, hrole3⟩ :=
                bob_call2_preserve hpki2 hSid2 hrole2 hnet2 hrm2
              rw [nextBundleIds_ev1, nextBundleIds_ev2] at hrm3 hrm4
              obtain ⟨ek3, ct3, hek3, hct3, hpki4, hSid4, hAct4, hids4⟩ :=
                alice_init_agree cls (callIdx := 3) (trClean := t7Opk) (dhsClean := dhsA2Clean)
                  (kyberEnt := ev3KyberEnt) hfit hCompat hgwf hpki3 hSid3 hrole3
                  ⟨ev3_cmd_and_exit.1, ev3_cmd_and_exit.2.1, ev3_cmd_and_exit.2.2.1⟩
                  ev3_in_eq_ev0 ev0_bundle_base.2.2.2.1
                  ⟨ev3_coins_base.1, ev3_coins_base.2.1, ev3_coins_base.2.2⟩
                  (by rw [t7Opk_length]; exact gClean_sigma_52 r cls 32)
                  (by rw [t7Opk_length]; exact gClean_sigma_53 r cls 32)
                  (by rw [t7Opk_length]; rfl)
                  (by rw [t7Opk_length]; exact gClean_sigma_54 r cls 32)
                  hnet3 hrm3 hsub3
              rw [hids4] at hrm4
              obtain ⟨_, _, _, hev4_out⟩ :=
                alice_send_agree cls (oClean := o2Clean) (stClean := stA2_0Clean)
                  (sIdx := 1) (tsPt := 61) (tsCoins := 62)
                  hgwf hpki4 hSid4 hek3 hct3 hAct4
                  ⟨ev4_facts.1, ⟨_, ev4_facts.2.1⟩, ev4_facts.2.2.2.2⟩
                  rfl (gClean_sigma_61 r cls 32) (gClean_sigma_62 r cls)
                  hnet4 hpre4 hlok4 hrm4 hsub4
              have hexClean5 := explains_ssClean_5 hfit hv hCompat hev1_out hev4_out
              have hb2 : (ev 2).input = _ :=
                (Prod.mk.inj (Option.some.inj (ev1_to_ev2.symm.trans hev1_out))).2
              have hlen2 : (ev 2).input.length < 2 ^ 63 := by rw [ev2In_eq]; decide +kernel
              have hm0 : gamma keepOpkI0 S (gClean r cls) (m0Clean cls) = p2.message :=
                (parsePreKeyWire_preKeyWire_inv hb2 hlen2 parse_ev2).2.2.2.symm
              have hb5 : (ev 5).input = _ :=
                (Prod.mk.inj (Option.some.inj (ev4_to_ev5.symm.trans hev4_out))).2
              have hlen5 : (ev 5).input.length < 2 ^ 63 := by rw [ev5In_eq]; decide +kernel
              have hm1 : gamma keepOpkI0 S (gClean r cls) (m1Clean cls) = p5.message :=
                (parsePreKeyWire_preKeyWire_inv hb5 hlen5 parse_ev5).2.2.2.symm
              exact ⟨cls, hv, hexClean5, cleanPreKeyRep_5_mem hfit hv hexClean5, hm0, hm1⟩

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefix
