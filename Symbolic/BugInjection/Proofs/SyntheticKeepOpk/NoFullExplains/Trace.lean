/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Parse
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.Opk
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Generic `¬ Explains` Disproof for `KeepOpkCli.trace` (`NoFullExplains/Trace.lean`)

Proves `not_explains_keepOpk_generic` for arbitrary `interp : ExternInterpretation` and
`r : ProtocolSetup`:

1. `setupTrace r` stores at most one `.oneTimePrekey` secret `opkSk₀` for `"bob"` (`OnlyOneBobOpk`)
   and starts with `bobDoneBaseKeys (setupTrace r) = []`.
2. Invisible `.network` prefixes and `"alice"` `.init`/`.send` steps preserve both `bobDoneBaseKeys`
   and `OnlyOneBobOpk opkSk₀` (and advance the trace monotonically, preserving `PQXDH.opkUsedB`).
3. On Call `2` (`ev 2`, Bob `.recv` with `p₂.preKeyId ≠ none`), `bobDoneBaseKeys = []` forces
   `Step.bobStart`, consuming `opkSk₀`, appending `[ek₂]` (`ecKey (γ ek₂) = p₂.baseKey.take 33`)
   to `bobDoneBaseKeys`, and logging `PQXDHEvent.OPKUsed "bob" (dhPk opkSk₀)` (`opkUsedB = true`).
4. On Call `5` (`ev 5`, Bob `.recv` with `p₅.preKeyId ≠ none` and `p₂.baseKey.take 33 ≠ p₅.baseKey.take 33`),
   `PathFaithfulAt` again forces `Step.bobStart` reading the unique `opkSk₀`, whose single-use
   guard requires `opkUsedB = false`, contradicting `opkUsedB = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Trace

open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant Traceful ExecTrace ExecTraceTypes TraceEntryHas)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH
  (PQXDHState PQXDHEvent KeyKind BundleHandles BobKeyHandles PreKeyMsgHandles
   registerIdentity genSignedPrekey genPQPrekey genOneTimePrekey opkUsedB)
open DY.Libsignal.TripleRatchet
  (TRState TREvent SessionInfo KeyDir logSkippedKeys logMessageKeyAndStore
   messageEncrypt messageEncryptAbort)
open DY.Libsignal.Composed (ComposedEvent reachability aliceStart)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds Move PreKeyFields
   gamma ecKey received receivedPlaintext bobOpkPk bobVis pqExposureAt trExposureAt exposures
   stepView bobDoneBaseKeys setupAct setupTrace runSteps nextBundleIds randTerm
   RunRejected RunMatches OutputsMatch BytesMatchEntry PreKeyRecvOpkMatches PreKeyRecvMatches
   OpkNamed MatchesEventsAt Explains inputKind runWrapped parsePreKeyWire)
open Symbolic.Swarm.COMPOSED
open Symbolic.Swarm.COMPOSED.CompTrace
  (PQXDHEntry PQXDHStEntry RndE NetE PQEvE PQStE TRStE TREvE CEvE PQXDHStoredAt
   pqxdhStoredAt_append_same pqxdhStoredAt_append_other)
open Symbolic.Swarm.CREF
  (StOpt bobOpkPk_eq bobStartPreSkipTr bobStartTr
   rpkT_bobStart_inv rpkT_bobDoneBaseKeys_append_other rpkT_bobDoneBaseKeys_append_pq
   rpkT_bobDoneBaseKeys_bobStartTr rpkT_getMessageSentAt_of_at?
   isOpkUsedPred opkUsedB_eq_false_iff opkUsedB_mono)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Parse
  (cliTrace ev trace_eq_evs ev_not_rejected ev_alice_init_or_send
   ev2_bob_recv ev5_bob_recv ev2_ev5_preKey_facts)

/-! ## 1. Trace Monotonicity, Step Projections, and `MatchesEventsAt` Peeling -/

private theorem run_le {α : Type} (m : Traceful α) (tr : ExecTrace) :
    tr ≤ (m.run tr).2.val :=
  (m.run tr).2.property

private theorem run_bind_pure_snd {α : Type} (x : Traceful α) (tr : ExecTrace) :
    ((x >>= fun _ => pure ()).run tr).2.val = (x.run tr).2.val := by
  rw [CompTrace.run_bind_snd]
  rcases x.run tr with ⟨_ | _, _⟩ <;> simp [DY.Traceful.run_pure]

private theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

private theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

private theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

private theorem step_next_bobStart (b a : Participant) (kh : BobKeyHandles)
    (regA : Nat) (mh : PreKeyMsgHandles) (pqIdx : Nat) (spqr : UInt32) (tr : ExecTrace) :
    (Step.bobStart b a kh regA mh pqIdx spqr).next tr =
      (Move.bobStart b a kh regA mh pqIdx spqr 0).next tr := by
  dsimp only [Move.next, Move.act, Step.next, Step.toInput]
  erw [stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

private theorem matchesEventsAt_peel_run {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {initIds : Option BundlePreKeyIds}
    {tr : ExecTrace} {ss : List Step} {e : RunEvent} {evs : List CliEvent} {vis : List VisEntry}
    (hnotRej : ¬ RunRejected e)
    (hm : MatchesEventsAt interp r S g initIds tr ss (.run e :: evs) vis) :
    ∃ pre s ss' v vs,
      (∀ x ∈ pre, ∃ msg, x = .network msg) ∧
      RunMatches interp r S g (runSteps pre tr) s e v initIds ∧
      MatchesEventsAt interp r S g (nextBundleIds initIds e)
        (s.next (runSteps pre tr)) ss' evs vs := by
  cases hm with
  | run0 _ hrej _ => exact False.elim (hnotRej hrej)
  | run1 hinv hrm hrest =>
    exact ⟨_, _, _, _, _, fun x hx => step_invisible_eq_network (hinv x hx), hrm, hrest⟩

/-! ## 2. `NoBobOpk`, `OnlyOneBobOpk`, and `FrameInv` Preservation -/

private def NoBobOpk (tr : ExecTrace) : Prop :=
  ∀ i sk, ¬ PQXDHStoredAt tr "bob" { kind := .oneTimePrekey, sk } i

private def OnlyOneBobOpk (opkSk₀ : DY.Bytes) (tr : ExecTrace) : Prop :=
  ∀ i sk, PQXDHStoredAt tr "bob" { kind := .oneTimePrekey, sk } i → sk = opkSk₀

private def SetupPreInv (tr : ExecTrace) : Prop :=
  bobDoneBaseKeys tr = [] ∧ NoBobOpk tr

private def FrameInv (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (tr : ExecTrace) : Prop :=
  bobDoneBaseKeys tr = L ∧ OnlyOneBobOpk opkSk₀ tr

private theorem noBobOpk_nil : NoBobOpk (DY.Trace.nil : ExecTrace) := by
  intro _ _ h
  simp only [PQXDHStoredAt, DY.Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt,
    ↓reduceDIte, reduceCtorEq] at h

private theorem setupPreInv_nil : SetupPreInv (DY.Trace.nil : ExecTrace) := by
  refine ⟨?_, noBobOpk_nil⟩
  simp [bobDoneBaseKeys, Symbolic.DYBridge.DY.Trace.length_eq_1]

private theorem noBobOpk_append_other {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (h : NoBobOpk tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none) :
    NoBobOpk (tr.append e) :=
  fun i sk hst => h i sk (pqxdhStoredAt_append_other hnone hst)

private theorem noBobOpk_append_pqSt {tr : ExecTrace} (h : NoBobOpk tr) (me : Participant)
    (st₀ : PQXDHState) (hk : st₀.kind ≠ .oneTimePrekey) :
    NoBobOpk (tr.append (PQStE me st₀)) := by
  intro i sk hst
  rcases pqxdhStoredAt_append_same hst with ⟨_, h0⟩ | ⟨_, _, heq⟩
  · exact h i sk h0
  · exact hk (heq ▸ rfl)

private theorem onlyOneBobOpk_of_noBobOpk {tr : ExecTrace} (h : NoBobOpk tr) (sk₀ : DY.Bytes) :
    OnlyOneBobOpk sk₀ tr :=
  fun i sk hst => False.elim (h i sk hst)

private theorem onlyOneBobOpk_append_opk {tr : ExecTrace} (h : NoBobOpk tr) (me : Participant)
    (sk₀ : DY.Bytes) :
    OnlyOneBobOpk sk₀ (tr.append (PQStE me { kind := .oneTimePrekey, sk := sk₀ })) := by
  intro i sk hst
  rcases pqxdhStoredAt_append_same hst with ⟨_, h0⟩ | ⟨_, _, heq⟩
  · exact False.elim (h i sk h0)
  · injection heq with _ hsk
    exact hsk.symm

private theorem onlyOneBobOpk_append_other {E : Type} [ExecTraceTypes.Has E] {sk₀ : DY.Bytes}
    {tr : ExecTrace} (h : OnlyOneBobOpk sk₀ tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none) :
    OnlyOneBobOpk sk₀ (tr.append e) :=
  fun i sk hst => h i sk (pqxdhStoredAt_append_other hnone hst)

private theorem onlyOneBobOpk_logSkippedKeys (sk₀ : DY.Bytes) (s : SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) :
    ∀ (k : Nat) (ck : DY.Bytes) (idx : UInt32),
      CompTrace.Preserves (OnlyOneBobOpk sk₀) (logSkippedKeys s pk rIdx src ck idx k)
  | 0, _, _ => by
    unfold logSkippedKeys
    exact CompTrace.Preserves.pure ()
  | k + 1, ck, idx => by
    unfold logSkippedKeys
    refine CompTrace.Preserves.bind ?_ fun _ =>
      onlyOneBobOpk_logSkippedKeys sk₀ s pk rIdx src k _ (idx + 1)
    intro t ht
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
      DY.Traceful.run_pure]
    exact onlyOneBobOpk_append_other ht (TREvE _) rfl

private theorem onlyOneBobOpk_bobStartTr {sk₀ : DY.Bytes} {tr : ExecTrace}
    (h : OnlyOneBobOpk sk₀ tr) (b a : Participant) (o : DY.Libsignal.PQXDH.BobHandshakeOut)
    (msg : DY.Libsignal.TripleRatchet.TRSignalMsg) (c' : DY.Libsignal.TripleRatchet.RecvChain)
    (spqr' key seed pqSalt m : DY.Bytes) :
    OnlyOneBobOpk sk₀ (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) := by
  have hpre : OnlyOneBobOpk sk₀ (bobStartPreSkipTr tr b a o msg key) := by
    unfold bobStartPreSkipTr
    dsimp only
    apply onlyOneBobOpk_append_other _ _ rfl
    apply onlyOneBobOpk_append_other _ _ rfl
    apply onlyOneBobOpk_append_other _ _ rfl
    apply onlyOneBobOpk_append_other _ _ rfl
    cases o.opk with
    | none =>
      exact onlyOneBobOpk_append_other (onlyOneBobOpk_append_other h _ rfl) _ rfl
    | some _ =>
      exact onlyOneBobOpk_append_other
        (onlyOneBobOpk_append_other (onlyOneBobOpk_append_other h _ rfl) _ rfl) _ rfl
  unfold bobStartTr
  dsimp only
  apply onlyOneBobOpk_append_other _ _ rfl
  apply onlyOneBobOpk_append_other _ _ rfl
  apply onlyOneBobOpk_append_other _ _ rfl
  exact onlyOneBobOpk_logSkippedKeys sk₀ _ _ _ _ _ _ _ _ hpre

/-! ## 3. Setup Invariant (`setupTrace_frameInv`) -/

private theorem setupPreInv_append_nonPq {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace}
    (h : SetupPreInv tr) (e : E)
    (hnone_ev : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none) :
    SetupPreInv (tr.append e) :=
  ⟨(rpkT_bobDoneBaseKeys_append_other tr e hnone_ev).trans h.1,
   noBobOpk_append_other h.2 e hnone_st⟩

private theorem setupPreInv_genRand (n : Nat) :
    CompTrace.Preserves SetupPreInv (DY.Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact setupPreInv_append_nonPq h (RndE n) rfl rfl

private theorem setupPreInv_sendMessage (msg : DY.Bytes) :
    CompTrace.Preserves SetupPreInv (DY.Network.sendMessage msg) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact setupPreInv_append_nonPq h (NetE msg) rfl rfl

private theorem setupPreInv_storePq (me : Participant) (st : PQXDHState)
    (hk : st.kind ≠ .oneTimePrekey) :
    CompTrace.Preserves SetupPreInv (DY.PersistentLocalState.storeLocalState me st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨(rpkT_bobDoneBaseKeys_append_other tr (PQStE me st) rfl).trans h.1,
         noBobOpk_append_pqSt h.2 me st hk⟩

private theorem setupPreInv_logPq (ev : PQXDHEvent)
    (hnb : (match ev with | .BobDone .. => [()] | _ => []) = []) :
    CompTrace.Preserves SetupPreInv (DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  refine ⟨?_, noBobOpk_append_other h.2 (PQEvE ev) rfl⟩
  rw [rpkT_bobDoneBaseKeys_append_pq, h.1]
  cases ev <;> simp at hnb ⊢

private theorem setupPreInv_getKey (p : Participant) (stateIdx : Nat) (kind : KeyKind) :
    CompTrace.Preserves SetupPreInv (DY.Libsignal.PQXDH.getKey p stateIdx kind) := by
  unfold DY.Libsignal.PQXDH.getKey
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_pq p stateIdx) fun _ => ?_
  exact CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => CompTrace.Preserves.pure _

private theorem setupPreInv_registerIdentity (p : Participant) :
    CompTrace.Preserves SetupPreInv (registerIdentity p) := by
  unfold registerIdentity
  refine CompTrace.Preserves.bind (CompTrace.Preserves.requireTracePredicate _) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_logPq _ rfl) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  exact setupPreInv_storePq p _ (by intro h; cases h)

private theorem setupPreInv_genSignedPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves SetupPreInv (genSignedPrekey b idStateIdx) := by
  unfold genSignedPrekey
  refine CompTrace.Preserves.bind (setupPreInv_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_genRand 32) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_logPq _ rfl) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_storePq b _ (by intro h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

private theorem setupPreInv_genPQPrekey (b : Participant) (idStateIdx : Nat) :
    CompTrace.Preserves SetupPreInv (genPQPrekey b idStateIdx) := by
  unfold genPQPrekey
  refine CompTrace.Preserves.bind (setupPreInv_getKey b idStateIdx .identity) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_genRand 64) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_logPq _ rfl) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_storePq b _ (by intro h; cases h)) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  refine CompTrace.Preserves.bind (setupPreInv_sendMessage _) fun _ => ?_
  exact CompTrace.Preserves.pure _

private theorem bind_preserves_to {P Q : ExecTrace → Prop} {α β : Type}
    {x : Traceful α} {f : α → Traceful β}
    (hpq : ∀ tr, P tr → Q tr)
    (hx : CompTrace.Preserves P x)
    (hf : ∀ a tr, P tr → Q ((f a).run tr).2.val) :
    ∀ tr, P tr → Q (((x >>= f).run tr).2.val) := by
  intro tr hP
  rw [CompTrace.run_bind_snd]
  have hMid : P (x.run tr).2.val := hx tr hP
  rcases (x.run tr).1 with _ | a
  · exact hpq _ hMid
  · exact hf a _ hMid

private theorem genOneTimePrekey_frameInv (b : Participant) {tr : ExecTrace}
    (h : SetupPreInv tr) :
    ∃ opkSk₀, FrameInv [] opkSk₀ ((genOneTimePrekey b).run tr).2.val := by
  unfold genOneTimePrekey
  rw [CompTrace.run_genRand_bind_snd]
  let sk₀ : DY.Bytes := CompTrace.mkRand tr.length 32
  have h1 : SetupPreInv (tr.append (RndE 32)) := setupPreInv_append_nonPq h (RndE 32) rfl rfl
  have hpq : ∀ t, SetupPreInv t → FrameInv [] sk₀ t :=
    fun _ ht => ⟨ht.1, onlyOneBobOpk_of_noBobOpk ht.2 sk₀⟩
  refine ⟨sk₀, bind_preserves_to hpq (setupPreInv_logPq _ rfl) (fun _ t ht => ?_) _ h1⟩
  rw [CompTrace.run_bind_snd]
  have hstore :
      (DY.PersistentLocalState.storeLocalState b
        ({ kind := .oneTimePrekey, sk := sk₀ } : PQXDHState)).run t =
      (some t.length, ⟨t.append (PQStE b { kind := .oneTimePrekey, sk := sk₀ }),
        DY.Trace.append_le _ _⟩) := by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  rw [hstore]
  dsimp only
  have h2 : FrameInv [] sk₀ (t.append (PQStE b { kind := .oneTimePrekey, sk := sk₀ })) :=
    ⟨(rpkT_bobDoneBaseKeys_append_other t _ rfl).trans ht.1,
     onlyOneBobOpk_append_opk ht.2 b sk₀⟩
  refine CompTrace.Preserves.bind ?_ (fun _ => CompTrace.Preserves.pure _) _ h2
  intro t₂ ht₂
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact ⟨(rpkT_bobDoneBaseKeys_append_other _ _ rfl).trans ht₂.1,
         onlyOneBobOpk_append_other ht₂.2 (NetE _) rfl⟩

private theorem setupTrace_frameInv (r : ProtocolSetup) :
    ∃ opkSk₀, FrameInv [] opkSk₀ (setupTrace r) := by
  unfold setupTrace setupAct
  have hpq : ∀ tr, SetupPreInv tr → ∃ opkSk₀, FrameInv [] opkSk₀ tr :=
    fun _ h => ⟨randTerm 0 0, h.1, onlyOneBobOpk_of_noBobOpk h.2 _⟩
  refine bind_preserves_to hpq (setupPreInv_registerIdentity r.alice)
    (fun _ => bind_preserves_to hpq (setupPreInv_registerIdentity r.bob)
    (fun hB => bind_preserves_to hpq (setupPreInv_genSignedPrekey r.bob hB)
    (fun _ => bind_preserves_to hpq (setupPreInv_genPQPrekey r.bob hB)
    (fun _ tr htr => ?_)))) DY.Trace.nil setupPreInv_nil
  cases r.withOpk
  · simp only [Bool.false_eq_true, ↓reduceIte, DY.Traceful.run_pure]
    exact hpq tr htr
  · simp only [↓reduceIte]
    rw [run_bind_pure_snd]
    exact genOneTimePrekey_frameInv r.bob htr

/-! ## 4. Network & Alice `.init`/`.send` Preservation of `FrameInv` -/

private theorem frameInv_append_nonPq {E : Type} [ExecTraceTypes.Has E] {L : List DY.Bytes}
    {opkSk₀ : DY.Bytes} {tr : ExecTrace} (h : FrameInv L opkSk₀ tr) (e : E)
    (hnone_ev : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHEntry) = none)
    (hnone_st : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQXDHStEntry) = none) :
    FrameInv L opkSk₀ (tr.append e) :=
  ⟨(rpkT_bobDoneBaseKeys_append_other tr e hnone_ev).trans h.1,
   onlyOneBobOpk_append_other h.2 e hnone_st⟩

private theorem frameInv_genRand (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (n : Nat) :
    CompTrace.Preserves (FrameInv L opkSk₀) (DY.Random.genRand n) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact frameInv_append_nonPq h (RndE n) rfl rfl

private theorem frameInv_sendMessage (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (msg : DY.Bytes) :
    CompTrace.Preserves (FrameInv L opkSk₀) (DY.Network.sendMessage msg) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact frameInv_append_nonPq h (NetE msg) rfl rfl

private theorem frameInv_logTr (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (ev : TREvent) :
    CompTrace.Preserves (FrameInv L opkSk₀) (DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact frameInv_append_nonPq h (TREvE ev) rfl rfl

private theorem frameInv_logC (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (ev : ComposedEvent) :
    CompTrace.Preserves (FrameInv L opkSk₀) (DY.ProtocolEvent.logEvent ev) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
    DY.Traceful.run_pure]
  exact frameInv_append_nonPq h (CEvE ev) rfl rfl

private theorem frameInv_storeTr (L : List DY.Bytes) (opkSk₀ : DY.Bytes) (me : Participant)
    (st : TRState) :
    CompTrace.Preserves (FrameInv L opkSk₀) (DY.PersistentLocalState.storeLocalState me st) := by
  intro tr h
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
    Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
    Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  exact frameInv_append_nonPq h (TRStE me st) rfl rfl

private theorem frameInv_logMessageKeyAndStore (L : List DY.Bytes) (opkSk₀ : DY.Bytes)
    (me : Participant) (s : SessionInfo) (dir : KeyDir) (seed pqSalt : DY.Bytes)
    (counter : UInt32) (rIdx childStateIdx : Nat) (st : TRState) :
    CompTrace.Preserves (FrameInv L opkSk₀)
      (logMessageKeyAndStore me s dir seed pqSalt counter rIdx childStateIdx st) := by
  unfold logMessageKeyAndStore
  refine CompTrace.Preserves.bind (frameInv_logTr L opkSk₀ _) fun _ => ?_
  exact frameInv_storeTr L opkSk₀ me st

private theorem frameInv_aliceStart (L : List DY.Bytes) (opkSk₀ : DY.Bytes)
    (a b : Participant) (idStateIdx regIdxB : Nat) (bh : BundleHandles) :
    CompTrace.Preserves (FrameInv L opkSk₀) (aliceStart a b idStateIdx regIdxB bh) := by
  intro tr h
  unfold aliceStart
  refine CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr h
    (frameInv_append_nonPq h (RndE 32) rfl rfl) ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h2 : FrameInv L opkSk₀ ((tr.append (RndE 32)).append (RndE 32)) :=
    frameInv_append_nonPq (frameInv_append_nonPq h (RndE 32) rfl rfl) (RndE 32) rfl rfl
  refine (show CompTrace.Preserves (FrameInv L opkSk₀) _ by
    refine CompTrace.Preserves.bind (frameInv_genRand L opkSk₀ 32) fun _ => ?_
    refine CompTrace.Preserves.bind (frameInv_sendMessage L opkSk₀ _) fun _ => ?_
    refine CompTrace.Preserves.bind (frameInv_sendMessage L opkSk₀ _) fun _ => ?_
    refine CompTrace.Preserves.bind CompTrace.Preserves.traceLength fun _ => ?_
    refine CompTrace.Preserves.bind ?_ fun _ => ?_
    · intro t ht
      simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
        Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind, DY.Traceful.run_mk,
        DY.Traceful.run_pure]
      refine ⟨?_, onlyOneBobOpk_append_other ht.2 (PQEvE _) rfl⟩
      rw [rpkT_bobDoneBaseKeys_append_pq, ht.1, List.append_nil]
    · refine CompTrace.Preserves.bind (frameInv_logTr L opkSk₀ _) fun _ => ?_
      refine CompTrace.Preserves.bind (frameInv_logC L opkSk₀ _) fun _ => ?_
      exact frameInv_storeTr L opkSk₀ a _) _ h2

private theorem frameInv_messageEncrypt (L : List DY.Bytes) (opkSk₀ : DY.Bytes)
    (me : Participant) (stH coinsLen pqIdx : Nat) :
    CompTrace.Preserves (FrameInv L opkSk₀) (messageEncrypt me stH coinsLen pqIdx) := by
  unfold messageEncrypt
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.guardP _) fun _ => ?_
  refine CompTrace.Preserves.bind (frameInv_genRand L opkSk₀ 32) fun _ => ?_
  refine CompTrace.Preserves.bind (frameInv_genRand L opkSk₀ coinsLen) fun _ => ?_
  refine CompTrace.Preserves.bind (frameInv_sendMessage L opkSk₀ _) fun _ => ?_
  refine CompTrace.Preserves.bind (CompTrace.Preserves.receiveMessage pqIdx) fun _ => ?_
  refine CompTrace.Preserves.bind (frameInv_logTr L opkSk₀ _) fun _ => ?_
  refine CompTrace.Preserves.bind
    (frameInv_logMessageKeyAndStore L opkSk₀ me _ .sender _ _ _ _ _ _) fun _ => ?_
  exact frameInv_sendMessage L opkSk₀ _

private theorem frameInv_messageEncryptAbort (L : List DY.Bytes) (opkSk₀ : DY.Bytes)
    (me : Participant) (stH : Nat) :
    CompTrace.Preserves (FrameInv L opkSk₀) (messageEncryptAbort me stH) := by
  unfold messageEncryptAbort
  refine CompTrace.Preserves.bind (CompTrace.Preserves.getLocalState_tr me stH) fun _ => ?_
  refine CompTrace.Preserves.bind (frameInv_genRand L opkSk₀ 32) fun _ => ?_
  exact CompTrace.Preserves.failure

private theorem frameInv_runSteps_network {L : List DY.Bytes} {opkSk₀ : DY.Bytes} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      FrameInv L opkSk₀ tr →
      FrameInv L opkSk₀ (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨msg, rfl⟩ := hnet s (List.mem_cons_self ..)
    have hs : FrameInv L opkSk₀ ((Step.network msg).next tr) := by
      rw [next_network]
      exact frameInv_append_nonPq h (NetE msg) rfl rfl
    exact frameInv_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hs

private theorem frameInv_init_or_send_step {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {L : List DY.Bytes} {opkSk₀ : DY.Bytes}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v : List VisEntry}
    (h : FrameInv L opkSk₀ tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hcmd : e.party = "alice" ∧
      ((∃ peer bp, e.cmd = .init peer bp) ∨ (∃ peer, e.cmd = .send peer)))
    (hrm : RunMatches interp r S g (runSteps pre tr) s e v initIds) :
    FrameInv L opkSk₀ (s.next (runSteps pre tr)) ∧ tr ≤ s.next (runSteps pre tr) := by
  set tr₁ := runSteps pre tr
  have h₁ : FrameInv L opkSk₀ tr₁ := frameInv_runSteps_network pre tr hnet h
  have hle : tr ≤ s.next tr₁ := DY.Trace.le_trans _ _ _ (runSteps_le pre tr) (step_le_next s tr₁)
  refine ⟨?_, hle⟩
  have hfits := hrm.2.2.1
  rcases hcmd.2 with ⟨peer, bp, hc⟩ | ⟨peer, hc⟩
  · rw [hc] at hfits
    cases s <;> try exact False.elim hfits
    rename_i a b idIdx regB bh
    rw [show (Step.aliceStart a b idIdx regB bh).next tr₁ =
        ((aliceStart a b idIdx regB bh).run tr₁).2.val from
      stepIn_next aliceStart.reachability (a, b, idIdx, regB, bh) tr₁]
    exact frameInv_aliceStart L opkSk₀ a b idIdx regB bh tr₁ h₁
  · rw [hc] at hfits
    cases s <;> try exact False.elim hfits
    · rename_i me stH cl pq
      rw [show (Step.messageEncrypt me stH cl pq).next tr₁ =
          ((messageEncrypt me stH cl pq).run tr₁).2.val from
        stepIn_next messageEncrypt.reachability (me, stH, cl, pq) tr₁]
      exact frameInv_messageEncrypt L opkSk₀ me stH cl pq tr₁ h₁
    · rename_i me stH
      rw [show (Step.messageEncryptAbort me stH).next tr₁ =
          ((messageEncryptAbort me stH).run tr₁).2.val from
        stepIn_next messageEncryptAbort.reachability (me, stH) tr₁]
      exact frameInv_messageEncryptAbort L opkSk₀ me stH tr₁ h₁

/-! ## 5. Bob PreKey `.recv` Step Unpacking & Single-Use OPK Enforcement -/

private theorem exposures_kind_leak {tr tr' : ExecTrace} {w : VisEntry}
    (hw : w ∈ exposures tr tr') : w.kind = .leak := by
  unfold exposures at hw
  rw [List.mem_append] at hw
  rcases hw with hw | hw
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

private theorem recv_outputs_accept {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {e : RunEvent} {outs : List VisEntry}
    {initIds : Option BundlePreKeyIds}
    (hexit : ∃ out, e.exit = some (0, out))
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (hout : OutputsMatch interp r S g e outs initIds) :
    ∃ w_out, outs = [w_out] ∧ w_out.kind = .accept := by
  obtain ⟨out, he⟩ := hexit
  obtain ⟨peer, hc⟩ := hcmd
  unfold OutputsMatch at hout
  rw [he, hc] at hout
  obtain ⟨w_out, rfl, hbm⟩ := hout
  exact ⟨w_out, rfl, hbm.1.symm⟩

private theorem bobStartTr_le_of_preSkip (tr : ExecTrace) (b a : Participant)
    (o : DY.Libsignal.PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m : DY.Bytes) :
    bobStartPreSkipTr tr b a o msg key ≤ bobStartTr tr b a o msg c' spqr' key seed pqSalt m := by
  unfold bobStartTr
  dsimp only
  exact DY.Trace.le_trans _ _ _ (run_le _ _)
    (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _)))

private theorem opkUsedB_bobStartTr_true (tr : ExecTrace) (b a : Participant)
    (o : DY.Libsignal.PQXDH.BobHandshakeOut) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (c' : DY.Libsignal.TripleRatchet.RecvChain) (spqr' key seed pqSalt m opkPk : DY.Bytes)
    (hopk : o.opk = some opkPk) :
    opkUsedB (bobStartTr tr b a o msg c' spqr' key seed pqSalt m) b opkPk = true := by
  let tr_send := (tr.append (RndE 32)).append (NetE key)
  let tr_opk := tr_send.append (PQEvE (.OPKUsed b opkPk))
  have hopk_here : opkUsedB tr_opk b opkPk = true := by
    unfold opkUsedB
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?, List.any_eq_true]
    have hat : (tr_opk.at? tr_send.length : Option PQXDHEntry) =
        some (PQEvE (.OPKUsed b opkPk)) :=
      DY.Trace.at?_append tr_send (PQEvE (.OPKUsed b opkPk))
    refine ⟨tr_send.length, List.mem_range.mpr ?_, ?_⟩
    · have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQXDHEntry) tr_opk tr_send.length
      rw [hat] at hlt; exact hlt
    · simp [hat]
  have hle_pre : tr_opk ≤ bobStartPreSkipTr tr b a o msg key := by
    unfold bobStartPreSkipTr
    dsimp only
    rw [hopk]
    dsimp only
    exact DY.Trace.le_trans _ _ _ (DY.Trace.append_le tr_opk _)
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
        (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _)))
  exact opkUsedB_mono
    (DY.Trace.le_trans _ _ _ hle_pre (bobStartTr_le_of_preSkip tr b a o msg c' spqr' key seed pqSalt m))
    hopk_here

private theorem bob_recv_preKey_step {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {L : List DY.Bytes} {opkSk₀ : DY.Bytes}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {s : Step} {e : RunEvent}
    {v : List VisEntry} {p : PreKeyFields}
    (hframe : FrameInv L opkSk₀ tr)
    (hbob : e.party = "bob" ∧ (∃ peer, e.cmd = .recv peer) ∧ runWrapped e = true)
    (hp : parsePreKeyWire e.input = some p)
    (hopk_some : p.preKeyId ≠ none)
    (hfresh_bk : ∀ ek ∈ L, ecKey (gamma interp S g ek) ≠ p.baseKey.take 33)
    (hrm : RunMatches interp r S g tr s e v initIds) :
    opkUsedB tr "bob" (DY.DiffieHellman.dhPk opkSk₀) = false ∧
    ∃ ek,
      ecKey (gamma interp S g ek) = p.baseKey.take 33 ∧
      FrameInv (L ++ [ek]) opkSk₀ (s.next tr) ∧
      opkUsedB (s.next tr) "bob" (DY.DiffieHellman.dhPk opkSk₀) = true := by
  obtain ⟨_hcls, hparty, hfits, _hpeer, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, _hdr, hout, _hrf, hpf⟩ := hrm
  obtain ⟨hparty_bob, ⟨peer, hcmd_eq⟩, _hwrap⟩ := hbob
  have hnot_known : ¬ ∃ ek ∈ bobDoneBaseKeys tr, ecKey (gamma interp S g ek) = p.baseKey.take 33 := by
    rintro ⟨ek, hek, heq⟩
    rw [hframe.1] at hek
    exact hfresh_bk ek hek heq
  have hpath := hpf p hp
  rw [hcmd_eq] at hfits
  cases s <;> try exact False.elim hfits
  case messageDecrypt => exact False.elim (hnot_known hpath)
  case messageDecryptSkipped => exact False.elim (hnot_known hpath)
  case bobStart b a kh regA mh pqIdx spqr =>
    rw [hparty_bob] at hparty
    simp only [Step.party?, Option.some.injEq] at hparty
    subst hparty
    obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer, hcmd_eq⟩ hout
    have hnext_mv := step_next_bobStart "bob" a kh regA mh pqIdx spqr tr
    have hview : stepView (.bobStart "bob" a kh regA mh pqIdx spqr) tr (runWrapped e) =
        bobVis tr ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr)
          mh (bobOpkPk "bob" kh tr) ++
        exposures tr ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr) := by
      unfold stepView
      simp only [hok, ↓reduceIte]
      rw [hnext_mv]
    have hpt_some : ∃ pt,
        receivedPlaintext tr ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr) =
          some pt := by
      rcases hpt : receivedPlaintext tr
          ((Move.bobStart "bob" a kh regA mh pqIdx spqr 0).next tr) with _ | pt
      · exfalso
        have hw_mem : w_out ∈ v := by rw [hv_split]; simp
        rw [hvis_eq, hview, List.mem_append] at hw_mem
        rcases hw_mem with hw_bob | hw_exp
        · simp only [bobVis, hpt, Option.map_none, Option.toList_none, List.append_nil,
            List.mem_cons, List.mem_map] at hw_bob
          rcases hw_bob with rfl | ⟨_, _, rfl⟩ <;>
            simp [DY.Libsignal.Composed.Refinement.rngEntry] at hw_accept
        · have := exposures_kind_leak hw_exp
          rw [hw_accept] at this; cases this
      · exact ⟨pt, rfl⟩
    obtain ⟨pt, hpt⟩ := hpt_some
    obtain ⟨w⟩ := rpkT_bobStart_inv hpt
    have htr' : (Step.bobStart "bob" a kh regA mh pqIdx spqr).next tr =
        bobStartTr tr "bob" a w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m :=
      hnext_mv.trans (w.next_eq 0)
    have hrec_terms : received tr [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hinp_eq :
        inp = ⟨.recv, [w.ek, w.ct, w.raw] ++ (w.opk.map DY.DiffieHellman.dhPk).toList,
          .preKeyRecv, none⟩ := by
      have hcons := hv_split.symm.trans (hvis_eq.trans hview)
      unfold bobVis at hcons
      rw [hrec_terms, bobOpkPk_eq tr "bob" kh w.opk w.hopk] at hcons
      exact List.head_eq_of_cons_eq hcons
    have hbm_opk : PreKeyRecvOpkMatches interp r S g e.input
        ([w.ek, w.ct, w.raw] ++ (w.opk.map DY.DiffieHellman.dhPk).toList) := by
      unfold BytesMatchEntry at hbm_in
      rw [hinp_eq] at hbm_in
      exact hbm_in.2
    rcases hw_opk : w.opk with _ | o
    · exfalso
      rw [hw_opk] at hbm_opk
      dsimp only [Option.map, Option.toList, List.append_nil, PreKeyRecvOpkMatches] at hbm_opk
      obtain ⟨p', hp', hp'_none⟩ := hbm_opk.2
      rw [hp] at hp'
      cases hp'
      exact hopk_some hp'_none
    · have ho_eq : o = opkSk₀ := by
        have hopk_st := w.hopk
        rw [hw_opk] at hopk_st
        rcases hkh : kh.opk with _ | idx
        · rw [hkh] at hopk_st; exact False.elim hopk_st
        · rw [hkh] at hopk_st
          exact hframe.2 idx o hopk_st
      subst o
      rw [hw_opk] at hbm_opk
      dsimp only [Option.map, Option.toList, List.cons_append, List.nil_append,
        PreKeyRecvOpkMatches] at hbm_opk
      obtain ⟨p', hp', hbk_eq, _⟩ := hbm_opk.1
      rw [hp] at hp'
      cases hp'
      have hused_false : opkUsedB tr "bob" (DY.DiffieHellman.dhPk opkSk₀) = false := by
        have hsend_false := w.hused opkSk₀ hw_opk
        rcases hu : opkUsedB tr "bob" (DY.DiffieHellman.dhPk opkSk₀) with _ | _
        · rfl
        · exfalso
          have hle_send : tr ≤ (tr.append (RndE 32)).append (NetE w.key) :=
            DY.Trace.le_trans _ _ _ (DY.Trace.append_le tr _) (DY.Trace.append_le _ _)
          have hsend_true := opkUsedB_mono hle_send hu
          rw [hsend_true] at hsend_false
          cases hsend_false
      refine ⟨hused_false, w.ek, hbk_eq.symm, ?_, ?_⟩
      · rw [htr']
        refine ⟨?_, onlyOneBobOpk_bobStartTr hframe.2 "bob" a w.out w.msg w.c'
          w.spqr' w.key w.seed w.pqSalt w.m⟩
        rw [rpkT_bobDoneBaseKeys_bobStartTr, hframe.1]
        rfl
      · rw [htr']
        exact opkUsedB_bobStartTr_true tr "bob" a w.out w.msg w.c' w.spqr'
          w.key w.seed w.pqSalt w.m (DY.DiffieHellman.dhPk opkSk₀)
          (by simp [Symbolic.Swarm.CREF.BobStartOk.out, Symbolic.Swarm.CREF.bobOut, hw_opk])

/-! ## 6. Full 6-Call Disproof (`not_explains_keepOpk_generic`) -/

attribute [local irreducible] Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Parse.ev

theorem not_explains_keepOpk_generic {interp : ExternInterpretation}
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) :
    ¬ Explains interp r S g ss vis cliTrace := by
  intro hex
  have hm0 : MatchesEventsAt interp r S g none (setupTrace r) ss cliTrace vis := hex.2.2.2
  rw [trace_eq_evs] at hm0
  obtain ⟨opkSk₀, hframe0⟩ := setupTrace_frameInv r
  obtain ⟨p₂, p₅, hp₂, hp₅, hp₂_opk, hp₅_opk, hbk_ne⟩ := ev2_ev5_preKey_facts
  -- Call 0 (Alice init)
  obtain ⟨pre0, s0, ss0, v0, vs0, hnet0, hrm0, hm1⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 0 (by decide)) hm0
  obtain ⟨hframe1, _⟩ :=
    frameInv_init_or_send_step hframe0 hnet0 (ev_alice_init_or_send 0 (by decide)) hrm0
  -- Call 1 (Alice send m1)
  obtain ⟨pre1, s1, ss1, v1, vs1, hnet1, hrm1, hm2⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 1 (by decide)) hm1
  obtain ⟨hframe2, _⟩ :=
    frameInv_init_or_send_step hframe1 hnet1 (ev_alice_init_or_send 1 (by decide)) hrm1
  -- Call 2 (Bob recv m1 -> consumes opkSk₀, sets opkUsedB = true)
  obtain ⟨pre2, s2, ss2, v2, vs2, hnet2, hrm2, hm3⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 2 (by decide)) hm2
  have hframe2_pre := frameInv_runSteps_network pre2 _ hnet2 hframe2
  obtain ⟨_, ek₂, hek₂_bytes, hframe3, hopk_used3⟩ :=
    bob_recv_preKey_step hframe2_pre ev2_bob_recv hp₂ hp₂_opk
      (fun _ hmem => nomatch hmem) hrm2
  -- Call 3 (Alice init reusing bundle)
  obtain ⟨pre3, s3, ss3, v3, vs3, hnet3, hrm3, hm4⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 3 (by decide)) hm3
  obtain ⟨hframe4, hle3⟩ :=
    frameInv_init_or_send_step hframe3 hnet3 (ev_alice_init_or_send 3 (by decide)) hrm3
  -- Call 4 (Alice send m2)
  obtain ⟨pre4, s4, ss4, v4, vs4, hnet4, hrm4, hm5⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 4 (by decide)) hm4
  obtain ⟨hframe5, hle4⟩ :=
    frameInv_init_or_send_step hframe4 hnet4 (ev_alice_init_or_send 4 (by decide)) hrm4
  -- Call 5 (Bob recv m2 -> attempts second session start with opkSk₀!)
  obtain ⟨pre5, s5, _ss5, v5, _vs5, hnet5, hrm5, _hm6⟩ :=
    matchesEventsAt_peel_run (ev_not_rejected 5 (by decide)) hm5
  have hframe5_pre := frameInv_runSteps_network pre5 _ hnet5 hframe5
  have hle_to_5 : s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r)))))) ≤
      runSteps pre5 (s4.next (runSteps pre4 (s3.next (runSteps pre3
        (s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r))))))))))) :=
    DY.Trace.le_trans _ _ _ hle3 (DY.Trace.le_trans _ _ _ hle4 (runSteps_le pre5 _))
  have hopk_used5 : opkUsedB _ "bob" (DY.DiffieHellman.dhPk opkSk₀) = true :=
    opkUsedB_mono hle_to_5 hopk_used3
  have hfresh5 : ∀ ek ∈ ([ek₂] : List DY.Bytes),
      ecKey (gamma interp S g ek) ≠ p₅.baseKey.take 33 := by
    intro ek hek
    rcases List.mem_singleton.mp hek with rfl
    rw [hek₂_bytes]
    exact hbk_ne
  obtain ⟨hopk_unused5, _⟩ :=
    bob_recv_preKey_step hframe5_pre ev5_bob_recv hp₅ hp₅_opk hfresh5 hrm5
  rw [hopk_used5] at hopk_unused5
  cases hopk_unused5

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.NoFullExplains.Trace
