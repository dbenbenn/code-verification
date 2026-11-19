/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.TR.Leaks
import Symbolic.Proofs.Swarm.CREF.TR.PQLeak
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.Base
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Generic Leak-Step Inversion & Double-Leak Length Contradiction (`LeakStepAnalysisAux.lean`)

Provides interpretation-parametric trace-splitting, `OnlyAliceIk` preservation across setup and
`.run`-only prefixes, `AliceLeakInv` preservation across `.network` prefixes and `exposeSpqr`,
exhaustive 7-constructor `.env (.leak "alice" k)` step inversion (`alice_leak_forces_spqr`), and
the 2-leak length contradiction (`not_double_alice_leak_of_ne_len`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysisAux

open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHEvent PQXDHState KeyKind)
open DY.Libsignal.TripleRatchet
  (TRState TREvent KeyComponent RecvChain findRecvChain isCurrentSnapshot isSkippedChainCurrent)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost GhostWF GhostAndSemMatchSetup Step VisEntry
   BundlePreKeyIds clamp gamma randTerm setupTrace setupSecret secretBytes
   runSteps runTrace StepsWF ModelRunWF stepView exposures newIndices
   RunMatches RunRejected EnvMatches BytesMatchEntry nextBundleIds MatchesEventsAt Explains)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves PQXDHStEntry TRStEntry TREntry RndE NetE TRStE PQStE CEvE TREvE PQEvE
   at?_append_cases proj_inj_eq run_bind_snd)
open Symbolic.Swarm.CREF.TR
  (Runs AppendsOnlyExposure IsAnyExposureEv exposeKey_next_eq exposeSpqr_next_eq
   exposeSpqr_appendsOnlyExposure getLocalState_fst getLocalState_snd
   getLocalState_fst_of_appendsOnlyExposure isCurrentSnapshot_of_appendsOnlyExposure
   visOf_exposeSpqr visOf_exposeKey_rk visOf_exposeKey_dhs visOf_exposeKey_cks visOf_exposeKey_ckr
   compromise_vis gamma_setupSecret setupSecret_eq setupTrace_eq
   setupTr1 setupTr2 setupTr3 setupTr4 setupTr5)
open Symbolic.Proofs.Swarm.UA.BI.Step (next_network)
open Symbolic.Proofs.Swarm.UA.Base (runSteps_append ghostWF_of_append modelRunWF_of_append)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)

/-! ## 1. `clamp` Length Preservation and `Explains` Prefix Splitting -/

theorem clamp_length (bs : HwBytes) : (clamp bs).length = bs.length := by
  unfold clamp
  split
  · simp
  · rfl

theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

theorem matchesEventsAt_append_split {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ (evs₁ : List CliEvent) {evs₂ : List CliEvent} {initIds : Option BundlePreKeyIds}
      {tr : ExecTrace} {ss : List Step} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss (evs₁ ++ evs₂) vis →
      ∃ ss₁ ss₂ vis₁ vis₂ initIds₁,
        ss = ss₁ ++ ss₂ ∧
        vis = vis₁ ++ vis₂ ∧
        MatchesEventsAt interp r S g initIds tr ss₁ evs₁ vis₁ ∧
        MatchesEventsAt interp r S g initIds₁ (runSteps ss₁ tr) ss₂ evs₂ vis₂
  | [], _, _, _, ss, vis, hm =>
    ⟨[], ss, [], vis, _, rfl, rfl, .nil (fun _ h => nomatch h), hm⟩
  | _ :: tl, _, _, _, _, _, hm => by
    cases hm with
    | @run1 _ _ pre s _ ev _ v _ hinv hrm hrest =>
      obtain ⟨ss₁', ss₂, vis₁', vis₂, initIds₁, rfl, rfl, hm₁, hm₂⟩ :=
        matchesEventsAt_append_split tl hrest
      refine ⟨pre ++ s :: ss₁', ss₂, v ++ vis₁', vis₂, initIds₁,
        by simp, by simp, .run1 hinv hrm hm₁, ?_⟩
      simpa only [runSteps_append, runSteps] using hm₂
    | @run0 _ _ pre _ ev _ _ hinv hrej hrest =>
      obtain ⟨ss₁', ss₂, vis₁', vis₂, initIds₁, rfl, rfl, hm₁, hm₂⟩ :=
        matchesEventsAt_append_split tl hrest
      refine ⟨pre ++ ss₁', ss₂, vis₁', vis₂, initIds₁,
        by simp, rfl, .run0 hinv hrej hm₁, ?_⟩
      simpa only [runSteps_append] using hm₂
    | @env _ _ pre s _ ev _ v _ hinv hem hrest =>
      obtain ⟨ss₁', ss₂, vis₁', vis₂, initIds₁, rfl, rfl, hm₁, hm₂⟩ :=
        matchesEventsAt_append_split tl hrest
      refine ⟨pre ++ s :: ss₁', ss₂, v ++ vis₁', vis₂, initIds₁,
        by simp, by simp, .env hinv hem hm₁, ?_⟩
      simpa only [runSteps_append, runSteps] using hm₂

theorem explains_append_split {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    {evs₁ evs₂ : List CliEvent}
    (hex : Explains interp r S g ss vis (evs₁ ++ evs₂)) :
    ∃ ss₁ ss₂ vis₁ vis₂ initIds₁,
      ss = ss₁ ++ ss₂ ∧
      vis = vis₁ ++ vis₂ ∧
      Explains interp r S g ss₁ vis₁ evs₁ ∧
      StepsWF ss₂ (runTrace r ss₁) ∧
      MatchesEventsAt interp r S g initIds₁ (runTrace r ss₁) ss₂ evs₂ vis₂ := by
  obtain ⟨hgs, hgwf, hmr, hm⟩ := hex
  obtain ⟨ss₁, ss₂, vis₁, vis₂, initIds₁, rfl, rfl, hm₁, hm₂⟩ :=
    matchesEventsAt_append_split evs₁ hm
  exact ⟨ss₁, ss₂, vis₁, vis₂, initIds₁, rfl, rfl,
    ⟨hgs, ghostWF_of_append hgwf, modelRunWF_of_append hmr, hm₁⟩,
    stepsWF_append_right ss₁ hmr.2.2.1, hm₂⟩

/-! ## 2. `OnlyAliceIk` on `setupTrace` and Across Non-Setup / Non-Corrupt Steps -/

/-- Every stored `PQXDHState` entry for `"alice"` on `tr` is her identity secret `sk₀`. -/
def OnlyAliceIk (sk₀ : DY.Bytes) (tr : ExecTrace) : Prop :=
  ∀ idx st, (tr.at? idx : Option PQXDHStEntry) = some ⟨⟨"alice", st⟩⟩ →
    st = { kind := .identity, sk := sk₀ }

theorem onlyAliceIk_nil (sk₀ : DY.Bytes) : OnlyAliceIk sk₀ DY.Trace.nil := by
  intro idx st hat
  simp [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.length_eq_1] at hat

theorem onlyAliceIk_append_other {E : Type} [ExecTraceTypes.Has E] {sk₀ : DY.Bytes} {tr : ExecTrace}
    (h : OnlyAliceIk sk₀ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQXDHStEntry) = none) :
    OnlyAliceIk sk₀ (tr.append e) := by
  intro idx st hat
  rcases at?_append_cases hat with ⟨_, hat₀⟩ | ⟨_, hproj⟩
  · exact h idx st hat₀
  · rw [hnone] at hproj; cases hproj

theorem onlyAliceIk_append_pqSt_alice {sk₀ : DY.Bytes} {tr : ExecTrace}
    (h : OnlyAliceIk sk₀ tr) :
    OnlyAliceIk sk₀ (tr.append (PQStE "alice" { kind := .identity, sk := sk₀ })) := by
  intro idx st hat
  rcases at?_append_cases hat with ⟨_, hat₀⟩ | ⟨_, hproj⟩
  · exact h idx st hat₀
  · simp only [PQStE, proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1
    injection h1 with _ hst
    exact hst.symm

theorem onlyAliceIk_append_pqSt_ne {sk₀ : DY.Bytes} {tr : ExecTrace}
    (h : OnlyAliceIk sk₀ tr) (p : Participant) (hp : p ≠ "alice") (st₀ : PQXDHState) :
    OnlyAliceIk sk₀ (tr.append (PQStE p st₀)) := by
  intro idx st hat
  rcases at?_append_cases hat with ⟨_, hat₀⟩ | ⟨_, hproj⟩
  · exact h idx st hat₀
  · simp only [PQStE, proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1
    injection h1 with hp_eq _
    exact absurd hp_eq hp

theorem onlyAliceIk_setupTrace {r : ProtocolSetup}
    (halice : r.alice = "alice") (hbob : r.bob = "bob") :
    OnlyAliceIk (setupSecret r 0) (setupTrace r) := by
  have hne : r.alice ≠ r.bob := by rw [halice, hbob]; decide
  rw [(setupSecret_eq r hne).1, setupTrace_eq r hne, halice, hbob]
  have h1 : OnlyAliceIk (randTerm 0 32) (setupTr1 "alice") := by
    unfold setupTr1
    apply onlyAliceIk_append_pqSt_alice
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    exact onlyAliceIk_nil _
  have h2 : OnlyAliceIk (randTerm 0 32) (setupTr2 "alice" "bob") := by
    unfold setupTr2
    apply onlyAliceIk_append_pqSt_ne _ "bob" (by decide)
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    exact h1
  have h3 : OnlyAliceIk (randTerm 0 32) (setupTr3 "alice" "bob") := by
    unfold setupTr3
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_pqSt_ne _ "bob" (by decide)
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    exact h2
  have h4 : OnlyAliceIk (randTerm 0 32) (setupTr4 "alice" "bob") := by
    unfold setupTr4
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_pqSt_ne _ "bob" (by decide)
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    exact h3
  split
  · unfold setupTr5
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_pqSt_ne _ "bob" (by decide)
    apply onlyAliceIk_append_other _ _ rfl
    apply onlyAliceIk_append_other _ _ rfl
    exact h4
  · exact h4

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem preserves_genRand_ik {sk₀ : DY.Bytes} (n : Nat) :
    Preserves (OnlyAliceIk sk₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ onlyAliceIk_append_other hInv (RndE n) rfl

private theorem preserves_sendMessage_ik {sk₀ : DY.Bytes} (m : DY.Bytes) :
    Preserves (OnlyAliceIk sk₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ onlyAliceIk_append_other hInv (NetE m) rfl

private theorem preserves_storeLocalState_tr_ik {sk₀ : DY.Bytes} (p : Participant) (st : TRState) :
    Preserves (OnlyAliceIk sk₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by
    rw [storeLocalState_tr_snd_eq]
    exact onlyAliceIk_append_other hInv (TRStE p st) rfl

private theorem preserves_logEventPQ_ik {sk₀ : DY.Bytes} (ev : PQXDHEvent) :
    Preserves (OnlyAliceIk sk₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Runs.logEvent tr ev).2.symm ▸ onlyAliceIk_append_other hInv (PQEvE ev) rfl

private theorem preserves_logEventC_ik {sk₀ : DY.Bytes} (ev : ComposedEvent) :
    Preserves (OnlyAliceIk sk₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact onlyAliceIk_append_other hInv (CEvE ev) rfl

private theorem preserves_logEventTR_ik {sk₀ : DY.Bytes} (ev : TREvent) :
    Preserves (OnlyAliceIk sk₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact onlyAliceIk_append_other hInv (TREvE ev) rfl

private theorem preserves_getKey_ik {sk₀ : DY.Bytes} (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_lookupIdentity_ik {sk₀ : DY.Bytes} (p : Participant) (h : Nat) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logMessageKeyAndStore_ik {sk₀ : DY.Bytes}
    (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (OnlyAliceIk sk₀)
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_logEventTR_ik _) fun _ => preserves_storeLocalState_tr_ik me st

private theorem preserves_dhRatchetStep_ik {sk₀ : DY.Bytes} (st : TRState) (pk : DY.Bytes) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  unfold DY.Libsignal.TripleRatchet.dhRatchetStep
  rcases DY.Libsignal.TripleRatchet.recvHalfStep st.toDRState pk with _ | ⟨_, _⟩
  · exact Preserves.failure
  · exact Preserves.bind (preserves_genRand_ik 32) fun _ => Preserves.pure _

private theorem preserves_ensureReceiverChain_ik {sk₀ : DY.Bytes} (st : TRState) (pk : DY.Bytes) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  unfold DY.Libsignal.TripleRatchet.ensureReceiverChain; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_dhRatchetStep_ik st pk) fun _ => Preserves.pure _

private theorem preserves_logSkippedKeys_ik {sk₀ : DY.Bytes}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (OnlyAliceIk sk₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_logEventTR_ik _) fun _ => ih _ _

local macro "onlyIk_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_genRand_ik
  | with_reducible apply preserves_storeLocalState_tr_ik
  | with_reducible apply preserves_sendMessage_ik
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_getKey_ik | with_reducible apply preserves_lookupIdentity_ik
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep_ik
  | with_reducible apply preserves_ensureReceiverChain_ik
  | with_reducible apply preserves_logSkippedKeys_ik | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_logMessageKeyAndStore_ik
  | with_reducible apply preserves_logEventPQ_ik | with_reducible apply preserves_logEventC_ik
  | with_reducible apply preserves_logEventTR_ik | split | with_reducible intro))

private theorem preserves_decryptInMemory_ik {sk₀ : DY.Bytes}
    (st0 : TRState) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves (OnlyAliceIk sk₀)
      (DY.Libsignal.TripleRatchet.decryptInMemory st0 msg pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.decryptInMemory; onlyIk_tac

private theorem preserves_logRatchet_ik {sk₀ : DY.Bytes}
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) (me : Participant) :
    Preserves (OnlyAliceIk sk₀) (p.logRatchet me) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.logRatchet; onlyIk_tac

private theorem preserves_commit_ik {sk₀ : DY.Bytes}
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) (me : Participant)
    (par : Option Nat := none) :
    Preserves (OnlyAliceIk sk₀) (p.commit me par) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.commit
  cases par <;> (dsimp only; onlyIk_tac)

private theorem preserves_aliceHandshake_ik {sk₀ : DY.Bytes} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; onlyIk_tac

private theorem preserves_bobHandshake_ik {sk₀ : DY.Bytes} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (OnlyAliceIk sk₀) (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; onlyIk_tac

theorem onlyAliceIk_step_invisible_or_party {sk₀ : DY.Bytes} {s : Step} {tr : ExecTrace}
    (hcls : s.cls = .invisible ∨ s.cls = .party) (h : OnlyAliceIk sk₀ tr) :
    OnlyAliceIk sk₀ (s.next tr) := by
  cases s with
  | network msg =>
    rw [next_network]
    exact onlyAliceIk_append_other h (NetE msg) rfl
  | aliceStart a b idStateIdx regIdxB bh =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.Composed.aliceStart a b idStateIdx regIdxB bh) := by
      unfold DY.Libsignal.Composed.aliceStart
      exact Preserves.bind (preserves_aliceHandshake_ik a b idStateIdx regIdxB bh)
        fun _ => by onlyIk_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.Composed.bobStart b a kh regIdxA mh pqIdx spqr) := by
      unfold DY.Libsignal.Composed.bobStart
      refine Preserves.bind (preserves_bobHandshake_ik b a kh regIdxA mh.ek mh.ct) fun o => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
      refine Preserves.bind (preserves_decryptInMemory_ik _ msg pqIdx spqr) fun pending => ?_
      cases o.opk with
      | none =>
        dsimp only
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_logEventPQ_ik _) fun _ => ?_
        refine Preserves.bind (preserves_logRatchet_ik pending b) fun _ => ?_
        refine Preserves.bind (preserves_logEventC_ik _) fun _ => ?_
        exact preserves_commit_ik pending b
      | some _ =>
        dsimp only
        refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
        refine Preserves.bind (preserves_logEventPQ_ik _) fun _ => ?_
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_logEventPQ_ik _) fun _ => ?_
        refine Preserves.bind (preserves_logRatchet_ik pending b) fun _ => ?_
        refine Preserves.bind (preserves_logEventC_ik _) fun _ => ?_
        exact preserves_commit_ik pending b
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | messageEncrypt me stH cl pq =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; onlyIk_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | messageEncryptAbort me stH =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stH) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; onlyIk_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | messageDecrypt me stH mH pq spqr =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.TripleRatchet.messageDecrypt me stH mH pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecrypt
      refine Preserves.bind (Preserves.getLocalState_tr me stH) fun st => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mH) fun msg => ?_
      refine Preserves.bind (preserves_decryptInMemory_ik st msg pq spqr) fun pending => ?_
      refine Preserves.bind (preserves_logRatchet_ik pending me) fun _ => ?_
      exact preserves_commit_ik pending me (some stH)
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | messageDecryptSkipped me stH mH sk pq spqr =>
    have hact : Preserves (OnlyAliceIk sk₀)
        (DY.Libsignal.TripleRatchet.messageDecryptSkipped me stH mH sk pq spqr) := by
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped; onlyIk_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr h
  | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _ | genPQPrekey _ _
  | genOneTimePrekey _ | exposeKey _ _ _ | exposeSpqr _ _ | exposeSkipped _
  | compromiseIK _ _ | compromiseSPK _ _ | compromisePQSPK _ _ | compromiseOPK _ _
  | breakDH | breakKEM | invertDH _ | invertKEM _ =>
    rcases hcls with h1 | h1 <;> cases h1

theorem onlyAliceIk_runSteps_invisible {sk₀ : DY.Bytes} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, x.cls = .invisible) →
      OnlyAliceIk sk₀ tr → OnlyAliceIk sk₀ (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, _, hinv, h =>
    onlyAliceIk_runSteps_invisible pre
      (fun x hx => hinv x (List.mem_cons_of_mem _ hx))
      (onlyAliceIk_step_invisible_or_party (.inl (hinv s List.mem_cons_self)) h)

theorem onlyAliceIk_of_runOnly_matchesEventsAt {interp : ExternInterpretation}
    {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost} {sk₀ : DY.Bytes} :
    ∀ {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
      {evs : List CliEvent} {vis : List VisEntry},
      MatchesEventsAt interp r S g initIds tr ss evs vis →
      (∀ e ∈ evs, ∃ rev, e = .run rev) →
      OnlyAliceIk sk₀ tr →
      OnlyAliceIk sk₀ (runSteps ss tr)
  | _, _, _, _, _, .nil hinv, _, h => onlyAliceIk_runSteps_invisible _ hinv h
  | _, _, _, _, _, .run1 hinv hrm hrest, hrun, h => by
    rw [runSteps_append, runSteps]
    have hpre := onlyAliceIk_runSteps_invisible _ hinv h
    have hs := onlyAliceIk_step_invisible_or_party (.inr hrm.1) hpre
    exact onlyAliceIk_of_runOnly_matchesEventsAt hrest
      (fun e he => hrun e (List.mem_cons_of_mem _ he)) hs
  | _, _, _, _, _, .run0 hinv _ hrest, hrun, h => by
    rw [runSteps_append]
    exact onlyAliceIk_of_runOnly_matchesEventsAt hrest
      (fun e he => hrun e (List.mem_cons_of_mem _ he))
      (onlyAliceIk_runSteps_invisible _ hinv h)
  | _, _, _, _, _, .env (ev := ev) .., hrun, _ => by
    obtain ⟨_, hcontra⟩ := hrun (.env ev) List.mem_cons_self
    cases hcontra

/-! ## 3. `AliceLeakInv` and Preservation Across `.network` and `exposeSpqr` -/

/-- Post-Call-4 trace invariant for Alice's leak analysis. -/
structure AliceLeakInv (r : ProtocolSetup) (stA : TRState) (tr : ExecTrace) : Prop where
  onlyIk : OnlyAliceIk (setupSecret r 0) tr
  noSkipped : ∀ idx s pk n seed rIdx src,
    tr.getEventAt TREvent idx ≠ some (.SkippedKeyStored s pk n seed rIdx src)
  uniqueCurr : ∀ idx st,
    ((DY.PersistentLocalState.getLocalState "alice" idx : Traceful TRState).run tr).1 = some st →
    isCurrentSnapshot tr idx = true → st = stA

private theorem noSkipped_of_appendsOnlyExposure {t t' : ExecTrace}
    (hexp : AppendsOnlyExposure t t')
    (hno : ∀ idx s pk n seed rIdx src,
      t.getEventAt TREvent idx ≠ some (.SkippedKeyStored s pk n seed rIdx src)) :
    ∀ idx s pk n seed rIdx src,
      t'.getEventAt TREvent idx ≠ some (.SkippedKeyStored s pk n seed rIdx src) := by
  intro idx s pk n seed rIdx src hev
  rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hev
  rcases hat' : (t'.at? idx : Option TREntry) with _ | ⟨⟨ev⟩⟩
  · rw [hat'] at hev; cases hev
  · rw [hat'] at hev
    injection hev with hev_eq
    subst hev_eq
    by_cases hi : idx < t.length
    · have hi' : idx < t'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le t t' hexp.1)
      have hat₀ : (t.at? idx : Option TREntry) =
          some ⟨.SkippedKeyStored s pk n seed rIdx src⟩ := by
        simp only [DY.Trace.at?, hi, hi', ↓reduceDIte] at hat' ⊢
        rwa [DY.Trace.at_le t t' idx hi hexp.1]
      refine hno idx s pk n seed rIdx src ?_
      rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat₀]
    · by_cases hi' : idx < t'.length
      · simp only [DY.Trace.at?, hi', ↓reduceDIte] at hat'
        exact (hexp.2 idx hi' (Nat.le_of_not_lt hi)).2 _ hat'
      · simp [DY.Trace.at?, hi'] at hat'

private theorem appendsOnlyExposure_append_net (t : ExecTrace) (msg : DY.Bytes) :
    AppendsOnlyExposure t (t.append (NetE msg)) := by
  refine ⟨DY.Trace.append_le t (NetE msg), fun i h hi => ?_⟩
  have hlen : (t.append (NetE msg)).length = t.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have heq : i = t.length := by omega
  subst heq
  have hat : (t.append (NetE msg)).at t.length h = DY.TraceEntryHas.inj (NetE msg) := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.at_eq_2]
  rw [hat]
  exact ⟨rfl, fun _ he => by cases he⟩

theorem aliceLeakInv_of_appendsOnlyExposure {r : ProtocolSetup} {stA : TRState} {t t' : ExecTrace}
    (hik : OnlyAliceIk (setupSecret r 0) t')
    (hexp : AppendsOnlyExposure t t')
    (hinv : AliceLeakInv r stA t) :
    AliceLeakInv r stA t' where
  onlyIk := hik
  noSkipped := noSkipped_of_appendsOnlyExposure hexp hinv.noSkipped
  uniqueCurr idx st hget hcur := by
    rw [getLocalState_fst_of_appendsOnlyExposure hexp] at hget
    rw [isCurrentSnapshot_of_appendsOnlyExposure hexp] at hcur
    exact hinv.uniqueCurr idx st hget hcur

theorem aliceLeakInv_runSteps_invisible {r : ProtocolSetup} {stA : TRState} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, x.cls = .invisible) →
      AliceLeakInv r stA tr → AliceLeakInv r stA (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hpre, h => by
    have hcls := hpre s List.mem_cons_self
    cases s <;> simp only [Step.cls, reduceCtorEq] at hcls
    rename_i msg
    have hstep : AliceLeakInv r stA ((Step.network msg).next tr) := by
      rw [next_network]
      exact aliceLeakInv_of_appendsOnlyExposure
        (onlyAliceIk_append_other h.onlyIk (NetE msg) rfl)
        (appendsOnlyExposure_append_net tr msg) h
    exact aliceLeakInv_runSteps_invisible pre
      (fun x hx => hpre x (List.mem_cons_of_mem _ hx)) hstep

theorem step_next_exposeSpqr (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.exposeSpqr me stateIdx).next tr =
      ((DY.Libsignal.TripleRatchet.exposeSpqr me stateIdx).run tr).2.val :=
  stepIn_next DY.Libsignal.TripleRatchet.exposeSpqr.reachability (me, stateIdx) tr

theorem step_next_exposeKey (me : Participant) (stateIdx : Nat) (kc : KeyComponent)
    (tr : ExecTrace) :
    (Step.exposeKey me stateIdx kc).next tr =
      ((DY.Libsignal.TripleRatchet.exposeKey me stateIdx kc).run tr).2.val :=
  stepIn_next DY.Libsignal.TripleRatchet.exposeKey.reachability (me, stateIdx, kc) tr

theorem aliceLeakInv_exposeSpqr {r : ProtocolSetup} {stA : TRState} {stateIdx : Nat}
    {tr : ExecTrace} (hinv : AliceLeakInv r stA tr) :
    AliceLeakInv r stA ((Step.exposeSpqr "alice" stateIdx).next tr) := by
  rw [step_next_exposeSpqr]
  have hik : OnlyAliceIk (setupSecret r 0)
      ((DY.Libsignal.TripleRatchet.exposeSpqr "alice" stateIdx).run tr).2.val := by
    have hact : Preserves (OnlyAliceIk (setupSecret r 0))
        (DY.Libsignal.TripleRatchet.exposeSpqr "alice" stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.exposeSpqr; onlyIk_tac
    exact hact tr hinv.onlyIk
  exact aliceLeakInv_of_appendsOnlyExposure hik
    (exposeSpqr_appendsOnlyExposure "alice" stateIdx tr) hinv

/-! ## 4. Exhaustive 7-Constructor `.env (.leak "alice" k)` Step Inversion -/

private theorem exposures_refl (tr : ExecTrace) : exposures tr tr = [] := by
  simp [exposures, newIndices]

private theorem stepView_leak_eq_exposures {s : Step} (hleak : s.IsLeak) (tr : ExecTrace) :
    stepView s tr false = exposures tr (s.next tr) := by
  cases s <;> cases hleak <;> (unfold stepView; dsimp only; split <;> rfl)

private theorem getKey_alice_snd {tr : ExecTrace}
    (stateIdx : Nat) (kind : KeyKind) :
    ((DY.Libsignal.PQXDH.getKey "alice" stateIdx kind).run tr).2.val = tr := by
  have hact : Preserves (fun t => t = tr) (DY.Libsignal.PQXDH.getKey "alice" stateIdx kind) :=
    Preserves.bind (Preserves.getLocalState_pq "alice" stateIdx) fun _ =>
      Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  exact hact tr rfl

private theorem getKey_alice_nonIdentity_none {sk₀ : DY.Bytes} {tr : ExecTrace}
    (hik : OnlyAliceIk sk₀ tr) (stateIdx : Nat) {kind : KeyKind} (hne : kind ≠ .identity) :
    ((DY.Libsignal.PQXDH.getKey "alice" stateIdx kind).run tr).1 = none := by
  unfold DY.Libsignal.PQXDH.getKey
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
    Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_fst,
    Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_snd]
  rcases hat : (tr.at? stateIdx : Option PQXDHStEntry) with _ | ⟨⟨p, st⟩⟩
  · rfl
  · dsimp only
    by_cases hp : p = "alice"
    · subst hp
      simp only [↓reduceIte]
      have hst := hik stateIdx st hat
      subst hst
      unfold _root_.guard
      rw [ite_eq_right_iff.mpr fun h => absurd h.symm hne]
      simp [DY.Traceful.run_bind, DY.Traceful.run_failure]
    · simp [hp]

/-- Every `.env (.leak "alice" k)` step from `AliceLeakInv r stA tr` whose leaked bytes `k`
match neither `secretBytes r 0` nor any DR key of `stA` (raw or `clamp`ed) is forced to be
`Step.exposeSpqr "alice" stateIdx`, pinning `k = γ stA.spqr ∨ k = clamp (γ stA.spqr)` and
preserving `AliceLeakInv r stA` onto the successor trace. -/
theorem alice_leak_forces_spqr {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {stA : TRState}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {k : HwBytes} {evs : List CliEvent} {vis : List VisEntry}
    (hinv : AliceLeakInv r stA tr)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt interp r S g initIds tr ss (.env (.leak "alice" k) :: evs) vis)
    (hgs : GhostAndSemMatchSetup interp r S g)
    (halice : r.alice = "alice") (hbob : r.bob = "bob")
    (hIk : k ≠ secretBytes r 0)
    (hRk : k ≠ gamma interp S g stA.rk ∧ k ≠ clamp (gamma interp S g stA.rk))
    (hDhs : k ≠ gamma interp S g stA.dhs ∧ k ≠ clamp (gamma interp S g stA.dhs))
    (hCks : k ≠ gamma interp S g stA.cks ∧ k ≠ clamp (gamma interp S g stA.cks))
    (hCkr : ∀ c ∈ stA.recv,
      k ≠ gamma interp S g c.chainKey ∧ k ≠ clamp (gamma interp S g c.chainKey)) :
    (k = gamma interp S g stA.spqr ∨ k = clamp (gamma interp S g stA.spqr)) ∧
    ∃ tr' ss' vs',
      AliceLeakInv r stA tr' ∧
      StepsWF ss' tr' ∧
      MatchesEventsAt interp r S g initIds tr' ss' evs vs' := by
  have hne_ab : r.alice ≠ r.bob := by rw [halice, hbob]; decide
  cases hm with
  | @env _ _ pre s ss' _ _ v vs' hpre_inv hem hrest =>
    have hwf5 := stepsWF_append_right pre hwf
    obtain ⟨_, hloc, hwf_after⟩ := hwf5
    set tr₅ := runSteps pre tr
    have hinv5 : AliceLeakInv r stA tr₅ := aliceLeakInv_runSteps_invisible pre hpre_inv hinv
    obtain ⟨_, hleak, hparty, hvis_eq, w, hw_single, hbm⟩ := hem
    rw [stepView_leak_eq_exposures hleak tr₅] at hvis_eq
    have hexp_eq : exposures tr₅ (s.next tr₅) = [w] := hvis_eq.symm.trans hw_single
    cases s with
    | compromiseIK p stateIdx =>
      have hp : p = "alice" := hparty p rfl
      subst hp
      have hnext_eq : (Step.compromiseIK "alice" stateIdx).next tr₅ =
          ((DY.Libsignal.PQXDH.compromiseIK "alice" stateIdx).run tr₅).2.val :=
        stepIn_next DY.Libsignal.PQXDH.compromiseIK.reachability ("alice", stateIdx) tr₅
      rcases hat : (tr₅.at? stateIdx : Option PQXDHStEntry) with _ | ⟨⟨p', st⟩⟩
      · have hnone : ((DY.Libsignal.PQXDH.getKey "alice" stateIdx .identity).run tr₅).1 = none := by
          unfold DY.Libsignal.PQXDH.getKey
          rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
            Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_fst, hat]
        have htr_eq : (Step.compromiseIK "alice" stateIdx).next tr₅ = tr₅ := by
          rw [hnext_eq]; unfold DY.Libsignal.PQXDH.compromiseIK
          rw [run_bind_snd, hnone, getKey_alice_snd]
        rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
      · by_cases hp' : p' = "alice"
        · subst hp'
          have hst := hinv5.onlyIk stateIdx st hat
          subst hst
          have hmove_next : (DY.Libsignal.Composed.Refinement.Move.compromiseIK "alice" stateIdx).next tr₅ =
              (Step.compromiseIK "alice" stateIdx).next tr₅ := by
            rw [hnext_eq]
            dsimp only [DY.Libsignal.Composed.Refinement.Move.next,
              DY.Libsignal.Composed.Refinement.Move.act]
            exact Symbolic.Proofs.Swarm.UA.XlateSteps.run_bind_pure_snd _ tr₅
          have hvis_c := compromise_vis
            (m := .compromiseIK "alice" stateIdx) (pq := false) rfl hat rfl
          unfold DY.Libsignal.Composed.Refinement.Move.vis at hvis_c
          dsimp only [List.nil_append] at hvis_c
          rw [hmove_next, hexp_eq] at hvis_c
          have hw_eq := List.singleton_inj.mp hvis_c.symm
          subst hw_eq
          unfold BytesMatchEntry at hbm
          dsimp only [List.map] at hbm
          have hk_eq : gamma interp S g (setupSecret r 0) = k := List.singleton_inj.mp hbm.2
          rw [(gamma_setupSecret interp r S g hgs hne_ab).1] at hk_eq
          exact absurd hk_eq.symm hIk
        · have hnone : ((DY.Libsignal.PQXDH.getKey "alice" stateIdx .identity).run tr₅).1 = none := by
            unfold DY.Libsignal.PQXDH.getKey
            rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst,
              Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_pq_fst, hat]
            simp [hp']
          have htr_eq : (Step.compromiseIK "alice" stateIdx).next tr₅ = tr₅ := by
            rw [hnext_eq]; unfold DY.Libsignal.PQXDH.compromiseIK
            rw [run_bind_snd, hnone, getKey_alice_snd]
          rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
    | compromiseSPK b stateIdx =>
      have hb : b = "alice" := hparty b rfl
      subst hb
      have hnone := getKey_alice_nonIdentity_none hinv5.onlyIk stateIdx (kind := .signedPrekey) (by decide)
      have hnext_eq : (Step.compromiseSPK "alice" stateIdx).next tr₅ =
          ((DY.Libsignal.PQXDH.compromiseSPK "alice" stateIdx).run tr₅).2.val :=
        stepIn_next DY.Libsignal.PQXDH.compromiseSPK.reachability ("alice", stateIdx) tr₅
      have htr_eq : (Step.compromiseSPK "alice" stateIdx).next tr₅ = tr₅ := by
        rw [hnext_eq]; unfold DY.Libsignal.PQXDH.compromiseSPK
        rw [run_bind_snd, hnone, getKey_alice_snd]
      rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
    | compromisePQSPK b stateIdx =>
      have hb : b = "alice" := hparty b rfl
      subst hb
      have hnone := getKey_alice_nonIdentity_none hinv5.onlyIk stateIdx (kind := .pqPrekey) (by decide)
      have hnext_eq : (Step.compromisePQSPK "alice" stateIdx).next tr₅ =
          ((DY.Libsignal.PQXDH.compromisePQSPK "alice" stateIdx).run tr₅).2.val :=
        stepIn_next DY.Libsignal.PQXDH.compromisePQSPK.reachability ("alice", stateIdx) tr₅
      have htr_eq : (Step.compromisePQSPK "alice" stateIdx).next tr₅ = tr₅ := by
        rw [hnext_eq]; unfold DY.Libsignal.PQXDH.compromisePQSPK
        rw [run_bind_snd, hnone, getKey_alice_snd]
      rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
    | compromiseOPK b stateIdx =>
      have hb : b = "alice" := hparty b rfl
      subst hb
      have hnone := getKey_alice_nonIdentity_none hinv5.onlyIk stateIdx (kind := .oneTimePrekey) (by decide)
      have hnext_eq : (Step.compromiseOPK "alice" stateIdx).next tr₅ =
          ((DY.Libsignal.PQXDH.compromiseOPK "alice" stateIdx).run tr₅).2.val :=
        stepIn_next DY.Libsignal.PQXDH.compromiseOPK.reachability ("alice", stateIdx) tr₅
      have htr_eq : (Step.compromiseOPK "alice" stateIdx).next tr₅ = tr₅ := by
        rw [hnext_eq]; unfold DY.Libsignal.PQXDH.compromiseOPK
        rw [run_bind_snd, hnone, getKey_alice_snd]
      rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
    | exposeSkipped skIdx =>
      dsimp only [Step.LocalOk] at hloc
      unfold isSkippedChainCurrent at hloc
      rcases hev : tr₅.getEventAt TREvent skIdx with _ | ev
      · rw [hev] at hloc; cases hloc
      · rw [hev] at hloc
        cases ev with
        | SkippedKeyStored s pk n seed rIdx src =>
          exact absurd hev (hinv5.noSkipped skIdx s pk n seed rIdx src)
        | _ => cases hloc
    | exposeKey me stateIdx kc =>
      have hme : me = "alice" := hparty me rfl
      subst hme
      dsimp only [Step.LocalOk] at hloc
      rcases hget : ((DY.PersistentLocalState.getLocalState "alice" stateIdx :
          Traceful TRState).run tr₅).1 with _ | st
      · have htr_eq : (Step.exposeKey "alice" stateIdx kc).next tr₅ = tr₅ := by
          rw [step_next_exposeKey]; unfold DY.Libsignal.TripleRatchet.exposeKey
          rw [run_bind_snd, hget, getLocalState_snd]
        rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
      · have hst_eq := hinv5.uniqueCurr stateIdx st hget hloc
        subst st
        have hmove_eq : exposures tr₅ ((Step.exposeKey "alice" stateIdx kc).next tr₅) =
            DY.Libsignal.Composed.Refinement.Move.vis (.exposeKey "alice" stateIdx kc) tr₅ := by
          unfold DY.Libsignal.Composed.Refinement.Move.vis
          rw [List.nil_append, exposeKey_next_eq, step_next_exposeKey]
        cases kc with
        | rk =>
          rw [hmove_eq, visOf_exposeKey_rk hget] at hexp_eq
          have hw_eq := List.singleton_inj.mp hexp_eq.symm
          subst hw_eq
          obtain ⟨_, ⟨t, ht_eq, hkb⟩⟩ := hbm
          cases List.singleton_inj.mp ht_eq.symm
          exact absurd hkb (by rintro (h | h); exact hRk.1 h; exact hRk.2 h)
        | dhs =>
          rw [hmove_eq, visOf_exposeKey_dhs hget] at hexp_eq
          have hw_eq := List.singleton_inj.mp hexp_eq.symm
          subst hw_eq
          obtain ⟨_, ⟨t, ht_eq, hkb⟩⟩ := hbm
          cases List.singleton_inj.mp ht_eq.symm
          exact absurd hkb (by rintro (h | h); exact hDhs.1 h; exact hDhs.2 h)
        | cks =>
          rw [hmove_eq, visOf_exposeKey_cks hget] at hexp_eq
          have hw_eq := List.singleton_inj.mp hexp_eq.symm
          subst hw_eq
          obtain ⟨_, ⟨t, ht_eq, hkb⟩⟩ := hbm
          cases List.singleton_inj.mp ht_eq.symm
          exact absurd hkb (by rintro (h | h); exact hCks.1 h; exact hCks.2 h)
        | ckr pk =>
          rcases hf : findRecvChain stA.recv pk with _ | c
          · have htr_eq : (Step.exposeKey "alice" stateIdx (.ckr pk)).next tr₅ = tr₅ := by
              rw [step_next_exposeKey]; unfold DY.Libsignal.TripleRatchet.exposeKey
              rw [run_bind_snd, hget, getLocalState_snd]
              simp [hf, DY.Traceful.run_failure]
            rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
          · have hc_mem : c ∈ stA.recv := List.mem_of_find?_eq_some hf
            rw [hmove_eq, visOf_exposeKey_ckr hget hf] at hexp_eq
            have hw_eq := List.singleton_inj.mp hexp_eq.symm
            subst hw_eq
            obtain ⟨_, ⟨t, ht_eq, hkb⟩⟩ := hbm
            cases List.singleton_inj.mp ht_eq.symm
            exact absurd hkb (by
              rintro (h | h)
              · exact (hCkr c hc_mem).1 h
              · exact (hCkr c hc_mem).2 h)
    | exposeSpqr me stateIdx =>
      have hme : me = "alice" := hparty me rfl
      subst hme
      dsimp only [Step.LocalOk] at hloc
      rcases hget : ((DY.PersistentLocalState.getLocalState "alice" stateIdx :
          Traceful TRState).run tr₅).1 with _ | st
      · have htr_eq : (Step.exposeSpqr "alice" stateIdx).next tr₅ = tr₅ := by
          rw [step_next_exposeSpqr]; unfold DY.Libsignal.TripleRatchet.exposeSpqr
          rw [run_bind_snd, hget, getLocalState_snd]
        rw [htr_eq, exposures_refl] at hexp_eq; cases hexp_eq
      · have hst_eq := hinv5.uniqueCurr stateIdx st hget hloc
        subst st
        have hmove_eq : exposures tr₅ ((Step.exposeSpqr "alice" stateIdx).next tr₅) =
            DY.Libsignal.Composed.Refinement.Move.vis (.exposeSpqr "alice" stateIdx) tr₅ := by
          unfold DY.Libsignal.Composed.Refinement.Move.vis
          rw [List.nil_append, exposeSpqr_next_eq, step_next_exposeSpqr]
        rw [hmove_eq, visOf_exposeSpqr hget] at hexp_eq
        have hw_eq := List.singleton_inj.mp hexp_eq.symm
        subst hw_eq
        obtain ⟨_, ⟨t, ht_eq, hkb⟩⟩ := hbm
        cases List.singleton_inj.mp ht_eq.symm
        exact ⟨hkb, _, ss', vs', aliceLeakInv_exposeSpqr hinv5, hwf_after, hrest⟩
    | network _ | registerIdentity _ | registerCorruptIdentity _ _ | genSignedPrekey _ _
    | genPQPrekey _ _ | genOneTimePrekey _ | aliceStart _ _ _ _ _ | bobStart _ _ _ _ _ _ _
    | messageEncrypt _ _ _ _ | messageEncryptAbort _ _ | messageDecrypt _ _ _ _ _
    | messageDecryptSkipped _ _ _ _ _ _ | breakDH | breakKEM | invertDH _ | invertKEM _ =>
      cases hleak

/-! ## 5. Double-Leak Length Contradiction (`not_double_alice_leak_of_ne_len`) -/

private theorem ne_and_ne_clamp_of_len {k y : HwBytes}
    (hk : k.length ≠ 32) (hy : y.length = 32) :
    k ≠ y ∧ k ≠ clamp y :=
  ⟨fun h => hk (h ▸ hy), fun h => hk ((congrArg List.length h).trans ((clamp_length y).trans hy))⟩

/-- Refutes any model explanation of two consecutive `.env (.leak "alice" k₁)` and
`.env (.leak "alice" k₂)` events from `AliceLeakInv r stA tr` when `k₁` (`32` bytes) differs from
Alice's `ikA` and `stA`'s `32`-byte DR keys, while `k₂` has length `≠ 32`. -/
theorem not_double_alice_leak_of_ne_len {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {stA : TRState}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {k₁ k₂ : HwBytes} {evs : List CliEvent} {vis : List VisEntry}
    (hinv : AliceLeakInv r stA tr)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt interp r S g initIds tr ss
      (.env (.leak "alice" k₁) :: .env (.leak "alice" k₂) :: evs) vis)
    (hgs : GhostAndSemMatchSetup interp r S g)
    (halice : r.alice = "alice") (hbob : r.bob = "bob")
    (hIk_len : (secretBytes r 0).length = 32)
    (hRk_len : (gamma interp S g stA.rk).length = 32)
    (hDhs_len : (gamma interp S g stA.dhs).length = 32)
    (hCks_len : (gamma interp S g stA.cks).length = 32)
    (hCkr_len : ∀ c ∈ stA.recv, (gamma interp S g c.chainKey).length = 32)
    (hk1_len : k₁.length = 32)
    (hk2_len : k₂.length ≠ 32)
    (hIk1 : k₁ ≠ secretBytes r 0)
    (hRk1 : k₁ ≠ gamma interp S g stA.rk ∧ k₁ ≠ clamp (gamma interp S g stA.rk))
    (hDhs1 : k₁ ≠ gamma interp S g stA.dhs ∧ k₁ ≠ clamp (gamma interp S g stA.dhs))
    (hCks1 : k₁ ≠ gamma interp S g stA.cks ∧ k₁ ≠ clamp (gamma interp S g stA.cks))
    (hCkr1 : ∀ c ∈ stA.recv,
      k₁ ≠ gamma interp S g c.chainKey ∧ k₁ ≠ clamp (gamma interp S g c.chainKey)) :
    False := by
  obtain ⟨hk1_spqr, tr', ss', vs', hinv', hwf', hm'⟩ :=
    alice_leak_forces_spqr hinv hwf hm hgs halice hbob hIk1 hRk1 hDhs1 hCks1 hCkr1
  obtain ⟨hk2_spqr, _⟩ :=
    alice_leak_forces_spqr hinv' hwf' hm' hgs halice hbob
      (fun h => hk2_len (h ▸ hIk_len))
      (ne_and_ne_clamp_of_len hk2_len hRk_len)
      (ne_and_ne_clamp_of_len hk2_len hDhs_len)
      (ne_and_ne_clamp_of_len hk2_len hCks_len)
      (fun c hc => ne_and_ne_clamp_of_len hk2_len (hCkr_len c hc))
  have hspqr_len : (gamma interp S g stA.spqr).length = 32 := by
    rcases hk1_spqr with h | h
    · exact h ▸ hk1_len
    · rw [← clamp_length, ← h, hk1_len]
  have hk2_eq32 : k₂.length = 32 := by
    rcases hk2_spqr with h | h
    · rw [h, hspqr_len]
    · rw [h, clamp_length, hspqr_len]
  exact hk2_len hk2_eq32

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysisAux
