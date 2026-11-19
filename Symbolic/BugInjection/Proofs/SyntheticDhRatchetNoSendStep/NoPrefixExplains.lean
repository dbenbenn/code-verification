/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
import Symbolic.Proofs.Swarm.CREF.SendWire.PendingPureA
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Send-Path Prefix Refutation for `DhRatchetNoSendStepCli` (`NoPrefixExplains.lean`)

Proves `not_explains_prefix4`: for every `S : OpaqueSymbolSemantics`, `g : Ghost`, `ss`, `vis`,
and suffix `tail`, `[.run dhEv0, .run dhEv1, .run dhEv2, .run dhEv3] ++ tail` has no `Explains`
witness under `dhRatchetI0` when `r.alice = "alice"`:
1. Calls 0 (`alice init`) and 1 (`alice send`) preserve `NoBobState` from `setupTrace r`.
2. At Call 2 (`dhEv2`, `bob recv`), `NoBobState` rules out `messageDecrypt` and
   `messageDecryptSkipped`, forcing `Step.bobStart "bob" "alice" ...`. `DrawsMatch` on Bob's
   32-byte ratchet coin draw pins `γ st.dhs = dhCoins2` (index `5`, public key
   `compPubOfIdx ⟨5, by decide⟩`) on the unique `"bob"` state stored on the trace.
3. Invisible `.network` steps before Call 3 (`dhEv3`, `bob send`) preserve `BobDhsInv`, so the
   `messageEncrypt "bob"` step at `dhEv3` emits a `SignalMessage` whose `sender_ratchet_key`
   bytes `(out.drop 5).take 32` equal `compPubOfIdx ⟨5, by decide⟩` (for **all** `S`),
   contradicting `dhOut3`'s recorded unratcheted SPK (`compPubOfIdx ⟨3, by decide⟩`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains

open scoped DY.Libsignal.Composed
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Refinement
  (WireFields FieldItem paddedVarint encodeField knownValue? canonicalVariation)
open DY.Libsignal.TripleRatchet
  (TRState TREvent kdfCk trMsgKeys computeMac trHonestWireMsg
   messageEncrypt messageDecrypt messageDecryptSkipped logMessageKeyAndStore u32Max)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds Move
   gamma clamp randTerm rngEntry received receivedPlaintext newRandoms
   bobOpkPk bobVis encDraws encSendEntry pqExposureAt trExposureAt exposures
   lastSent pendingPreKey stepView trItemEncode honestTrItems trFields trWireBytes
   setupTrace runSteps StepsWF RunMatches RunRejected DrawsMatch OutputsMatch BytesMatchEntry
   GhostWF nextBundleIds MatchesEventsAt Explains runWrapped stepIn)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compPubOfIdx compLookupPub)
open Symbolic.BugInjection.Proofs.Common443.CompRGamma (gamma_dhPk)
open Symbolic.Swarm.COMPOSED.CompTrace
  (Preserves TRStEntry RndE NetE TRStE PQStE CEvE TREvE PQEvE
   run_bind_fst run_bind_snd receiveMessage_snd at?_le_some)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState bks_lt_length_of_at?
   rpkT_bobStart_inv rpkR_finalSt rpkR_bobStartTr_last rpkBH_trStateStoredAt_bobStartTr
   rpkT_receiveMessage_fst rpkT_getMessageSentAt_of_at? bobRatchetedSt bobRatchetedChain)
open Symbolic.Swarm.CREF.CliPure (newRandoms_bobStartTr receivedPlaintext_bobStartTr)
open Symbolic.Swarm.CREF.CliPure.SndPure (gamma_trHonestWireMsg_addr)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (traceStatesP_setupTrace traceStatesP_at?_st)
open Symbolic.Swarm.CREF.TR.RecvDec (getLocalState_snd)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (gamma_randTerm_eq stepIn_next run_bind_pure_snd)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0 (dhRatchetI0)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.I0Laws (dhRatchetI0_publicKey)

/-! ## 1. `MatchesEventsAt` Peeling & `DrawsMatch` Single-Draw Pinning -/

private theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

private theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

private theorem matchesEventsAt_run_peel {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis visAll : List VisEntry}
    (hnotRej : ¬ RunRejected ev)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt dhRatchetI0 r S g initIds tr ss (.run ev :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ pre s ss' v vs,
      (∀ x ∈ pre, ∃ msg, x = .network msg) ∧
      StepsWF ss' (s.next (runSteps pre tr)) ∧
      RunMatches dhRatchetI0 r S g (runSteps pre tr) s ev v initIds ∧
      (∀ w ∈ v, w ∈ visAll) ∧
      (∀ w ∈ vs, w ∈ visAll) ∧
      MatchesEventsAt dhRatchetI0 r S g (nextBundleIds initIds ev)
        (s.next (runSteps pre tr)) ss' evs vs := by
  cases hm with
  | run0 _ hrej _ => exact False.elim (hnotRej hrej)
  | run1 hinv hrm hrest =>
    obtain ⟨_, _, hwf_tail⟩ := stepsWF_append_right _ hwf
    refine ⟨_, _, _, _, _, fun x hx => step_invisible_eq_network (hinv x hx),
      hwf_tail, hrm,
      fun w hw => hsub w (List.mem_append_left _ hw),
      fun w hw => hsub w (List.mem_append_right _ hw), hrest⟩

private theorem drawsMatch_single_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll rest : List VisEntry} {ts : Nat} {coins : HwBytes}
    (hgwf : GhostWF g visAll)
    (hmem : rngEntry (randTerm ts 32) ∈ visAll)
    (hdr : DrawsMatch dhRatchetI0 r S g (rngEntry (randTerm ts 32) :: rest) coins) :
    gamma dhRatchetI0 S g (randTerm ts 32) = coins.take 32 := by
  obtain ⟨pieces, _hne, hpref, hfa⟩ := hdr
  obtain ⟨p, ps, hbm, _, rfl⟩ := List.forall₂_cons_right_iff.mp hfa
  unfold BytesMatchEntry rngEntry at hbm
  dsimp only [List.map] at hbm
  have hp_eq : gamma dhRatchetI0 S g (randTerm ts 32) = p := List.singleton_inj.mp hbm.2
  have hlen_sig : (g.σ ts 32).length = 32 :=
    hgwf.1 _ hmem rfl ts 32 (by decide) (by simp [rngEntry])
  have hp_len : p.length = 32 := by
    rw [← hp_eq, gamma_randTerm_eq _ _ _ _ _ (by decide)]
    exact hlen_sig
  obtain ⟨tail, hcoins⟩ := hpref
  change p ++ ps.flatten ++ tail = coins at hcoins
  rw [hp_eq, ← hcoins, List.append_assoc, ← hp_len, List.take_left]

/-! ## 2. `NoBobState` & `NoNewBobState` Across Setup, Network, and Alice Steps -/

def NoBobState (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) ≠ some ⟨⟨"bob", st⟩⟩

theorem noBobState_setupTrace (r : ProtocolSetup) : NoBobState (setupTrace r) := by
  intro i st hat
  exact traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r) hat

def NoNewBobState (tr₀ tr : ExecTrace) : Prop :=
  tr₀ ≤ tr ∧ ∀ j st, tr₀.length ≤ j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"bob", st⟩⟩

private theorem noNewBobState_refl (tr : ExecTrace) : NoNewBobState tr tr := by
  refine ⟨DY.Trace.le_refl tr, fun j st hj hat => ?_⟩
  exact absurd (bks_lt_length_of_at? hat) (by omega)

private theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

private theorem noNewBobState_trans {tr₀ tr₁ tr₂ : ExecTrace}
    (h01 : NoNewBobState tr₀ tr₁) (h12 : NoNewBobState tr₁ tr₂) :
    NoNewBobState tr₀ tr₂ := by
  refine ⟨DY.Trace.le_trans _ _ _ h01.1 h12.1, fun j st hj hat => ?_⟩
  by_cases hlt : j < tr₁.length
  · rw [at?_of_le_lt h12.1 hlt] at hat
    exact h01.2 j st hj hat
  · exact h12.2 j st (Nat.le_of_not_lt hlt) hat

private theorem noNewBobState_append_other {E : Type} [ExecTraceTypes.Has E] {tr₀ tr : ExecTrace}
    (h : NoNewBobState tr₀ tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    NoNewBobState tr₀ (tr.append e) := by
  refine noNewBobState_trans h ⟨DY.Trace.append_le tr e, fun j st hj hat => ?_⟩
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨hlt, _⟩ | ⟨_, hproj⟩
  · omega
  · rw [hnone] at hproj; cases hproj

private theorem noNewBobState_append_trSt_ne {tr₀ tr : ExecTrace} (h : NoNewBobState tr₀ tr)
    (p : Participant) (hp : p ≠ "bob") (st₀ : TRState) :
    NoNewBobState tr₀ (tr.append (TRStE p st₀)) := by
  refine noNewBobState_trans h ⟨DY.Trace.append_le tr _, fun j st hj hat => ?_⟩
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨hlt, _⟩ | ⟨rfl, hproj⟩
  · omega
  · simp only [TRStE, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq, Option.some.injEq] at hproj
    injection hproj with h1
    injection h1 with hp_eq _
    exact hp hp_eq

private theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

private theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem preserves_genRand {tr₀ : ExecTrace} (n : Nat) :
    Preserves (NoNewBobState tr₀) (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr hInv => (Runs.genRand tr n).2.symm ▸ noNewBobState_append_other hInv (RndE n) rfl

private theorem preserves_sendMessage {tr₀ : ExecTrace} (m : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Network.sendMessage m) :=
  fun tr hInv => (Runs.sendMessage tr m).2.symm ▸ noNewBobState_append_other hInv (NetE m) rfl

private theorem preserves_storeLocalState_tr {tr₀ : ExecTrace} (p : Participant) (hp : p ≠ "bob")
    (st : TRState) :
    Preserves (NoNewBobState tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => by
    rw [storeLocalState_tr_snd_eq]
    exact noNewBobState_append_trSt_ne hInv p hp st

private theorem preserves_storeLocalState_pq {tr₀ : ExecTrace}
    (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) :
    Preserves (NoNewBobState tr₀) (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr hInv => (Runs.storeLocalState tr p st).2.symm ▸
    noNewBobState_append_other hInv (PQStE p st) rfl

private theorem preserves_logEventPQ {tr₀ : ExecTrace} (ev : DY.Libsignal.PQXDH.PQXDHEvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => (Runs.logEvent tr ev).2.symm ▸
    noNewBobState_append_other hInv (PQEvE ev) rfl

private theorem preserves_logEventC {tr₀ : ExecTrace} (ev : ComposedEvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewBobState_append_other hInv (CEvE ev) rfl

private theorem preserves_logEventTR {tr₀ : ExecTrace} (ev : TREvent) :
    Preserves (NoNewBobState tr₀) (DY.ProtocolEvent.logEvent ev) :=
  fun tr hInv => by rw [logEvent_snd_eq]; exact noNewBobState_append_other hInv (TREvE ev) rfl

private theorem preserves_getKey {tr₀ : ExecTrace}
    (p : Participant) (h : Nat) (kind : DY.Libsignal.PQXDH.KeyKind) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_lookupIdentity {tr₀ : ExecTrace} (p : Participant) (h : Nat) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logMessageKeyAndStore {tr₀ : ExecTrace}
    (me : Participant) (hme : me ≠ "bob") (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : DY.Bytes) (n : UInt32)
    (r par : Nat) (st : TRState) :
    Preserves (NoNewBobState tr₀) (logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_logEventTR _) fun _ => preserves_storeLocalState_tr me hme st

private theorem preserves_dhRatchetStep {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]
  exact Preserves.bind (Preserves.guardP _) fun _ =>
    Preserves.bind (preserves_genRand 32) fun _ => Preserves.pure _

private theorem preserves_ensureReceiverChain {tr₀ : ExecTrace} (st : TRState) (pk : DY.Bytes) :
    Preserves (NoNewBobState tr₀) (DY.Libsignal.TripleRatchet.ensureReceiverChain st pk) := by
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]
  split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_dhRatchetStep st pk) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_logSkippedKeys {tr₀ : ExecTrace}
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : DY.Bytes)
    (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_logEventTR _) fun _ => ih _ _

local macro "noBobSt_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_genRand
  | with_reducible apply preserves_storeLocalState_tr _ (by decide)
  | with_reducible apply preserves_storeLocalState_pq | with_reducible apply preserves_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_getKey | with_reducible apply preserves_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt | with_reducible apply preserves_dhRatchetStep
  | with_reducible apply preserves_ensureReceiverChain
  | with_reducible apply preserves_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_logMessageKeyAndStore _ (by decide)
  | with_reducible apply preserves_logEventPQ | with_reducible apply preserves_logEventC
  | with_reducible apply preserves_logEventTR | split | with_reducible intro))

private theorem preserves_aliceHandshake_noNewBobSt {tr₀ : ExecTrace} (a b : Participant)
    (idStateIdx regIdxB : Nat) (h : DY.Libsignal.PQXDH.BundleHandles) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.PQXDH.aliceHandshake a b idStateIdx regIdxB h) := by
  unfold DY.Libsignal.PQXDH.aliceHandshake; noBobSt_tac

private theorem preserves_bobHandshake_noNewBobSt {tr₀ : ExecTrace} (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves (NoNewBobState tr₀)
      (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; noBobSt_tac

private theorem noNewBobState_step_network (m : DY.Bytes) (tr : ExecTrace) :
    NoNewBobState tr ((Step.network m).next tr) := by
  rw [next_network]
  exact noNewBobState_append_other (noNewBobState_refl tr) (NetE m) rfl

private theorem noNewBobState_runSteps_network :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      NoNewBobState tr (runSteps pre tr)
  | [], tr, _ => noNewBobState_refl tr
  | s :: pre, tr, hnet => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    exact noNewBobState_trans (noNewBobState_step_network m tr)
      (noNewBobState_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)))

private theorem noNewBobState_step_alice {s : Step} (tr : ExecTrace)
    (hcls : s.cls = .party) (hp : s.party? = some "alice") :
    NoNewBobState tr (s.next tr) := by
  cases s with
  | aliceStart a b idStateIdx regIdxB bh =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.Composed.aliceStart "alice" b idStateIdx regIdxB bh) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
      exact Preserves.bind
        (preserves_aliceHandshake_noNewBobSt "alice" b idStateIdx regIdxB bh)
        fun _ => by noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | bobStart b a kh regIdxA mh pqIdx spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.Composed.bobStart "alice" a kh regIdxA mh pqIdx spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
      exact Preserves.bind
        (preserves_bobHandshake_noNewBobSt "alice" a kh regIdxA mh.ek mh.ct)
        fun _ => by noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageEncrypt me stateIdx cl pq =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr) (messageEncrypt "alice" stateIdx cl pq) := by
      unfold messageEncrypt; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageEncryptAbort me stateIdx =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (DY.Libsignal.TripleRatchet.messageEncryptAbort "alice" stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageDecrypt me stateIdx mIdx pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr) (messageDecrypt "alice" stateIdx mIdx pq spqr) := by
      simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
      noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    simp only [Step.party?, Option.some.injEq] at hp; subst hp
    have hact : Preserves (NoNewBobState tr)
        (messageDecryptSkipped "alice" stateIdx mIdx sk pq spqr) := by
      unfold messageDecryptSkipped; noBobSt_tac
    dsimp only [Step.next, Step.toInput]; erw [stepIn_next]
    exact hact tr (noNewBobState_refl tr)
  | _ => simp [Step.cls] at hcls

private theorem noBobState_of_noNew {tr tr' : ExecTrace}
    (hnew : NoNewBobState tr tr') (h0 : NoBobState tr) : NoBobState tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat
    exact h0 i st hat
  · exact hnew.2 i st (Nat.le_of_not_lt hlt) hat

private theorem alice_step_noBobState {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v : List VisEntry}
    (h0 : NoBobState tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (halice : e.party = "alice")
    (hrm : RunMatches dhRatchetI0 r S g (runSteps pre tr) s e v initIds) :
    NoBobState (s.next (runSteps pre tr)) := by
  have hp : s.party? = some "alice" := hrm.2.1.trans (congrArg some halice)
  exact noBobState_of_noNew
    (noNewBobState_trans (noNewBobState_runSteps_network pre tr hnet)
      (noNewBobState_step_alice (runSteps pre tr) hrm.1 hp))
    h0

/-! ## 3. Call 2 (`bob recv`) `BobDhsInv` & Call 3 (`bob send`) Wire Header Mismatch -/

def BobDhsInv (S : OpaqueSymbolSemantics) (g : Ghost) (coins : HwBytes) (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ →
    gamma dhRatchetI0 S g st.dhs = coins.take 32

private theorem bobDhsInv_of_noNew {S : OpaqueSymbolSemantics} {g : Ghost} {coins : HwBytes}
    {tr tr' : ExecTrace} (hnew : NoNewBobState tr tr')
    (hinv : BobDhsInv S g coins tr) : BobDhsInv S g coins tr' := by
  intro i st hat
  by_cases hlt : i < tr.length
  · rw [at?_of_le_lt hnew.1 hlt] at hat
    exact hinv i st hat
  · exact False.elim (hnew.2 i st (Nat.le_of_not_lt hlt) hat)

private theorem step_next_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.bobStart b a kh regA mh pqIdx spqr).next tr =
      (Move.bobStart b a kh regA mh pqIdx spqr 0).next tr := by
  dsimp only [Move.next, Move.act, Step.next, Step.toInput]
  erw [stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

private theorem step_ok_decrypt (me : Participant) (stateIdx mIdx pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecrypt me stateIdx mIdx pq spqr).ok tr =
      ((messageDecrypt me stateIdx mIdx pq spqr).run tr).1.isSome :=
  stepIn_ok messageDecrypt.reachability (me, stateIdx, mIdx, pq, spqr) tr

private theorem step_ok_decryptSkipped (me : Participant) (stateIdx mIdx sk pq : Nat)
    (spqr : UInt32) (tr : ExecTrace) :
    (Step.messageDecryptSkipped me stateIdx mIdx sk pq spqr).ok tr =
      ((messageDecryptSkipped me stateIdx mIdx sk pq spqr).run tr).1.isSome :=
  stepIn_ok messageDecryptSkipped.reachability (me, stateIdx, mIdx, sk, pq, spqr) tr

private theorem exposures_kind_leak {tr tr' : ExecTrace} {w : VisEntry}
    (hw : w ∈ exposures tr tr') : w.kind = .leak := by
  unfold exposures at hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold pqExposureAt at hj
    rcases h : tr'.getEventAt DY.Libsignal.PQXDH.PQXDHEvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw
    unfold trExposureAt at hj
    rcases h : tr'.getEventAt TREvent j with _ | ev <;> rw [h] at hj
    · cases hj
    · cases ev <;> simp at hj <;> subst hj <;> rfl

private theorem recv_outputs_accept {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {e : RunEvent} {outs : List VisEntry} {initIds : Option BundlePreKeyIds}
    (hexit : ∃ out, e.exit = some (0, out))
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (hout : OutputsMatch dhRatchetI0 r S g e outs initIds) :
    ∃ w_out, outs = [w_out] ∧ w_out.kind = .accept := by
  obtain ⟨out, he⟩ := hexit
  obtain ⟨peer, hc⟩ := hcmd
  unfold OutputsMatch at hout
  rw [he, hc] at hout
  obtain ⟨w_out, rfl, hbm⟩ := hout
  exact ⟨w_out, rfl, hbm.1.symm⟩

private theorem split_vis_recv_rng {inp v₀ v₂ w_out : VisEntry} {drs rest : List VisEntry}
    {ts : Nat}
    (hvis : inp :: (drs ++ [w_out]) = v₀ :: rngEntry (randTerm ts 32) :: v₂ :: rest)
    (hkind : w_out.kind = .accept) :
    inp = v₀ ∧ ∃ drs_rest, drs = rngEntry (randTerm ts 32) :: drs_rest := by
  injection hvis with hinp htail
  refine ⟨hinp, ?_⟩
  cases drs with
  | nil =>
    dsimp only [List.nil_append] at htail
    injection htail with hw _
    rw [hw] at hkind; cases hkind
  | cons d drs_rest =>
    dsimp only [List.cons_append] at htail
    injection htail with hd _
    exact ⟨drs_rest, congrArg (· :: drs_rest) hd⟩

private theorem bob_recv_step_dhsInv {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {pre : List Step} {s : Step}
    {e : RunEvent} {v visAll : List VisEntry}
    (halice_r : r.alice = "alice")
    (hgwf : GhostWF g visAll)
    (hnoBob : NoBobState tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hbob : e.party = "bob")
    (hcmd : ∃ peer, e.cmd = .recv peer)
    (hrm : RunMatches dhRatchetI0 r S g (runSteps pre tr) s e v initIds)
    (hsub : ∀ w ∈ v, w ∈ visAll) :
    BobDhsInv S g e.coins (s.next (runSteps pre tr)) := by
  set tr₂ := runSteps pre tr
  have hnoBob₂ : NoBobState tr₂ :=
    noBobState_of_noNew (noNewBobState_runSteps_network pre tr hnet) hnoBob
  obtain ⟨_hcls, hparty, hfits, hpeer, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, _hbm_in, hdr, hout, _hrf, _hpf⟩ := hrm
  obtain ⟨peer₂, hcmd₂⟩ := hcmd
  rw [hbob] at hparty; rw [hcmd₂] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨peer₂, hcmd₂⟩ hout
  cases s with
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    exfalso
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decrypt] at hok; unfold messageDecrypt at hok; rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₂ stateIdx st (bks_stored_of_getLocalState hst)
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decryptSkipped] at hok; unfold messageDecryptSkipped at hok; rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₂ stateIdx st (bks_stored_of_getLocalState hst)
  | bobStart b a kh regA mh pqIdx spqr =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have ha : a = "alice" := by simpa [Step.MatchesSetupPeer, halice_r] using hpeer
    subst ha
    have hnext_mv := step_next_bobStart "bob" "alice" kh regA mh pqIdx spqr tr₂
    have hview : stepView (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₂ (runWrapped e) =
        bobVis tr₂ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₂)
          mh (bobOpkPk "bob" kh tr₂) ++
        exposures tr₂ ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₂) := by
      unfold stepView; simp only [hok, ↓reduceIte]; rw [hnext_mv]
    have hpt_some : ∃ pt,
        receivedPlaintext tr₂
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₂) = some pt := by
      rcases hpt : receivedPlaintext tr₂
          ((Move.bobStart "bob" "alice" kh regA mh pqIdx spqr 0).next tr₂) with _ | pt
      · exfalso
        have hw_mem : w_out ∈ v := by rw [hv_split]; simp
        rw [hvis_eq, hview, List.mem_append] at hw_mem
        rcases hw_mem with hw_bob | hw_exp
        · simp only [bobVis, hpt, Option.map_none, Option.toList_none, List.append_nil,
            List.mem_cons, List.mem_map] at hw_bob
          rcases hw_bob with rfl | ⟨_, _, rfl⟩ <;> simp [rngEntry] at hw_accept
        · have := exposures_kind_leak hw_exp
          rw [hw_accept] at this; cases this
      · exact ⟨pt, rfl⟩
    obtain ⟨pt, hpt⟩ := hpt_some
    obtain ⟨w⟩ := rpkT_bobStart_inv hpt
    have htr' : (Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂ =
        Symbolic.Swarm.CREF.bobStartTr tr₂ "bob" "alice" w.out w.msg w.c'
          w.spqr' w.key w.seed w.pqSalt w.m :=
      hnext_mv.trans (w.next_eq 0)
    have hrec_terms : received tr₂ [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hvis_full : v =
        ⟨.recv, [w.ek, w.ct, w.raw] ++ (bobOpkPk "bob" kh tr₂).toList, .preKeyRecv, none⟩ ::
        rngEntry (randTerm tr₂.length 32) ::
        ⟨.accept, [w.m], .single,
          DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone tr₂
            (Symbolic.Swarm.CREF.bobStartTr tr₂ "bob" "alice"
              w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m)⟩ ::
        exposures tr₂ (Symbolic.Swarm.CREF.bobStartTr tr₂ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m) := by
      rw [hvis_eq, hview, w.next_eq 0]
      unfold bobVis
      rw [hrec_terms, newRandoms_bobStartTr, receivedPlaintext_bobStartTr]
      rfl
    obtain ⟨_, drs_rest, hdrs_eq⟩ :=
      split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
    have hrng_mem : rngEntry (randTerm tr₂.length 32) ∈ visAll := by
      apply hsub; rw [hv_split, hdrs_eq]; simp
    rw [hdrs_eq] at hdr
    have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
    rw [htr']
    intro i st hat
    rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨_, h0⟩ | ⟨_, _, rfl⟩
    · exact False.elim (hnoBob₂ _ _ h0)
    · unfold rpkR_finalSt bobRatchetedSt
      exact hdhs_bytes
  | _ => cases hfits

private theorem not_send_mem_encDraws {nr : List (DY.Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws nr) (hk : v.kind = .send) : False := by
  unfold encDraws at hv; split at hv
  · cases hv
  · rcases List.mem_cons.mp hv with rfl | hrest
    · cases hk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrest; cases hk

private theorem not_send_mem_exposures {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') (hk : v.kind = .send) : False := by
  have := exposures_kind_leak hv
  rw [hk] at this; cases this

private theorem step_ok_encryptAbort_false (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.messageEncryptAbort me stateIdx).ok tr = false := by
  unfold Step.ok Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, stateIdx) tr]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability,
    DY.Libsignal.TripleRatchet.messageEncryptAbort]
  rw [run_bind_fst]
  rcases ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | _
  · rfl
  · dsimp only; rw [run_bind_fst, (Runs.genRand _ 32).1]; dsimp only
    rw [DY.Traceful.run_failure]; rfl

private theorem messageEncrypt_lastSent {me : Participant} {stateIdx cl pq : Nat} {tr₁ : ExecTrace}
    (hok : (Step.messageEncrypt me stateIdx cl pq).ok tr₁ = true) :
    ∃ st ctTerm pqTerm mac,
      (tr₁.at? stateIdx : Option TRStEntry) = some ⟨⟨me, st⟩⟩ ∧
      lastSent tr₁ ((Step.messageEncrypt me stateIdx cl pq).next tr₁) =
        some (DY.Concat.concat
          (trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn ctTerm pqTerm) mac) := by
  unfold Step.ok Step.toInput at hok
  rw [stepIn_ok messageEncrypt.reachability (me, stateIdx, cl, pq) tr₁] at hok
  have hnext : (Step.messageEncrypt me stateIdx cl pq).next tr₁ = _ :=
    stepIn_next messageEncrypt.reachability (me, stateIdx, cl, pq) tr₁
  dsimp only [messageEncrypt.reachability] at hok hnext
  unfold messageEncrypt at hok hnext
  rw [run_bind_fst] at hok; rw [run_bind_snd] at hnext
  rcases hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr₁).1
    with _ | st
  · rw [hst] at hok; cases hok
  · have hat_st := bks_stored_of_getLocalState hst
    rw [hst, getLocalState_snd] at hok hnext; dsimp only at hok hnext
    have hguard : (_root_.guard (st.ns ≠ u32Max) : Traceful Unit) = pure () := by
      unfold _root_.guard; split
      · rfl
      · next hneg =>
        exfalso; unfold _root_.guard at hok; split at hok
        · next hpos => exact hneg hpos
        · rw [run_bind_fst, DY.Traceful.run_failure] at hok; cases hok
    rw [hguard] at hok hnext
    rw [run_bind_fst, DY.Traceful.run_pure] at hok; dsimp only at hok
    rw [run_bind_snd, DY.Traceful.run_pure] at hnext; dsimp only at hnext
    rw [run_bind_fst, (Runs.genRand tr₁ 32).1, (Runs.genRand tr₁ 32).2] at hok
    rw [run_bind_snd, (Runs.genRand tr₁ 32).1, (Runs.genRand tr₁ 32).2] at hnext
    dsimp only at hok hnext
    let tr_r1 := tr₁.append (RndE 32)
    rw [run_bind_fst, (Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2] at hok
    rw [run_bind_snd, (Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2] at hnext
    dsimp only at hok hnext
    let tr_r2 := tr_r1.append (RndE cl)
    let spqrOut := DY.Spqr.spqrSend st.spqr (randTerm tr_r1.length cl)
    rw [run_bind_fst, (Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Runs.sendMessage tr_r2 spqrOut.2.1).2] at hok
    rw [run_bind_snd, (Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Runs.sendMessage tr_r2 spqrOut.2.1).2] at hnext
    dsimp only at hok hnext
    let tr_k := tr_r2.append (NetE spqrOut.2.1)
    rw [run_bind_fst, rpkT_receiveMessage_fst, receiveMessage_snd] at hok
    rw [run_bind_snd, rpkT_receiveMessage_fst, receiveMessage_snd] at hnext
    rcases hpq : tr_k.getMessageSentAt pq with _ | pqSalt
    · rw [hpq] at hok; cases hok
    · rw [hpq] at hnext; dsimp only at hnext
      let m := randTerm tr₁.length 32
      let seed := (kdfCk st.cks).2
      let keys := trMsgKeys pqSalt seed
      let ctTerm := DY.SymEnc.symEnc keys.cipherKey keys.iv m
      let wire := trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn ctTerm spqrOut.2.2
      let mac := computeMac keys.macKey st.myIk st.peerIk wire
      let evSent := TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m
      have hl1 : ((DY.ProtocolEvent.logEvent evSent).run tr_k).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [run_bind_snd, hl1, logEvent_snd_eq evSent tr_k] at hnext; dsimp only at hnext
      let tr_s := tr_k.append (TREvE evSent)
      rw [run_bind_snd] at hnext; unfold logMessageKeyAndStore at hnext
      let evMk := TREvent.MessageKey (st.sessionInfo me) .sender seed pqSalt st.ns st.rIdx stateIdx
      have hmk1 : ((DY.ProtocolEvent.logEvent evMk).run tr_s).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [run_bind_snd, run_bind_fst, hmk1, logEvent_snd_eq evMk tr_s] at hnext
      dsimp only at hnext
      let tr_mk := tr_s.append (TREvE evMk)
      let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := spqrOut.1 }
      have hst1 : ((DY.PersistentLocalState.storeLocalState me st').run tr_mk).1 =
          some tr_mk.length := by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
      rw [hst1, storeLocalState_tr_snd_eq me st' tr_mk] at hnext; dsimp only at hnext
      let tr_bef := tr_mk.append (TRStE me st')
      let msgTerm := DY.Concat.concat wire mac
      rw [(Runs.sendMessage tr_bef msgTerm).2] at hnext
      refine ⟨st, ctTerm, spqrOut.2.2, mac, hat_st, ?_⟩
      rw [hnext]; unfold lastSent
      have hlen_app : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (x : E),
          (t.append x).length = t.length + 1 := fun _ _ => by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hlt : tr₁.length < (tr_bef.append (NetE msgTerm)).length := by
        dsimp [tr_bef, tr_mk, tr_s, tr_k, tr_r2, tr_r1]
        simp only [hlen_app]; omega
      simp only [hlt, ↓reduceIte]
      have hidx : (tr_bef.append (NetE msgTerm)).length - 1 = tr_bef.length := by
        rw [hlen_app]; omega
      rw [hidx]
      exact rpkT_getMessageSentAt_of_at? (Symbolic.Swarm.CREF.at?_append_length tr_bef (NetE msgTerm))

private theorem whisper_ratchetKey_slice
    (addr rkB ctB pqB macB : HwBytes) (c pc : Nat) (hrk_len : rkB.length = 32) :
    ((wireWhisperTag ::
      (trWireBytes addr canonicalVariation ⟨4, rkB, c, pc, ctB⟩ pqB ++ macB)).drop 5).take 32 =
      rkB := by
  have hp10 : paddedVarint 10 0 = [0x0a#8] := by rw [paddedVarint]; simp
  have hlen33 : (0x05#8 :: rkB).length = 33 := by simp [hrk_len]
  have hp33 : paddedVarint 33 0 = [0x21#8] := by rw [paddedVarint]; simp
  have hf1 : encodeField 1 0 0 (.bytes (0x05#8 :: rkB)) = 0x0a#8 :: 0x21#8 :: 0x05#8 :: rkB := by
    simp only [encodeField, Nat.reduceMul, Nat.reduceAdd, hp10, hlen33, hp33,
      List.cons_append, List.nil_append]
  rw [DY.Libsignal.Composed.Refinement.trWireBytes_canonical]
  simp only [wireWhisperTag, DY.Libsignal.Refinement.encodeWith, canonicalVariation,
    FieldItem.encode, knownValue?, Option.map_some, Option.getD_some, List.append_nil, hf1,
    List.flatMap_cons, List.cons_append, List.drop_succ_cons, List.drop_zero, List.append_assoc]
  exact List.take_left' hrk_len

/-! ## 4. Concrete Events of `DhRatchetNoSendStepCli` & `not_explains_prefix4` -/

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }

def dhEv0 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace with
  | .run e0 :: _ => e0
  | _ => dummyRunEvent

def dhEv1 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace with
  | _ :: .run e1 :: _ => e1
  | _ => dummyRunEvent

def dhEv2 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace with
  | _ :: _ :: .run e2 :: _ => e2
  | _ => dummyRunEvent

def dhEv3 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace with
  | _ :: _ :: _ :: .run e3 :: _ => e3
  | _ => dummyRunEvent

def dhEv4 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.trace with
  | _ :: _ :: _ :: _ :: .run e4 :: _ => e4
  | _ => dummyRunEvent

def dhCoins2 : HwBytes :=
  Symbolic.BugInjection.hexBytes "277e2a7f356d98732990e6c96848114813f782d86b9349fbf714af9e97857fdc"

def dhOut3 : HwBytes :=
  Symbolic.BugInjection.hexBytes "02440a2105b6b88896bce6c272053abf1c7717aca151d472728303ff4cea12496c9fe31418100018002220980ab9bf08c186fb0e3a7ed92b0887c33e423c0532b631994d79e05942b84b502a040101010004dfc7ff1396cd12"

private theorem dhEv0_not_rej : ¬ RunRejected dhEv0 := fun h => h _ rfl
private theorem dhEv1_not_rej : ¬ RunRejected dhEv1 := fun h => h _ rfl
private theorem dhEv2_not_rej : ¬ RunRejected dhEv2 := fun h => h _ rfl
private theorem dhEv3_not_rej : ¬ RunRejected dhEv3 := fun h => h _ rfl

private theorem dhCoins2_pub :
    compLookupPub (clamp (dhCoins2.take 32)) = compPubOfIdx ⟨5, by decide⟩ := by
  decide +kernel

private theorem dhEv3_wrapped : runWrapped dhEv3 = false := by
  have hexit : dhEv3.exit = some (0, dhOut3) := rfl
  unfold runWrapped
  rw [hexit]
  decide +kernel

private theorem dhOut3_rk_ne_pub5 :
    (dhOut3.drop 5).take 32 ≠ compPubOfIdx ⟨5, by decide⟩ := by
  decide +kernel

theorem not_explains_prefix4
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) (tail : List CliEvent)
    (halice_r : r.alice = "alice")
    (hex : Explains dhRatchetI0 r S g ss vis
      (.run dhEv0 :: .run dhEv1 :: .run dhEv2 :: .run dhEv3 :: tail)) :
    False := by
  obtain ⟨_, hgwf, ⟨_, _, hwf_ss, _⟩, hme⟩ := hex
  obtain ⟨pre₀, s₀, ss₁, _, vs₁, hnet₀, hwf₁, hrm₀, _, hvs₁_sub, hme₁⟩ :=
    matchesEventsAt_run_peel dhEv0_not_rej hwf_ss hme (fun _ h => h)
  have hnb₁ : NoBobState (s₀.next (runSteps pre₀ (setupTrace r))) :=
    alice_step_noBobState (noBobState_setupTrace r) hnet₀ rfl hrm₀
  obtain ⟨pre₁, s₁, ss₂, _, vs₂, hnet₁, hwf₂, hrm₁, _, hvs₂_sub, hme₂⟩ :=
    matchesEventsAt_run_peel dhEv1_not_rej hwf₁ hme₁ hvs₁_sub
  have hnb₂ : NoBobState (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))))) :=
    alice_step_noBobState hnb₁ hnet₁ rfl hrm₁
  obtain ⟨pre₂, s₂, ss₃, v₂, vs₃, hnet₂, hwf₃, hrm₂, hv₂_sub, hvs₃_sub, hme₃⟩ :=
    matchesEventsAt_run_peel dhEv2_not_rej hwf₂ hme₂ hvs₂_sub
  have hdhs₃ : BobDhsInv S g dhCoins2
      (s₂.next (runSteps pre₂ (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r))))))) :=
    bob_recv_step_dhsInv halice_r hgwf hnb₂ hnet₂ rfl ⟨_, rfl⟩ hrm₂ hv₂_sub
  obtain ⟨pre₃, s₃, _, v₃, _, hnet₃, _, hrm₃, _, _, _⟩ :=
    matchesEventsAt_run_peel dhEv3_not_rej hwf₃ hme₃ hvs₃_sub
  set tr₃ := runSteps pre₃
    (s₂.next (runSteps pre₂ (s₁.next (runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r)))))))
  have hdhs_tr₃ : BobDhsInv S g dhCoins2 tr₃ :=
    bobDhsInv_of_noNew (noNewBobState_runSteps_network pre₃ _ hnet₃) hdhs₃
  obtain ⟨_, hparty₃, hfits₃, _, hok₃, _, hv₃_eq, _, _, outs₃, hv₃_split,
    _, _, houts₃, _, _⟩ := hrm₃
  have hcmd₃ : dhEv3.cmd = .send ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩ := rfl
  have hexit₃ : dhEv3.exit = some (0, dhOut3) := rfl
  have hp₃ : dhEv3.party = "bob" := rfl
  rw [hp₃] at hparty₃; rw [hcmd₃] at hfits₃
  cases s₃ with
  | messageEncryptAbort me stateIdx =>
    rw [step_ok_encryptAbort_false] at hok₃; cases hok₃
  | messageEncrypt me stateIdx cl pq =>
    simp only [Step.party?, Option.some.injEq] at hparty₃; subst hparty₃
    obtain ⟨st, ctTerm, pqTerm, mac, hat_st, hls⟩ := messageEncrypt_lastSent hok₃
    have hdhs_st : gamma dhRatchetI0 S g st.dhs = dhCoins2.take 32 := hdhs_tr₃ stateIdx st hat_st
    have hdhPk_st : gamma dhRatchetI0 S g (DY.DiffieHellman.dhPk st.dhs) =
        compPubOfIdx ⟨5, by decide⟩ := by
      rw [gamma_dhPk, hdhs_st, dhRatchetI0_publicKey, Option.getD_some]
      exact dhCoins2_pub
    unfold OutputsMatch at houts₃
    rw [hexit₃, hcmd₃] at houts₃
    obtain ⟨v_out, rfl, hbme_out⟩ := houts₃
    have hv_in_v₃ : v_out ∈ v₃ := by
      rw [hv₃_split]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
    rw [hv₃_eq] at hv_in_v₃
    unfold stepView at hv_in_v₃
    simp only [hok₃, ↓reduceIte] at hv_in_v₃
    have hv_in_enc : v_out ∈ encSendEntry tr₃
        ((Step.messageEncrypt "bob" stateIdx cl pq).next tr₃) stateIdx (runWrapped dhEv3) := by
      rcases List.mem_append.mp hv_in_v₃ with hown | hexp
      · rcases List.mem_append.mp hown with hdr | henc
        · exact False.elim (not_send_mem_encDraws hdr hbme_out.1.symm)
        · exact henc
      · exact False.elim (not_send_mem_exposures hexp hbme_out.1.symm)
    rw [dhEv3_wrapped] at hv_in_enc
    unfold encSendEntry at hv_in_enc
    rw [hls] at hv_in_enc
    dsimp only at hv_in_enc
    rcases hppk : pendingPreKey tr₃ stateIdx with _ | ⟨ekT, ctT⟩ <;> rw [hppk] at hv_in_enc
    · rcases List.mem_singleton.mp hv_in_enc with rfl
      unfold BytesMatchEntry at hbme_out
      obtain ⟨_, t, ht_eq, hout_eq⟩ := hbme_out
      rcases List.singleton_inj.mp ht_eq with rfl
      rw [Symbolic.Swarm.CREF.TR.gamma_concat, gamma_trHonestWireMsg_addr, hdhPk_st] at hout_eq
      have hslice := whisper_ratchetKey_slice
        (g.addr (trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn ctTerm pqTerm))
        (compPubOfIdx ⟨5, by decide⟩) (gamma dhRatchetI0 S g ctTerm)
        (gamma dhRatchetI0 S g pqTerm) (gamma dhRatchetI0 S g mac)
        st.ns.toNat st.pn.toNat (by decide)
      rw [← hout_eq] at hslice
      exact dhOut3_rk_ne_pub5 hslice
    · cases hv_in_enc
  | _ => cases hfits₃

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.NoPrefixExplains
