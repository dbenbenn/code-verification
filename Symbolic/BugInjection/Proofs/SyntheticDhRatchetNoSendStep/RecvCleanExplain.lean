/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvPeelPins
public import Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvMemoTermAt
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Random
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Symbolic.BugInjection.Proofs.Common443.CliEventBridge
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Clean 2-Step Prefix & Trial Term Lists for `DhRatchetNoSendStepCli` Call 2 (`RecvCleanExplain.lean`)

1. Clean 2-step prefix `(gClean cl, ssClean2 cl, visClean2 cl)` and `xClean cl : PreKeyRep`,
   together with `gClean_compat`, `m1Clean_ok`, `m1Clean_next`, `vis_m1Clean`,
   `ghostWF_clean2`, and `modelRunWF_clean2`.
2. `not_implicitReject_xClean` and closed-form equations for `storedSecrets`, `storedStates`,
   `honestSaltsOf`, `plaintextTerms`, `sendTerms`, `bobTrials`, and `bobTrialTermsClean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvCleanExplain

unseal DY.Bytes

open scoped DY.Libsignal.Composed
open DY (Traceful ExecTrace)
open DY.Libsignal.TripleRatchet
  (TRState TREvent kdfCk trMsgKeys computeMac
   createChain messageEncrypt logMessageKeyAndStore u32Max consumeMessageKey skippedSeeds spqrA2B)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   PreKeyRep TrialCtx
   randTerm setupTrace setupRandoms setupRandomsAt setupSecret setupPublic secretBytes
   runSteps runTrace newIndices newRandoms lastSent pendingPreKey
   encDraws encSendEntry pqExposureAt trExposureAt exposures stepView honestKeysOf
   storedSecrets storedStates honestSaltsOf plaintextTerms trialTerms bobTrials
   GhostAndSemMatchSetup GhostWF ModelRunWF)
open DY.Libsignal.Composed.Refinement.Cli (serializeAddresses aliceUuid bobUuid)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.BugInjection (cliCompShape fillFresh)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs
  (encPreSaltTr encSalt encWire encMac encOut encSt encNextTr)
open Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner (encParsedMsg)
open Symbolic.Swarm.COMPOSED.CompTrace
  (RndE NetE TRStE TREvE run_bind_fst run_bind_snd receiveMessage_snd)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of m1Of setupTrace_false_eq m0_next_false m1_ok_false m1_next_false
   vis_m0_false vis_m1_false visStep visEncStep
   modelRunWF_msPrefix2)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
  (zeroKey_ne_spqrSendKey symDec_ne_salt)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (bytesTag length_append_entry_eq storeLocalState_tr_snd_eq logEvent_snd_eq
   receiveMessage_fst_eq getLocalState_snd_eq getEventAt_eq_at? getMessageSentAt_eq_at?
   spqrSend_spqrInit_key_eq setupPublic_0_bridge setupPublic_2_bridge)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.DefsI0
  (dhRatchetI0 dhAesPt0 cliCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvDagData
open Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvPeelPins

/-! ## 0. Sealed-Trace `.append` Helpers -/

private theorem at?_append_of_lt {E1 E2 : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append_entry_eq]; omega
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append e) i hi (DY.Trace.append_le tr e)]

private theorem at?_append_self {E1 E2 : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

private theorem range_filterMap_at?_append {E1 E2 α : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [length_append_entry_eq, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

private theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr₀ tr : ExecTrace) (e : E1) (f : Nat → Option E2 → Option α)
    (hle : tr₀.length ≤ tr.length) :
    ((newIndices tr₀ (tr.append e)).filterMap fun i => f i ((tr.append e).at? i)) =
      ((newIndices tr₀ tr).filterMap fun i => f i (tr.at? i)) ++
      (f tr.length (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  unfold newIndices
  rw [length_append_entry_eq, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  have hi' := List.mem_range'_1.mp hi
  rw [at?_append_of_lt tr e (by omega)]

private theorem newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms, newIndices]

private theorem newRandoms_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr₀ tr : ExecTrace) (e : E1) (hle : tr₀.length ≤ tr.length) :
    newRandoms tr₀ (tr.append e) =
      newRandoms tr₀ tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option DY.Random.ExecEntryT)).map fun r => (randTerm tr.length r.length, r.length)).toList := by
  unfold newRandoms
  exact newIndices_filterMap_at?_append (E2 := DY.Random.ExecEntryT) tr₀ tr e
    (fun i (o : Option DY.Random.ExecEntryT) => o.map fun r => (randTerm i r.length, r.length)) hle

private def isPqCompromise : DY.Libsignal.PQXDH.PQXDHEvent → Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => true
  | _ => false

private def optNoPqCompromise
    (o : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) : Bool :=
  match o with
  | some ⟨ev⟩ => !isPqCompromise ev
  | none => true

private theorem pqExposureAt_eq_none_of {tr : ExecTrace} {i : Nat}
    (h : optNoPqCompromise (tr.at? i) = true) :
    pqExposureAt tr i = none := by
  unfold pqExposureAt
  rw [getEventAt_eq_at? DY.Libsignal.PQXDH.PQXDHEvent]
  rcases hat : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)) with _ | ⟨⟨ev⟩⟩
  · rfl
  · rw [hat] at h
    cases ev <;> simp_all [optNoPqCompromise, isPqCompromise]

private def isTrExposure : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr ..
  | .ExposedMK .. | .ExposedSpqr .. => true
  | _ => false

private def optNoTrExposure (o : Option (DY.ProtocolEvent.ExecEntryT TREvent)) : Bool :=
  match o with
  | some ⟨ev⟩ => !isTrExposure ev
  | none => true

private theorem trExposureAt_eq_none_of {tr : ExecTrace} {i : Nat}
    (h : optNoTrExposure (tr.at? i) = true) :
    trExposureAt tr i = none := by
  unfold trExposureAt
  rw [getEventAt_eq_at? TREvent]
  rcases hat : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with _ | ⟨⟨ev⟩⟩
  · rfl
  · rw [hat] at h
    cases ev <;> simp_all [optNoTrExposure, isTrExposure]

private def NoNewExposures (tr₀ tr : ExecTrace) : Prop :=
  ∀ i ∈ newIndices tr₀ tr,
    optNoPqCompromise (tr.at? i) = true ∧ optNoTrExposure (tr.at? i) = true

private theorem noNewExposures_self (tr : ExecTrace) : NoNewExposures tr tr := by
  simp [NoNewExposures, newIndices]

private theorem noNewExposures_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    {tr₀ tr : ExecTrace} {e : E1} (hle : tr₀.length ≤ tr.length)
    (hpq : optNoPqCompromise (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry)) = true)
    (htr : optNoTrExposure (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry)) = true)
    (hprev : NoNewExposures tr₀ tr) :
    NoNewExposures tr₀ (tr.append e) := by
  intro i hi
  unfold newIndices at hi
  rw [length_append_entry_eq, show tr.length + 1 - tr₀.length = (tr.length - tr₀.length) + 1 by omega,
    List.range'_concat, show tr₀.length + 1 * (tr.length - tr₀.length) = tr.length by omega,
    List.mem_append, List.mem_singleton] at hi
  rcases hi with hi | rfl
  · have hi_lt : i < tr.length := by have := List.mem_range'_1.mp hi; omega
    rw [at?_append_of_lt tr e hi_lt, at?_append_of_lt tr e hi_lt]
    exact hprev i hi
  · rw [at?_append_self, at?_append_self]
    exact ⟨hpq, htr⟩

private theorem exposures_eq_nil_of_noNewExposures {tr₀ tr : ExecTrace}
    (h : NoNewExposures tr₀ tr) : exposures tr₀ tr = [] := by
  unfold exposures
  rw [List.append_eq_nil_iff]
  exact ⟨List.filterMap_eq_nil_iff.mpr fun i hi => pqExposureAt_eq_none_of (h i hi).1,
         List.filterMap_eq_nil_iff.mpr fun i hi => trExposureAt_eq_none_of (h i hi).2⟩

private theorem spqrSend_stA0_key_eq (c : DY.Bytes) :
    (DY.Spqr.spqrSend HonestSession.stA0.spqr c).2.1 = HonestSession.key0 :=
  (spqrSend_spqrInit_key_eq HonestSession.keys1.pqr spqrA2B c).trans
    (spqrSend_spqrInit_key_eq HonestSession.keys1.pqr spqrA2B HonestSession.coins0).symm

/-! ## 1. Clean 2-Step Prefix `(gClean cl, ssClean2 cl, visClean2 cl)` & `xClean cl` -/

def m1Clean (cl : Nat) : Step := .messageEncrypt "alice" 30 cl 33

def ssClean2 (cl : Nat) : List Step :=
  [m0Of false, m1Clean cl]

def t6Clean (cl : Nat) : ExecTrace :=
  encNextTr HonestSession.t5 "alice" 30 HonestSession.stA0 cl 33

def gClean (cl : Nat) : Ghost where
  σ t n :=
    if t == 0 && n == 32 then bytesOf ikAId
    else if t == 5 && n == 32 then bytesOf ikBId
    else if t == 10 && n == 32 then bytesOf spkBId
    else if t == 11 && n == 64 then fillFresh 11 64
    else if t == 16 && n == 64 then bytesOf pqskBId
    else if t == 17 && n == 64 then fillFresh 17 64
    else if t == 22 && n == 32 then bytesOf r22Id
    else if t == 23 && n == 32 then bytesOf r23Id
    else if t == 24 && n == 32 then bytesOf dhsAId
    else if t == 31 && n == 32 then dhAesPt0
    else if t == 32 && n == cl && cl != 0 && cl <= 64 then dhEv1CoinsFast.take cl
    else List.replicate n 0#8
  addr _ := serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩

def xClean (cl : Nat) : PreKeyRep :=
  ⟨HonestSession.o1.ek, HonestSession.o1.ct, encOut HonestSession.t5 HonestSession.stA0 cl 33⟩

def visClean2 (cl : Nat) : List VisEntry :=
  stepView (m0Of false) HonestSession.t4 false ++
  stepView (m1Clean cl) HonestSession.t5 true

theorem pqAddrBytes_eq_serialize :
    serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ = pqAddrBytes := by
  decide +kernel

theorem gClean_compat {iw : cliCompShape.Interp} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} (cl : Nat)
    (hfit : cliCompFitsPinned iw r) (hc : GhostAndSemMatchSetup dhRatchetI0 r S g) :
    GhostAndSemMatchSetup dhRatchetI0 r S (gClean cl) := by
  obtain ⟨⟨⟨hwf, hopk, _, _, _, _, hs0, hs1, hs2, _, _, _, _, _, _, _⟩,
    _, ⟨hs3, hs4, hs5⟩, ⟨ha, hb⟩, _, _⟩, _, _⟩ := hfit
  have hs_r0 : setupRandomsAt r = [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
    rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1, hopk]; rfl
  have hfresh : ∀ p ∈ setupRandomsAt r, (gClean cl).σ p.1 p.2 = r.fresh p.1 p.2 := by
    rw [hs_r0]
    unfold secretBytes at hs0 hs1 hs2 hs3 hs4 hs5
    rw [hs_r0] at hs0 hs1 hs2 hs3 hs4 hs5
    dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some, Option.getD_some]
      at hs0 hs1 hs2 hs3 hs4 hs5
    have h0 : bytesOf ikAId = Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.aliceId := by decide +kernel
    have h1 : bytesOf ikBId = Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.bobId := by decide +kernel
    have h2 : bytesOf spkBId = Symbolic.BugInjection.Synthetic.Witnesses.DhRatchetNoSendStepCli.setup.spk := by decide +kernel
    have h4 : bytesOf pqskBId = fillFresh 16 64 := by decide +kernel
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · change bytesOf ikAId = r.fresh 0 32; exact h0.trans hs0.symm
    · change bytesOf ikBId = r.fresh 5 32; exact h1.trans hs1.symm
    · change bytesOf spkBId = r.fresh 10 32; exact h2.trans hs2.symm
    · change fillFresh 11 64 = r.fresh 11 64; exact hs3.symm
    · change bytesOf pqskBId = r.fresh 16 64; exact h4.trans hs4.symm
    · change fillFresh 17 64 = r.fresh 17 64; exact hs5.symm
  have hpub := Symbolic.BugInjection.Proofs.Common443.CliEventBridge.gamma_setupPublic_eq_of_sigma_eq
    dhRatchetI0 r S (gClean cl) g hwf hfresh hc.1
  exact ⟨hfresh, fun k hk => (hpub k hk).trans (hc.2.1 k hk), hc.2.2⟩

theorem m1Clean_ok_and_next (cl : Nat) :
    (m1Clean cl).ok HonestSession.t5 = true ∧
    (m1Clean cl).next HonestSession.t5 = t6Clean cl := by
  unfold m1Clean Step.ok Step.next Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability ("alice", 30, cl, 33) HonestSession.t5,
      stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability ("alice", 30, cl, 33) HonestSession.t5]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability]
  unfold messageEncrypt
  have hget : ((DY.PersistentLocalState.getLocalState "alice" 30 : Traceful TRState).run HonestSession.t5).1 =
      some HonestSession.stA0 := by
    rw [Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_fst, HonestSession.t5_stA0_at]
    simp
  rw [run_bind_fst, run_bind_snd, hget, getLocalState_snd_eq "alice" 30 HonestSession.t5]; dsimp only
  have hns : HonestSession.stA0.ns ≠ u32Max := by decide
  have hguard : (_root_.guard (HonestSession.stA0.ns ≠ u32Max) : Traceful Unit) = pure () := by
    unfold _root_.guard; simp [hns]
  rw [hguard, run_bind_fst, run_bind_snd, DY.Traceful.run_pure]; dsimp only
  rw [run_bind_fst, run_bind_snd, (Runs.genRand HonestSession.t5 32).1, (Runs.genRand HonestSession.t5 32).2]
  dsimp only
  let tr_r1 := HonestSession.t5.append (RndE 32)
  rw [run_bind_fst, run_bind_snd, (Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2]
  dsimp only
  let tr_r2 := tr_r1.append (RndE cl)
  have hlen5 : HonestSession.t5.length = 31 := HonestSession.t5_length
  have hlen_r1 : tr_r1.length = 32 := by
    dsimp [tr_r1]; rw [length_append_entry_eq, hlen5]
  rw [hlen_r1]
  let spqrOut := DY.Spqr.spqrSend HonestSession.stA0.spqr (randTerm 32 cl)
  rw [run_bind_fst, run_bind_snd, (Runs.sendMessage tr_r2 spqrOut.2.1).1,
      (Runs.sendMessage tr_r2 spqrOut.2.1).2]; dsimp only
  let tr_k := tr_r2.append (NetE spqrOut.2.1)
  have hpq : tr_k.getMessageSentAt 33 = some spqrOut.2.1 := by
    have heq : tr_k = Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr
        HonestSession.t5 HonestSession.stA0 cl := by
      unfold Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr
      dsimp only [tr_k, tr_r2, tr_r1, spqrOut]; simp only [hlen5, Nat.reduceAdd]
    rw [heq]
    have hs := Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr_getMessageSentAt_self
      HonestSession.t5 HonestSession.stA0 cl
    simpa only [hlen5, Nat.reduceAdd] using hs
  rw [run_bind_fst, run_bind_snd, receiveMessage_fst_eq 33 tr_k, receiveMessage_snd, hpq]; dsimp only
  let evSent := TREvent.Sent "alice" HonestSession.stA0.peer
    (DY.DiffieHellman.dhPk HonestSession.stA0.dhs) HonestSession.stA0.ns
    (randTerm HonestSession.t5.length 32)
  have hl1 : ((DY.ProtocolEvent.logEvent evSent).run tr_k).1 = some () := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
      DY.Traceful.run_mk, DY.Traceful.run_pure]
  rw [run_bind_fst, run_bind_snd, hl1, logEvent_snd_eq evSent tr_k]; dsimp only
  let tr_s := tr_k.append (TREvE evSent)
  let evMk := TREvent.MessageKey (HonestSession.stA0.sessionInfo "alice") .sender
    (kdfCk HonestSession.stA0.cks).2 spqrOut.2.1 HonestSession.stA0.ns HonestSession.stA0.rIdx 30
  have hmk1 : ((DY.ProtocolEvent.logEvent evMk).run tr_s).1 = some () := by
    simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
      DY.Traceful.run_mk, DY.Traceful.run_pure]
  let tr_mk := tr_s.append (TREvE evMk)
  let st' : TRState := encSt HonestSession.t5 HonestSession.stA0 cl
  have hst'_eq : ({ HonestSession.stA0 with cks := (kdfCk HonestSession.stA0.cks).1, ns := HonestSession.stA0.ns + 1, spqr := spqrOut.1 } : TRState) = st' := by
    dsimp only [st', encSt, spqrOut]; simp only [hlen5, Nat.reduceAdd]
  have hst1 : ((DY.PersistentLocalState.storeLocalState "alice" st').run tr_mk).1 =
      some tr_mk.length := by
    simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
      Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
      Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
  let tr_bef := tr_mk.append (TRStE "alice" st')
  have hlmk_fst : ((logMessageKeyAndStore "alice" (HonestSession.stA0.sessionInfo "alice") .sender
      (kdfCk HonestSession.stA0.cks).2 spqrOut.2.1 HonestSession.stA0.ns HonestSession.stA0.rIdx 30
      { HonestSession.stA0 with cks := (kdfCk HonestSession.stA0.cks).1, ns := HonestSession.stA0.ns + 1, spqr := spqrOut.1 }).run tr_s).1 =
      some tr_mk.length := by
    rw [hst'_eq]; unfold logMessageKeyAndStore
    rw [run_bind_fst, hmk1, logEvent_snd_eq evMk tr_s]; dsimp only
    exact hst1
  have hlmk_snd : ↑((logMessageKeyAndStore "alice" (HonestSession.stA0.sessionInfo "alice") .sender
      (kdfCk HonestSession.stA0.cks).2 spqrOut.2.1 HonestSession.stA0.ns HonestSession.stA0.rIdx 30
      { HonestSession.stA0 with cks := (kdfCk HonestSession.stA0.cks).1, ns := HonestSession.stA0.ns + 1, spqr := spqrOut.1 }).run tr_s).2 =
      tr_bef := by
    rw [hst'_eq]; unfold logMessageKeyAndStore
    rw [run_bind_snd, hmk1, logEvent_snd_eq evMk tr_s]; dsimp only
    exact storeLocalState_tr_snd_eq "alice" st' tr_mk
  rw [run_bind_fst, run_bind_snd, hlmk_fst, hlmk_snd]; dsimp only
  have hsalt_eq : spqrOut.2.1 = encSalt HonestSession.t5 HonestSession.stA0 cl 33 := by
    have hs : encSalt HonestSession.t5 HonestSession.stA0 cl (HonestSession.t5.length + 2) =
        (DY.Spqr.spqrSend HonestSession.stA0.spqr (randTerm (HonestSession.t5.length + 1) cl)).2.1 :=
      Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encSalt_self
        HonestSession.t5 HonestSession.stA0 cl
    simp only [hlen5, Nat.reduceAdd] at hs
    exact hs.symm
  have hout_eq : DY.Concat.concat
      (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk HonestSession.stA0.dhs)
        HonestSession.stA0.ns HonestSession.stA0.pn
        (DY.SymEnc.symEnc (trMsgKeys spqrOut.2.1 (kdfCk HonestSession.stA0.cks).2).cipherKey
          (trMsgKeys spqrOut.2.1 (kdfCk HonestSession.stA0.cks).2).iv
          (randTerm HonestSession.t5.length 32)) spqrOut.2.2)
      (computeMac (trMsgKeys spqrOut.2.1 (kdfCk HonestSession.stA0.cks).2).macKey
        HonestSession.stA0.myIk HonestSession.stA0.peerIk
        (DY.Libsignal.TripleRatchet.trHonestWireMsg (DY.DiffieHellman.dhPk HonestSession.stA0.dhs)
          HonestSession.stA0.ns HonestSession.stA0.pn
          (DY.SymEnc.symEnc (trMsgKeys spqrOut.2.1 (kdfCk HonestSession.stA0.cks).2).cipherKey
            (trMsgKeys spqrOut.2.1 (kdfCk HonestSession.stA0.cks).2).iv
            (randTerm HonestSession.t5.length 32)) spqrOut.2.2)) =
      encOut HonestSession.t5 HonestSession.stA0 cl 33 := by
    unfold encOut encMac encWire; simp only [← hsalt_eq, hlen5, Nat.reduceAdd]; rfl
  rw [hout_eq, (Runs.sendMessage tr_bef (encOut HonestSession.t5 HonestSession.stA0 cl 33)).1,
      (Runs.sendMessage tr_bef (encOut HonestSession.t5 HonestSession.stA0 cl 33)).2]
  refine ⟨rfl, ?_⟩
  unfold t6Clean encNextTr encPreSaltTr
  dsimp only [tr_bef, tr_mk, tr_s, tr_k, tr_r2, tr_r1, evMk, evSent, spqrOut, st']
  simp only [← hsalt_eq, hlen5, Nat.reduceAdd]
  rfl

theorem m1Clean_ok (cl : Nat) : (m1Clean cl).ok HonestSession.t5 = true :=
  (m1Clean_ok_and_next cl).1

theorem m1Clean_next (cl : Nat) : (m1Clean cl).next HonestSession.t5 = t6Clean cl :=
  (m1Clean_ok_and_next cl).2

theorem runTrace_ssClean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl : Nat) :
    runTrace r (ssClean2 cl) = t6Clean cl := by
  unfold runTrace ssClean2
  rw [setupTrace_eq_t4 ha hb hopk]
  dsimp only [runSteps]
  rw [m0_next_false, m1Clean_next]

theorem lastSent_t5_t6Clean (cl : Nat) :
    lastSent HonestSession.t5 (t6Clean cl) = some ((xClean cl).msg) :=
  Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.lastSent_encNextTr
    HonestSession.t5 "alice" 30 HonestSession.stA0 cl 33

private theorem pendingPreKey_t5_eq :
    pendingPreKey HonestSession.t5 30 = some (HonestSession.o1.ek, HonestSession.o1.ct) := by
  have hv32 := vis_m1_false
  have hm1_eq : m1Of false = m1Clean 32 := rfl
  have ht6_eq : HonestSession.t6 = t6Clean 32 :=
    m1_next_false.symm.trans (by rw [hm1_eq]; exact m1Clean_next 32)
  rw [hm1_eq, ht6_eq] at hv32
  unfold stepView visEncStep at hv32
  rw [m1Clean_ok 32] at hv32
  dsimp only [m1Clean, ↓reduceIte] at hv32
  have hv_mid : encDraws (newRandoms HonestSession.t5 ((m1Clean 32).next HonestSession.t5)) ++
      encSendEntry HonestSession.t5 ((m1Clean 32).next HonestSession.t5) 30 true ++
      exposures HonestSession.t5 ((m1Clean 32).next HonestSession.t5) =
      (encDraws (newRandoms HonestSession.t5 (t6Clean 32)) ++
        match lastSent HonestSession.t5 (t6Clean 32) with
        | some w => [⟨.send, [HonestSession.o1.ek, HonestSession.o1.ct, w], .preKeySend, none⟩]
        | none => []) ++
      exposures HonestSession.t5 (t6Clean 32) := hv32
  rw [m1Clean_next 32] at hv_mid
  have h1 := List.append_cancel_left (List.append_cancel_right hv_mid)
  unfold encSendEntry at h1
  rw [lastSent_t5_t6Clean 32] at h1
  dsimp only at h1
  rcases hppk : pendingPreKey HonestSession.t5 30 with _ | ⟨ek, ct⟩ <;> rw [hppk] at h1
  · cases h1
  · simp only [List.cons.injEq, VisEntry.mk.injEq, true_and, and_true] at h1
    rcases h1 with ⟨rfl, rfl⟩
    rfl

theorem vis_m1Clean (cl : Nat) :
    stepView (m1Clean cl) HonestSession.t5 true =
      visEncStep HonestSession.t5 (t6Clean cl) HonestSession.o1.ek HonestSession.o1.ct := by
  unfold stepView visEncStep
  rw [m1Clean_ok cl]
  dsimp only [m1Clean, ↓reduceIte]
  change encDraws (newRandoms HonestSession.t5 ((m1Clean cl).next HonestSession.t5)) ++
      encSendEntry HonestSession.t5 ((m1Clean cl).next HonestSession.t5) 30 true ++
      exposures HonestSession.t5 ((m1Clean cl).next HonestSession.t5) = _
  rw [m1Clean_next cl]
  unfold encSendEntry
  rw [pendingPreKey_t5_eq]
  cases lastSent HonestSession.t5 (t6Clean cl) <;> rfl

theorem exposures_t4_t5 : exposures HonestSession.t4 HonestSession.t5 = [] := by
  apply exposures_eq_nil_of_noNewExposures
  unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  iterate 9 refine noNewExposures_append (by simp -failIfUnchanged only [length_append_entry_eq, HonestSession.t4_length]; omega) rfl rfl ?_
  exact noNewExposures_self HonestSession.t4

theorem newRandoms_t4_t5 :
    newRandoms HonestSession.t4 HonestSession.t5 =
      [(randTerm 22 32, 32), (randTerm 23 32, 32), (randTerm 24 32, 32)] := by
  unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [newRandoms_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, HonestSession.t4_length]; omega)]
  rw [newRandoms_self, HonestSession.t4_length]
  simp only [length_append_entry_eq, HonestSession.t4_length]
  rfl

theorem exposures_t5_t6Clean (cl : Nat) : exposures HonestSession.t5 (t6Clean cl) = [] := by
  apply exposures_eq_nil_of_noNewExposures
  unfold t6Clean encNextTr encPreSaltTr
  dsimp only
  iterate 7 refine noNewExposures_append (by simp -failIfUnchanged only [length_append_entry_eq, HonestSession.t5_length]; omega) rfl rfl ?_
  exact noNewExposures_self HonestSession.t5

theorem newRandoms_t5_t6Clean (cl : Nat) :
    newRandoms HonestSession.t5 (t6Clean cl) = [(randTerm 31 32, 32), (randTerm 32 cl, cl)] := by
  unfold t6Clean encNextTr encPreSaltTr
  dsimp only
  repeat rw [newRandoms_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, HonestSession.t5_length]; omega)]
  rw [newRandoms_self]
  simp only [length_append_entry_eq, HonestSession.t5_length]
  rfl

theorem ghostWF_clean2 {cl : Nat} (hcl : cl ≤ 64) :
    GhostWF (gClean cl) (visClean2 cl) := by
  refine ⟨?_, fun _ => Or.inr rfl, ?_⟩
  · intro v hv hvk ts n _ hmem
    unfold visClean2 at hv
    rcases List.mem_append.mp hv with hv0 | hv1
    · rw [vis_m0_false] at hv0
      unfold visStep at hv0
      rw [exposures_t4_t5, List.append_nil] at hv0
      dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte,
        DY.Libsignal.Composed.Refinement.aliceVis] at hv0
      have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
          [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by
        rw [newRandoms_t4_t5]; rfl
      rw [hnr0] at hv0
      dsimp only [DY.Libsignal.Composed.Refinement.aliceDraws,
        DY.Libsignal.Composed.Refinement.kyberCoinEntries,
        List.drop, List.take, List.cons_append, List.nil_append] at hv0
      simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv0
      rcases hv0 with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩
      · cases hvk
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem
        simp [gClean]; decide +kernel
      · simp only [List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem
        simp [gClean]; decide +kernel
      · simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at hmem
        obtain ⟨rfl, rfl⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem
        simp [gClean]; decide +kernel
    · rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
          exposures_t5_t6Clean, List.append_nil] at hv1
      rcases List.mem_append.mp hv1 with hdr | hsnd
      · unfold encDraws at hdr
        simp only [List.filter_cons, List.filter_nil, List.mem_cons] at hdr
        rcases hdr with rfl | hdr'
        · cases hvk
        · by_cases hcl0 : cl = 0
          · subst hcl0; simp at hdr'
          · simp only [hcl0, bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte,
              List.map_cons, List.map_nil, List.mem_singleton] at hdr'
            subst hdr'
            simp only [DY.Libsignal.Composed.Refinement.rngEntry, List.mem_singleton] at hmem
            obtain ⟨rfl, hn⟩ := Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem
            subst hn
            have hbne : (n != 0) = true := bne_iff_ne.mpr hcl0
            have hble : decide (n ≤ 64) = true := decide_eq_true hcl
            have hg : (gClean n).σ 32 n = dhEv1CoinsFast.take n := by
              unfold gClean
              simp [hbne, hble]
            rw [hg, List.length_take, dhEv1CoinsFast_len, Nat.min_eq_left hcl]
      · simp only [List.mem_singleton] at hsnd; subst hsnd; cases hvk
  · intro v hv hvk
    unfold visClean2 at hv
    have hlay : v.layout = .preKeySend := by
      rcases List.mem_append.mp hv with hv0 | hv1
      · rw [vis_m0_false] at hv0
        unfold visStep at hv0
        rw [exposures_t4_t5, List.append_nil] at hv0
        dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte,
          DY.Libsignal.Composed.Refinement.aliceVis] at hv0
        have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
            [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by
          rw [newRandoms_t4_t5]; rfl
        rw [hnr0] at hv0
        dsimp only [DY.Libsignal.Composed.Refinement.aliceDraws,
          DY.Libsignal.Composed.Refinement.kyberCoinEntries,
          List.drop, List.take, List.cons_append, List.nil_append] at hv0
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv0
        rcases hv0 with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩ <;> cases hvk
      · rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
            exposures_t5_t6Clean, List.append_nil] at hv1
        rcases List.mem_append.mp hv1 with hdr | hsnd
        · unfold encDraws at hdr
          by_cases hcl0 : cl = 0 <;> simp [hcl0, DY.Libsignal.Composed.Refinement.rngEntry] at hdr
          · subst hdr; cases hvk
          · rcases hdr with rfl | rfl <;> cases hvk
        · simp only [List.mem_singleton] at hsnd; subst hsnd; rfl
    exact ⟨fun _ _ _ _ _ _ _ => rfl, fun hwh => by rw [hlay] at hwh; cases hwh⟩

private theorem stepIn_preCond_iff (c : DY.ReachabilityConfig)
    [i : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    reachability.PreCond (DY.Libsignal.Composed.Refinement.stepIn c x) tr ↔ c.PreCond x tr :=
  (i.pf_pre x tr).symm.to_iff

theorem modelRunWF_clean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl : Nat)
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64) :
    ModelRunWF r (ssClean2 cl) := by
  rw [modelRunWF_iff_r0 ha hb hopk]
  obtain ⟨hiscur0, hdom0, ⟨hm0_ok, hm0_loc, hm1_pre, _⟩, _⟩ := modelRunWF_msPrefix2 false
  refine ⟨hiscur0, hdom0, ?_, ?_⟩
  · dsimp only [ssClean2, DY.Libsignal.Composed.Refinement.StepsWF]
    refine ⟨hm0_ok, hm0_loc, ?_⟩
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, m0_next_false]
    rw [show setupTrace (Symbolic.Proofs.Tests.CliNonvacuity.Witness.mkRecords false) =
        HonestSession.t4 from setupTrace_false_eq, m0_next_false] at hm1_pre
    refine ⟨?_, ?_, trivial⟩
    · change Step.PreCond (Step.messageEncrypt "alice" 30 32 33) HonestSession.t5 at hm1_pre
      unfold m1Clean
      unfold Step.PreCond Step.toInput at hm1_pre ⊢
      dsimp only at hm1_pre ⊢
      rw [stepIn_preCond_iff DY.Libsignal.TripleRatchet.messageEncrypt.reachability
            ("alice", 30, 32, 33) HonestSession.t5] at hm1_pre
      rw [stepIn_preCond_iff DY.Libsignal.TripleRatchet.messageEncrypt.reachability
            ("alice", 30, cl, 33) HonestSession.t5]
      exact hm1_pre
    · dsimp only [m1Clean, Step.LocalOk]
      exact ⟨hcl, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [HonestSession.t5_length])⟩
  · intro i j si sj p k b hij hmi hmj hli _ _
    rcases i with _ | _ | i
    · simp only [ssClean2, List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi; cases hli
    · rcases j with _ | _ | j <;> try omega
      simp [ssClean2] at hmj
    · simp [ssClean2] at hmi

/-! ## 2. Closed-Form Prefix & Trial Term Lists on `t6Clean cl` and `visClean2 cl` -/

def storedSecretsClean : List DY.Bytes :=
  Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.pqSecretsList

private theorem storedSecrets_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    storedSecrets (tr.append e) =
      storedSecrets tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)))).map
        fun x => DY.Comparse.serialize x.st).toList := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map]
  exact range_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState))
    tr e (fun o => o.map (DY.Comparse.serialize ∘ (·.st)))

theorem storedSecrets_t6Clean (cl : Nat) :
    storedSecrets (t6Clean cl) = storedSecretsClean := by
  have hc : storedSecrets (t6Clean cl) = storedSecrets HonestSession.t5 := by
    unfold t6Clean encNextTr encPreSaltTr
    simp only [storedSecrets_append]
    repeat erw [List.append_nil]
  have h3 : storedSecrets HonestSession.t7 = storedSecrets HonestSession.t5 := by
    unfold HonestSession.t7 HonestSession.t6 Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
    simp only [storedSecrets_append]
    repeat erw [List.append_nil]
  exact hc.trans (h3.symm.trans
    (show storedSecrets HonestSession.t7 = storedSecretsClean from
      Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.storedSecrets_trAt_3))

def storedStatesClean (cl : Nat) : List (DY.PersistentLocalState.LocalState TRState) :=
  [{ participant := "alice", state := HonestSession.stA0 },
   { participant := "alice", state := encSt HonestSession.t5 HonestSession.stA0 cl }]

private theorem storedStates_self (r : ProtocolSetup) :
    storedStates r (setupTrace r) = [] := by
  simp [storedStates]

private theorem storedStates_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (r : ProtocolSetup) (tr : ExecTrace) (e : E1)
    (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) =
      storedStates r tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState TRState)))).map (·.st)).toList := by
  unfold storedStates
  exact newIndices_filterMap_at?_append
    (E2 := DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState TRState))
    (setupTrace r) tr e (fun _ o => o.map (·.st)) hle

theorem storedStates_t6Clean {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl : Nat) :
    storedStates r (t6Clean cl) = storedStatesClean cl := by
  rw [storedStates_eq_r0 ha hb hopk]
  have ht4 : (setupTrace r0).length = 22 := by
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, HonestSession.t4_length]
  have hs5 : storedStates r0 HonestSession.t5 =
      [{ participant := "alice", state := HonestSession.stA0 }] := by
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    repeat rw [storedStates_append _ _ _
      (by simp -failIfUnchanged only [length_append_entry_eq, ht4, HonestSession.t4_length]; omega)]
    rw [← (show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq), storedStates_self,
      show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, HonestSession.t4_length]
    rfl
  unfold t6Clean encNextTr encPreSaltTr storedStatesClean
  dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, ht4, HonestSession.t5_length]; omega)]
  rw [hs5]
  rfl

theorem honestSaltsOf_ssClean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl : Nat) :
    honestSaltsOf r (ssClean2 cl) = [DY.Spqr.zeroKey, HonestSession.key0] := by
  rw [honestSaltsOf_eq_r0 ha hb hopk]
  unfold honestSaltsOf ssClean2 m0Of m1Clean
  simp only [Bool.false_eq_true, ↓reduceIte, honestKeysOf,
    Step.publishedSpqrKey?, DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx]
  rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq,
      show (Step.aliceStart "alice" "bob" 4 6 HonestSession.bh1).next HonestSession.t4 =
        HonestSession.t5 from m0_next_false,
      show (Step.messageEncrypt "alice" 30 cl 33).next HonestSession.t5 =
        t6Clean cl from m1Clean_next cl,
      HonestSession.t5_length]
  have hpq : (t6Clean cl).getMessageSentAt 33 = some HonestSession.key0 := by
    have hpre := Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr_getMessageSentAt_self
      HonestSession.t5 HonestSession.stA0 cl
    rw [HonestSession.t5_length, spqrSend_stA0_key_eq] at hpre
    have hle : Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr
        HonestSession.t5 HonestSession.stA0 cl ≤ t6Clean cl := by
      unfold t6Clean encNextTr
      exact DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
        (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
          (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _)))
    rw [getMessageSentAt_eq_at?] at hpre ⊢
    rcases hat : ((Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encPreSaltTr
        HonestSession.t5 HonestSession.stA0 cl).at? 33 : Option DY.Network.ExecEntryT) with _ | ⟨m⟩ <;>
      rw [hat] at hpre
    · cases hpre
    · injection hpre with hm
      rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle hat]
      exact congrArg some hm
  simp only [Nat.reduceAdd, hpq]
  rfl

private theorem filter_kind_vis0 (k : DY.Libsignal.Composed.Refinement.VisEventKind)
    (hrecv : (.recv == k) = false) (hrng : (.rng == k) = false) :
    (visStep (m0Of false) HonestSession.t4 HonestSession.t5 false).filter (·.kind == k) = [] := by
  unfold visStep
  rw [exposures_t4_t5, List.append_nil]
  dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte, DY.Libsignal.Composed.Refinement.aliceVis]
  have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
      [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by
    rw [newRandoms_t4_t5]; rfl
  rw [hnr0, List.filter_eq_nil_iff]
  intro v hv
  dsimp only [DY.Libsignal.Composed.Refinement.aliceDraws,
    DY.Libsignal.Composed.Refinement.kyberCoinEntries,
    DY.Libsignal.Composed.Refinement.rngEntry,
    List.drop, List.take, List.cons_append, List.nil_append] at hv
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩
  · exact Bool.eq_false_iff.mp hrecv
  · exact Bool.eq_false_iff.mp hrng
  · exact Bool.eq_false_iff.mp hrng
  · exact Bool.eq_false_iff.mp hrng

theorem plaintextTerms_visClean2 (cl : Nat) :
    plaintextTerms (visClean2 cl) = [HonestSession.m0] := by
  unfold plaintextTerms visClean2
  rw [vis_m0_false, vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
      exposures_t5_t6Clean]
  rw [List.filter_append, filter_kind_vis0 .pt rfl rfl, List.nil_append, List.append_nil,
      List.filter_append]
  unfold encDraws
  have hm0 : HonestSession.m0 = randTerm 31 32 := rfl
  rw [hm0]
  by_cases hcl0 : cl = 0 <;> simp [hcl0, DY.Libsignal.Composed.Refinement.rngEntry]

theorem sendTerms_visClean2 (cl : Nat) :
    (((visClean2 cl).filter (·.kind == .send)).flatMap (·.terms)) =
      [HonestSession.o1.ek, HonestSession.o1.ct, (xClean cl).msg] := by
  unfold visClean2
  rw [vis_m0_false, vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
      exposures_t5_t6Clean]
  rw [List.filter_append, filter_kind_vis0 .send rfl rfl, List.nil_append, List.append_nil,
      List.filter_append]
  unfold encDraws
  by_cases hcl0 : cl = 0 <;> simp [hcl0, DY.Libsignal.Composed.Refinement.rngEntry]

def bobCtxClean : TrialCtx :=
  { peerIk := DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikA)
    myIk := DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikB)
    extra := [HonestSession.keys1.rk, HonestSession.keys1.ck, HonestSession.keys1.pqr,
              HonestSession.stA0.cks, (kdfCk HonestSession.stA0.cks).1]
    ownSalts := [HonestSession.key0]
    seed? := some (kdfCk HonestSession.stA0.cks).2 }

theorem bobTrials_clean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (cl : Nat) :
    bobTrials r tr dhP0 (xClean cl) (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33) =
      [bobCtxClean] := by
  rw [bobTrials_dhP0_eq_r0 ha hb hopk tr tr]
  unfold bobTrials DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
  rw [dhP0_preKeyId]
  have hp0 : setupPublic r0 0 = DY.DiffieHellman.dhPk HonestSession.ikA :=
    setupPublic_0_bridge r0 (by show "alice" ≠ "bob"; decide)
  have hp2 : setupPublic r0 2 = DY.DiffieHellman.dhPk HonestSession.ikB :=
    setupPublic_2_bridge r0 (by show "alice" ≠ "bob"; decide)
  have hsr := Symbolic.Swarm.CREF.TR.setupRandoms_eq r0 (by show "alice" ≠ "bob"; decide)
  have hs1 : setupSecret r0 1 = HonestSession.ikB := by unfold setupSecret; rw [hsr]; rfl
  have hs2 : setupSecret r0 2 = HonestSession.spkB := by unfold setupSecret; rw [hsr]; rfl
  have hs4 : setupSecret r0 4 = HonestSession.pqskB := by unfold setupSecret; rw [hsr]; rfl
  dsimp only
  rw [hp0, hp2, hs1, hs2, hs4]
  have hek : (xClean cl).ek =
      DY.DiffieHellman.dhPk (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 22 32) := by
    unfold xClean
    dsimp only [HonestSession.o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut]
    rw [HonestSession.t4_length]
    rfl
  have hct : (xClean cl).ct =
      (DY.PQKem.kemEncap (DY.PQKem.kemPk HonestSession.pqskB)
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 23 32)).1 := by
    unfold xClean
    dsimp only [HonestSession.o1, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [HonestSession.t4_length]
    rfl
  have hss : (DY.Libsignal.PQXDH.errToOption
      (DY.PQKem.kemDecap HonestSession.pqskB (xClean cl).ct)).getD
      (DY.PQKem.kemRejKey HonestSession.pqskB (xClean cl).ct) =
      (DY.PQKem.kemEncap (DY.PQKem.kemPk HonestSession.pqskB)
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 23 32)).2 := by
    rw [hct, Symbolic.Proofs.Tests.Shared.Composed.Runs.kemDecap_kemEncap]; rfl
  rw [hss]
  have hkeys : DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
      (DY.X25519.agree (DY.DiffieHellman.dhPk HonestSession.ikA) HonestSession.spkB)
      (DY.X25519.agree (xClean cl).ek HonestSession.ikB)
      (DY.X25519.agree (xClean cl).ek HonestSession.spkB)
      (Option.map (fun x => DY.X25519.agree (xClean cl).ek x) none)
      (DY.PQKem.kemEncap (DY.PQKem.kemPk HonestSession.pqskB)
        (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 23 32)).2) = HonestSession.keys1 := by
    rw [hek]
    dsimp only [Option.map_none]
    rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm HonestSession.ikA HonestSession.spkB,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 22 32) HonestSession.ikB,
        Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm (Symbolic.Proofs.Tests.Shared.Composed.Runs.rnd 22 32) HonestSession.spkB]
    dsimp only [HonestSession.keys1, HonestSession.o1,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOutOpt,
      DY.Libsignal.PQXDH.aliceAgreement]
    rw [HonestSession.t4_length]
    rfl
  rw [hkeys]
  have hc : (createChain HonestSession.keys1.rk
      (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ratchetKey HonestSession.spkB).2 =
      HonestSession.stA0.cks := by
    show (createChain HonestSession.keys1.rk (DY.DiffieHellman.dhPk HonestSession.dhsA) HonestSession.spkB).2 =
      (createChain HonestSession.keys1.rk (DY.DiffieHellman.dhPk HonestSession.spkB) HonestSession.dhsA).2
    rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.createChain_comm
      HonestSession.keys1.rk HonestSession.dhsA HonestSession.spkB]
  rw [hc]
  have hcnt : (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).counter = 0 := rfl
  have hv_var : ∀ sk : DY.Bytes, ((DY.DiffieHellman.dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hv_lit : ∀ sk : DY.Bytes, ((DY.DiffieHellman.dhPk sk).view? DY.Literal.Literal.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hlow_dhPk : ∀ sk : DY.Bytes, DY.X25519.x25519LowOrder (DY.DiffieHellman.dhPk sk) = false := fun sk => by
    simp only [DY.X25519.x25519LowOrder, DY.X25519.normalizeX25519Key,
      hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hpb1 : decide (DY.X25519.leValue
      (List.map BitVec.toNat (List.drop 1 (List.take 33 dhP0.baseKey))) < DY.X25519.p25519) = true := by
    decide +kernel
  have hpb2 : DY.X25519.isLowOrderKey
      (List.map BitVec.toNat (List.drop 1 (List.take 33 dhP0.baseKey))) = false := by
    decide +kernel
  have hpb3 : DY.X25519.isLowOrderKey
      (List.map BitVec.toNat dhP0.inner.senderRatchetKey.bytes.toList) = false := by
    decide +kernel
  have hek_lo : DY.X25519.x25519LowOrder (xClean cl).ek = false := by
    rw [hek]; exact hlow_dhPk _
  have hrk_lo : DY.X25519.x25519LowOrder
      (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ratchetKey = false :=
    hlow_dhPk HonestSession.dhsA
  have hver : decide ((encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).version =
      DY.Libsignal.TripleRatchet.messageVersion) = true := rfl
  have hcmk : consumeMessageKey
      { ratchetKey := (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ratchetKey,
        chainKey := HonestSession.stA0.cks, index := 0, rIdx := 2 } 0 =
      some ((kdfCk HonestSession.stA0.cks).2,
        { ratchetKey := (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ratchetKey,
          chainKey := (kdfCk HonestSession.stA0.cks).1, index := 1, rIdx := 2 }) := rfl
  have hsk : skippedSeeds
      { ratchetKey := (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ratchetKey,
        chainKey := HonestSession.stA0.cks, index := 0, rIdx := 2 } 0 = [] := rfl
  rw [hpb1, hpb2, hek_lo, hver, hpb3, hrk_lo, hcnt, dhP0_spqrIdx, hcmk, hsk]
  dsimp only [Option.all, Bool.not_false, Bool.not_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  have hnlit : DY.Literal.bytesToLiteral
      (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).pqRatchet = none := by
    have hlit := DY.Literal.literalToBytes_bytesToLiteral
      (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).pqRatchet
    rcases hbl : DY.Literal.bytesToLiteral
        (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).pqRatchet with _ | b
    · rfl
    · rw [hbl] at hlit
      have htag := congrArg bytesTag hlit
      simp [encParsedMsg] at htag
  have hrecv := Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas.spqrRecv_init_agree
    HonestSession.keys1.pqr HonestSession.coins0
    (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).pqRatchet .b2a hnlit
  rw [show DY.Libsignal.TripleRatchet.spqrB2A = DY.Spqr.encodeSpqrDirectionParams .b2a from rfl,
      hrecv]
  rfl

def bobTrialTermsClean (cl : Nat) : List DY.Bytes :=
  let seed := (kdfCk HonestSession.stA0.cks).2
  let wire := (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).wire
  let mk0 := trMsgKeys DY.Spqr.zeroKey seed
  let mk1 := trMsgKeys HonestSession.key0 seed
  [HonestSession.keys1.rk, HonestSession.keys1.ck, HonestSession.keys1.pqr,
   HonestSession.stA0.cks, (kdfCk HonestSession.stA0.cks).1,
   mk0.cipherKey, mk0.macKey, mk0.iv,
   computeMac mk0.macKey
     (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikA))
     (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikB)) wire,
   mk1.cipherKey, mk1.macKey, mk1.iv,
   computeMac mk1.macKey
     (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikA))
     (DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk HonestSession.ikB)) wire,
   HonestSession.m0]

theorem bobTrialTerms_clean2 (cl : Nat) :
    ([bobCtxClean].flatMap (trialTerms [DY.Spqr.zeroKey, HonestSession.key0]
      (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33))) =
      bobTrialTermsClean cl := by
  unfold bobCtxClean trialTerms bobTrialTermsClean
  simp only [List.flatMap_cons, List.flatMap_nil]
  have hsalt : encSalt HonestSession.t5 HonestSession.stA0 cl 33 = HonestSession.key0 := by
    have hs : encSalt HonestSession.t5 HonestSession.stA0 cl (HonestSession.t5.length + 2) =
        (DY.Spqr.spqrSend HonestSession.stA0.spqr (randTerm (HonestSession.t5.length + 1) cl)).2.1 :=
      Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc.encSalt_self
        HonestSession.t5 HonestSession.stA0 cl
    rw [HonestSession.t5_length] at hs
    exact hs.trans (spqrSend_stA0_key_eq _)
  have hct : (encParsedMsg HonestSession.t5 HonestSession.stA0 cl 33).ciphertext =
      (Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig
        HonestSession.stA0 HonestSession.coins0 HonestSession.key0 HonestSession.m0).ciphertext := by
    dsimp only [encParsedMsg, Symbolic.Proofs.Tests.Shared.Composed.Runs.encSig]
    rw [hsalt, HonestSession.t5_length]
    rfl
  rw [hct, symDec_ne_salt (show DY.Spqr.zeroKey ≠ HonestSession.key0 from
        zeroKey_ne_spqrSendKey HonestSession.stA0.spqr HonestSession.coins0),
      Symbolic.Proofs.Tests.Shared.Composed.Runs.dec_ok rfl]
  rfl

end Symbolic.BugInjection.Proofs.SyntheticDhRatchetNoSendStep.RecvCleanExplain
