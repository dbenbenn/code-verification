/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Random
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.Shared.Composed.PrunedSpecLemmas
import Symbolic.Proofs.Tests.CliNonvacuity.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
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
# Clean 2-Step Prefix & `bobStart` Non-Collision for Seed 7003 (`Clean2BobStart7003.lean`)

Provides reusable trace-append combinators, the parametric clean 2-step prefix
`(gClean7003 mode cl₁ cl₃, ssClean2 cl₁, visClean2 cl₁)`, `Explains` on `[.run ev0, .run (ev1Of mode)]`,
and `not_nextEventCollides_ev2_m1` / `not_nextEventCollides_ev2_m2`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003

unseal DY.Bytes

open ByteSpecs (hmacWith)
open scoped DY.Libsignal.Composed
open DY (Traceful ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent serializedIk)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag preKeyBundleByteLength)
open DY.Libsignal.TripleRatchet
  (TRState TREvent TRSignalMsg kdfCk trMsgKeys computeMac createChain
   consumeMessageKey skippedSeeds parseTrSignalMsg spqrA2B spqrB2A u32Max)
open DY.Libsignal.Composed (reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup ProtocolSetupWF OpaqueSymbolSemantics Ghost Step VisEntry VisEventKind
   BundlePreKeyIds PreKeyFields PreKeyRep TrialCtx
   gamma gamma' ecKey kyberKey pubBytes secretBytes slice preKeyWire parsePreKeyWire preKeySpqrIndex
   randTerm setupTrace setupRandoms setupRandomsAt setupSecret setupPublic
   runSteps runTrace newIndices newRandoms lastSent pendingPreKey received
   rngEntry kyberCoinEntries aliceDraws aliceVis encDraws encSendEntry
   pqExposureAt trExposureAt exposures stepView honestKeysOf
   storedSecrets storedStates honestSaltsOf plaintextTerms trialTerms bobTrials
   spqrHeaded getMessageSentAt_attackerKnows preKeyRepresentationsOn
   GhostAndSemMatchSetup GhostWF ModelRunWF FaithfulInner PreKeyRecvMatches
   BytesMatchEntry DrawsMatch OutputsMatch RunMatches MatchesEventsAt Explains
   BobSessionStartCollidesOrImplicitRejectsOn KnownBaseKeyOn bobDoneBaseKeys)
open DY.Libsignal.Composed.Refinement.Cli (NextEventCollides serializeAddresses aliceUuid bobUuid)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next stepIn_ok)
open Symbolic.Swarm.CREF
  (b1_setupTr1 b1_setupTr2 b1_setupTr3 b1_setupTr4 b1_RndE b1_NetE b1_EvE b1_StE
   b1_setupPublic_5 b1_setupPublic_6 b1_setupPublic_7)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd RndE NetE EvP EvT EvC StP StT encMsg encSig encSt parse_encMsg)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (mkRecords)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (matchesEvents_run1)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of setupTrace_false_eq m0_ok_false m0_next_false vis_m0_false vis_m1_false
   visStep visEncStep modelRunWF_msPrefix2)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (bytesTag view_pack_none length_append_entry_eq getEventAt_eq_at? getMessageSentAt_eq_at?
   setupPublic_0_bridge setupPublic_2_bridge)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (not_preKeyStartCollidesOrRejects_of_clean not_nextEventCollides_accepted_prekey)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003 compPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws (F7 not_kyberMismatch_compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003 (setup_ids_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
  (SemPinned2 encTrCl if_pos' if_neg' getMessageSentAt_of_at?_net
   at?_append_other_eq at?_append_same_eq at?_nil_eq length_append_eq)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003B
  (bobDone_nil_of_explains_m1_2 bobDone_nil_of_explains_m2_2
   semPinned2_of_explains_m1_2 semPinned2_of_explains_m2_2)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators
  (SafeMemo TermAt safeMemo_of_termAt gamma_of_termAt not_memoCollisionOn_of_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt (safeMemo_plaintext)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
  (isAliceWire isAliceWire_tTrW_dhPk_rnd gClean7003 gClean7003_σ_length
   o1Pure o1_eq_pure stA0Pure stA0_eq_pure key0Pure spqrSend_stA0_key
   pqMsg1Pure stA1Pure encMsg1Pure encSig1Pure coins32_safe_and_gamma
   CommonNodes mkCommonNodes M1Nodes mkM1Nodes M2Nodes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
  (symDec_symEnc_mem_eq ghostAndSemMatchSetup_gClean7003 pqSecrets7003
   safeMemo_pqSecrets7003 safeMemo_stA0 safeMemo_stA1)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.MacLaws7003
  (not_readCollisionCli_of_no_decrypt not_macTagForgery_singleton_honest)

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

/-! ## 1. Setup Normalization (`r` vs `r0 := mkRecords false`) -/

abbrev r0 : ProtocolSetup := mkRecords false

theorem setupTrace_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupTrace r = setupTrace r0 := by
  unfold setupTrace r0 mkRecords; rw [ha, hb, hopk]

theorem setupTrace_eq_t4 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupTrace r = HonestSession.t4 := by
  rw [setupTrace_eq_r0 ha hb hopk, setupTrace_false_eq]

theorem setupRandoms_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    setupRandoms r = setupRandoms r0 := by
  unfold setupRandoms; rw [setupTrace_eq_r0 ha hb hopk]

theorem setupSecret_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (k : Nat) :
    setupSecret r k = setupSecret r0 k := by
  unfold setupSecret; rw [setupRandoms_eq_r0 ha hb hopk]

theorem runTrace_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    runTrace r ss = runTrace r0 ss := by
  unfold runTrace; rw [setupTrace_eq_r0 ha hb hopk]

theorem storedStates_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (tr : ExecTrace) :
    storedStates r tr = storedStates r0 tr := by
  unfold storedStates; rw [setupTrace_eq_r0 ha hb hopk]

theorem honestSaltsOf_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    honestSaltsOf r ss = honestSaltsOf r0 ss := by
  unfold honestSaltsOf; rw [setupTrace_eq_r0 ha hb hopk]

theorem modelRunWF_iff_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (ss : List Step) :
    ModelRunWF r ss ↔ ModelRunWF r0 ss := by
  have hr0 : r0.withOpk = false := rfl
  have hsf : DY.Libsignal.Composed.Refinement.StepsStateFaithful r ss ↔
      DY.Libsignal.Composed.Refinement.StepsStateFaithful r0 ss := by
    unfold DY.Libsignal.Composed.Refinement.StepsStateFaithful
    simp only [runTrace_eq_r0 ha hb hopk]
  unfold ModelRunWF
  rw [setupRandoms_eq_r0 ha hb hopk, setupTrace_eq_r0 ha hb hopk, hopk, hr0, hsf]

/-! ## 2. Reusable Sealed-Trace `.append` & `messageEncrypt` Helpers -/

theorem at?_append_of_lt {E1 E2 : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i < tr.length) :
    ((tr.append e).at? i : Option E2) = (tr.at? i : Option E2) := by
  have hi' : i < (tr.append e).length := by rw [length_append_entry_eq]; omega
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr (tr.append e) i hi (DY.Trace.append_le tr e)]

theorem at?_append_self {E1 E2 : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) :
    ((tr.append e).at? tr.length : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) := by
  rw [Symbolic.DYBridge.DY.Trace.append_eq_1]
  have hlt : tr.length < (tr.snoc (DY.TraceEntryHas.inj e)).length := by
    rw [Symbolic.DYBridge.DY.Trace.length_eq_2]; omega
  simp only [DY.Trace.at?, hlt, Symbolic.DYBridge.DY.Trace.at_eq_2, ↓reduceDIte]

theorem at?_append_eq_self {E1 E2 : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) {i : Nat} (hi : i = tr.length) :
    ((tr.append e).at? i : Option E2) =
      (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) : Option E2) :=
  hi ▸ at?_append_self tr e

theorem range_filterMap_at?_append {E1 E2 α : Type}
    [DY.ExecTraceTypes.Has E1] [DY.ExecTraceTypes.Has E2]
    (tr : ExecTrace) (e : E1) (f : Option E2 → Option α) :
    ((List.range (tr.append e).length).filterMap fun i => f ((tr.append e).at? i)) =
      ((List.range tr.length).filterMap fun i => f (tr.at? i)) ++
      (f (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry))).toList := by
  rw [length_append_entry_eq, List.range_succ, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, at?_append_self]
  refine congrArg (· ++ _) (List.filterMap_congr fun i hi => ?_)
  rw [at?_append_of_lt tr e (List.mem_range.mp hi)]

theorem newIndices_filterMap_at?_append {E1 E2 α : Type}
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

theorem newRandoms_self (tr : ExecTrace) : newRandoms tr tr = [] := by
  simp [newRandoms, newIndices]

theorem newRandoms_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr₀ tr : ExecTrace) (e : E1) (hle : tr₀.length ≤ tr.length) :
    newRandoms tr₀ (tr.append e) =
      newRandoms tr₀ tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option DY.Random.ExecEntryT)).map fun r => (randTerm tr.length r.length, r.length)).toList := by
  unfold newRandoms
  exact newIndices_filterMap_at?_append (E2 := DY.Random.ExecEntryT) tr₀ tr e
    (fun i (o : Option DY.Random.ExecEntryT) => o.map fun r => (randTerm i r.length, r.length)) hle

def isPqCompromise : PQXDHEvent → Bool
  | .CompromisedIK .. | .CompromisedSPK .. | .CompromisedOPK .. | .CompromisedPQSPK .. => true
  | _ => false

def optNoPqCompromise (o : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) : Bool :=
  match o with | some ⟨ev⟩ => !isPqCompromise ev | none => true

def isTrExposure : TREvent → Bool
  | .ExposedRK .. | .ExposedDHs .. | .ExposedCKs .. | .ExposedCKr ..
  | .ExposedMK .. | .ExposedSpqr .. => true
  | _ => false

def optNoTrExposure (o : Option (DY.ProtocolEvent.ExecEntryT TREvent)) : Bool :=
  match o with | some ⟨ev⟩ => !isTrExposure ev | none => true

def NoNewExposures (tr₀ tr : ExecTrace) : Prop :=
  ∀ i ∈ newIndices tr₀ tr,
    optNoPqCompromise (tr.at? i) = true ∧ optNoTrExposure (tr.at? i) = true

theorem noNewExposures_self (tr : ExecTrace) : NoNewExposures tr tr := by
  simp [NoNewExposures, newIndices]

theorem noNewExposures_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
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
  · rw [at?_append_self, at?_append_self]; exact ⟨hpq, htr⟩

theorem exposures_eq_nil_of_noNewExposures {tr₀ tr : ExecTrace}
    (h : NoNewExposures tr₀ tr) : exposures tr₀ tr = [] := by
  unfold exposures; rw [List.append_eq_nil_iff]
  refine ⟨List.filterMap_eq_nil_iff.mpr fun i hi => ?_, List.filterMap_eq_nil_iff.mpr fun i hi => ?_⟩
  · have hp := (h i hi).1
    unfold pqExposureAt; rw [getEventAt_eq_at? PQXDHEvent]
    rcases hat : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) with _ | ⟨⟨ev⟩⟩
    · rfl
    · rw [hat] at hp; cases ev <;> simp_all [optNoPqCompromise, isPqCompromise]
  · have ht := (h i hi).2
    unfold trExposureAt; rw [getEventAt_eq_at? TREvent]
    rcases hat : (tr.at? i : Option (DY.ProtocolEvent.ExecEntryT TREvent)) with _ | ⟨⟨ev⟩⟩
    · rfl
    · rw [hat] at ht; cases ev <;> simp_all [optNoTrExposure, isTrExposure]

theorem storedSecrets_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (tr : ExecTrace) (e : E1) :
    storedSecrets (tr.append e) =
      storedSecrets tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState PQXDHState)))).map
        fun x => DY.Comparse.serialize x.st).toList := by
  unfold storedSecrets DY.ExecTrace.getLocalStateAt
  simp only [Option.map_map]
  exact range_filterMap_at?_append tr e
    (fun (o : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState PQXDHState))) => o.map (DY.Comparse.serialize ∘ (·.st)))

theorem storedStates_self (r : ProtocolSetup) : storedStates r (setupTrace r) = [] := by
  simp [storedStates]

theorem storedStates_append {E1 : Type} [DY.ExecTraceTypes.Has E1]
    (r : ProtocolSetup) (tr : ExecTrace) (e : E1) (hle : (setupTrace r).length ≤ tr.length) :
    storedStates r (tr.append e) =
      storedStates r tr ++
      (((DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option (DY.PersistentGlobalState.State.ExecEntryT
            (DY.PersistentLocalState.LocalState TRState)))).map (·.st)).toList := by
  unfold storedStates
  exact newIndices_filterMap_at?_append (setupTrace r) tr e
    (fun _ (o : Option (DY.PersistentGlobalState.State.ExecEntryT
      (DY.PersistentLocalState.LocalState TRState))) => o.map (·.st)) hle

theorem getMessageSentAt_le {tr₁ tr₂ : ExecTrace} {i : Nat} {m : DY.Bytes}
    (hle : tr₁ ≤ tr₂) (h : tr₁.getMessageSentAt i = some m) :
    tr₂.getMessageSentAt i = some m := by
  rw [getMessageSentAt_eq_at?] at h ⊢
  rcases hat : (tr₁.at? i : Option DY.Network.ExecEntryT) with _ | ⟨x⟩ <;> rw [hat] at h
  · cases h
  · injection h with hx
    rw [Symbolic.Swarm.COMPOSED.CompTrace.at?_le_some hle hat]
    exact congrArg some hx

theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h₁ : List.Forall₂ R l₁ m₁) (h₂ : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem stepIn_preCond_iff (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) :
    reachability.PreCond (DY.Libsignal.Composed.Refinement.stepIn c x) tr ↔ c.PreCond x tr :=
  (inst.pf_pre x tr).symm.to_iff

theorem spqrHeaded_computeMac (mk pIk mIk w : DY.Bytes) :
    spqrHeaded (computeMac mk pIk mIk w) = false := by
  unfold spqrHeaded computeMac
  dsimp only [DY.Trunc.trunc8]
  rw [view_pack_none, view_pack_none, view_pack_none, view_pack_none,
      view_pack_none, view_pack_none, view_pack_none]
  rfl

theorem encTrCl_props {tr : ExecTrace} {me : DY.Participant} {stH pqH : Nat} {st : TRState} (cl : Nat)
    (hat_st : tr.at? stH = some (StT me st)) (hcur : stH + 1 = tr.length)
    (hpqH : pqH = tr.length + 2) (hns : st.ns ≠ u32Max) :
    (Step.messageEncrypt me stH cl pqH).PreCond tr ∧
    (Step.messageEncrypt me stH cl pqH).ok tr = true ∧
    (Step.messageEncrypt me stH cl pqH).next tr = encTrCl tr me stH st cl ∧
    (encTrCl tr me stH st cl).length = tr.length + 7 ∧
    tr ≤ encTrCl tr me stH st cl ∧
    (encTrCl tr me stH st cl).getMessageSentAt pqH =
      some (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1 ∧
    lastSent tr (encTrCl tr me stH st cl) =
      some (encMsg st (randTerm (tr.length + 1) cl)
        (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1
        (randTerm tr.length 32)) ∧
    exposures tr (encTrCl tr me stH st cl) = [] ∧
    newRandoms tr (encTrCl tr me stH st cl) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
  subst hpqH
  have hpre : (Step.messageEncrypt me stH cl (tr.length + 2)).PreCond tr := by
    unfold Step.PreCond Step.toInput; dsimp only
    rw [stepIn_preCond_iff DY.Libsignal.TripleRatchet.messageEncrypt.reachability
      (me, stH, cl, tr.length + 2) tr]
    dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability,
      DY.Libsignal.TripleRatchet.isCurrentSnapshot,
      DY.Libsignal.TripleRatchet.getStoredLocalStateAt?]
    rw [hat_st, hcur, Nat.sub_self]; rfl
  have hlen1 : (tr.append (RndE 32)).length = tr.length + 1 := length_append_entry_eq _ _
  have hrnd : ∀ t n, rnd t n = randTerm t n := fun _ _ => rfl
  have hpq_at : (((tr.append (RndE 32)).append (RndE cl)).append
      (NetE (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1)).at? (tr.length + 2) =
      some (NetE (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1) := by
    rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, Nat.add_assoc])]; rfl
  have hruns : Runs (DY.Libsignal.TripleRatchet.messageEncrypt me stH cl (tr.length + 2)) tr
      (tr.length + 6) (encTrCl tr me stH st cl) := by
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    refine Runs.bind (Runs.getLocalState hat_st) ?_
    refine Runs.bind (Runs.guard _ hns) ?_
    refine Runs.bind (Runs.genRand _ _) ?_
    refine Runs.bind (Runs.genRand _ _) ?_
    refine Runs.bind (Runs.sendMessage _ _) ?_
    rw [hlen1, hrnd, hrnd]
    refine Runs.bind (Runs.receiveMessage hpq_at) ?_
    refine Runs.bind (Runs.logEvent _ _) ?_
    refine Runs.bind (Runs.logMessageKeyAndStore _ _ _ _ _ _ _ _ _ _) ?_
    refine ⟨?_, ?_⟩
    · rw [(Runs.sendMessage _ _).1]
      simp [NetE, EvT, StT, length_append_entry_eq, Nat.add_assoc]
    · rw [(Runs.sendMessage _ _).2]
      simp only [encTrCl, encSt, encMsg, RndE, NetE, EvT, StT]
      dsimp only [kdfCk, DY.Spqr.spqrSend, rnd]
  have hok : (Step.messageEncrypt me stH cl (tr.length + 2)).ok tr = true := by
    unfold Step.ok Step.toInput; erw [stepIn_ok, hruns.1]; rfl
  have hnext : (Step.messageEncrypt me stH cl (tr.length + 2)).next tr = encTrCl tr me stH st cl := by
    unfold Step.next Step.toInput; erw [stepIn_next]; exact hruns.2
  have hlen : (encTrCl tr me stH st cl).length = tr.length + 7 := by
    simp only [encTrCl, length_append_entry_eq, Nat.add_assoc]
  have hle : tr ≤ encTrCl tr me stH st cl := by
    unfold encTrCl
    exact DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
        (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
          (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
            (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
              (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _))))))
  have hpq_sent : (encTrCl tr me stH st cl).getMessageSentAt (tr.length + 2) =
      some (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1 := by
    refine getMessageSentAt_le ?_ (getMessageSentAt_of_at?_net hpq_at)
    unfold encTrCl
    exact DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
      (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _)
        (DY.Trace.le_trans _ _ _ (DY.Trace.append_le _ _) (DY.Trace.append_le _ _)))
  have hls : lastSent tr (encTrCl tr me stH st cl) =
      some (encMsg st (randTerm (tr.length + 1) cl)
        (DY.Spqr.spqrSend st.spqr (randTerm (tr.length + 1) cl)).2.1
        (randTerm tr.length 32)) := by
    unfold lastSent
    rw [hlen, if_pos' (by omega), show tr.length + 7 - 1 = tr.length + 6 by omega]
    apply getMessageSentAt_of_at?_net
    unfold encTrCl
    rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, Nat.add_assoc])]; rfl
  have hexp : exposures tr (encTrCl tr me stH st cl) = [] := by
    apply exposures_eq_nil_of_noNewExposures
    unfold encTrCl; dsimp only
    iterate 7 refine (noNewExposures_append
        (by simp -failIfUnchanged only [length_append_entry_eq]; omega) rfl rfl ?_)
    exact noNewExposures_self tr
  have hnr : newRandoms tr (encTrCl tr me stH st cl) =
      [(randTerm tr.length 32, 32), (randTerm (tr.length + 1) cl, cl)] := by
    unfold encTrCl; dsimp only
    repeat rw [newRandoms_append _ _ _ (by simp -failIfUnchanged only [length_append_entry_eq]; omega)]
    rw [newRandoms_self]; simp only [length_append_entry_eq, Nat.add_assoc]; rfl
  exact ⟨hpre, hok, hnext, hlen, hle, hpq_sent, hls, hexp, hnr⟩

/-! ## 3. Clean 2-Step Prefix `(gClean7003, ssClean2, visClean2)` -/

def ev1Of (mode : Bool) : RunEvent := if mode then ev1_m2 else ev1_m1
def ev2Of (mode : Bool) : RunEvent := if mode then ev2_m2 else ev2_m1
def out1Of (mode : Bool) : HwBytes := if mode then out1M2Bytes else out1M1Bytes

theorem out1Of_parses (mode : Bool) : (parsePreKeyWire (out1Of mode)).isSome = true := by
  cases mode <;> decide +kernel

def p1Of (mode : Bool) : PreKeyFields := (parsePreKeyWire (out1Of mode)).get (out1Of_parses mode)

theorem parse_out1Of (mode : Bool) : parsePreKeyWire (out1Of mode) = some (p1Of mode) :=
  (Option.some_get (out1Of_parses mode)).symm

def m1Clean (cl₁ : Nat) : Step := .messageEncrypt "alice" 30 cl₁ 33
def ssClean2 (cl₁ : Nat) : List Step := [m0Of false, m1Clean cl₁]
def t6Clean (cl₁ : Nat) : ExecTrace := encTrCl HonestSession.t5 "alice" 30 stA0Pure cl₁
def xClean (cl₁ : Nat) : PreKeyRep := ⟨o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁⟩
def visClean2 (cl₁ : Nat) : List VisEntry :=
  stepView (m0Of false) HonestSession.t4 false ++ stepView (m1Clean cl₁) HonestSession.t5 true

theorem t5_at_30_stA0 : HonestSession.t5.at? 30 = some (StT "alice" stA0Pure) := by
  rw [← stA0_eq_pure]
  unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, HonestSession.t4_length])]
  simp only [HonestSession.stA0, HonestSession.o1, HonestSession.dhsA,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceOut,
    Symbolic.Proofs.Tests.Shared.Composed.Runs.ComposedRuns.aliceOut, HonestSession.t4_length]
  rfl

theorem m1Clean_props (cl₁ : Nat) :
    (m1Clean cl₁).PreCond HonestSession.t5 ∧
    (m1Clean cl₁).ok HonestSession.t5 = true ∧
    (m1Clean cl₁).next HonestSession.t5 = t6Clean cl₁ ∧
    (t6Clean cl₁).length = HonestSession.t5.length + 7 ∧
    HonestSession.t5 ≤ t6Clean cl₁ ∧
    (t6Clean cl₁).getMessageSentAt 33 =
      some (DY.Spqr.spqrSend stA0Pure.spqr (randTerm (HonestSession.t5.length + 1) cl₁)).2.1 ∧
    lastSent HonestSession.t5 (t6Clean cl₁) =
      some (encMsg stA0Pure (randTerm (HonestSession.t5.length + 1) cl₁)
        (DY.Spqr.spqrSend stA0Pure.spqr (randTerm (HonestSession.t5.length + 1) cl₁)).2.1
        (randTerm HonestSession.t5.length 32)) ∧
    exposures HonestSession.t5 (t6Clean cl₁) = [] ∧
    newRandoms HonestSession.t5 (t6Clean cl₁) =
      [(randTerm HonestSession.t5.length 32, 32), (randTerm (HonestSession.t5.length + 1) cl₁, cl₁)] :=
  encTrCl_props (tr := HonestSession.t5) (me := "alice") (stH := 30) (pqH := 33)
    (st := stA0Pure) cl₁ t5_at_30_stA0 (by rw [HonestSession.t5_length])
    (by rw [HonestSession.t5_length]) (by decide)

theorem runTrace_ssClean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    runTrace r (ssClean2 cl₁) = t6Clean cl₁ := by
  unfold runTrace ssClean2
  rw [setupTrace_eq_t4 ha hb hopk]
  dsimp only [runSteps]
  rw [m0_next_false, (m1Clean_props cl₁).2.2.1]

theorem lastSent_t5_t6Clean (cl₁ : Nat) :
    lastSent HonestSession.t5 (t6Clean cl₁) = some (encMsg1Pure cl₁) := by
  have h := (m1Clean_props cl₁).2.2.2.2.2.2.1
  have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
  have h32 : HonestSession.t5.length + 1 = 32 := by rw [HonestSession.t5_length]
  rw [h32, HonestSession.t5_length, hr, hr, spqrSend_stA0_key] at h
  exact h

theorem exposures_t4_t5 : exposures HonestSession.t4 HonestSession.t5 = [] := by
  apply exposures_eq_nil_of_noNewExposures
  unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  iterate 9 refine (noNewExposures_append
      (by simp -failIfUnchanged only [length_append_entry_eq, HonestSession.t4_length]; omega) rfl rfl ?_)
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
  simp only [length_append_entry_eq, HonestSession.t4_length]; rfl

theorem newRandoms_t5_t6Clean (cl₁ : Nat) :
    newRandoms HonestSession.t5 (t6Clean cl₁) = [(randTerm 31 32, 32), (randTerm 32 cl₁, cl₁)] := by
  simpa [t6Clean, HonestSession.t5_length] using (m1Clean_props cl₁).2.2.2.2.2.2.2.2

theorem exposures_t5_t6Clean (cl₁ : Nat) : exposures HonestSession.t5 (t6Clean cl₁) = [] :=
  (m1Clean_props cl₁).2.2.2.2.2.2.2.1

theorem pendingPreKey_t5_eq :
    pendingPreKey HonestSession.t5 30 = some (o1Pure.ek, o1Pure.ct) := by
  have hv32 := vis_m1_false
  have hm1_eq : Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps.m1Of false = m1Clean 32 := rfl
  have ht6_eq : HonestSession.t6 = t6Clean 32 :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps.m1_next_false.symm.trans
      (by rw [hm1_eq]; exact (m1Clean_props 32).2.2.1)
  rw [hm1_eq, ht6_eq, o1_eq_pure] at hv32
  unfold stepView visEncStep at hv32
  rw [(m1Clean_props 32).2.1] at hv32
  dsimp only [m1Clean, ↓reduceIte] at hv32
  have hv_mid : encDraws (newRandoms HonestSession.t5 ((m1Clean 32).next HonestSession.t5)) ++
      encSendEntry HonestSession.t5 ((m1Clean 32).next HonestSession.t5) 30 true ++
      exposures HonestSession.t5 ((m1Clean 32).next HonestSession.t5) =
      (encDraws (newRandoms HonestSession.t5 (t6Clean 32)) ++
        match lastSent HonestSession.t5 (t6Clean 32) with
        | some w => [⟨.send, [o1Pure.ek, o1Pure.ct, w], .preKeySend, none⟩]
        | none => []) ++
      exposures HonestSession.t5 (t6Clean 32) := hv32
  rw [(m1Clean_props 32).2.2.1] at hv_mid
  have h1 := List.append_cancel_left (List.append_cancel_right hv_mid)
  unfold encSendEntry at h1
  rw [lastSent_t5_t6Clean 32] at h1; dsimp only at h1
  rcases hppk : pendingPreKey HonestSession.t5 30 with _ | ⟨ek, ct⟩ <;> rw [hppk] at h1
  · cases h1
  · simp only [List.cons.injEq, VisEntry.mk.injEq, true_and, and_true] at h1
    rcases h1 with ⟨rfl, rfl⟩; rfl

theorem vis_m1Clean (cl₁ : Nat) :
    stepView (m1Clean cl₁) HonestSession.t5 true =
      visEncStep HonestSession.t5 (t6Clean cl₁) o1Pure.ek o1Pure.ct := by
  unfold stepView visEncStep
  rw [(m1Clean_props cl₁).2.1]
  dsimp only [m1Clean, ↓reduceIte]
  change encDraws (newRandoms HonestSession.t5 ((m1Clean cl₁).next HonestSession.t5)) ++
      encSendEntry HonestSession.t5 ((m1Clean cl₁).next HonestSession.t5) 30 true ++
      exposures HonestSession.t5 ((m1Clean cl₁).next HonestSession.t5) = _
  rw [(m1Clean_props cl₁).2.2.1]
  unfold encSendEntry
  rw [pendingPreKey_t5_eq]
  cases lastSent HonestSession.t5 (t6Clean cl₁) <;> rfl

theorem ghostWF_clean2 (mode : Bool) (cl₁ cl₃ : Nat) :
    GhostWF (gClean7003 mode cl₁ cl₃) (visClean2 cl₁) := by
  refine ⟨?_, fun t => by
    unfold gClean7003; dsimp only
    by_cases h : isAliceWire t
    · rw [if_pos' h]; exact Or.inr addr1_eq_serialized
    · rw [if_neg' h]; exact Or.inl rfl, ?_⟩
  · intro v hv hvk ts n _ hmem
    have hts : ts = 22 ∨ ts = 23 ∨ ts = 24 ∨ ts = 32 := by
      unfold visClean2 at hv
      rcases List.mem_append.mp hv with hv0 | hv1
      · rw [vis_m0_false] at hv0; unfold visStep at hv0
        rw [exposures_t4_t5, List.append_nil] at hv0
        dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte, aliceVis] at hv0
        have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
            [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by rw [newRandoms_t4_t5]; rfl
        rw [hnr0] at hv0
        dsimp only [aliceDraws, kyberCoinEntries, List.drop, List.take,
          List.cons_append, List.nil_append] at hv0
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv0
        rcases hv0 with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩
        · cases hvk
        · simp only [rngEntry, List.mem_singleton] at hmem
          exact Or.inl (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1
        · simp only [List.mem_singleton] at hmem
          exact Or.inr (Or.inl (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1)
        · simp only [rngEntry, List.mem_singleton] at hmem
          exact Or.inr (Or.inr (Or.inl (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1))
      · rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
            exposures_t5_t6Clean, List.append_nil] at hv1
        rcases List.mem_append.mp hv1 with hdr | hsnd
        · unfold encDraws at hdr
          by_cases hcl0 : cl₁ = 0 <;> simp [hcl0, rngEntry] at hdr
          · subst hdr; cases hvk
          · rcases hdr with rfl | rfl
            · cases hvk
            · simp only [List.mem_singleton] at hmem
              exact Or.inr (Or.inr (Or.inr (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1))
        · simp only [List.mem_singleton] at hsnd; subst hsnd; cases hvk
    exact gClean7003_σ_length (by omega) (by omega)
  · intro v hv hvk
    have hv_eq : v = ⟨.send, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeySend, none⟩ := by
      unfold visClean2 at hv
      rcases List.mem_append.mp hv with hv0 | hv1
      · rw [vis_m0_false] at hv0; unfold visStep at hv0
        rw [exposures_t4_t5, List.append_nil] at hv0
        dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte, aliceVis] at hv0
        have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
            [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by rw [newRandoms_t4_t5]; rfl
        rw [hnr0] at hv0
        dsimp only [aliceDraws, kyberCoinEntries, List.drop, List.take,
          List.cons_append, List.nil_append] at hv0
        simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv0
        rcases hv0 with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩ <;> cases hvk
      · rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
            exposures_t5_t6Clean, List.append_nil] at hv1
        rcases List.mem_append.mp hv1 with hdr | hsnd
        · unfold encDraws at hdr
          by_cases hcl0 : cl₁ = 0 <;> simp [hcl0, rngEntry] at hdr
          · subst hdr; cases hvk
          · rcases hdr with rfl | rfl <;> cases hvk
        · exact List.mem_singleton.mp hsnd
    subst hv_eq
    refine ⟨fun _ ek ct msg pm hterms hpm => ?_, fun hwh => nomatch hwh⟩
    simp only [List.cons.injEq, and_true] at hterms
    rcases hterms with ⟨_, _, rfl⟩
    unfold encMsg1Pure at hpm
    rw [parse_encMsg] at hpm; injection hpm with hpm; subst hpm
    dsimp only [gClean7003, encSig, DY.Libsignal.TripleRatchet.trHonestWireMsg, stA0Pure,
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
    erw [isAliceWire_tTrW_dhPk_rnd]; exact addr1_eq_serialized

theorem modelRunWF_clean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat)
    (hcl₁ : cl₁ = 0 ∨ cl₁ = 32 ∨ cl₁ = 64) :
    ModelRunWF r (ssClean2 cl₁) := by
  rw [modelRunWF_iff_r0 ha hb hopk]
  obtain ⟨hiscur0, hdom0, ⟨hm0_ok, hm0_loc, _⟩, _⟩ := modelRunWF_msPrefix2 false
  refine ⟨hiscur0, hdom0, ?_, ?_⟩
  · dsimp only [ssClean2, DY.Libsignal.Composed.Refinement.StepsWF]
    refine ⟨hm0_ok, hm0_loc, ?_⟩
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, m0_next_false]
    exact ⟨(m1Clean_props cl₁).1, ⟨hcl₁, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [HonestSession.t5_length])⟩, trivial⟩
  · intro i j si sj p k b hij hmi hmj hli _ _
    rcases i with _ | _ | i
    · simp only [ssClean2, List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi; cases hli
    · rcases j with _ | _ | j <;> try omega
      simp [ssClean2] at hmj
    · simp [ssClean2] at hmi

/-! ## 4. Closed-Form Prefix & Trial Lists on `t6Clean` and `visClean2` -/

theorem storedSecrets_t5 : storedSecrets HonestSession.t5 = pqSecrets7003 := by
  have h3 : storedSecrets HonestSession.t7 = storedSecrets HonestSession.t5 := by
    unfold HonestSession.t7 HonestSession.t6 Symbolic.Proofs.Tests.Shared.Composed.Runs.encTr
    simp only [storedSecrets_append]; repeat erw [List.append_nil]
  exact h3.symm.trans Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux.storedSecrets_trAt_3

theorem storedSecrets_t6Clean (cl₁ : Nat) : storedSecrets (t6Clean cl₁) = pqSecrets7003 := by
  have hc : storedSecrets (t6Clean cl₁) = storedSecrets HonestSession.t5 := by
    unfold t6Clean encTrCl; simp only [storedSecrets_append]; repeat erw [List.append_nil]
  exact hc.trans storedSecrets_t5

theorem storedStates_t5 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) :
    storedStates r HonestSession.t5 = [⟨"alice", stA0Pure⟩] := by
  rw [storedStates_eq_r0 ha hb hopk]
  have ht4 : (setupTrace r0).length = 22 := by
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, HonestSession.t4_length]
  unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
    Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
  dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, ht4, HonestSession.t4_length]; omega)]
  rw [← (show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq), storedStates_self,
      show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, HonestSession.t4_length,
      ← stA0_eq_pure]
  rfl

theorem storedStates_t6Clean {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    storedStates r (t6Clean cl₁) = [⟨"alice", stA0Pure⟩, ⟨"alice", stA1Pure cl₁⟩] := by
  have ht4 : (setupTrace r).length = 22 := by
    rw [setupTrace_eq_t4 ha hb hopk, HonestSession.t4_length]
  unfold t6Clean encTrCl; dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, ht4, HonestSession.t5_length]; omega)]
  rw [storedStates_t5 ha hb hopk, HonestSession.t5_length]
  rfl

theorem honestSaltsOf_ssClean2 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ : Nat) :
    honestSaltsOf r (ssClean2 cl₁) = [DY.Spqr.zeroKey, key0Pure] := by
  rw [honestSaltsOf_eq_r0 ha hb hopk]
  have hnext : (Step.messageEncrypt "alice" 30 cl₁ 33).next HonestSession.t5 = t6Clean cl₁ :=
    (m1Clean_props cl₁).2.2.1
  unfold honestSaltsOf ssClean2 m0Of m1Clean
  simp only [Bool.false_eq_true, ↓reduceIte, honestKeysOf,
    Step.publishedSpqrKey?, DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx]
  rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq,
      show (Step.aliceStart "alice" "bob" 4 6 HonestSession.bh1).next HonestSession.t4 =
        HonestSession.t5 from m0_next_false,
      hnext, HonestSession.t5_length]
  have hpq : (t6Clean cl₁).getMessageSentAt 33 = some key0Pure := by
    have h := (m1Clean_props cl₁).2.2.2.2.2.1
    have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
    have h32 : HonestSession.t5.length + 1 = 32 := by rw [HonestSession.t5_length]
    rw [h32, hr, spqrSend_stA0_key] at h
    exact h
  simp only [Nat.reduceAdd, hpq]
  rfl

theorem filter_kind_vis0 (k : VisEventKind)
    (hrecv : (.recv == k) = false) (hrng : (.rng == k) = false) :
    (visStep (m0Of false) HonestSession.t4 HonestSession.t5 false).filter (·.kind == k) = [] := by
  unfold visStep; rw [exposures_t4_t5, List.append_nil]
  dsimp only [m0Of, Bool.false_eq_true, ↓reduceIte, aliceVis]
  have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
      [randTerm 22 32, randTerm 23 32, randTerm 24 32] := by rw [newRandoms_t4_t5]; rfl
  rw [hnr0, List.filter_eq_nil_iff]
  intro v hv
  dsimp only [aliceDraws, kyberCoinEntries, rngEntry, List.drop, List.take,
    List.cons_append, List.nil_append] at hv
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | ⟨_, _, rfl⟩ | ⟨_, rfl, rfl⟩
  · exact Bool.eq_false_iff.mp hrecv
  · exact Bool.eq_false_iff.mp hrng
  · exact Bool.eq_false_iff.mp hrng
  · exact Bool.eq_false_iff.mp hrng

theorem plaintextTerms_visClean2 (cl₁ : Nat) :
    plaintextTerms (visClean2 cl₁) = [tRnd 31 32] := by
  unfold plaintextTerms visClean2
  rw [vis_m0_false, vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
      exposures_t5_t6Clean, List.filter_append, filter_kind_vis0 .pt rfl rfl,
      List.nil_append, List.append_nil, List.filter_append]
  unfold encDraws
  by_cases hcl0 : cl₁ = 0 <;> simp [hcl0, rngEntry, tRnd, randTerm]

theorem sendTerms_visClean2 (cl₁ : Nat) :
    (((visClean2 cl₁).filter (·.kind == .send)).flatMap (·.terms)) =
      [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁] := by
  unfold visClean2
  rw [vis_m0_false, vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
      exposures_t5_t6Clean, List.filter_append, filter_kind_vis0 .send rfl rfl,
      List.nil_append, List.append_nil, List.filter_append]
  unfold encDraws
  by_cases hcl0 : cl₁ = 0 <;> simp [hcl0, rngEntry]

theorem setupPublic_eq_r0 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (k : Nat) :
    setupPublic r k = setupPublic r0 k := by
  unfold setupPublic DY.Libsignal.Composed.Refinement.setupSent
  rw [setupTrace_eq_r0 ha hb hopk]

theorem bobTrials_clean2_exists {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (tr : ExecTrace) (mode : Bool) (cl₁ : Nat) :
    ∃ own : List DY.Bytes,
      bobTrials r tr (p1Of mode) (xClean cl₁) (encSig1Pure cl₁).2 =
        [{ peerIk := stA0Pure.myIk
           myIk := stA0Pure.peerIk
           extra := [o1Pure.keys.rk, o1Pure.keys.ck, o1Pure.keys.pqr,
                     stA0Pure.cks, (stA1Pure cl₁).cks]
           ownSalts := own
           seed? := some (kdfCk stA0Pure.cks).2 }] := by
  have hp_opk : (p1Of mode).preKeyId = none := by cases mode <;> decide +kernel
  unfold bobTrials DY.Libsignal.Composed.Refinement.ProtocolSetup.ikAPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBPubTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.ikBSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSecTerm
    DY.Libsignal.Composed.Refinement.ProtocolSetup.pqskSecTerm
  rw [hp_opk,
      setupSecret_eq_r0 ha hb hopk 1, setupSecret_eq_r0 ha hb hopk 2,
      setupSecret_eq_r0 ha hb hopk 4,
      setupPublic_eq_r0 ha hb hopk 0, setupPublic_eq_r0 ha hb hopk 2]
  have hp0 : setupPublic r0 0 = dhPk (tRnd 0 32) :=
    setupPublic_0_bridge r0 (by show "alice" ≠ "bob"; decide)
  have hp2 : setupPublic r0 2 = dhPk (tRnd 5 32) :=
    setupPublic_2_bridge r0 (by show "alice" ≠ "bob"; decide)
  have hsr := Symbolic.Swarm.CREF.TR.setupRandoms_eq r0 (by show "alice" ≠ "bob"; decide)
  have hs1 : setupSecret r0 1 = tRnd 5 32 := by unfold setupSecret; rw [hsr]; rfl
  have hs2 : setupSecret r0 2 = tRnd 10 32 := by unfold setupSecret; rw [hsr]; rfl
  have hs4 : setupSecret r0 4 = tRnd 16 64 := by unfold setupSecret; rw [hsr]; rfl
  dsimp only
  rw [hp0, hp2, hs1, hs2, hs4]
  have hct : (xClean cl₁).ct = (DY.PQKem.kemEncap (DY.PQKem.kemPk (tRnd 16 64)) (tRnd 23 32)).1 := rfl
  have hss : (DY.Libsignal.PQXDH.errToOption
      (DY.PQKem.kemDecap (tRnd 16 64) (xClean cl₁).ct)).getD
      (DY.PQKem.kemRejKey (tRnd 16 64) (xClean cl₁).ct) =
      (DY.PQKem.kemEncap (DY.PQKem.kemPk (tRnd 16 64)) (tRnd 23 32)).2 := by
    rw [hct, Symbolic.Proofs.Tests.Shared.Composed.Runs.kemDecap_kemEncap]; rfl
  rw [hss]
  have hkeys : DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm
      (DY.X25519.agree (dhPk (tRnd 0 32)) (tRnd 10 32))
      (DY.X25519.agree (xClean cl₁).ek (tRnd 5 32))
      (DY.X25519.agree (xClean cl₁).ek (tRnd 10 32))
      (Option.map (fun x => DY.X25519.agree (xClean cl₁).ek x) none)
      (DY.PQKem.kemEncap (DY.PQKem.kemPk (tRnd 16 64)) (tRnd 23 32)).2) = o1Pure.keys := by
    dsimp only [xClean, o1Pure, Option.map_none, DY.Libsignal.PQXDH.aliceAgreement]
    rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm (tRnd 0 32) (tRnd 10 32),
        Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm (tRnd 22 32) (tRnd 5 32),
        Symbolic.Proofs.Tests.Shared.Composed.Runs.agree_comm (tRnd 22 32) (tRnd 10 32)]
  rw [hkeys]
  have hc : (createChain o1Pure.keys.rk (encSig1Pure cl₁).2.ratchetKey (tRnd 10 32)).2 =
      stA0Pure.cks := by
    show (createChain o1Pure.keys.rk (dhPk (tRnd 24 32)) (tRnd 10 32)).2 =
      (createChain o1Pure.keys.rk (dhPk (tRnd 10 32)) (tRnd 24 32)).2
    rw [Symbolic.Proofs.Tests.Shared.Composed.Runs.createChain_comm]
  rw [hc]
  have hcnt : (encSig1Pure cl₁).2.counter = 0 := rfl
  have hv_var : ∀ sk : DY.Bytes, ((dhPk sk).view? DY.X25519.Variant.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hv_lit : ∀ sk : DY.Bytes, ((dhPk sk).view? DY.Literal.Literal.SubF) = none := fun sk =>
    Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Literal.Literal.SubF
      ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes)
  have hlow_dhPk : ∀ sk : DY.Bytes, DY.X25519.x25519LowOrder (dhPk sk) = false := fun sk => by
    simp only [DY.X25519.x25519LowOrder, DY.X25519.normalizeX25519Key,
      hv_var, DY.Literal.bytesToLiteral, DY.Literal.CanMkLiteral.bytesToLiteral, hv_lit]
  have hpb1 : decide (DY.X25519.leValue
      (List.map BitVec.toNat (List.drop 1 (List.take 33 (p1Of mode).baseKey))) < DY.X25519.p25519) = true := by
    cases mode <;> decide +kernel
  have hpb2 : DY.X25519.isLowOrderKey
      (List.map BitVec.toNat (List.drop 1 (List.take 33 (p1Of mode).baseKey))) = false := by
    cases mode <;> decide +kernel
  have hpb3 : DY.X25519.isLowOrderKey
      (List.map BitVec.toNat (p1Of mode).inner.senderRatchetKey.bytes.toList) = false := by
    cases mode <;> decide +kernel
  have hek_lo : DY.X25519.x25519LowOrder (xClean cl₁).ek = false := hlow_dhPk (tRnd 22 32)
  have hrk_lo : DY.X25519.x25519LowOrder (encSig1Pure cl₁).2.ratchetKey = false := hlow_dhPk (tRnd 24 32)
  have hver : decide ((encSig1Pure cl₁).2.version = DY.Libsignal.TripleRatchet.messageVersion) = true := rfl
  have hcmk : consumeMessageKey
      { ratchetKey := (encSig1Pure cl₁).2.ratchetKey, chainKey := stA0Pure.cks, index := 0, rIdx := 2 } 0 =
      some ((kdfCk stA0Pure.cks).2,
        { ratchetKey := (encSig1Pure cl₁).2.ratchetKey, chainKey := (stA1Pure cl₁).cks, index := 1, rIdx := 2 }) := rfl
  have hsk : skippedSeeds
      { ratchetKey := (encSig1Pure cl₁).2.ratchetKey, chainKey := stA0Pure.cks, index := 0, rIdx := 2 } 0 = [] := rfl
  rw [hpb1, hpb2, hek_lo, hver, hpb3, hrk_lo, hcnt, hcmk, hsk]
  dsimp only [Option.all, Bool.not_false, Bool.not_true, Bool.and_self, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  exact ⟨_, rfl⟩

def ct1IdOf (mode : Bool) : Nat := if mode then ct1M2Id else ct1M1Id
def wire1IdOf (mode : Bool) : Nat := if mode then wire1M2Id else wire1M1Id
def mac1IdOf (mode : Bool) : Nat := if mode then mac1M2Id else mac1M1Id
def out1IdOf (mode : Bool) : Nat := if mode then out1M2Id else out1M1Id
def zMac1IdOf (mode : Bool) : Nat := if mode then zMac1M2Id else zMac1M1Id

theorem mkMsg1Nodes {mode : Bool} {S : OpaqueSymbolSemantics} {pts : List DY.Bytes}
    {cl₁ cl₃ : Nat} (cn : CommonNodes mode S pts cl₁ cl₃) (hpt1 : tRnd 31 32 ∈ pts) :
    TermAt mode S (gClean7003 mode cl₁ cl₃) pts (encSig1Pure cl₁).2.ciphertext (ct1IdOf mode) ∧
    TermAt mode S (gClean7003 mode cl₁ cl₃) pts (encSig1Pure cl₁).2.wire (wire1IdOf mode) ∧
    TermAt mode S (gClean7003 mode cl₁ cl₃) pts (encSig1Pure cl₁).2.mac (mac1IdOf mode) ∧
    TermAt mode S (gClean7003 mode cl₁ cl₃) pts (encMsg1Pure cl₁) (out1IdOf mode) ∧
    TermAt mode S (gClean7003 mode cl₁ cl₃) pts
      (computeMac (trMsgKeys DY.Spqr.zeroKey (kdfCk stA0Pure.cks).2).macKey
        stA0Pure.myIk stA0Pure.peerIk (encSig1Pure cl₁).2.wire) (zMac1IdOf mode) := by
  let g := gClean7003 mode cl₁ cl₃
  cases mode
  · have hct1 : TermAt false S g pts (encSig1Pure cl₁).2.ciphertext ct1M1Id :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_symEncPt
        (id := ct1M1Id) (hkey := cn.a0Ckey) (hiv := cn.a0Iv)
        (hpt_mem := hpt1) (hpt_bs := Or.inl rfl) (hg_pt := rfl)
    have hwire1 : TermAt false S g pts (encSig1Pure cl₁).2.wire wire1M1Id :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_trWire
        (id := wire1M1Id) (addr := addr1Bytes) (useEv4Var := false)
        (hrk := cn.pk4) (hct := hct1) (hpq := cn.pqMsg1)
        (haddr := by
          dsimp only [g, gClean7003, encSig1Pure, encSig, DY.Libsignal.TripleRatchet.trHonestWireMsg,
            stA0Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
            Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs.trWireEvOf]
          rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
    have hmiR1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := miR1M1Id) (hl := cn.ik1s) (hr := hwire1)
    have hmi1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := mi1M1Id) (hl := cn.ik0s) (hr := hmiR1)
    have hmac1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.ta_macFromMi
      (fm := fmac1M1Id) (mac := mac1M1Id) cn.a0Mkey hmi1
    have hout1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := out1M1Id) (hl := hwire1) (hr := hmac1)
    have hzMac1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.ta_macFromMi
      (fm := zFmac1M1Id) (mac := zMac1M1Id) cn.zA0Mkey hmi1
    exact ⟨hct1, hwire1, hmac1, hout1, hzMac1⟩
  · have hct1 : TermAt true S g pts (encSig1Pure cl₁).2.ciphertext ct1M2Id :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_symEncPt
        (id := ct1M2Id) (hkey := cn.a0Ckey) (hiv := cn.a0Iv)
        (hpt_mem := hpt1) (hpt_bs := Or.inr (Or.inl rfl)) (hg_pt := rfl)
    have hwire1 : TermAt true S g pts (encSig1Pure cl₁).2.wire wire1M2Id :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_trWire
        (id := wire1M2Id) (addr := addr1Bytes) (useEv4Var := false)
        (hrk := cn.pk4) (hct := hct1) (hpq := cn.pqMsg1)
        (haddr := by
          dsimp only [g, gClean7003, encSig1Pure, encSig, DY.Libsignal.TripleRatchet.trHonestWireMsg,
            stA0Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt,
            Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Defs.trWireEvOf]
          rw [isAliceWire_tTrW_dhPk_rnd]; rfl)
    have hmiR1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := miR1M2Id) (hl := cn.ik1s) (hr := hwire1)
    have hmi1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := mi1M2Id) (hl := cn.ik0s) (hr := hmiR1)
    have hmac1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.ta_macFromMi
      (fm := fmac1M2Id) (mac := mac1M2Id) cn.a0Mkey hmi1
    have hout1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003TermAt.termAt_concat
      (id := out1M2Id) (hl := hwire1) (hr := hmac1)
    have hzMac1 := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.ta_macFromMi
      (fm := zFmac1M2Id) (mac := zMac1M2Id) cn.zA0Mkey hmi1
    exact ⟨hct1, hwire1, hmac1, hout1, hzMac1⟩

theorem not_bobStartCollides_clean2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false)
    (mode : Bool) (cl₁ : Nat)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn compI7003 r S (gClean7003 mode cl₁ 0)
      (runTrace r (ssClean2 cl₁)) (visClean2 cl₁) (honestSaltsOf r (ssClean2 cl₁))
      (p1Of mode) (xClean cl₁) := by
  let g := gClean7003 mode cl₁ 0
  let pts := [tRnd 31 32]
  have cn := mkCommonNodes (mode := mode) (S := S) (pts := pts) (cl₁ := cl₁) (cl₃ := 0) hkpk hsem2
  obtain ⟨hct1, hwire1, hmac1, hout1, hzMac1⟩ := mkMsg1Nodes cn List.mem_cons_self
  unfold BobSessionStartCollidesOrImplicitRejectsOn; dsimp only
  have hparse : parseTrSignalMsg (xClean cl₁).msg = some (encSig1Pure cl₁).2 :=
    parse_encMsg stA0Pure (tRnd 32 cl₁) key0Pure (tRnd 31 32)
  rw [hparse]; dsimp only
  obtain ⟨own, htrials⟩ := bobTrials_clean2_exists ha hb hopk (t6Clean cl₁) mode cl₁
  rw [runTrace_ssClean2 ha hb hopk, htrials, honestSaltsOf_ssClean2 ha hb hopk]
  rintro (hmemo | hmac)
  · refine not_memoCollisionOn_of_safeMemo (mode := mode) (pts := pts)
      (plaintextTerms_visClean2 cl₁) ?_ ?_ ?_ ?_ ?_ hmemo
    · intro t ht
      rw [sendTerms_visClean2] at ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact safeMemo_of_termAt cn.ek
      · exact safeMemo_of_termAt cn.ctKem
      · exact safeMemo_of_termAt hout1
    · rw [storedStates_t6Clean ha hb hopk]
      intro ls hls
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hls
      rcases hls with rfl | rfl
      · exact safeMemo_stA0 cn
      · exact safeMemo_stA1 cn
    · rw [storedSecrets_t6Clean]; exact safeMemo_pqSecrets7003 cn
    · intro t ht
      rcases List.mem_singleton.mp ht with rfl
      exact safeMemo_plaintext List.mem_cons_self
        (by cases mode with | false => exact Or.inl rfl | true => exact Or.inr (Or.inl rfl)) rfl
    · intro t ht
      simp only [xClean, trialTerms, List.flatMap_cons, List.flatMap_nil,
        List.cons_append, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | hdec0 | rfl | rfl | rfl | rfl | hdec1
      · exact safeMemo_of_termAt cn.ek
      · exact safeMemo_of_termAt cn.ctKem
      · exact safeMemo_of_termAt hout1
      · exact safeMemo_of_termAt cn.rkInit
      · exact safeMemo_of_termAt cn.ckInit
      · exact safeMemo_of_termAt cn.pqrInit
      · exact safeMemo_of_termAt cn.stA0Cks
      · exact safeMemo_of_termAt cn.stA1Cks
      · exact safeMemo_of_termAt cn.zA0Ckey
      · exact safeMemo_of_termAt cn.zA0Mkey
      · exact safeMemo_of_termAt cn.zA0Iv
      · exact safeMemo_of_termAt hzMac1
      · rw [symDec_symEnc_mem_eq hdec0]
        exact safeMemo_plaintext List.mem_cons_self
          (by cases mode with | false => exact Or.inl rfl | true => exact Or.inr (Or.inl rfl)) rfl
      · exact safeMemo_of_termAt cn.a0Ckey
      · exact safeMemo_of_termAt cn.a0Mkey
      · exact safeMemo_of_termAt cn.a0Iv
      · exact safeMemo_of_termAt hmac1
      · rw [symDec_symEnc_mem_eq hdec1]
        exact safeMemo_plaintext List.mem_cons_self
          (by cases mode with | false => exact Or.inl rfl | true => exact Or.inr (Or.inl rfl)) rfl
  · refine not_macTagForgery_singleton_honest
      (salt_h := key0Pure) (seed_h := (kdfCk stA0Pure.cks).2)
      (mk_ref := macKey1Bytes) (msg_ref := if mode then macIn1M2Bytes else macIn1M1Bytes)
      (List.mem_cons_of_mem _ List.mem_cons_self)
      (by rw [gamma_of_termAt cn.pqKey1]; decide)
      (by rw [gamma_of_termAt hmac1]; cases mode <;> decide +kernel)
      (by rw [gamma_of_termAt cn.a0Mkey]; decide +kernel)
      (by decide)
      (by cases mode <;> decide +kernel)
      (by decide +kernel)
      (by
        unfold DY.Libsignal.TripleRatchet.hmac
        rw [Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_kdfExtract,
            gamma_of_termAt cn.pqKey1, gamma_of_termAt cn.seedA0]
        decide +kernel)
      hmac

theorem t5_sent_25_26 :
    HonestSession.t5.getMessageSentAt 25 = some o1Pure.ek ∧
    HonestSession.t5.getMessageSentAt 26 = some o1Pure.ct := by
  have hat25 : (HonestSession.t5.at? 25 : Option DY.Network.ExecEntryT) = some (NetE o1Pure.ek) := by
    rw [← o1_eq_pure]
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    iterate 5 rw [at?_append_of_lt _ _ (by simp only [length_append_entry_eq, HonestSession.t4_length]; omega)]
    rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, HonestSession.t4_length])]; rfl
  have hat26 : (HonestSession.t5.at? 26 : Option DY.Network.ExecEntryT) = some (NetE o1Pure.ct) := by
    rw [← o1_eq_pure]
    unfold HonestSession.t5 Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTr
      Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceTrOpt
    dsimp only
    iterate 4 rw [at?_append_of_lt _ _ (by simp only [length_append_entry_eq, HonestSession.t4_length]; omega)]
    rw [at?_append_eq_self _ _ (by simp [length_append_entry_eq, HonestSession.t4_length])]; rfl
  exact ⟨getMessageSentAt_of_at?_net hat25, getMessageSentAt_of_at?_net hat26⟩

theorem xClean_mem {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    xClean cl₁ ∈ preKeyRepresentationsOn compI7003 r S (gClean7003 mode cl₁ cl₃)
      (runTrace r (ssClean2 cl₁)) (out1Of mode) := by
  obtain ⟨ha, hb, hopk, _, _, hspkId, hkpkId⟩ := setup_ids_7003 hf
  obtain ⟨hs0, _⟩ := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.setup_secrets_7003 hf
  let g := gClean7003 mode cl₁ cl₃
  have cn := mkCommonNodes (mode := mode) (S := S) (pts := [tRnd 31 32]) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem2
  obtain ⟨hct1, hwire1, hmac1, hout1, _⟩ := mkMsg1Nodes cn List.mem_cons_self
  rw [runTrace_ssClean2 ha hb hopk]
  obtain ⟨hs25, hs26⟩ := t5_sent_25_26
  have hle56 : HonestSession.t5 ≤ t6Clean cl₁ := (m1Clean_props cl₁).2.2.2.2.1
  have hkek : (xClean cl₁).ek.AttackerKnows (t6Clean cl₁) :=
    getMessageSentAt_attackerKnows (getMessageSentAt_le hle56 hs25)
  have hkct : (xClean cl₁).ct.AttackerKnows (t6Clean cl₁) :=
    getMessageSentAt_attackerKnows (getMessageSentAt_le hle56 hs26)
  have hkmsg : (xClean cl₁).msg.AttackerKnows (t6Clean cl₁) := by
    have hls := lastSent_t5_t6Clean cl₁
    unfold lastSent at hls
    split at hls
    · exact getMessageSentAt_attackerKnows hls
    · cases hls
  have hp := parse_out1Of mode
  have hp_opk : (p1Of mode).preKeyId = none := by cases mode <;> decide +kernel
  refine ⟨hkek, hkct, hkmsg,
    ⟨p1Of mode, hp, ?_, ?_, ?_, by cases mode <;> decide +kernel, ?_, ?_, ?_,
      ⟨false, p1Of mode, hp, hp_opk⟩⟩,
    ⟨p1Of mode, hp, ⟨(encSig1Pure cl₁).2, parse_encMsg _ _ _ _, ?_, ?_,
      spqrHeaded_computeMac _ _ _ _, ?_, ?_, ?_,
      by change (0 : UInt32).toNat = _; cases mode <;> decide +kernel,
      by change (4 : UInt8).toNat = _; cases mode <;> decide +kernel⟩⟩⟩
  · dsimp only [xClean]; rw [gamma_of_termAt cn.ek]; cases mode <;> decide +kernel
  · dsimp only [xClean]; rw [gamma_of_termAt cn.ctKem]; cases mode <;> decide +kernel
  · dsimp only [xClean]; rw [gamma_of_termAt hout1]; cases mode <;> decide +kernel
  · rw [hspkId]; cases mode <;> decide +kernel
  · rw [hkpkId]; cases mode <;> decide +kernel
  · unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
    rw [hs0]; cases mode <;> decide +kernel
  · rw [gamma_of_termAt hwire1]; cases mode <;> decide +kernel
  · rw [gamma_of_termAt hmac1]; cases mode <;> decide +kernel
  · rw [gamma_of_termAt hct1]; cases mode <;> decide +kernel
  · dsimp only [encSig1Pure, encSig, stA0Pure, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt]
    rw [gamma_of_termAt cn.pk4]; cases mode <;> decide +kernel
  · dsimp only [encSig1Pure, encSig]; change gamma compI7003 S g (pqMsg1Pure cl₁) = _
    rw [gamma_of_termAt cn.pqMsg1]; cases mode <;> decide +kernel

private def initCoinsPieces7003 : List HwBytes :=
  [bytesOf r22Id] ++
    ((List.range 32).map fun j => (coins0Bytes.drop (32 + 4 * j)).take 4) ++
    [bytesOf dhsAId]

private theorem initCoinsPieces7003_spec :
    initCoinsPieces7003.all (· != []) = true ∧
    initCoinsPieces7003.flatten = coins0Bytes ∧
    ((List.range 32).all fun j =>
      let p := (coins0Bytes.drop (32 + 4 * j)).take 4
      (p.length == 4) && (p.head? == (bytesOf r23Id)[j]?)) = true := by
  decide +kernel

theorem ev0_nextBundleIds :
    DY.Libsignal.Composed.Refinement.nextBundleIds none ev0 =
      some ((none, 7#32, 9#32) : BundlePreKeyIds) := by
  unfold DY.Libsignal.Composed.Refinement.nextBundleIds
  dsimp only [ev0]; rw [bun0Raw_eq]; decide +kernel

private theorem setupTr4_net_at (i : Nat) :
    ((b1_setupTr4 "alice" "bob").at? i : Option DY.Network.ExecEntryT) =
    if i = 21 then some (b1_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
      (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64)))))
    else if i = 20 then some (b1_NetE (DY.PQKem.kemPk (randTerm 16 64)))
    else if i = 15 then some (b1_NetE (DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
      (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32)))))
    else if i = 14 then some (b1_NetE (DY.DiffieHellman.dhPk (randTerm 10 32)))
    else if i = 8 then some (b1_NetE (DY.Signature.vk (randTerm 5 32)))
    else if i = 7 then some (b1_NetE (DY.DiffieHellman.dhPk (randTerm 5 32)))
    else if i = 3 then some (b1_NetE (DY.Signature.vk (randTerm 0 32)))
    else if i = 2 then some (b1_NetE (DY.DiffieHellman.dhPk (randTerm 0 32)))
    else none := by
  unfold b1_setupTr4 b1_setupTr3 b1_setupTr2 b1_setupTr1 b1_RndE b1_NetE b1_EvE b1_StE
  repeat first
    | rw [at?_append_other_eq (E₂ := DY.Network.ExecEntryT) rfl]
    | rw [at?_append_same_eq (fun _ => rfl)]
  rw [at?_nil_eq]
  simp only [length_append_eq]
  have hnil : (DY.Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  rw [hnil]

theorem runMatches_clean0 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hgc : GhostAndSemMatchSetup compI7003 r S (gClean7003 mode cl₁ cl₃))
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    RunMatches compI7003 r S (gClean7003 mode cl₁ cl₃) (setupTrace r) (m0Of false) ev0
      (stepView (m0Of false) HonestSession.t4 false) none := by
  let g := gClean7003 mode cl₁ cl₃
  have cn := mkCommonNodes (mode := mode) (S := S) (pts := [tRnd 31 32]) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem2
  have hwf := hf.1.1
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨_, _, _, _, _, _, _, ho5, ho6, ho7⟩ :=
    Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.setup_secrets_7003 hf
  have hst_eq := setupTrace_eq_t4 ha hb hopk
  have ht4_b1 : HonestSession.t4 = b1_setupTr4 "alice" "bob" :=
    setupTrace_false_eq.symm.trans
      (Symbolic.Swarm.CREF.b1_setupTrace_eq r0 (by show "alice" ≠ "bob"; decide))
  have hrec_eq : received HonestSession.t4 [14, 15, 20, 21] =
      [dhPk (tRnd 10 32), setupPublic r 5, setupPublic r 6, setupPublic r 7] := by
    rw [ht4_b1, b1_setupPublic_5 r hwf.1, b1_setupPublic_6 r hwf.1, b1_setupPublic_7 r hwf.1]
    simp only [received, List.filterMap_cons, List.filterMap_nil, getMessageSentAt_eq_at?,
      setupTr4_net_at, b1_NetE, tRnd, randTerm]
    rfl
  let inp0 : VisEntry :=
    ⟨.recv, [dhPk (tRnd 10 32), setupPublic r 5, setupPublic r 6, setupPublic r 7], .bundle, none⟩
  let done0 := DY.Libsignal.Composed.Refinement.eventIdx
    DY.Libsignal.Composed.Refinement.isAliceDone HonestSession.t4 HonestSession.t5
  let drs0 : List VisEntry :=
    [rngEntry (randTerm 22 32)] ++ kyberCoinEntries (randTerm 23 32) ++
      [{ rngEntry HonestSession.dhsA with anchor := done0 }]
  have hvis0 : stepView (m0Of false) HonestSession.t4 false = inp0 :: (drs0 ++ []) := by
    rw [vis_m0_false, List.append_nil]; unfold visStep; rw [exposures_t4_t5, List.append_nil]
    simp only [m0Of, Bool.false_eq_true, ↓reduceIte, aliceVis, HonestSession.bh1, Option.toList, List.append_nil]
    have hnr0 : (newRandoms HonestSession.t4 HonestSession.t5).map (·.1) =
        [randTerm 22 32, randTerm 23 32, HonestSession.dhsA] := by rw [newRandoms_t4_t5]; rfl
    rw [hrec_eq, hnr0]; rfl
  refine ⟨rfl, rfl, trivial, hb.symm, by rw [hst_eq]; exact m0_ok_false, ⟨out0Raw, rfl⟩,
    by rw [hst_eq, vis_m0_false (DY.Libsignal.Composed.Refinement.runWrapped ev0), vis_m0_false false],
    inp0, drs0, [], hvis0, ?_, ?_, ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨rfl, ?_, by dsimp only [ev0]; rw [bun0Raw_eq]; decide +kernel⟩
    dsimp only [ev0]; rw [bun0Raw_eq]
    have hg4 : gamma compI7003 S g (dhPk (tRnd 10 32)) = bytesOf pk2Id := gamma_of_termAt cn.pk2
    have hg5 : gamma compI7003 S g (setupPublic r 5) = setup7003.spkSig := (hgc.2.1 r.spkSigTerm (by simp)).trans ho5
    have hg6 : gamma compI7003 S g (setupPublic r 6) = setup7003.kyberPk := (hgc.2.1 r.pqpkPubTerm (by simp)).trans ho6
    have hg7 : gamma compI7003 S g (setupPublic r 7) = setup7003.kyberPkSig := (hgc.2.1 r.pqpkSigTerm (by simp)).trans ho7
    refine ⟨by decide +kernel, by rw [hg4]; decide +kernel, by rw [hg5]; decide +kernel,
      by rw [hg6]; decide +kernel, by rw [hg7]; decide +kernel⟩
  · refine ⟨initCoinsPieces7003,
      fun p hp => bne_iff_ne.mp (List.all_eq_true.mp initCoinsPieces7003_spec.1 p hp),
      by dsimp only [ev0]; rw [coins0Raw_eq, initCoinsPieces7003_spec.2.1], ?_⟩
    dsimp only [initCoinsPieces7003, drs0]
    refine forall₂_append (forall₂_append ?_ ?_) ?_
    · refine .cons ⟨rfl, ?_⟩ .nil
      dsimp only [rngEntry, List.map]
      exact congrArg (· :: []) (gamma_of_termAt cn.r22)
    · have hr23_gam : gamma compI7003 S g (randTerm 23 32) = bytesOf r23Id := gamma_of_termAt cn.r23
      have hr23_len : (bytesOf r23Id).length = 32 := by decide
      unfold kyberCoinEntries
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro j hj
      have hok := List.all_eq_true.mp initCoinsPieces7003_spec.2.2 j hj
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      exact ⟨rfl, hok.1, randTerm 23 32, rfl, by rw [hr23_gam, hr23_len], by rw [hr23_gam]; exact hok.2⟩
    · refine .cons ⟨rfl, ?_⟩ .nil
      dsimp only [rngEntry, List.map]
      exact congrArg (· :: []) (gamma_of_termAt cn.dhsA)
  · dsimp only [OutputsMatch, ev0]; rw [out0Raw_eq]; rfl

theorem runMatches_clean1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId) (hsem2 : SemPinned2 S cl₁) :
    RunMatches compI7003 r S (gClean7003 mode cl₁ cl₃)
      ((m0Of false).next (setupTrace r)) (m1Clean cl₁) (ev1Of mode)
      (stepView (m1Clean cl₁) HonestSession.t5 true) (some (none, 7#32, 9#32)) := by
  let g := gClean7003 mode cl₁ cl₃
  have cn := mkCommonNodes (mode := mode) (S := S) (pts := [tRnd 31 32]) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem2
  obtain ⟨_, _, _, hout1, _⟩ := mkMsg1Nodes cn List.mem_cons_self
  obtain ⟨ha, hb, hopk, hregA, _⟩ := setup_ids_7003 hf
  obtain ⟨hs0, _⟩ := Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.setup_secrets_7003 hf
  have htr1 : (m0Of false).next (setupTrace r) = HonestSession.t5 := by
    rw [setupTrace_eq_t4 ha hb hopk, m0_next_false]
  have hw1 : DY.Libsignal.Composed.Refinement.runWrapped (ev1Of mode) = true := by
    unfold DY.Libsignal.Composed.Refinement.runWrapped
    cases mode with
    | false => dsimp [ev1Of, ev1_m1]; rw [out1M1Raw_eq]; decide +kernel
    | true => dsimp [ev1Of, ev1_m2]; rw [out1M2Raw_eq]; decide +kernel
  let inp1 : VisEntry := ⟨.pt, [tRnd 31 32], .single, none⟩
  let drs1 : List VisEntry := if cl₁ = 0 then [] else [rngEntry (randTerm 32 cl₁)]
  let out1 : VisEntry := ⟨.send, [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁], .preKeySend, none⟩
  have hvis1 : stepView (m1Clean cl₁) HonestSession.t5 true = inp1 :: (drs1 ++ [out1]) := by
    rw [vis_m1Clean, visEncStep, newRandoms_t5_t6Clean, lastSent_t5_t6Clean,
        exposures_t5_t6Clean, List.append_nil]
    unfold encDraws
    by_cases hn0 : cl₁ = 0 <;> simp [hn0, inp1, drs1, out1, tRnd, randTerm]
  refine ⟨by cases mode <;> rfl, by cases mode <;> rfl, by cases mode <;> trivial, trivial,
    by rw [htr1]; exact (m1Clean_props cl₁).2.1,
    by cases mode with | false => exact ⟨out1M1Raw, rfl⟩ | true => exact ⟨out1M2Raw, rfl⟩,
    by rw [htr1, hw1], inp1, drs1, [out1], hvis1, ?_, ?_, ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by cases mode <;> rfl, ?_⟩
    have hm0_gam : gamma compI7003 S g (tRnd 31 32) = (if mode then pt1M2Bytes else pt1M1Bytes) :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_randTerm_pos S g 31 32 (by decide)
    dsimp only [inp1, List.map]; rw [hm0_gam]
    cases mode with
    | false => dsimp [ev1Of, ev1_m1]; rw [pt1M1Raw_eq]
    | true => dsimp [ev1Of, ev1_m2]; rw [pt1M2Raw_eq]
  · by_cases hn0 : cl₁ = 0
    · simp only [drs1, hn0, ↓reduceIte]
      refine ⟨[], ?_, List.nil_prefix, List.Forall₂.nil⟩
      intro _ h; cases h
    · simp only [drs1, hn0, ↓reduceIte]
      have hc_eq : (ev1Of mode).coins = coins1Bytes := by
        cases mode with | false => exact coins1Raw_eq | true => exact coins1Raw_eq
      have hc_len : coins1Bytes.length = 64 := by decide
      refine ⟨[coins1Bytes.take cl₁], ?_, by rw [hc_eq, List.flatten_singleton]; exact List.take_prefix _ _, ?_⟩
      · intro p hp
        rcases List.mem_singleton.mp hp with rfl
        intro hempty
        have hlen := congrArg List.length hempty
        rw [List.length_take, hc_len, Nat.min_eq_left hsem2.le64] at hlen
        exact hn0 hlen
      · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
        dsimp only [rngEntry, List.map]
        exact congrArg (· :: [])
          (coins32_safe_and_gamma (mode := mode) (S := S) (pts := [tRnd 31 32]) (cl₃ := cl₃) hsem2.le64).2
  · dsimp only [OutputsMatch]
    have hek_gam := gamma_of_termAt cn.ek
    have hct_gam := gamma_of_termAt cn.ctKem
    have hmsg_gam := gamma_of_termAt hout1
    cases mode
    · dsimp only [ev1Of, ev1_m1]; rw [out1M1Raw_eq]
      refine ⟨out1, rfl, rfl, none, 7#32, 9#32, rfl, ?_⟩
      unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
      rw [hek_gam, hct_gam, hmsg_gam, hregA, hs0]; decide +kernel
    · dsimp only [ev1Of, ev1_m2]; rw [out1M2Raw_eq]
      refine ⟨out1, rfl, rfl, none, 7#32, 9#32, rfl, ?_⟩
      unfold DY.Libsignal.Composed.Refinement.ProtocolSetup.ikASecBytes
      rw [hek_gam, hct_gam, hmsg_gam, hregA, hs0]; decide +kernel

theorem explains_clean2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry}
    (mode : Bool) (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g₀ ss₀ vis₀ [.run ev0, .run (ev1Of mode)])
    (hsem2 : SemPinned2 S cl₁) :
    Explains compI7003 r S (gClean7003 mode cl₁ cl₃) (ssClean2 cl₁) (visClean2 cl₁)
      [.run ev0, .run (ev1Of mode)] := by
  obtain ⟨hgc, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 mode cl₁ cl₃ hf hex.1
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  refine ⟨hgc, ghostWF_clean2 mode cl₁ cl₃, modelRunWF_clean2 ha hb hopk cl₁ hsem2.1, ?_⟩
  have hnil : MatchesEventsAt compI7003 r S (gClean7003 mode cl₁ cl₃)
      (DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) (ev1Of mode))
      ((m1Clean cl₁).next ((m0Of false).next (setupTrace r))) [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h1 := matchesEvents_run1 (runMatches_clean1 mode cl₁ cl₃ hf hkpk hsem2) hnil
  rw [List.append_nil, ← ev0_nextBundleIds] at h1
  exact matchesEvents_run1 (runMatches_clean0 mode cl₁ cl₃ hf hgc hkpk hsem2) h1

theorem eq_cons_tail_of_head? {α : Type} {l : List α} {x : α} (h : l.head? = some x) :
    l = x :: l.tail := by
  cases l with
  | nil => cases h
  | cons a as => injection h with h; exact congrArg (· :: as) h

attribute [local irreducible] p1Of

theorem not_nextEventCollides_ev2_m1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m1]) :
    ¬ NextEventCollides compI7003 r S g ss vis [.run ev0, .run ev1_m1] ev2_m1 := by
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨_, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 false 0 0 hf hex.1
  obtain ⟨cl₁, hsem2⟩ := semPinned2_of_explains_m1_2 hf hex
  have hbd := bobDone_nil_of_explains_m1_2 hf hex
  have hhd : out1M1Bytes.head? = some wirePrekeyTag := by decide +kernel
  obtain ⟨body, hcons⟩ : ∃ body, out1M1Bytes = wirePrekeyTag :: body :=
    ⟨_, eq_cons_tail_of_head? hhd⟩
  have hin : ev2_m1.input = wirePrekeyTag :: body := out1M1Raw_eq.trans hcons
  have hp : parsePreKeyWire (wirePrekeyTag :: body) = some (p1Of false) := by
    rw [← hcons]; exact parse_out1Of false
  exact not_nextEventCollides_accepted_prekey rfl hin hp
    (by rintro ⟨ek, hek, _⟩; rw [hbd] at hek; cases hek)
    (not_preKeyStartCollidesOrRejects_of_clean
      (not_kyberMismatch_compI7003 r (p1Of false))
      (explains_clean2 false cl₁ 0 hf hex hsem2)
      (not_readCollisionCli_of_no_decrypt (by intro m hm; simp [ssClean2, m0Of, m1Clean] at hm; rcases hm with rfl | rfl <;> rfl))
      (by rw [← hcons]; exact xClean_mem false cl₁ 0 hf hkpk hsem2)
      (not_bobStartCollides_clean2 ha hb hopk false cl₁ hkpk hsem2))

theorem not_nextEventCollides_ev2_m2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g ss vis [.run ev0, .run ev1_m2]) :
    ¬ NextEventCollides compI7003 r S g ss vis [.run ev0, .run ev1_m2] ev2_m2 := by
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  obtain ⟨_, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 true 0 0 hf hex.1
  obtain ⟨cl₁, hsem2⟩ := semPinned2_of_explains_m2_2 hf hex
  have hbd := bobDone_nil_of_explains_m2_2 hf hex
  have hhd : out1M2Bytes.head? = some wirePrekeyTag := by decide +kernel
  obtain ⟨body, hcons⟩ : ∃ body, out1M2Bytes = wirePrekeyTag :: body :=
    ⟨_, eq_cons_tail_of_head? hhd⟩
  have hin : ev2_m2.input = wirePrekeyTag :: body := out1M2Raw_eq.trans hcons
  have hp : parsePreKeyWire (wirePrekeyTag :: body) = some (p1Of true) := by
    rw [← hcons]; exact parse_out1Of true
  exact not_nextEventCollides_accepted_prekey rfl hin hp
    (by rintro ⟨ek, hek, _⟩; rw [hbd] at hek; cases hek)
    (not_preKeyStartCollidesOrRejects_of_clean
      (not_kyberMismatch_compI7003 r (p1Of true))
      (explains_clean2 true cl₁ 0 hf hex hsem2)
      (not_readCollisionCli_of_no_decrypt (by intro m hm; simp [ssClean2, m0Of, m1Clean] at hm; rcases hm with rfl | rfl <;> rfl))
      (by rw [← hcons]; exact xClean_mem true cl₁ 0 hf hkpk hsem2)
      (not_bobStartCollides_clean2 ha hb hopk true cl₁ hkpk hsem2))

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
