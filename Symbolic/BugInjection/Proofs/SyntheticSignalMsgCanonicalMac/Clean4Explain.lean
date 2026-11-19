/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
public import Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac.NoExplains
import DY.Bytes.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Random
import DY.Actions.Network
import DY.Actions.ProtocolEvent
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
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
# Clean 4-Step Prefix (`m3Clean`) for `SignalMsgCanonicalMac` (`Clean4Explain.lean`)

Extends `(gClean7003 true cl₁ cl₃, ssClean3 cl₁, visClean3 cl₁)` with `m3Clean cl₃`
(Bob's whisper reply `ev3_m2`), proving `Explains` on `[.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2]`
and closed-form trace/state/salt/visibility projections on `t8Clean cl₁ cl₃` and `visClean4 cl₁ cl₃`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac

unseal DY.Bytes

open ByteSpecs (hmacWith)
open scoped DY.Libsignal.Composed
open DY (ExecTrace)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.TripleRatchet
  (TRState parseTrSignalMsg trHonestWireMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry VisEventKind
   gamma randTerm setupTrace runSteps runTrace newRandoms lastSent pendingPreKey
   rngEntry encDraws encSendEntry exposures stepView honestKeysOf runWrapped
   storedSecrets storedStates honestSaltsOf plaintextTerms
   GhostAndSemMatchSetup GhostWF ModelRunWF
   BytesMatchEntry DrawsMatch OutputsMatch RunMatches MatchesEventsAt Explains)
open Symbolic.Proofs.Tests.Shared.Composed
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encMsg encSig parse_encMsg)
open Symbolic.Proofs.Tests.CliNonvacuity.Defs (matchesEvents_run1)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (m0Of setupTrace_false_eq m0_next_false modelRunWF_msPrefix2)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (length_append_entry_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (tRnd)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003 (compI7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003 (compFitsPinned7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003 (setup_ids_7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.PrefixPins7003
  (SemPinned4_M2 encTrCl if_pos')
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceState7003
  (NoSkippedKeys noSkippedKeys_encTrCl)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Data
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Memo7003Combinators (gamma_of_termAt)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes
  (isAliceWire isAliceWire_tTrW_dhPk_rnd gClean7003 gClean7003_σ_length
   o1Pure stA0Pure key0Pure stA1Pure encMsg1Pure
   dhsBPure stB1Pure key3Pure stB2Pure encMsg3Pure encSig3Pure
   coins48_safe_and_gamma CommonNodes mkCommonNodes M2Nodes mkM2Nodes)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003States
  (ghostAndSemMatchSetup_gClean7003 pqSecrets7003)
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean2BobStart7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Clean3BobStart7003

attribute [local irreducible] Symbolic.BugInjection.hexBytes
attribute [local irreducible] ByteSpecs.hmacWith

def m3Clean (cl₃ : Nat) : Step := .messageEncrypt "bob" 46 cl₃ 49
def ssClean4 (cl₁ cl₃ : Nat) : List Step := [m0Of false, m1Clean cl₁, m2Clean, m3Clean cl₃]
def t8Clean (cl₁ cl₃ : Nat) : ExecTrace := encTrCl (t7Clean cl₁) "bob" 46 (stB1Pure cl₁) cl₃
def visClean4 (cl₁ cl₃ : Nat) : List VisEntry :=
  visClean3 cl₁ ++ stepView (m3Clean cl₃) (t7Clean cl₁) false

theorem m3Clean_props (cl₁ cl₃ : Nat) :
    (m3Clean cl₃).PreCond (t7Clean cl₁) ∧
    (m3Clean cl₃).ok (t7Clean cl₁) = true ∧
    (m3Clean cl₃).next (t7Clean cl₁) = t8Clean cl₁ cl₃ ∧
    (t8Clean cl₁ cl₃).length = (t7Clean cl₁).length + 7 ∧
    t7Clean cl₁ ≤ t8Clean cl₁ cl₃ ∧
    (t8Clean cl₁ cl₃).getMessageSentAt 49 =
      some (DY.Spqr.spqrSend (stB1Pure cl₁).spqr (randTerm ((t7Clean cl₁).length + 1) cl₃)).2.1 ∧
    lastSent (t7Clean cl₁) (t8Clean cl₁ cl₃) =
      some (encMsg (stB1Pure cl₁) (randTerm ((t7Clean cl₁).length + 1) cl₃)
        (DY.Spqr.spqrSend (stB1Pure cl₁).spqr (randTerm ((t7Clean cl₁).length + 1) cl₃)).2.1
        (randTerm (t7Clean cl₁).length 32)) ∧
    exposures (t7Clean cl₁) (t8Clean cl₁ cl₃) = [] ∧
    newRandoms (t7Clean cl₁) (t8Clean cl₁ cl₃) =
      [(randTerm (t7Clean cl₁).length 32, 32), (randTerm ((t7Clean cl₁).length + 1) cl₃, cl₃)] :=
  encTrCl_props (tr := t7Clean cl₁) (me := "bob") (stH := 46) (pqH := 49)
    (st := stB1Pure cl₁) cl₃ (t7Clean_at_46_stB1 cl₁)
    (by rw [t7Clean_length]) (by rw [t7Clean_length])
    (by show (0 : UInt32) ≠ DY.Libsignal.TripleRatchet.u32Max; decide)

theorem t8Clean_length (cl₁ cl₃ : Nat) : (t8Clean cl₁ cl₃).length = 54 := by
  rw [(m3Clean_props cl₁ cl₃).2.2.2.1, t7Clean_length]

theorem t7Clean_le_t8Clean (cl₁ cl₃ : Nat) : t7Clean cl₁ ≤ t8Clean cl₁ cl₃ :=
  (m3Clean_props cl₁ cl₃).2.2.2.2.1

theorem lastSent_t7Clean_t8Clean (cl₁ cl₃ : Nat) :
    lastSent (t7Clean cl₁) (t8Clean cl₁ cl₃) = some (encMsg3Pure cl₁ cl₃) := by
  have h := (m3Clean_props cl₁ cl₃).2.2.2.2.2.2.1
  have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
  have h48 : (t7Clean cl₁).length + 1 = 48 := by rw [t7Clean_length]
  rw [h48, t7Clean_length, hr, hr] at h
  exact h

theorem newRandoms_t7Clean_t8Clean (cl₁ cl₃ : Nat) :
    newRandoms (t7Clean cl₁) (t8Clean cl₁ cl₃) =
      [(randTerm 47 32, 32), (randTerm 48 cl₃, cl₃)] := by
  simpa [t7Clean_length] using (m3Clean_props cl₁ cl₃).2.2.2.2.2.2.2.2

theorem exposures_t7Clean_t8Clean (cl₁ cl₃ : Nat) :
    exposures (t7Clean cl₁) (t8Clean cl₁ cl₃) = [] :=
  (m3Clean_props cl₁ cl₃).2.2.2.2.2.2.2.1

theorem vis_m3Clean (cl₁ cl₃ : Nat) :
    stepView (m3Clean cl₃) (t7Clean cl₁) false =
      encDraws [(randTerm 47 32, 32), (randTerm 48 cl₃, cl₃)] ++
      [⟨.send, [encMsg3Pure cl₁ cl₃], .whisper, none⟩] := by
  unfold stepView
  rw [(m3Clean_props cl₁ cl₃).2.1]
  dsimp only [m3Clean, ↓reduceIte]
  change encDraws (newRandoms (t7Clean cl₁) ((m3Clean cl₃).next (t7Clean cl₁))) ++
      encSendEntry (t7Clean cl₁) ((m3Clean cl₃).next (t7Clean cl₁)) 46 false ++
      exposures (t7Clean cl₁) ((m3Clean cl₃).next (t7Clean cl₁)) = _
  rw [(m3Clean_props cl₁ cl₃).2.2.1, exposures_t7Clean_t8Clean, List.append_nil,
      newRandoms_t7Clean_t8Clean]
  unfold encSendEntry
  rw [lastSent_t7Clean_t8Clean, pendingPreKey_t7Clean_46]

theorem runTrace_ssClean4 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat) :
    runTrace r (ssClean4 cl₁ cl₃) = t8Clean cl₁ cl₃ := by
  unfold runTrace ssClean4
  rw [setupTrace_eq_t4 ha hb hopk]
  dsimp only [runSteps]
  rw [m0_next_false, (m1Clean_props cl₁).2.2.1, m2Clean_next, (m3Clean_props cl₁ cl₃).2.2.1]

theorem storedSecrets_t8Clean (cl₁ cl₃ : Nat) :
    storedSecrets (t8Clean cl₁ cl₃) = pqSecrets7003 := by
  have hc : storedSecrets (t8Clean cl₁ cl₃) = storedSecrets (t7Clean cl₁) := by
    unfold t8Clean encTrCl; simp only [storedSecrets_append]; repeat erw [List.append_nil]
  exact hc.trans (storedSecrets_t7Clean cl₁)

theorem storedStates_t8Clean {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat) :
    storedStates r (t8Clean cl₁ cl₃) =
      [⟨"alice", stA0Pure⟩, ⟨"alice", stA1Pure cl₁⟩,
       ⟨"bob", stB1Pure cl₁⟩, ⟨"bob", stB2Pure cl₁ cl₃⟩] := by
  have ht4 : (setupTrace r).length = 22 := by
    rw [setupTrace_eq_t4 ha hb hopk, HonestSession.t4_length]
  unfold t8Clean encTrCl; dsimp only
  repeat rw [storedStates_append _ _ _
    (by simp -failIfUnchanged only [length_append_entry_eq, ht4, t7Clean_length]; omega)]
  rw [storedStates_t7Clean ha hb hopk, t7Clean_length]
  rfl

theorem noSkippedKeys_t8Clean (cl₁ cl₃ : Nat) : NoSkippedKeys (t8Clean cl₁ cl₃) :=
  noSkippedKeys_encTrCl (noSkippedKeys_t7Clean cl₁)

theorem honestSaltsOf_ssClean4 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat) :
    honestSaltsOf r (ssClean4 cl₁ cl₃) =
      [DY.Spqr.zeroKey, key0Pure, key3Pure cl₁ cl₃] := by
  rw [honestSaltsOf_eq_r0 ha hb hopk]
  have h1 := (m1Clean_props cl₁).2.2.1
  have h2 := m2Clean_next cl₁
  have h3 := (m3Clean_props cl₁ cl₃).2.2.1
  have hpq1 : (t6Clean cl₁).getMessageSentAt 33 = some key0Pure := by
    have h := (m1Clean_props cl₁).2.2.2.2.2.1
    have hr : ∀ t n, randTerm t n = tRnd t n := fun _ _ => rfl
    have h32 : HonestSession.t5.length + 1 = 32 := by rw [HonestSession.t5_length]
    rw [h32, hr, Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Dag7003Nodes.spqrSend_stA0_key] at h
    exact h
  have hpq3 : (t8Clean cl₁ cl₃).getMessageSentAt 49 = some (key3Pure cl₁ cl₃) := by
    have h := (m3Clean_props cl₁ cl₃).2.2.2.2.2.1
    have h48 : (t7Clean cl₁).length + 1 = 48 := by rw [t7Clean_length]
    rw [h48] at h; exact h
  dsimp only [m1Clean, m2Clean, m3Clean] at h1 h2 h3
  unfold honestSaltsOf ssClean4 m0Of m1Clean m2Clean m3Clean
  simp only [Bool.false_eq_true, ↓reduceIte, honestKeysOf,
    Step.publishedSpqrKey?, DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx,
    DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx]
  rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq,
      show (Step.aliceStart "alice" "bob" 4 6 HonestSession.bh1).next HonestSession.t4 =
        HonestSession.t5 from m0_next_false,
      h1, h2, h3, HonestSession.t5_length, t7Clean_length]
  simp only [Nat.reduceAdd, ↓reduceIte, hpq1, hpq3]
  rfl

theorem plaintextTerms_visClean4 (cl₁ cl₃ : Nat) :
    plaintextTerms (visClean4 cl₁ cl₃) = [tRnd 31 32, tRnd 47 32] := by
  have h3 := plaintextTerms_visClean3 cl₁
  unfold plaintextTerms at h3
  unfold plaintextTerms visClean4
  rw [List.filter_append, List.flatMap_append, h3, vis_m3Clean,
      List.filter_append, List.flatMap_append]
  unfold encDraws
  by_cases hcl0 : cl₃ = 0 <;> simp [hcl0, rngEntry, tRnd, randTerm]

theorem sendTerms_visClean4 (cl₁ cl₃ : Nat) :
    (((visClean4 cl₁ cl₃).filter (·.kind == .send)).flatMap (·.terms)) =
      [o1Pure.ek, o1Pure.ct, encMsg1Pure cl₁, encMsg3Pure cl₁ cl₃] := by
  unfold visClean4
  rw [List.filter_append, List.flatMap_append, sendTerms_visClean3, vis_m3Clean,
      List.filter_append, List.flatMap_append]
  unfold encDraws
  by_cases hcl0 : cl₃ = 0 <;> simp [hcl0, rngEntry]

theorem ghostWF_clean4 (cl₁ cl₃ : Nat) :
    GhostWF (gClean7003 true cl₁ cl₃) (visClean4 cl₁ cl₃) := by
  have hg3 := ghostWF_clean3 true cl₁ cl₃
  refine ⟨?_, hg3.2.1, ?_⟩
  · intro v hv hvk ts n hn hmem
    unfold visClean4 at hv
    rcases List.mem_append.mp hv with hv3 | hv4
    · exact hg3.1 v hv3 hvk ts n hn hmem
    · rw [vis_m3Clean] at hv4
      unfold encDraws at hv4
      by_cases hcl0 : cl₃ = 0 <;> simp [hcl0, rngEntry] at hv4
      · rcases hv4 with rfl | rfl <;> cases hvk
      · rcases hv4 with rfl | rfl | rfl
        · cases hvk
        · simp only [List.mem_singleton] at hmem
          have hts := (Symbolic.Swarm.COMPOSED.CompTrace.mkRand_inj hmem).1
          exact gClean7003_σ_length (by omega) (by omega)
        · cases hvk
  · intro v hv hvk
    unfold visClean4 at hv
    rcases List.mem_append.mp hv with hv3 | hv4
    · exact hg3.2.2 v hv3 hvk
    · rw [vis_m3Clean] at hv4
      unfold encDraws at hv4
      have hsend : v = ⟨.send, [encMsg3Pure cl₁ cl₃], .whisper, none⟩ := by
        simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
          List.not_mem_nil, or_false] at hv4
        rcases hv4 with rfl | ⟨_, _, rfl⟩ | rfl
        · cases hvk
        · cases hvk
        · rfl
      subst hsend
      refine ⟨(fun h => nomatch h), fun _ msg pm hterms hparse => ?_⟩
      simp only [List.cons.injEq, and_true] at hterms; subst hterms
      have hp : parseTrSignalMsg (encMsg3Pure cl₁ cl₃) = some (encSig3Pure cl₁ cl₃) :=
        parse_encMsg _ _ _ _
      rw [hp] at hparse; injection hparse with hparse; subst hparse
      have hdhs : (stB1Pure cl₁).dhs = tRnd 38 32 := rfl
      dsimp only [gClean7003, encSig3Pure, encSig, trHonestWireMsg]
      rw [hdhs]; erw [isAliceWire_tTrW_dhPk_rnd]; rfl

theorem modelRunWF_clean4 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob") (hopk : r.withOpk = false) (cl₁ cl₃ : Nat)
    (hcl₁ : cl₁ = 0 ∨ cl₁ = 32 ∨ cl₁ = 64) (hcl₃ : cl₃ = 0 ∨ cl₃ = 32 ∨ cl₃ = 64) :
    ModelRunWF r (ssClean4 cl₁ cl₃) := by
  rw [modelRunWF_iff_r0 ha hb hopk]
  obtain ⟨hiscur0, hdom0, ⟨hm0_ok, hm0_loc, _⟩, _⟩ := modelRunWF_msPrefix2 false
  refine ⟨hiscur0, hdom0, ?_, ?_⟩
  · dsimp only [ssClean4, DY.Libsignal.Composed.Refinement.StepsWF]
    refine ⟨hm0_ok, hm0_loc, ?_⟩
    rw [show setupTrace r0 = HonestSession.t4 from setupTrace_false_eq, m0_next_false]
    refine ⟨(m1Clean_props cl₁).1, ⟨hcl₁, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [HonestSession.t5_length])⟩, ?_⟩
    rw [(m1Clean_props cl₁).2.2.1]
    refine ⟨m2Clean_preCond cl₁, trivial, ?_⟩
    rw [m2Clean_next]
    exact ⟨(m3Clean_props cl₁ cl₃).1, ⟨hcl₃, Or.inl (by unfold DY.Libsignal.Composed.Refinement.encryptOwnSpqrKeyIdx; rw [t7Clean_length])⟩, trivial⟩
  · intro i j si sj p k b hij hmi hmj hli _ hlj
    rcases i with _ | _ | _ | _ | i
    · simp only [ssClean4, List.getElem?_cons_zero, Option.some.injEq] at hmi; subst hmi; cases hli
    · rcases j with _ | _ | _ | _ | j <;> try omega
      · simp only [ssClean4, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmj
        subst hmj; cases hlj
      · simp only [ssClean4, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmi hmj
        subst hmi; subst hmj
        dsimp only [m1Clean, m3Clean, DY.Libsignal.Composed.Refinement.Step.stateLoad?] at hli hlj
        simp only [Option.some.injEq, Prod.mk.injEq] at hli hlj
        omega
      · simp [ssClean4] at hmj
    · simp only [ssClean4, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hmi
      subst hmi; cases hli
    · rcases j with _ | _ | _ | _ | j <;> try omega
      simp [ssClean4] at hmj
    · simp [ssClean4] at hmi

theorem runMatches_clean3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hkpk : S.kemPk (bytesOf pqskBId) = bytesOf pqpkId)
    (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    RunMatches compI7003 r S (gClean7003 true cl₁ cl₃)
      (m2Clean.next ((m1Clean cl₁).next ((m0Of false).next (setupTrace r)))) (m3Clean cl₃) ev3_m2
      (stepView (m3Clean cl₃) (t7Clean cl₁) false) (some (none, 7#32, 9#32)) := by
  let g := gClean7003 true cl₁ cl₃
  let pts := [tRnd 31 32, tRnd 47 32]
  have cn := mkCommonNodes (mode := true) (S := S) (pts := pts) (cl₁ := cl₁) (cl₃ := cl₃) hkpk hsem4.1
  have mn := mkM2Nodes cn hsem4 List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  have htr3 : m2Clean.next ((m1Clean cl₁).next ((m0Of false).next (setupTrace r))) = t7Clean cl₁ := by
    rw [setupTrace_eq_t4 ha hb hopk, m0_next_false, (m1Clean_props cl₁).2.2.1, m2Clean_next]
  have hw3 : runWrapped ev3_m2 = false := by
    unfold runWrapped; dsimp only [ev3_m2]; rw [out3M2Raw_eq, out3M2_split_eq.1]; decide
  let inp3 : VisEntry := ⟨.pt, [tRnd 47 32], .single, none⟩
  let drs3 : List VisEntry := if cl₃ = 0 then [] else [rngEntry (randTerm 48 cl₃)]
  let out3 : VisEntry := ⟨.send, [encMsg3Pure cl₁ cl₃], .whisper, none⟩
  have hvis3 : stepView (m3Clean cl₃) (t7Clean cl₁) false = inp3 :: (drs3 ++ [out3]) := by
    rw [vis_m3Clean]; unfold encDraws
    by_cases hn0 : cl₃ = 0 <;> simp [hn0, inp3, drs3, out3, tRnd, randTerm]
  refine ⟨rfl, rfl, trivial, trivial,
    by rw [htr3]; exact (m3Clean_props cl₁ cl₃).2.1,
    ⟨out3M2Raw, rfl⟩,
    by rw [htr3, hw3], inp3, drs3, [out3], hvis3, ?_, ?_, ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨rfl, ?_⟩
    have hm3_gam : gamma compI7003 S g (tRnd 47 32) = pt3M2Bytes :=
      Symbolic.BugInjection.Proofs.SyntheticRecvCommon.Gamma7003.gamma_randTerm_pos S g 47 32 (by decide)
    dsimp only [inp3, List.map, ev3_m2]; rw [hm3_gam, pt3M2Raw_eq]
  · by_cases hn0 : cl₃ = 0
    · simp only [drs3, hn0, ↓reduceIte]
      refine ⟨[], ?_, List.nil_prefix, List.Forall₂.nil⟩
      intro _ h; cases h
    · simp only [drs3, hn0, ↓reduceIte]
      have hc_eq : ev3_m2.coins = coins3M2Bytes := coins3M2Raw_eq
      have hc_len : coins3M2Bytes.length = 64 := by decide
      refine ⟨[coins3M2Bytes.take cl₃], ?_, by rw [hc_eq, List.flatten_singleton]; exact List.take_prefix _ _, ?_⟩
      · intro p hp
        rcases List.mem_singleton.mp hp with rfl
        intro hempty
        have hlen := congrArg List.length hempty
        rw [List.length_take, hc_len, Nat.min_eq_left hsem4.le64] at hlen
        exact hn0 hlen
      · refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
        dsimp only [rngEntry, List.map]
        exact congrArg (· :: [])
          (coins48_safe_and_gamma (mode := true) (S := S) (pts := pts) (cl₁ := cl₁) hsem4.le64).2
  · dsimp only [OutputsMatch, ev3_m2]; rw [out3M2Raw_eq]
    refine ⟨out3, rfl, rfl, encMsg3Pure cl₁ cl₃, rfl, ?_⟩
    rw [out3M2_split_eq.1, gamma_of_termAt mn.out3]; decide +kernel

theorem explains_clean4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g₀ : Ghost} {ss₀ : List Step} {vis₀ : List VisEntry}
    (cl₁ cl₃ : Nat)
    (hf : compFitsPinned7003 setup7003 compI7003 r)
    (hex : Explains compI7003 r S g₀ ss₀ vis₀ [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2])
    (hsem4 : SemPinned4_M2 S cl₁ cl₃) :
    Explains compI7003 r S (gClean7003 true cl₁ cl₃) (ssClean4 cl₁ cl₃) (visClean4 cl₁ cl₃)
      [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2] := by
  obtain ⟨hgc, hkpk⟩ := ghostAndSemMatchSetup_gClean7003 true cl₁ cl₃ hf hex.1
  obtain ⟨ha, hb, hopk, _⟩ := setup_ids_7003 hf
  refine ⟨hgc, ghostWF_clean4 cl₁ cl₃, modelRunWF_clean4 ha hb hopk cl₁ cl₃ hsem4.1.1 hsem4.2.1, ?_⟩
  unfold DY.Libsignal.Composed.Refinement.MatchesEvents ssClean4
  have hnb1 : DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) ev1_m2 =
      some (none, 7#32, 9#32) := rfl
  have hnb2 : DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) ev2_m2 =
      some (none, 7#32, 9#32) := rfl
  have hnil : MatchesEventsAt compI7003 r S (gClean7003 true cl₁ cl₃)
      (DY.Libsignal.Composed.Refinement.nextBundleIds (some (none, 7#32, 9#32)) ev3_m2)
      ((m3Clean cl₃).next (m2Clean.next ((m1Clean cl₁).next ((m0Of false).next (setupTrace r)))))
      [] [] [] :=
    MatchesEventsAt.nil (fun _ h => nomatch h)
  have h3 := matchesEvents_run1 (runMatches_clean3 cl₁ cl₃ hf hkpk hsem4) hnil
  rw [List.append_nil, ← hnb2] at h3
  have h2 := matchesEvents_run1 (runMatches_clean2 true cl₁ cl₃ hf hkpk hsem4.1) h3
  rw [← hnb1] at h2
  have h1 := matchesEvents_run1 (runMatches_clean1 true cl₁ cl₃ hf hkpk hsem4.1) h2
  rw [← ev0_nextBundleIds] at h1
  simpa [visClean4, visClean3, visClean2, List.append_assoc, ev1Of, ev2Of] using
    matchesEvents_run1 (runMatches_clean0 true cl₁ cl₃ hf hgc hkpk hsem4.1) h1

end Symbolic.BugInjection.Proofs.SyntheticSignalMsgCanonicalMac
