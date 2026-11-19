/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix
import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysisAux

/-!
# Double-Leak Refutation on `rcprTrace` (`not_explains_full`)

Proves that no model execution `Explains rcprI0 r S g ss vis rcprTrace` exists under
`rcprCompFitsPinned`:
1. Splitting `rcprTrace` after Calls `0..4` (`rcprTrace.take 5`) yields `tr₄ := runTrace r ss₅`
   satisfying `AliceLeakInv r stP tr₄`, where `stP` is Alice's unique current `TRState` snapshot
   after Call 4 (`messageDecrypt` on `m1`, which rotated Alice's DH ratchet secret away from
   `dhs_A0 = rcprLeakKey1`).
2. Because `rcprLeakKey1` (`32` bytes) differs from `ikA = rcprSetup.aliceId` and every `32`-byte
   DR key of `stP` (raw and `clamp`ed), Leak 1 (`.env (.leak "alice" rcprLeakKey1)`) is forced to
   be `Step.exposeSpqr "alice" stateIdx₁`, pinning `(gamma rcprI0 S g stP.spqr).length = 32` and
   preserving `AliceLeakInv r stP`.
3. Because `rcprSpqrState1` has length `3888 ≠ 32`, Leak 2 (`.env (.leak "alice" rcprSpqrState1)`)
   is likewise forced to be `Step.exposeSpqr "alice" stateIdx₂`, forcing
   `(gamma rcprI0 S g stP.spqr).length = 3888` — contradiction!
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysis

open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   secretBytes runTrace Explains)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained (rcprTrace_take5)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprI0 rcprHooks0 rcprCompFitsPinned
   rcprLeakKey1 rcprLeakKey1_length rcprSpqrState1 rcprSpqrState1_length
   rcprStopEv rcprTrace)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix
  (rcprAliceRk4_length rcprAliceDhs4_length rcprAliceCks4_length
   rcprAliceCk0_length rcprAliceCk1_length
   rcprLeakKey1_ne_aliceRk4 rcprLeakKey1_ne_aliceDhs4 rcprLeakKey1_ne_aliceCks4
   rcprLeakKey1_ne_aliceCk0 rcprLeakKey1_ne_aliceCk1
   rcprLeakKey1_ne_clamp_aliceRk4 rcprLeakKey1_ne_clamp_aliceDhs4
   rcprLeakKey1_ne_clamp_aliceCks4 rcprLeakKey1_ne_clamp_aliceCk0
   rcprLeakKey1_ne_clamp_aliceCk1
   no_skippedKeyStored_take5 alice_unique_snapshot_take5 alice_pin_current_snapshot_here)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysisAux
  (explains_append_split onlyAliceIk_setupTrace onlyAliceIk_of_runOnly_matchesEventsAt
   AliceLeakInv not_double_alice_leak_of_ne_len)

private theorem rcprTrace_split :
    rcprTrace = rcprTrace.take 5 ++
      [ .env (.leak "alice" rcprLeakKey1),
        .env (.leak "alice" rcprSpqrState1),
        .run rcprStopEv ] := rfl

private theorem take5_all_run : ∀ e ∈ rcprTrace.take 5, ∃ rev, e = .run rev := by
  intro e he
  simp only [rcprTrace_take5, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

private theorem rcprSetup_aliceId_length : rcprSetup.aliceId.length = 32 := by decide

private theorem rcprLeakKey1_ne_aliceId : rcprLeakKey1 ≠ rcprSetup.aliceId := by decide

theorem not_explains_full
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r) :
    ¬ Explains rcprI0 r S g ss vis rcprTrace := by
  intro hex
  have hex' : Explains rcprI0 r S g ss vis
      (rcprTrace.take 5 ++
        [ .env (.leak "alice" rcprLeakKey1),
          .env (.leak "alice" rcprSpqrState1),
          .run rcprStopEv ]) := rcprTrace_split ▸ hex
  obtain ⟨ss₅, ss_rem, vis₅, vis_rem, initIds₄, _, _, hex5, hwf_rem, hm_rem⟩ :=
    explains_append_split hex'
  have halice : r.alice = "alice" := hfit.1.2.2.2.1.1
  have hbob : r.bob = "bob" := hfit.1.2.2.2.1.2
  have hIk_eq : secretBytes r 0 = rcprSetup.aliceId := hfit.1.1.2.2.2.2.2.2.1
  obtain ⟨idxP, stP, hatP, hmaxP, hrole, hRk, hDhs, hCks, hRecv⟩ :=
    alice_unique_snapshot_take5 hfit hex5
  have hinv4 : AliceLeakInv r stP (runTrace r ss₅) :=
    { onlyIk := onlyAliceIk_of_runOnly_matchesEventsAt hex5.2.2.2 take5_all_run
        (onlyAliceIk_setupTrace halice hbob)
      noSkipped := no_skippedKeyStored_take5 hfit hex5
      uniqueCurr := fun _ _ hget hcur =>
        (alice_pin_current_snapshot_here hatP hmaxP hrole hget hcur).2 }
  exact not_double_alice_leak_of_ne_len hinv4 hwf_rem hm_rem hex5.1 halice hbob
    (by rw [hIk_eq]; exact rcprSetup_aliceId_length)
    (by rw [hRk]; exact rcprAliceRk4_length)
    (by rw [hDhs]; exact rcprAliceDhs4_length)
    (by rw [hCks]; exact rcprAliceCks4_length)
    (fun c hc => by
      rcases hRecv c hc with h | h
      · rw [h]; exact rcprAliceCk0_length
      · rw [h]; exact rcprAliceCk1_length)
    rcprLeakKey1_length
    (by rw [rcprSpqrState1_length]; decide)
    (by rw [hIk_eq]; exact rcprLeakKey1_ne_aliceId)
    (by rw [hRk]; exact ⟨rcprLeakKey1_ne_aliceRk4, rcprLeakKey1_ne_clamp_aliceRk4⟩)
    (by rw [hDhs]; exact ⟨rcprLeakKey1_ne_aliceDhs4, rcprLeakKey1_ne_clamp_aliceDhs4⟩)
    (by rw [hCks]; exact ⟨rcprLeakKey1_ne_aliceCks4, rcprLeakKey1_ne_clamp_aliceCks4⟩)
    (fun c hc => by
      rcases hRecv c hc with h | h
      · rw [h]; exact ⟨rcprLeakKey1_ne_aliceCk0, rcprLeakKey1_ne_clamp_aliceCk0⟩
      · rw [h]; exact ⟨rcprLeakKey1_ne_aliceCk1, rcprLeakKey1_ne_clamp_aliceCk1⟩)

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.LeakStepAnalysis
