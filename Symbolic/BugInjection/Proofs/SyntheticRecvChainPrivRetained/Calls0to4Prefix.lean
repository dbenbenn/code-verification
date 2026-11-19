/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Parse
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Schedule
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Gamma
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4PrefixAux
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Inv0to2
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Inv3to4
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import DY.Trace.Basic
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad

/-!
# Public Calls `0..4` Prefix Inversion API (`Calls0to4Prefix.lean`)

Exports:
1. For `LeakStepAnalysis.lean` on `Explains rcprI0 r S g ss vis (rcprTrace.take 5)`:
   - Reducible `rcprAliceRk4`, `rcprAliceDhs4`, `rcprAliceCks4`, `rcprAliceCk0`, `rcprAliceCk1`
     (re-exported from `Calls0to4Prefix.Gamma`) together with `decide`-proved `.length = 32`,
     `≠ rcprLeakKey1`, and `clamp _ ≠ rcprLeakKey1` lemmas.
   - `pkiUnchanged_take5`, `pki_pin_st`, and `gamma_setup_secret_take5`.
   - `no_skippedKeyStored_take5`.
   - `alice_unique_snapshot_take5` and `alice_pin_current_snapshot`.
2. For `RecvNoCollision.lean` on `Explains rcprI0 r S g ss vis (rcprTrace.take k)` (`k ≤ 5`):
   - Clean 5-step schedule & ghost re-exports (`ValidCoinLens`, `cleanCallSteps`, `ssClean`,
     `gClean`, `trClean1..trClean5`, `stA1Clean`, `stB2Clean`, `stB3Clean`, `stA4Clean`,
     `m0Clean`, `m1Clean`, `s0_next_ok..s4_next_ok`, `ghostAndSemMatchSetup_gClean`).
   - `extract_clean_prefix` (`k ≤ 5`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (ExecTrace Traceful)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma clamp ecKey pubBytes secretBytes preKeyWire
   runTrace GhostAndSemMatchSetup Explains)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry at?_le_some)
open Symbolic.Swarm.CREF (bks_stored_of_getLocalState isCurrentSnapshot_false_of_later)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB spkB pqskB o1)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned rcprLeakKey1)

/-! ## 1. Concrete `decide`-Proved Facts for `rcprAliceRk4 .. rcprAliceCk1` -/

theorem rcprAliceRk4_length : rcprAliceRk4.length = 32 := by decide
theorem rcprAliceDhs4_length : rcprAliceDhs4.length = 32 := by decide
theorem rcprAliceCks4_length : rcprAliceCks4.length = 32 := by decide
theorem rcprAliceCk0_length : rcprAliceCk0.length = 32 := by decide
theorem rcprAliceCk1_length : rcprAliceCk1.length = 32 := by decide

theorem rcprAliceRk4_ne_leakKey1 : rcprAliceRk4 ≠ rcprLeakKey1 := by decide
theorem rcprAliceDhs4_ne_leakKey1 : rcprAliceDhs4 ≠ rcprLeakKey1 := by decide
theorem rcprAliceCks4_ne_leakKey1 : rcprAliceCks4 ≠ rcprLeakKey1 := by decide
theorem rcprAliceCk0_ne_leakKey1 : rcprAliceCk0 ≠ rcprLeakKey1 := by decide
theorem rcprAliceCk1_ne_leakKey1 : rcprAliceCk1 ≠ rcprLeakKey1 := by decide

theorem rcprLeakKey1_ne_aliceRk4 : rcprLeakKey1 ≠ rcprAliceRk4 := by decide
theorem rcprLeakKey1_ne_aliceDhs4 : rcprLeakKey1 ≠ rcprAliceDhs4 := by decide
theorem rcprLeakKey1_ne_aliceCks4 : rcprLeakKey1 ≠ rcprAliceCks4 := by decide
theorem rcprLeakKey1_ne_aliceCk0 : rcprLeakKey1 ≠ rcprAliceCk0 := by decide
theorem rcprLeakKey1_ne_aliceCk1 : rcprLeakKey1 ≠ rcprAliceCk1 := by decide

theorem clamp_rcprAliceRk4_ne_leakKey1 : clamp rcprAliceRk4 ≠ rcprLeakKey1 := by decide
theorem clamp_rcprAliceDhs4_ne_leakKey1 : clamp rcprAliceDhs4 ≠ rcprLeakKey1 := by decide
theorem clamp_rcprAliceCks4_ne_leakKey1 : clamp rcprAliceCks4 ≠ rcprLeakKey1 := by decide
theorem clamp_rcprAliceCk0_ne_leakKey1 : clamp rcprAliceCk0 ≠ rcprLeakKey1 := by decide
theorem clamp_rcprAliceCk1_ne_leakKey1 : clamp rcprAliceCk1 ≠ rcprLeakKey1 := by decide

theorem rcprLeakKey1_ne_clamp_aliceRk4 : rcprLeakKey1 ≠ clamp rcprAliceRk4 := by decide
theorem rcprLeakKey1_ne_clamp_aliceDhs4 : rcprLeakKey1 ≠ clamp rcprAliceDhs4 := by decide
theorem rcprLeakKey1_ne_clamp_aliceCks4 : rcprLeakKey1 ≠ clamp rcprAliceCks4 := by decide
theorem rcprLeakKey1_ne_clamp_aliceCk0 : rcprLeakKey1 ≠ clamp rcprAliceCk0 := by decide
theorem rcprLeakKey1_ne_clamp_aliceCk1 : rcprLeakKey1 ≠ clamp rcprAliceCk1 := by decide

/-! ## 2. Post-Call-4 (`rcprTrace.take 5`) Theorems for `LeakStepAnalysis` -/

theorem pkiUnchanged_take5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 5)) :
    PkiUnchanged (runTrace r ss) := by
  obtain ⟨_, d⟩ := prefix_inv_5 hfit hex
  exact d.pki

theorem gamma_setup_secret_take5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 5)) :
    gamma rcprI0 S g ikA = r.fresh 0 32 ∧
    gamma rcprI0 S g ikB = r.fresh 5 32 ∧
    gamma rcprI0 S g spkB = r.fresh 10 32 ∧
    gamma rcprI0 S g pqskB = r.fresh 16 64 := by
  have hrandAt := setupRandomsAt_of_fit hfit
  have hCompat := hex.1
  have hpin (ts n : Nat)
      (hmem : (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)])
      (hn : n ≠ 0) : gamma rcprI0 S g (rnd ts n) = r.fresh ts n := by
    have hmem' : (ts, n) ∈ DY.Libsignal.Composed.Refinement.setupRandomsAt r := hrandAt ▸ hmem
    unfold rnd; rw [gamma_rand]; simp only [hn, ↓reduceIte]
    exact hCompat.1 (ts, n) hmem'
  exact ⟨hpin 0 32 (by decide) (by decide),
         hpin 5 32 (by decide) (by decide),
         hpin 10 32 (by decide) (by decide),
         hpin 16 64 (by decide) (by decide)⟩

theorem no_skippedKeyStored_take5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 5)) :
    ∀ idx s pk n seed rIdx src,
      (runTrace r ss).getEventAt TREvent idx ≠
        some (.SkippedKeyStored s pk n seed rIdx src) := by
  obtain ⟨_, d⟩ := prefix_inv_5 hfit hex
  exact d.noSkip

theorem alice_unique_snapshot_take5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 5)) :
    ∃ idxP stP,
      ((runTrace r ss).at? idxP : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩ ∧
      (∀ j st, idxP < j → ((runTrace r ss).at? j : Option TRStEntry) ≠ some ⟨⟨"alice", st⟩⟩) ∧
      (∀ i st, ((runTrace r ss).at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ →
        st.initiator = true) ∧
      gamma rcprI0 S g stP.rk = rcprAliceRk4 ∧
      gamma rcprI0 S g stP.dhs = rcprAliceDhs4 ∧
      gamma rcprI0 S g stP.cks = rcprAliceCks4 ∧
      (∀ c ∈ stP.recv,
        gamma rcprI0 S g c.chainKey = rcprAliceCk0 ∨
        gamma rcprI0 S g c.chainKey = rcprAliceCk1) := by
  obtain ⟨cls, d⟩ := prefix_inv_5 hfit hex
  obtain ⟨hrole, idxP, stP, hatP, hmaxP, hagree, _, _⟩ := d.actAlice
  obtain ⟨hRk, hDhs, hCks, hCk0, hCk1⟩ :=
    gamma_stA4Clean_keys (S := S) (cls := cls) hfit
  refine ⟨idxP, stP, hatP, hmaxP, hrole,
    hagree.rk_eq.trans hRk, hagree.dhs_eq.trans hDhs, hagree.cks_eq.trans hCks, ?_⟩
  intro c hc
  have hmem_map : gamma rcprI0 S g c.chainKey ∈
      stP.recv.map (fun x => gamma rcprI0 S g x.chainKey) :=
    List.mem_map_of_mem hc
  rw [hagree.recvCk_eq] at hmem_map
  simp only [stA4Clean, List.map, hCk0, hCk1,
    List.mem_cons, List.not_mem_nil, or_false] at hmem_map
  exact hmem_map

theorem alice_pin_current_snapshot {tr₀ tr : ExecTrace} {idxP stateIdx : Nat}
    {stP st : TRState}
    (hatP : (tr₀.at? idxP : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩)
    (hmaxP : ∀ j s, idxP < j → (tr₀.at? j : Option TRStEntry) ≠ some ⟨⟨"alice", s⟩⟩)
    (hrole : ∀ i s, (tr₀.at? i : Option TRStEntry) = some ⟨⟨"alice", s⟩⟩ → s.initiator = true)
    (hnew : NoNewPartyState "alice" tr₀ tr)
    (hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    stateIdx = idxP ∧ st = stP := by
  have hatP' : (tr.at? idxP : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩ :=
    at?_le_some hnew.1 hatP
  have hmaxP' : ∀ j s, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"alice", s⟩⟩ := by
    intro j s hj hat
    by_cases hlt : j < tr₀.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat; exact hmaxP j s hj hat
    · exact hnew.2 j s (Nat.le_of_not_lt hlt) hat
  have hrole' : ∀ i s, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", s⟩⟩ → s.initiator = true := by
    intro i s hat
    by_cases hlt : i < tr₀.length
    · rw [at?_of_le_lt hnew.1 hlt] at hat; exact hrole i s hat
    · exact False.elim (hnew.2 i s (Nat.le_of_not_lt hlt) hat)
  have hat := bks_stored_of_getLocalState hst
  have hle : stateIdx ≤ idxP := by
    by_contra hgt; exact hmaxP' stateIdx st (by omega) hat
  by_cases hlt : stateIdx < idxP
  · exfalso
    have hfalse := isCurrentSnapshot_false_of_later hat hatP' hlt
      (by rw [hrole' _ _ hatP', hrole' _ _ hat])
    rw [hfalse] at hcur; cases hcur
  · have hidx : stateIdx = idxP := by omega
    subst hidx; rw [hatP'] at hat; cases hat
    exact ⟨rfl, rfl⟩

theorem alice_pin_current_snapshot_here {tr : ExecTrace} {idxP stateIdx : Nat}
    {stP st : TRState}
    (hatP : (tr.at? idxP : Option TRStEntry) = some ⟨⟨"alice", stP⟩⟩)
    (hmaxP : ∀ j s, idxP < j → (tr.at? j : Option TRStEntry) ≠ some ⟨⟨"alice", s⟩⟩)
    (hrole : ∀ i s, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", s⟩⟩ → s.initiator = true)
    (hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx : Traceful TRState).run tr).1 =
      some st)
    (hcur : isCurrentSnapshot tr stateIdx = true) :
    stateIdx = idxP ∧ st = stP :=
  alice_pin_current_snapshot hatP hmaxP hrole (noNewPartyState_refl "alice" tr) hst hcur

/-! ## 3. Clean Prefix Extraction (`k ≤ 5`) for `RecvNoCollision` -/

theorem extract_clean_prefix {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry} {k : Nat}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hk : k ≤ 5)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take k)) :
    ∃ cls : Nat → Nat,
      ValidCoinLens cls ∧
      GhostAndSemMatchSetup rcprI0 r S (gClean r cls) ∧
      (2 ≤ k → (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
        (ecKey (pubBytes rcprI0 (secretBytes r 0)))
        (gamma rcprI0 S (gClean r cls) o1.ek)
        (gamma rcprI0 S (gClean r cls) o1.ct)
        (gamma rcprI0 S (gClean r cls) (m0Clean cls)))) ∧
      (4 ≤ k → (ev 3).exit =
        some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))) := by
  match k with
  | 0 =>
    let cls : Nat → Nat := fun _ => 32
    have hv : ValidCoinLens cls := fun _ _ => Or.inr (Or.inl rfl)
    exact ⟨cls, hv, ghostAndSemMatchSetup_gClean cls hfit hex.1,
      fun h => by omega, fun h => by omega⟩
  | 1 =>
    obtain ⟨cls, d⟩ := prefix_inv_1 hfit hex
    exact ⟨cls, d.validCls, d.compatClean, fun h => by omega, fun h => by omega⟩
  | 2 =>
    obtain ⟨cls, d⟩ := prefix_inv_2 hfit hex
    exact ⟨cls, d.validCls, d.compatClean, fun _ => d.ev1_out, fun h => by omega⟩
  | 3 =>
    obtain ⟨cls, d⟩ := prefix_inv_3 hfit hex
    exact ⟨cls, d.validCls, d.compatClean, fun _ => d.ev1_out, fun h => by omega⟩
  | 4 =>
    obtain ⟨cls, d⟩ := prefix_inv_4 hfit hex
    exact ⟨cls, d.validCls, d.compatClean, fun _ => d.ev1_out, fun _ => d.ev3_out⟩
  | 5 =>
    obtain ⟨cls, d⟩ := prefix_inv_5 hfit hex
    exact ⟨cls, d.validCls, d.compatClean, fun _ => d.ev1_out, fun _ => d.ev3_out⟩
  | n + 6 => omega

namespace Calls0to4Prefix

export Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (ValidCoinLens cleanCallSteps ssClean gClean
   trClean1 trClean2 trClean3 trClean4 trClean5
   stA1Clean stB2Clean stB3Clean stA4Clean m0Clean m1Clean
   s0_next_ok s1_next_ok s2_next_ok s3_next_ok s4_next_ok
   ghostAndSemMatchSetup_gClean
   rcprAliceRk4 rcprAliceDhs4 rcprAliceCks4 rcprAliceCk0 rcprAliceCk1
   rcprAliceRk4_length rcprAliceDhs4_length rcprAliceCks4_length
   rcprAliceCk0_length rcprAliceCk1_length
   rcprAliceRk4_ne_leakKey1 rcprAliceDhs4_ne_leakKey1 rcprAliceCks4_ne_leakKey1
   rcprAliceCk0_ne_leakKey1 rcprAliceCk1_ne_leakKey1
   rcprLeakKey1_ne_aliceRk4 rcprLeakKey1_ne_aliceDhs4 rcprLeakKey1_ne_aliceCks4
   rcprLeakKey1_ne_aliceCk0 rcprLeakKey1_ne_aliceCk1
   clamp_rcprAliceRk4_ne_leakKey1 clamp_rcprAliceDhs4_ne_leakKey1
   clamp_rcprAliceCks4_ne_leakKey1 clamp_rcprAliceCk0_ne_leakKey1
   clamp_rcprAliceCk1_ne_leakKey1
   rcprLeakKey1_ne_clamp_aliceRk4 rcprLeakKey1_ne_clamp_aliceDhs4
   rcprLeakKey1_ne_clamp_aliceCks4 rcprLeakKey1_ne_clamp_aliceCk0
   rcprLeakKey1_ne_clamp_aliceCk1
   PkiUnchanged pki_pin_st pki_pin_reg NoSkippedKeyStored NoNewPartyState
   pkiUnchanged_take5 gamma_setup_secret_take5 no_skippedKeyStored_take5
   alice_unique_snapshot_take5 alice_pin_current_snapshot alice_pin_current_snapshot_here
   extract_clean_prefix)

end Calls0to4Prefix

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
