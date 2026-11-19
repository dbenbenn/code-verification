/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay.Step2CleanState

/-!
# KnownBaseKey, Clean Ghost Override, and SPQR Salt Extraction Helpers
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

/-! ### 1. Prefix `KnownBaseKeyOn` & `ReadCollisionCli` Helpers -/

theorem bobDoneBaseKeys_nil_of_noBobBefore3 {tr : ExecTrace}
    (hNoBob : NoBobBefore3 tr) :
    bobDoneBaseKeys tr = [] := by
  unfold bobDoneBaseKeys
  rw [List.filterMap_eq_nil_iff]
  intro i _
  split
  · rename_i b a ikB ikA spk pqpk opk ek ct keys h
    exfalso
    rw [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at h
    cases hat : (tr.at? i : Option CompTrace.PQXDHEntry) with
    | none => rw [hat] at h; cases h
    | some entry =>
      rcases entry with ⟨ev⟩
      rw [hat] at h
      injection h with h
      subst h
      have hlog : tr.EventLoggedAt
          (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a ikB ikA spk pqpk opk ek ct keys) i := by
        rw [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1]
        exact hat
      exact hNoBob.2.2 i b a ikB ikA spk pqpk opk ek ct keys hlog
  · rfl

theorem noBobBefore3_of_explains_ev012 {r : ProtocolSetup}
    (hb : r.bob = "bob")
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2]) :
    NoBobBefore3 (runTrace r ss) ∧
      ¬ KnownBaseKeyOn compI0 S g (runTrace r ss) p_c2 := by
  rcases hex with ⟨_, _, _, hM⟩
  obtain ⟨pre0, s0, ss1, v0, vs1, rfl, _, hInv0, hRun0, hM1⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hM
  have hNoBob0 := noBobBefore3_runSteps_invisible hInv0 (noBobBefore3_setupTrace r)
  have hs0 := step_of_init_alice hb hRun0.2.1 (fun _ _ h => h ▸ hRun0.2.2.1) hRun0.2.2.2.1
  have hNoBob0' := noBobBefore3_alice_step (.inl hs0) hNoBob0
  obtain ⟨pre1, s1, ss2, v1, vs2, rfl, _, hInv1, hRun1, hM2⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM1
  have hNoBob1 := noBobBefore3_runSteps_invisible hInv1 hNoBob0'
  have hs1 := step_of_send_alice hRun1.2.1 hRun1.2.2.1
  have hNoBob1' := noBobBefore3_alice_step (.inr hs1) hNoBob1
  obtain ⟨pre2, s2, ss3, v2, vs3, rfl, _, hInv2, hRun2, hM3⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hM2
  have hNoBob2 := noBobBefore3_runSteps_invisible hInv2 hNoBob1'
  have hs2 := step_of_send_alice hRun2.2.1 hRun2.2.2.1
  have hNoBob2' := noBobBefore3_alice_step (.inr hs2) hNoBob2
  have hInv3 : ∀ x ∈ ss3, x.cls = .invisible := by
    cases hM3 with
    | nil hp => exact hp
  have hRunTrace :
      runTrace r (pre0 ++ s0 :: (pre1 ++ s1 :: (pre2 ++ s2 :: ss3))) =
        runSteps ss3 (s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r))))))) := by
    unfold runTrace
    rw [runSteps_append_local]
    dsimp only [runSteps]
    rw [runSteps_append_local]
    dsimp only [runSteps]
    rw [runSteps_append_local]
    rfl
  have hNB : NoBobBefore3 (runTrace r (pre0 ++ s0 :: (pre1 ++ s1 :: (pre2 ++ s2 :: ss3)))) := by
    rw [hRunTrace]
    exact noBobBefore3_runSteps_invisible hInv3 hNoBob2'
  refine ⟨hNB, ?_⟩
  rintro ⟨ek, hek, _⟩
  rw [bobDoneBaseKeys_nil_of_noBobBefore3 hNB] at hek
  exact List.not_mem_nil hek

theorem knownBaseKeyOn_of_bobPost {S : OpaqueSymbolSemantics} {g : Ghost}
    {skIdx0 : Nat} {used : Bool} {tr : ExecTrace}
    (hPost : BobPost S g skIdx0 used tr) :
    KnownBaseKeyOn compI0 S g tr p_c1 := by
  obtain ⟨b, a, ikB, ikA, spk, pqpk, opk, ek, ct, keys, i, hi, hek⟩ := hPost.hasBobDone
  exact ⟨ek, mem_bobDoneBaseKeys_of_loggedAt hi, hek.symm⟩

theorem knownBaseKeyOn_of_explains_ev0123 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob")
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3]) :
    KnownBaseKeyOn compI0 S g (runTrace r ss) p_c1 := by
  rcases hex with ⟨_, _, _, hM⟩
  obtain ⟨pre0, s0, ss1, _, _, rfl, _, hInv0, hRun0, hM1⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hM
  have hNoBob0' := noBobBefore3_alice_step
    (.inl (step_of_init_alice hb hRun0.2.1 (fun _ _ h => h ▸ hRun0.2.2.1) hRun0.2.2.2.1))
    (noBobBefore3_runSteps_invisible hInv0 (noBobBefore3_setupTrace r))
  obtain ⟨pre1, s1, ss2, _, _, rfl, _, hInv1, hRun1, hM2⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM1
  have hNoBob1' := noBobBefore3_alice_step (.inr (step_of_send_alice hRun1.2.1 hRun1.2.2.1))
    (noBobBefore3_runSteps_invisible hInv1 hNoBob0')
  obtain ⟨pre2, s2, ss3, _, _, rfl, _, hInv2, hRun2, hM3⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hM2
  have hNoBob2' := noBobBefore3_alice_step (.inr (step_of_send_alice hRun2.2.1 hRun2.2.2.1))
    (noBobBefore3_runSteps_invisible hInv2 hNoBob1')
  obtain ⟨pre3, s3, ss4, _, _, rfl, _, hInv3, hRun3, hM4⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev3 hM3
  set tr3 := runSteps pre3 (s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r)))))))
  have hNoBob3 : NoBobBefore3 tr3 := noBobBefore3_runSteps_invisible hInv3 hNoBob2'
  have hs3Cases := step_of_recv_bob ha hRun3.2.1 hRun3.2.2.1 hRun3.2.2.2.1
  have hPost3' : ∃ skIdx0, BobPost S g skIdx0 false (s3.next tr3) := by
    rcases hs3Cases with ⟨kh, regIdxA, mh, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3, rfl⟩
    · exact bobStart_ev3_establishes_bobPost hNoBob3 hRun3
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecrypt.reachability
          ("bob", stIdx, msgIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecrypt at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
          "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
          ("bob", stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
  obtain ⟨skIdx0, hPost3⟩ := hPost3'
  have hInv4 : ∀ x ∈ ss4, x.cls = .invisible := by
    cases hM4 with
    | nil hp => exact hp
  have hRunTrace :
      runTrace r (pre0 ++ s0 :: (pre1 ++ s1 :: (pre2 ++ s2 :: (pre3 ++ s3 :: ss4)))) =
        runSteps ss4 (s3.next tr3) := by
    unfold runTrace tr3
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; rfl
  rw [hRunTrace]
  exact knownBaseKeyOn_of_bobPost (bobPost_runSteps_invisible hInv4 hPost3)

theorem knownBaseKeyOn_of_explains_ev01234 {r : ProtocolSetup}
    (ha : r.alice = "alice") (hb : r.bob = "bob")
    {S : OpaqueSymbolSemantics} {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hex : Explains compI0 r S g ss vis [.run ev0, .run ev1, .run ev2, .run ev3, .run ev4]) :
    KnownBaseKeyOn compI0 S g (runTrace r ss) p_c1 := by
  rcases hex with ⟨_, _, _, hM⟩
  obtain ⟨pre0, s0, ss1, _, _, rfl, _, hInv0, hRun0, hM1⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev0 hM
  have hNoBob0' := noBobBefore3_alice_step
    (.inl (step_of_init_alice hb hRun0.2.1 (fun _ _ h => h ▸ hRun0.2.2.1) hRun0.2.2.2.1))
    (noBobBefore3_runSteps_invisible hInv0 (noBobBefore3_setupTrace r))
  obtain ⟨pre1, s1, ss2, _, _, rfl, _, hInv1, hRun1, hM2⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev1 hM1
  have hNoBob1' := noBobBefore3_alice_step (.inr (step_of_send_alice hRun1.2.1 hRun1.2.2.1))
    (noBobBefore3_runSteps_invisible hInv1 hNoBob0')
  obtain ⟨pre2, s2, ss3, _, _, rfl, _, hInv2, hRun2, hM3⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev2 hM2
  have hNoBob2' := noBobBefore3_alice_step (.inr (step_of_send_alice hRun2.2.1 hRun2.2.2.1))
    (noBobBefore3_runSteps_invisible hInv2 hNoBob1')
  obtain ⟨pre3, s3, ss4, _, _, rfl, _, hInv3, hRun3, hM4⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev3 hM3
  set tr3 := runSteps pre3 (s2.next (runSteps pre2 (s1.next (runSteps pre1 (s0.next (runSteps pre0 (setupTrace r)))))))
  have hNoBob3 : NoBobBefore3 tr3 := noBobBefore3_runSteps_invisible hInv3 hNoBob2'
  have hs3Cases := step_of_recv_bob ha hRun3.2.1 hRun3.2.2.1 hRun3.2.2.2.1
  have hPost3' : ∃ skIdx0, BobPost S g skIdx0 false (s3.next tr3) := by
    rcases hs3Cases with ⟨kh, regIdxA, mh, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, pqIdx3, spqrIdx3, rfl⟩ |
      ⟨stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3, rfl⟩
    · exact bobStart_ev3_establishes_bobPost hNoBob3 hRun3
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecrypt "bob" stIdx msgIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecrypt.reachability
          ("bob", stIdx, msgIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecrypt at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
    · exfalso
      have hok3 := hRun3.2.2.2.2.1
      rw [show (Step.messageDecryptSkipped "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).ok tr3 =
        ((DY.Libsignal.TripleRatchet.messageDecryptSkipped
          "bob" stIdx msgIdx skIdx pqIdx3 spqrIdx3).run tr3).1.isSome from
        stepIn_ok DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
          ("bob", stIdx, msgIdx, skIdx, pqIdx3, spqrIdx3) tr3] at hok3
      unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped at hok3
      obtain ⟨st, hst, _, _⟩ := run_bind_isSome hok3
      exact hNoBob3.1 stIdx st (getLocalState_tr_some hst)
  obtain ⟨skIdx0, hPost3⟩ := hPost3'
  obtain ⟨pre4, s4, ss5, _, _, rfl, _, hInv4, hRun4, hM5⟩ :=
    matchesEventsAt_run_of_not_rejected no_runRejected_ev4 hM4
  have hPost4 := bobPost_runSteps_invisible hInv4 hPost3
  have ⟨_, hPost4'⟩ :=
    bobStep_c1_contradiction_or_advances (ev := ev4) ha rfl rfl rfl runWrapped_ev4 hPost4 hRun4
  have hInv5 : ∀ x ∈ ss5, x.cls = .invisible := by
    cases hM5 with
    | nil hp => exact hp
  have hRunTrace :
      runTrace r (pre0 ++ s0 :: (pre1 ++ s1 :: (pre2 ++ s2 :: (pre3 ++ s3 :: (pre4 ++ s4 :: ss5))))) =
        runSteps ss5 (s4.next (runSteps pre4 (s3.next tr3))) := by
    unfold runTrace tr3
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; dsimp only [runSteps]
    rw [runSteps_append_local]; rfl
  rw [hRunTrace]
  exact knownBaseKeyOn_of_bobPost (bobPost_runSteps_invisible hInv5 hPost4')

theorem not_readCollisionCli_ev012 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g' : Ghost} {ss' : List Step} :
    ¬ ReadCollisionCli compI0 r S g' ss' [.run ev0, .run ev1, .run ev2] := by
  rintro ⟨evs₁, ev, evs₂, _, _, _, _, _, _, _, _, hev_eq, _, ⟨peer, hcmd⟩, _⟩
  have hmem : CliEvent.run ev ∈ ([.run ev0, .run ev1, .run ev2] : List CliEvent) := by
    rw [hev_eq]; exact List.mem_append_right _ List.mem_cons_self
  simp only [List.mem_cons, List.not_mem_nil, or_false, CliEvent.run.injEq] at hmem
  rcases hmem with rfl | rfl | rfl <;> cases hcmd

/-! ### 2. `setupTrace r = setupTrace r0` and Clean Steps, States & Traces -/

theorem setupTrace_eq_of_fits {r : ProtocolSetup} (hp : FitsPins r) :
    setupTrace r = setupTrace r0 :=
  setupTrace_eq_of_parties hp.ha hp.hb hp.hopk

def s0Clean : Step :=
  .aliceStart "alice" "bob" 4 6 ⟨14, 15, 20, 21, none⟩

def s1Clean (cl1 : Nat) : Step :=
  .messageEncrypt "alice" 30 cl1 33

def s2Clean (cl2 : Nat) : Step :=
  .messageEncrypt "alice" 36 cl2 40

def s3Clean : Step :=
  .bobStart "bob" "alice" ⟨9, 13, 19, none⟩ 1 ⟨25, 26, 44⟩ 40 1

def s4Clean : Step :=
  .messageDecryptSkipped "bob" 54 37 51 33 1

def ss3Clean (cl1 cl2 : Nat) : List Step :=
  [s0Clean, s1Clean cl1, s2Clean cl2]

def ss4Clean (cl1 cl2 : Nat) : List Step :=
  [s0Clean, s1Clean cl1, s2Clean cl2, s3Clean]

def ss5Clean (cl1 cl2 : Nat) : List Step :=
  [s0Clean, s1Clean cl1, s2Clean cl2, s3Clean, s4Clean]

def tr1Clean : ExecTrace :=
  localAliceStartTr (setupTrace r0) "alice" "bob" oClean

def tr2Clean (cl1 : Nat) : ExecTrace :=
  localEncTr tr1Clean "alice" 30 cl1 stA0Clean (salt1Clean cl1)

def tr3Clean (cl1 cl2 : Nat) : ExecTrace :=
  localEncTr (tr2Clean cl1) "alice" 36 cl2 (stA1Clean cl1) (salt2Clean cl1 cl2)

theorem tr1Clean_len : tr1Clean.length = 31 := by
  have h := setupTrace_r0_len
  simp only [tr1Clean, localAliceStartTr, length_append_entry]
  omega

theorem tr2Clean_len (cl1 : Nat) : (tr2Clean cl1).length = 38 := by
  have h := tr1Clean_len
  simp only [tr2Clean, localEncTr, length_append_entry]
  omega

theorem tr3Clean_len (cl1 cl2 : Nat) : (tr3Clean cl1 cl2).length = 45 := by
  have h := tr2Clean_len cl1
  simp only [tr3Clean, localEncTr, length_append_entry]
  omega

/-! ### 3. Parsed Clean Messages, Bob's Clean States (`stB3Clean`, `stB4Clean`), and `SafeMemo2` -/

def msg1Clean (cl1 : Nat) : DY.Libsignal.TripleRatchet.TRSignalMsg :=
  Runs.encSig stA0Clean (coins1Clean cl1) (salt1Clean cl1) (randTerm 31 32)

def msg2Clean (cl1 cl2 : Nat) : DY.Libsignal.TripleRatchet.TRSignalMsg :=
  Runs.encSig (stA1Clean cl1) (coins2Clean cl2) (salt2Clean cl1 cl2) (randTerm 38 32)

theorem parse_m1Clean (cl1 : Nat) :
    DY.Libsignal.TripleRatchet.parseTrSignalMsg (m1Clean cl1) = some (msg1Clean cl1) :=
  Runs.parse_honest _ _ _ _ _ _ _ _

theorem parse_m2Clean (cl1 cl2 : Nat) :
    DY.Libsignal.TripleRatchet.parseTrSignalMsg (m2Clean cl1 cl2) = some (msg2Clean cl1 cl2) :=
  Runs.parse_honest _ _ _ _ _ _ _ _

def dhsBClean : DY.Bytes := randTerm 45 32

def spqrB0Clean : DY.Bytes :=
  DY.Spqr.spqrInit oClean.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A

def spqrB3Clean (cl1 cl2 : Nat) : DY.Bytes :=
  ({ st := spqrB0Clean, msg := pqm2Clean cl1 cl2 } : DY.Spqr.RecvState.SubF DY.Bytes).pack

def spqrKeyB3Clean : DY.Bytes :=
  DY.Spqr.spqrChainKey oClean.keys.pqr
    (DY.Spqr.encodeSpqrDirectionParams .a2b) (DY.Spqr.encodeSpqrIndexTerm 1)

def spqrB4Clean (cl1 cl2 : Nat) : DY.Bytes :=
  ({ st := spqrB3Clean cl1 cl2, msg := pqm1Clean cl1 } : DY.Spqr.RecvState.SubF DY.Bytes).pack

def spqrKeyB4Clean (cl1 cl2 : Nat) : DY.Bytes :=
  ({ st := spqrB3Clean cl1 cl2, msg := pqm1Clean cl1 } : DY.Spqr.RecvKey.SubF DY.Bytes).pack

def rkB3Clean : DY.Bytes :=
  (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (DY.DiffieHellman.dhPk stA0Clean.dhs) dhsBClean).1

def cksB3Clean : DY.Bytes :=
  (DY.Libsignal.TripleRatchet.createChain stA0Clean.rk (DY.DiffieHellman.dhPk stA0Clean.dhs) dhsBClean).2

def recvChainB3Clean (cl1 cl2 : Nat) : DY.Libsignal.TripleRatchet.RecvChain :=
  { ratchetKey := DY.DiffieHellman.dhPk stA0Clean.dhs,
    chainKey := (stA2Clean cl1 cl2).cks,
    index := 2,
    rIdx := 2 }

def stB3Clean (cl1 cl2 : Nat) : DY.Libsignal.TripleRatchet.TRState :=
  { peer := "alice",
    myIk := stA0Clean.peerIk,
    peerIk := stA0Clean.myIk,
    rk := rkB3Clean,
    dhs := dhsBClean,
    cks := cksB3Clean,
    ns := 0,
    pn := 0,
    sid := stA0Clean.sid,
    initiator := false,
    rIdx := 2,
    recv := [recvChainB3Clean cl1 cl2],
    spqr := spqrB3Clean cl1 cl2 }

def stB4Clean (cl1 cl2 : Nat) : DY.Libsignal.TripleRatchet.TRState :=
  { stB3Clean cl1 cl2 with spqr := spqrB4Clean cl1 cl2 }

theorem dagTermAt_bobRatchet {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {cl1 cl2 : Nat}
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    DagTermAt S g pts dhsBClean 127 ∧
    DagTermAt S g pts rkB3Clean 131 ∧
    DagTermAt S g pts cksB3Clean 133 := by
  obtain ⟨hrkA0, _, _, _, _, _, _, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  have hlen := setupTrace_r0_len
  have hdhsB : DagTermAt S g pts dhsBClean 127 := dagN_127 hw
  have hdh : DagTermAt S g pts
      (DY.X25519.agree (DY.DiffieHellman.dhPk stA0Clean.dhs) dhsBClean) 129 := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [hlen]
    change DagTermAt S g pts (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 24 32)) dhsBClean) 129
    rw [agree_dhPk]
    exact dagN_129_symm hw
  have hprk := termAt_kdf (id := 130) dag_nodes_ok (by decide) rfl hrkA0 hdh
  have hrkB3 := termAt_kdf (id := 131) dag_nodes_ok (by decide) rfl hprk (dagN_13 hw)
  have hkc := termAt_concat (id := 132) dag_nodes_ok (by decide) rfl hrkB3 (dagN_14 hw)
  have hcksB3 := termAt_kdf (id := 133) dag_nodes_ok (by decide) rfl hprk hkc
  exact ⟨hdhsB, hrkB3, hcksB3⟩

theorem safeMemo2_bobStates {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List DY.Bytes}
    {cl1 cl2 : Nat}
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"bob", stB3Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) ∧
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"bob", stB4Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  obtain ⟨_, _, _, _, hpqr0⟩ := dagTermAt_oClean hw
  obtain ⟨_, _, _, hsid0, _, _, hcks2, _⟩ := dagTermAt_aliceRatchetAndMsgs hw
  obtain ⟨hdhsB, hrkB3, hcksB3⟩ := dagTermAt_bobRatchet hw
  have hspqr0 : DagSafeMemo S g pts spqrB0Clean :=
    safeMemo_spqrInit hpqr0.safeMemo (safeMemo_lit_short (by decide))
  have hspqr3 : DagSafeMemo S g pts (spqrB3Clean cl1 cl2) :=
    safeMemo_spqrRecvState_pack hspqr0 (dagN_24 hw).safeMemo
  have hspqr4 : DagSafeMemo S g pts (spqrB4Clean cl1 cl2) :=
    safeMemo_spqrRecvState_pack hspqr3 (dagN_22 hw).safeMemo
  have hmyIk : DagSafeMemo S g pts stA0Clean.peerIk := (dagN_31 hw).safeMemo
  have hpeerIk : DagSafeMemo S g pts stA0Clean.myIk := (dagN_28 hw).safeMemo
  have hdhsAPk : DagSafeMemo S g pts (DY.DiffieHellman.dhPk stA0Clean.dhs) := by
    unfold stA0Clean localAliceStartState; dsimp only; rw [setupTrace_r0_len]
    exact (dagN_73 hw).safeMemo
  have hs3 : SafeMemo2 S g pts (DY.Comparse.serialize (⟨"bob", stB3Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := ⟨"bob", stB3Clean cl1 cl2⟩)
      (cLast := recvChainB3Clean cl1 cl2)
      rfl rfl (Or.inr rfl) (Or.inl rfl) hspqr3 ?_ ?_ rfl (Nat.le_succ 1)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmyIk
      · exact hpeerIk
      · exact hrkB3.safeMemo
      · exact hdhsB.safeMemo
      · exact hcksB3.safeMemo
      · exact hsid0.safeMemo
    · intro c hc
      simp only [stB3Clean, List.mem_singleton] at hc
      subst hc; exact ⟨hdhsAPk, hcks2.safeMemo⟩
  have hs4 : SafeMemo2 S g pts (DY.Comparse.serialize (⟨"bob", stB4Clean cl1 cl2⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
    refine safeMemo2_trState_of_dr (ls₀ := ⟨"bob", stB3Clean cl1 cl2⟩)
      (cLast := recvChainB3Clean cl1 cl2)
      rfl rfl (Or.inr rfl) (Or.inl rfl) hspqr4 ?_ ?_ rfl (Nat.le_succ 1)
    · intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmyIk
      · exact hpeerIk
      · exact hrkB3.safeMemo
      · exact hdhsB.safeMemo
      · exact hcksB3.safeMemo
      · exact hsid0.safeMemo
    · intro c hc
      simp only [stB3Clean, List.mem_singleton] at hc
      subst hc; exact ⟨hdhsAPk, hcks2.safeMemo⟩
  exact ⟨hs3, hs4⟩

/-! ### 4. Exact `storedSecrets`, `setupRandoms`, `storedStates`, and `TREvent` Lists -/

theorem filterMap_range_pqSt_append {E : Type} [DY.ExecTraceTypes.Has E]
    (tr : ExecTrace) (e : E) :
    (List.range (tr.append e : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append e) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) ++
      match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
          Option CompTrace.PQXDHStEntry) with
      | none => []
      | some entry => [DY.Comparse.serialize entry.st] := by
  have hcongr : ∀ (l : List Nat) (f g : Nat → Option DY.Bytes),
      (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
    intro l f g hfg
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
  have hlen : (tr.append e : ExecTrace).length = tr.length + 1 := by
    simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [hlen, List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  · refine hcongr _ _ _ fun i hi => ?_
    have hlt : i < tr.length := List.mem_range.mp hi
    have hlt2 : i < (tr.append e : ExecTrace).length := by omega
    unfold ExecTrace.getLocalStateAt
    simp only [DY.Trace.at?, hlt, hlt2, ↓reduceDIte,
      DY.Trace.at_le tr (tr.append e) i hlt (DY.Trace.append_le tr e)]
  · unfold ExecTrace.getLocalStateAt
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.PQXDHStEntry) <;> rfl

theorem storedSecrets_tr3Clean_eq (cl1 cl2 : Nat) :
    storedSecrets (tr3Clean cl1 cl2) =
      [DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := ikASkClean }⟩ :
          DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
       DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := ikBSkClean }⟩ :
          DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
       DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkBSkClean }⟩ :
          DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState),
       DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskBClean }⟩ :
          DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)] := by
  have hnil : ∀ (f : Nat → Option DY.Bytes),
      (List.range (Trace.nil : ExecTrace).length).filterMap f = [] := by
    intro f; rw [Symbolic.DYBridge.DY.Trace.length_eq_1]; rfl
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      (List.range (tr.append (RndE n) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (RndE n)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr n; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      (List.range (tr.append (NetE m) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (NetE m)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr m; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevp : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      (List.range (tr.append (EvP ev) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (EvP ev)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr ev; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevt : ∀ (tr : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent),
      (List.range (tr.append (EvT ev) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (EvT ev)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr ev; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hevc : ∀ (tr : ExecTrace) (ev : DY.Libsignal.Composed.ComposedEvent),
      (List.range (tr.append (Runs.EvC ev) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (Runs.EvC ev)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr ev; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hstt : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.TripleRatchet.TRState),
      (List.range (tr.append (StT me s) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (StT me s)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) := by
    intro tr me s; rw [filterMap_range_pqSt_append]; exact List.append_nil _
  have hstp : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.PQXDH.PQXDHState),
      (List.range (tr.append (StP me s) : ExecTrace).length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState (tr.append (StP me s)) i).map DY.Comparse.serialize) =
      (List.range tr.length).filterMap
        (fun i => (ExecTrace.getLocalStateAt DY.Libsignal.PQXDH.PQXDHState tr i).map DY.Comparse.serialize) ++
        [DY.Comparse.serialize (⟨me, s⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)] :=
    fun tr me s => filterMap_range_pqSt_append tr (StP me s)
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr
    simp [hl1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr
    simp [hl2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  unfold storedSecrets tr3Clean tr2Clean tr1Clean localEncTr localAliceStartTr
  dsimp only
  simp only [hrnd, hnet, hevp, hevt, hevc, hstt, setupTrace_r0_eq]
  unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
  unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
  unfold setupTr2 registerIdentityTr; dsimp only; rw [hl1]
  unfold setupTr1 registerIdentityTr; dsimp only
  simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, hrnd, hnet, hevp, hstp]
  rfl

theorem safeMemo2_storedSecrets_tr3Clean {S : OpaqueSymbolSemantics} {g : Ghost}
    {pts : List DY.Bytes} {cl1 cl2 : Nat}
    (hw : CleanDagHyp S g pts pqpkBClean (salt1Clean cl1) (pqm1Clean cl1) (salt2Clean cl1 cl2) (pqm2Clean cl1 cl2)) :
    ∀ u ∈ storedSecrets (tr3Clean cl1 cl2), SafeMemo2 S g pts u := by
  rw [storedSecrets_tr3Clean_eq]
  obtain ⟨baF, _, hbaF, hserF⟩ := bool_serialize_singleton_head false
  obtain ⟨baT, _, hbaT, hserT⟩ := bool_serialize_singleton_head true
  subst hbaF; subst hbaT
  have h1 : DY.Comparse.serialize (⟨"alice", { kind := .identity, sk := ikASkClean }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) = dagT_45 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, show "alice".utf8ByteSize = 5 by decide]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, hserF, hserT,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    rfl
  have h2 : DY.Comparse.serialize (⟨"bob", { kind := .identity, sk := ikBSkClean }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) = dagT_52 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, show "bob".utf8ByteSize = 3 by decide]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, hserF, hserT,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    rfl
  have h3 : DY.Comparse.serialize (⟨"bob", { kind := .signedPrekey, sk := spkBSkClean }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) = dagT_59 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, show "bob".utf8ByteSize = 3 by decide]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, hserF, hserT,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    rfl
  have h4 : DY.Comparse.serialize (⟨"bob", { kind := .pqPrekey, sk := pqskBClean }⟩ :
      DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) = dagT_66 := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_pqxdh_eq_bridge]
    dsimp only [DY.Libsignal.PQXDH.KeyKind.toBits]
    rw [slowString_serialize_eq, show "bob".utf8ByteSize = 3 by decide]
    simp only [slowNat_serialize_succ, slowNat_serialize_zero, hserF, hserT,
      List.cons_append, List.nil_append, concatPrefixes_cons, concatPrefixes_nil]
    rfl
  intro u hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · rw [h1]; exact safeMemo_toSafeMemo2 (dagN_45 hw).safeMemo
  · rw [h2]; exact safeMemo_toSafeMemo2 (dagN_52 hw).safeMemo
  · rw [h3]; exact safeMemo_toSafeMemo2 (dagN_59 hw).safeMemo
  · rw [h4]; exact safeMemo_toSafeMemo2 (dagN_66 hw).safeMemo

theorem filterMap_newIndices_trSt_append {E : Type} [DY.ExecTraceTypes.Has E]
    (tr0 tr : ExecTrace) (e : E) (hle : tr0.length ≤ tr.length) :
    (newIndices tr0 (tr.append e)).filterMap (ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState (tr.append e)) =
      (newIndices tr0 tr).filterMap (ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState tr) ++
        match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.TRStEntry) with
        | none => []
        | some entry => [entry.st] := by
  have hcongr : ∀ (l : List Nat) (f g : Nat → Option (DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)),
      (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
    intro l f g hfg
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
  have hni : newIndices tr0 (tr.append e) = newIndices tr0 tr ++ [tr.length] := by
    unfold newIndices
    have hsub : (tr.append e : ExecTrace).length - tr0.length = (tr.length - tr0.length) + 1 := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    rw [hsub, List.range'_concat]
    simp [Nat.add_sub_of_le hle]
  rw [hni, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  congr 1
  · refine hcongr _ _ _ fun i hi => ?_
    unfold newIndices at hi
    simp only [List.mem_range'_1] at hi
    have hlt : i < tr.length := by omega
    have hlt2 : i < (tr.append e : ExecTrace).length := by
      simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      omega
    unfold ExecTrace.getLocalStateAt
    simp only [DY.Trace.at?, hlt, hlt2, ↓reduceDIte,
      DY.Trace.at_le tr (tr.append e) i hlt (DY.Trace.append_le tr e)]
  · unfold ExecTrace.getLocalStateAt
    simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
      Symbolic.DYBridge.DY.Trace.at_eq_2]
    cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option CompTrace.TRStEntry) <;> rfl

theorem storedStates_tr3Clean_eq (cl1 cl2 : Nat) :
    storedStates r0 (tr3Clean cl1 cl2) =
      [⟨"alice", stA0Clean⟩, ⟨"alice", stA1Clean cl1⟩, ⟨"alice", stA2Clean cl1 cl2⟩] := by
  have hself : (newIndices (setupTrace r0) (setupTrace r0)).filterMap
      (ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState (setupTrace r0)) = [] := by
    simp [newIndices]
  have hstep : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E)
      (h : (setupTrace r0).length ≤ tr.length),
      (newIndices (setupTrace r0) (tr.append e)).filterMap
        (ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState (tr.append e)) =
      (newIndices (setupTrace r0) tr).filterMap
        (ExecTrace.getLocalStateAt DY.Libsignal.TripleRatchet.TRState tr) ++
        match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
            Option CompTrace.TRStEntry) with
        | none => []
        | some entry => [entry.st] :=
    fun tr e h => filterMap_newIndices_trSt_append (setupTrace r0) tr e h
  have htrst : ∀ p st,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TRStE p st) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [⟨p, st⟩] := fun _ _ => rfl
  have hrnd : ∀ n,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.RndE n) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [] := fun _ => rfl
  have hnet : ∀ m,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.NetE m) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [] := fun _ => rfl
  have hpq : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.PQEvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [] := fun _ => rfl
  have htr : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.TREvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [] := fun _ => rfl
  have hce : ∀ ev,
      (match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj (CompTrace.CEvE ev) : ExecTrace.Entry) :
          Option CompTrace.TRStEntry) with
       | none => []
       | some entry => [entry.st]) = [] := fun _ => rfl
  unfold storedStates tr3Clean tr2Clean tr1Clean localEncTr localAliceStartTr
  dsimp only
  repeat rw [hstep _ _ (by simp (config := { failIfUnchanged := false }) only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)]
  rw [hself]
  simp only [htrst, hrnd, hnet, hpq, htr, hce, List.append_nil, List.nil_append, List.cons_append,
    length_append_entry, setupTrace_r0_len]
  rfl

theorem setupRandoms_r0_eq :
    setupRandoms r0 =
      [randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 11 64, randTerm 16 64, randTerm 17 64] := by
  have hstep : ∀ {E : Type} [DY.ExecTraceTypes.Has E] (tr : ExecTrace) (e : E),
      (newRandoms Trace.nil (tr.append e)).map (·.1) =
        (newRandoms Trace.nil tr).map (·.1) ++
          match (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
              Option DY.Random.ExecEntryT) with
          | none => []
          | some entry => [randTerm tr.length entry.length] := by
    intro E _ tr e
    have hcongr : ∀ (l : List Nat) (f g : Nat → Option (DY.Bytes × Nat)),
        (∀ i ∈ l, f i = g i) → l.filterMap f = l.filterMap g := by
      intro l f g hfg
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.filterMap_cons, hfg x (.head _), ih (fun i hi => hfg i (.tail _ hi))]
    have hni : newIndices Trace.nil (tr.append e) = newIndices Trace.nil tr ++ [tr.length] := by
      unfold newIndices
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero,
        Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
        List.range'_concat, Nat.zero_add, Nat.one_mul]
    unfold newRandoms
    rw [hni, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.map_append]
    congr 1
    · congr 1
      refine hcongr _ _ _ fun i hi => ?_
      unfold newIndices at hi
      simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Nat.sub_zero, List.mem_range'_1,
        Nat.zero_add] at hi
      have hi2 : i < (tr.append e : ExecTrace).length := by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        omega
      simp only [DY.Trace.at?, hi.2, hi2, ↓reduceDIte,
        DY.Trace.at_le tr (tr.append e) i hi.2 (DY.Trace.append_le tr e)]
    · simp only [DY.Trace.at?, Symbolic.DYBridge.DY.Trace.append_eq_1,
        Symbolic.DYBridge.DY.Trace.length_eq_2, Nat.lt_succ_self, ↓reduceDIte,
        Symbolic.DYBridge.DY.Trace.at_eq_2]
      cases (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
        Option DY.Random.ExecEntryT) <;> rfl
  have hnil : (newRandoms Trace.nil (Trace.nil : ExecTrace)).map (·.1) = [] := by
    simp [newRandoms, newIndices, Symbolic.DYBridge.DY.Trace.length_eq_1]
  have hrnd : ∀ (tr : ExecTrace) (n : Nat),
      (newRandoms Trace.nil (tr.append (RndE n))).map (·.1) =
        (newRandoms Trace.nil tr).map (·.1) ++ [randTerm tr.length n] :=
    fun tr n => hstep tr (RndE n)
  have hnet : ∀ (tr : ExecTrace) (m : DY.Bytes),
      (newRandoms Trace.nil (tr.append (NetE m))).map (·.1) = (newRandoms Trace.nil tr).map (·.1) := by
    intro tr m; rw [hstep]; exact List.append_nil _
  have hevp : ∀ (tr : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent),
      (newRandoms Trace.nil (tr.append (EvP ev))).map (·.1) = (newRandoms Trace.nil tr).map (·.1) := by
    intro tr ev; rw [hstep]; exact List.append_nil _
  have hstp : ∀ (tr : ExecTrace) (me : DY.Participant) (s : DY.Libsignal.PQXDH.PQXDHState),
      (newRandoms Trace.nil (tr.append (StP me s))).map (·.1) = (newRandoms Trace.nil tr).map (·.1) := by
    intro tr me s; rw [hstep]; exact List.append_nil _
  have hl1 : setupTr1.length = 5 := by
    simp [setupTr1, registerIdentityTr, Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl2 : setupTr2.length = 10 := by
    unfold setupTr2 registerIdentityTr
    simp [hl1, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hl3 : setupTr3.length = 16 := by
    unfold setupTr3 genSignedPrekeyTr
    simp [hl2, Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
  rw [setupRandoms, setupTrace_r0_eq]
  unfold setupTr0 genPQPrekeyTr; dsimp only; rw [hl3]
  unfold setupTr3 genSignedPrekeyTr; dsimp only; rw [hl2]
  unfold setupTr2 registerIdentityTr; dsimp only; rw [hl1]
  unfold setupTr1 registerIdentityTr; dsimp only
  simp only [hrnd, hnet, hevp, hstp]
  rw [hnil]
  simp only [Symbolic.DYBridge.DY.Trace.length_eq_1, Symbolic.DYBridge.DY.Trace.append_eq_1,
    Symbolic.DYBridge.DY.Trace.length_eq_2]
  rfl


end Step2Part2D

end
end Symbolic.BugInjection.Proofs.SyntheticSkippedKeyReplay
