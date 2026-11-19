/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Gamma
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.BobStartRun
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-! # Step Projections, Coin-Pinning, `PkiUnchanged`, & `OnlyAliceDone` (`AuxA.lean`) -/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Participant Trace Traceful ExecTrace ExecTraceTypes TraceEntryHas)
open DY.DiffieHellman (dhPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH (PQXDHState PQXDHEvent KeyKind AliceHandshakeOut)
open DY.Libsignal.TripleRatchet (TRState TREvent RecvChain setRecvChain isCurrentSnapshot
  ensureReceiverChain messageDecrypt messageDecryptSkipped)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
  BundlePreKeyIds Move gamma slice randTerm rngEntry kyberCoinEntries setupTrace runSteps
  pendingPreKey bobDoneBaseKeys GhostWF DrawsMatch BytesMatchEntry stepIn)
open Symbolic.Swarm.COMPOSED.CompTrace (Preserves TRStEntry RndE NetE TRStE PQEvE CEvE TREvE
  at?_append_cases proj_inj_eq run_bind_fst)
open Symbolic.Swarm.CREF (bks_getEventAt_of_le)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (gamma_randTerm_eq run_bind_pure_snd)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB t1 t2 t3 t4 t1_length t2_length t3_length t4_length)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
  (iniAliceStartTr getEventAt_pq_iniAliceStartTr)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0 (rcprI0)

attribute [local irreducible] ev

/-! ## 1. `Step` Projections, `PeeledValid` Monotonicity, & `DrawsMatch` Helpers -/

theorem step_le_next (s : Step) (tr : ExecTrace) : tr ≤ s.next tr :=
  ((reachability.step s.toInput).2.run tr).2.property

theorem runSteps_append : ∀ (pre ss : List Step) (tr : ExecTrace),
    runSteps (pre ++ ss) tr = runSteps ss (runSteps pre tr)
  | [], _, _ => rfl
  | s :: pre, ss, tr => runSteps_append pre ss (s.next tr)

theorem runSteps_le : ∀ (ss : List Step) (tr : ExecTrace), tr ≤ runSteps ss tr
  | [], tr => DY.Trace.le_refl tr
  | s :: ss, tr => DY.Trace.le_trans _ _ _ (step_le_next s tr) (runSteps_le ss (s.next tr))

theorem peeledValid_trace_le {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} :
    ∀ {j : Nat} {initIds : Option BundlePreKeyIds}
      {tr : ExecTrace} {cs : List PeeledCall} {ss : List Step},
      PeeledValid r S g visAll j initIds tr cs ss →
      tr ≤ runSteps ss tr
  | _, _, tr, _, tail, .nil _ => runSteps_le tail tr
  | _, _, tr, c :: _, _, .cons _ _ _ _ _ hpv => by
    rw [runSteps_append]
    dsimp only [runSteps]
    exact DY.Trace.le_trans _ _ _
      (DY.Trace.le_trans _ _ _ (runSteps_le c.pre tr) (step_le_next c.s _))
      (peeledValid_trace_le hpv)

theorem bobDoneBaseKeys_mono {tr tr' : ExecTrace} (hle : tr ≤ tr') :
    bobDoneBaseKeys tr ⊆ bobDoneBaseKeys tr' := by
  intro ek hek
  unfold bobDoneBaseKeys at hek ⊢
  obtain ⟨i, hi_mem, hfind⟩ := List.mem_filterMap.mp hek
  have hi : i < tr.length := List.mem_range.mp hi_mem
  refine List.mem_filterMap.mpr
    ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)), ?_⟩
  rw [bks_getEventAt_of_le PQXDHEvent hle hi]
  exact hfind

theorem setRecvChain_map_ratchetKey (recv : List RecvChain) (c' : RecvChain) :
    (setRecvChain recv c').map (·.ratchetKey) = recv.map (·.ratchetKey) := by
  unfold setRecvChain
  induction recv with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.map]
    rw [ih]
    split
    · next h => rw [beq_iff_eq.mp h]
    · rfl

theorem preCond_of_stepIn (c : DY.ReachabilityConfig)
    [inst : DY.ReachabilityConfig.HasStep c reachability]
    (x : c.Input) (tr : ExecTrace) (h : reachability.PreCond (stepIn c x) tr) :
    c.PreCond x tr :=
  (inst.pf_pre x tr).mpr h

theorem preCond_messageEncrypt {me : Participant} {stateIdx cl pq : Nat} {tr : ExecTrace}
    (h : (Step.messageEncrypt me stateIdx cl pq).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    (me, stateIdx, cl, pq) tr h

theorem preCond_messageDecrypt {me : Participant} {stateIdx mIdx pq : Nat} {spqr : UInt32}
    {tr : ExecTrace} (h : (Step.messageDecrypt me stateIdx mIdx pq spqr).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageDecrypt.reachability
    (me, stateIdx, mIdx, pq, spqr) tr h

theorem preCond_messageDecryptSkipped {me : Participant} {stateIdx mIdx sk pq : Nat}
    {spqr : UInt32} {tr : ExecTrace}
    (h : (Step.messageDecryptSkipped me stateIdx mIdx sk pq spqr).PreCond tr) :
    isCurrentSnapshot tr stateIdx = true :=
  preCond_of_stepIn DY.Libsignal.TripleRatchet.messageDecryptSkipped.reachability
    (me, stateIdx, mIdx, sk, pq, spqr) tr h

theorem step_next_bobStart (b a : Participant) (kh : DY.Libsignal.PQXDH.BobKeyHandles)
    (regA : Nat) (mh : DY.Libsignal.PQXDH.PreKeyMsgHandles) (pqIdx : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.bobStart b a kh regA mh pqIdx spqr).next tr =
      (Move.bobStart b a kh regA mh pqIdx spqr 0).next tr := by
  dsimp only [Move.next, Move.act, Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

theorem step_ok_encrypt (me : Participant) (stateIdx cl pq : Nat) (tr : ExecTrace) :
    (Step.messageEncrypt me stateIdx cl pq).ok tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq).run tr).1.isSome :=
  stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr

theorem step_next_encrypt (me : Participant) (stateIdx cl pq : Nat) (tr : ExecTrace) :
    (Step.messageEncrypt me stateIdx cl pq).next tr =
      ((DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq).run tr).2.val :=
  Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next
    DY.Libsignal.TripleRatchet.messageEncrypt.reachability (me, stateIdx, cl, pq) tr

theorem step_ok_encryptAbort_false (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.messageEncryptAbort me stateIdx).ok tr = false := by
  unfold Step.ok Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, stateIdx) tr]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability,
    DY.Libsignal.TripleRatchet.messageEncryptAbort]
  rw [run_bind_fst]
  rcases ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | _
  · rfl
  · dsimp only
    rw [run_bind_fst, (Symbolic.Swarm.CREF.TR.Runs.genRand _ 32).1]
    dsimp only
    rw [DY.Traceful.run_failure]
    rfl

theorem step_ok_decrypt (me : Participant) (stateIdx mIdx pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecrypt me stateIdx mIdx pq spqr).ok tr =
      ((messageDecrypt me stateIdx mIdx pq spqr).run tr).1.isSome :=
  stepIn_ok messageDecrypt.reachability (me, stateIdx, mIdx, pq, spqr) tr

theorem step_next_decrypt (me : Participant) (stateIdx mIdx pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecrypt me stateIdx mIdx pq spqr).next tr =
      (Move.decrypt me stateIdx mIdx pq spqr false).next tr := by
  dsimp only [Move.next, Move.act, Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
  exact (run_bind_pure_snd _ tr).symm

theorem step_ok_decryptSkipped (me : Participant) (stateIdx mIdx sk pq : Nat) (spqr : UInt32)
    (tr : ExecTrace) :
    (Step.messageDecryptSkipped me stateIdx mIdx sk pq spqr).ok tr =
      ((messageDecryptSkipped me stateIdx mIdx sk pq spqr).run tr).1.isSome :=
  stepIn_ok messageDecryptSkipped.reachability (me, stateIdx, mIdx, sk, pq, spqr) tr

theorem drawsMatch_single_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll rest : List VisEntry} {ts : Nat} {coins : HwBytes}
    (hgwf : GhostWF g visAll)
    (hmem : rngEntry (randTerm ts 32) ∈ visAll)
    (hdr : DrawsMatch rcprI0 r S g (rngEntry (randTerm ts 32) :: rest) coins) :
    gamma rcprI0 S g (randTerm ts 32) = coins.take 32 := by
  obtain ⟨pieces, _, hpref, hfa⟩ := hdr
  obtain ⟨p, ps, hbm, _, rfl⟩ := List.forall₂_cons_right_iff.mp hfa
  unfold BytesMatchEntry rngEntry at hbm
  dsimp only [List.map] at hbm
  have hp_eq : gamma rcprI0 S g (randTerm ts 32) = p := List.singleton_inj.mp hbm.2
  have hlen_sig : (g.σ ts 32).length = 32 :=
    hgwf.1 _ hmem rfl ts 32 (by decide) (by simp [rngEntry])
  have hp_len : p.length = 32 := by
    rw [← hp_eq, gamma_randTerm_eq _ _ _ _ _ (by decide)]
    exact hlen_sig
  obtain ⟨tail, hcoins⟩ := hpref
  change p ++ ps.flatten ++ tail = coins at hcoins
  rw [hp_eq, ← hcoins, List.append_assoc, ← hp_len, List.take_left]

private theorem forall₂_append_inv {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys₁ ys₂ : List β}
    (h : List.Forall₂ R xs (ys₁ ++ ys₂)) :
    xs.take ys₁.length ++ xs.drop ys₁.length = xs ∧
    List.Forall₂ R (xs.take ys₁.length) ys₁ ∧
    List.Forall₂ R (xs.drop ys₁.length) ys₂ := by
  refine ⟨List.take_append_drop _ _, ?_⟩
  induction ys₁ generalizing xs with
  | nil => exact ⟨.nil, by simpa using h⟩
  | cons y ys₁ ih =>
    cases xs with
    | nil => cases h
    | cons x xs =>
      cases h with
      | cons hx hxs =>
        obtain ⟨h1, h2⟩ := ih hxs
        exact ⟨.cons hx h1, h2⟩

private theorem flatten_len_of_all_4 :
    ∀ {xs : List HwBytes}, (∀ x ∈ xs, x.length = 4) → xs.flatten.length = 4 * xs.length
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x List.mem_cons_self
    have hxs := flatten_len_of_all_4 (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hx, hxs]; omega

private theorem flatten_drop_4mul_head? {xs : List HwBytes}
    (h4 : ∀ x ∈ xs, x.length = 4) :
    ∀ {j : Nat} (hj : j < xs.length), (xs.flatten.drop (4 * j)).head? = xs[j].head? := by
  induction xs with
  | nil => intro j hj; simp at hj
  | cons x xs ih =>
    intro j hj
    have hx4 : x.length = 4 := h4 x List.mem_cons_self
    have hxs4 : ∀ y ∈ xs, y.length = 4 := fun y hy => h4 y (List.mem_cons_of_mem _ hy)
    cases j with
    | zero =>
      simp only [Nat.mul_zero, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
      cases x with | nil => simp at hx4 | cons _ _ => rfl
    | succ j' =>
      have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [show 4 * (j' + 1) = x.length + 4 * j' by omega,
          List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
          List.nil_append, Nat.add_sub_cancel_left]
      exact ih hxs4 hj'

theorem ev0_draws_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {ts0 : Nat} {anc : Option Nat}
    (hgwf : GhostWF g visAll)
    (hsub : ∀ w ∈ (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }]), w ∈ visAll)
    (hdr : DrawsMatch rcprI0 r S g
      (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }])
      (ev 0).coins) :
    gamma rcprI0 S g (randTerm ts0 32) = slice (ev 0).coins 0 32 ∧
    gamma rcprI0 S g (randTerm (ts0 + 1) 32) = ev0KyberEnt ∧
    gamma rcprI0 S g (randTerm (ts0 + 2) 32) = slice (ev 0).coins 160 32 := by
  obtain ⟨pieces, _, hpref, hrel⟩ := hdr
  simp only [List.cons_append] at hrel hsub
  cases pieces with
  | nil => cases hrel
  | cons p0 ps1 =>
    cases hrel with
    | cons h0 hrel1 =>
      have hp0_eq : gamma rcprI0 S g (randTerm ts0 32) = p0 := by simpa [rngEntry] using h0.2
      have hp0_len : p0.length = 32 := by
        have hmem0 : rngEntry (randTerm ts0 32) ∈ visAll := hsub _ List.mem_cons_self
        have hsig := hgwf.1 _ hmem0 rfl ts0 32 (by decide) (by simp [rngEntry])
        rw [← hp0_eq]; unfold randTerm; rw [gamma_rand]; simpa using hsig
      obtain ⟨hps1_split, hrel_kem, hrel_last⟩ := forall₂_append_inv hrel1
      have hkem_len : (kyberCoinEntries (randTerm (ts0 + 1) 32)).length = 32 := by
        simp [kyberCoinEntries]
      set ps_kem := ps1.take 32
      have hps_kem_eq : ps1.take (kyberCoinEntries (randTerm (ts0 + 1) 32)).length = ps_kem := by
        rw [hkem_len]
      rw [hps_kem_eq] at hrel_kem hps1_split
      rw [hkem_len] at hrel_last hps1_split
      cases hdrop : ps1.drop 32 with
      | nil => rw [hdrop] at hrel_last; cases hrel_last
      | cons p33 ps_rem =>
        rw [hdrop] at hrel_last hps1_split
        cases hrel_last with
        | cons hlast hrem =>
          cases ps_rem with
          | cons _ _ => cases hrem
          | nil =>
            have hp33_eq : gamma rcprI0 S g (randTerm (ts0 + 2) 32) = p33 := by
              simpa [rngEntry] using hlast.2
            have hp33_len : p33.length = 32 := by
              have hmem33 : { rngEntry (randTerm (ts0 + 2) 32) with anchor := anc } ∈ visAll :=
                hsub _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
              have hsig := hgwf.1 _ hmem33 rfl (ts0 + 2) 32 (by decide) (by simp [rngEntry])
              rw [← hp33_eq]; unfold randTerm; rw [gamma_rand]; simpa using hsig
            have hps_kem_len : ps_kem.length = 32 := hrel_kem.length_eq.trans hkem_len
            have hkem_item : ∀ (j : Nat) (hj : j < 32),
                (ps_kem[j]'(by omega)).length = 4 ∧
                (gamma rcprI0 S g (randTerm (ts0 + 1) 32)).length = 32 ∧
                (ps_kem[j]'(by omega)).head? =
                  (gamma rcprI0 S g (randTerm (ts0 + 1) 32))[j]? := by
              intro j hj
              have hget := (List.forall₂_iff_get.mp hrel_kem).2 j
                (by omega) (by rw [hkem_len]; exact hj)
              simp only [List.get_eq_getElem, kyberCoinEntries, List.getElem_map,
                List.getElem_range] at hget
              obtain ⟨_, hlen4, t, ht_eq, hlen32, hhead⟩ := hget
              simp only [List.cons.injEq, and_true] at ht_eq; subst ht_eq
              exact ⟨hlen4, hlen32, hhead⟩
            have hall4 : ∀ q ∈ ps_kem, q.length = 4 := by
              intro q hq; obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
              exact (hkem_item j (by omega)).1
            have hflat_kem_len : ps_kem.flatten.length = 128 := by
              rw [flatten_len_of_all_4 hall4, hps_kem_len]
            have hflat_eq : (p0 :: ps1).flatten = p0 ++ (ps_kem.flatten ++ p33) := by
              rw [← hps1_split]; simp [List.flatten_cons, List.flatten_append]
            obtain ⟨coins_Fact_len, _, _, hent_len, _, hent_idx⟩ := ev0_coins_facts
            obtain ⟨tail_rem, hcoins_eq⟩ := hpref
            rw [hflat_eq] at hcoins_eq
            have htail_nil : tail_rem = [] := by
              have hlen := congrArg List.length hcoins_eq
              simp only [List.length_append, hp0_len, hflat_kem_len, hp33_len,
                coins_Fact_len] at hlen
              exact List.eq_nil_of_length_eq_zero (by omega)
            rw [htail_nil, List.append_nil] at hcoins_eq
            have hs0 : slice (ev 0).coins 0 32 = p0 := by
              rw [← hcoins_eq]; unfold slice; simp only [List.drop_zero]
              exact List.take_left' hp0_len
            have hs160 : slice (ev 0).coins 160 32 = p33 := by
              rw [← hcoins_eq, ← List.append_assoc]; unfold slice
              have h160 : (p0 ++ ps_kem.flatten).length = 160 := by simp [hp0_len, hflat_kem_len]
              rw [List.drop_left' h160, List.take_of_length_le (by omega)]
            have he1_eq : gamma rcprI0 S g (randTerm (ts0 + 1) 32) = ev0KyberEnt := by
              have hlen_e1 : (gamma rcprI0 S g (randTerm (ts0 + 1) 32)).length = 32 :=
                (hkem_item 0 (by decide)).2.1
              apply List.ext_getElem?; intro j
              by_cases hj : j < 32
              · have hhead_j := (hkem_item j hj).2.2
                have hdrop_kem := flatten_drop_4mul_head? hall4 (j := j) (by omega)
                have hcoins_drop : ((ev 0).coins.drop (32 + 4 * j)).head? =
                    (ps_kem.flatten.drop (4 * j)).head? := by
                  rw [← hcoins_eq, show 32 + 4 * j = p0.length + 4 * j by omega,
                      List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
                      List.nil_append, Nat.add_sub_cancel_left, List.drop_append]
                  cases hdk : ps_kem.flatten.drop (4 * j) with
                  | nil =>
                    have hlen_dk := congrArg List.length hdk
                    simp only [List.length_drop, List.length_nil, hflat_kem_len] at hlen_dk; omega
                  | cons _ _ => rfl
                rw [← hhead_j, ← hdrop_kem, ← hcoins_drop, hent_idx j hj]
              · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
            exact ⟨hp0_eq.trans hs0.symm, he1_eq, hp33_eq.trans hs160.symm⟩

/-! ## 2. `PkiUnchanged` and `OnlyAliceDone` -/

abbrev PQStEntry :=
  DY.PersistentGlobalState.State.ExecEntryT (DY.PersistentLocalState.LocalState PQXDHState)
abbrev PQEvEntry := DY.ProtocolEvent.ExecEntryT PQXDHEvent

/-- After `setupTrace r = t4`, no step adds any `PQXDHState` or `IdentityRegistered` entry. -/
def PkiUnchanged (tr : ExecTrace) : Prop :=
  t4 ≤ tr ∧
  (∀ i p kst, 22 ≤ i → (tr.at? i : Option PQStEntry) ≠ some ⟨⟨p, kst⟩⟩) ∧
  (∀ i p pk vk c, 22 ≤ i → (tr.at? i : Option PQEvEntry) ≠ some ⟨.IdentityRegistered p pk vk c⟩)

theorem pkiUnchanged_t4 : PkiUnchanged t4 := by
  refine ⟨DY.Trace.le_refl t4, ?_, ?_⟩
  · intro i p kst hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry) t4 i
    rw [hat, t4_length] at hlt; simp at hlt; omega
  · intro i p pk vk c hi hat
    have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry) t4 i
    rw [hat, t4_length] at hlt; simp at hlt; omega

private theorem pkiUnchanged_append_non {E : Type} [ExecTraceTypes.Has E]
    {tr : ExecTrace} (h : PkiUnchanged tr) (e : E)
    (hnoneSt : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQStEntry) = none)
    (hnoneEv : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntry) = none) :
    PkiUnchanged (tr.append e) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr e), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · rw [hnoneSt] at hproj; cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · rw [hnoneEv] at hproj; cases hproj

private theorem pkiUnchanged_append_pqEv {tr : ExecTrace} (h : PkiUnchanged tr)
    (ev : PQXDHEvent) (hnreg : ∀ p pk vk c, ev ≠ .IdentityRegistered p pk vk c) :
    PkiUnchanged (tr.append (PQEvE ev)) := by
  refine ⟨DY.Trace.le_trans _ _ _ h.1 (DY.Trace.append_le tr _), ?_, ?_⟩
  · intro i p kst hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.1 i p kst hi hat0
    · cases hproj
  · intro i p pk vk c hi hat
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h.2.2 i p pk vk c hi hat0
    · simp only [PQEvE, proj_inj_eq, Option.some.injEq] at hproj
      injection hproj with hev; exact hnreg p pk vk c hev

theorem preserves_prodCasesOn {Inv : ExecTrace → Prop} {α β γ : Type} (p : α × β)
    (f : α → β → Traceful γ) (hf : ∀ a b, Preserves Inv (f a b)) :
    Preserves Inv (Prod.casesOn p f) := by rcases p with ⟨a, b⟩; exact hf a b

theorem preserves_optionCasesOn {Inv : ExecTrace → Prop} {α β : Type} (o : Option α)
    (noneCase : Traceful β) (someCase : α → Traceful β) (hn : Preserves Inv noneCase)
    (hs : ∀ a, Preserves Inv (someCase a)) : Preserves Inv (Option.casesOn o noneCase someCase) := by
  rcases o with _ | a; exact hn; exact hs a

private theorem preserves_pki_genRand (n : Nat) :
    Preserves PkiUnchanged (DY.Random.genRand n : Traceful DY.Bytes) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.genRand tr n).2.symm ▸
    pkiUnchanged_append_non h (RndE n) rfl rfl

private theorem preserves_pki_sendMessage (m : DY.Bytes) :
    Preserves PkiUnchanged (DY.Network.sendMessage m) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.sendMessage tr m).2.symm ▸
    pkiUnchanged_append_non h (NetE m) rfl rfl

private theorem preserves_pki_storeTR (p : Participant) (st : TRState) :
    Preserves PkiUnchanged (DY.PersistentLocalState.storeLocalState p st) :=
  fun tr h => by rw [storeLocalState_tr_snd_eq]; exact pkiUnchanged_append_non h (TRStE p st) rfl rfl

private theorem preserves_pki_logC (ev : ComposedEvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (CEvE ev) rfl rfl

private theorem preserves_pki_logTR (ev : TREvent) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => by rw [logEvent_snd_eq]; exact pkiUnchanged_append_non h (TREvE ev) rfl rfl

private theorem preserves_pki_logPQ (ev : PQXDHEvent)
    (hnreg : ∀ p pk vk c, ev ≠ .IdentityRegistered p pk vk c) :
    Preserves PkiUnchanged (DY.ProtocolEvent.logEvent ev) :=
  fun tr h => (Symbolic.Swarm.CREF.TR.Runs.logEvent tr ev).2.symm ▸
    pkiUnchanged_append_pqEv h ev hnreg

private theorem preserves_pki_getKey (p : Participant) (h : Nat) (kind : KeyKind) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.getKey p h kind) :=
  Preserves.bind (Preserves.getLocalState_pq p h) fun _ =>
    Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _

private theorem preserves_pki_lookupIdentity (p : Participant) (h : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.lookupIdentity p h) := by
  unfold DY.Libsignal.PQXDH.lookupIdentity
  refine Preserves.bind (Preserves.getEntry h) fun _ => ?_
  split
  · exact Preserves.bind (Preserves.guardP _) fun _ => Preserves.pure _
  · exact Preserves.failure

private theorem preserves_pki_logSkippedKeys (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (pk : DY.Bytes) (rIdx src : Nat) (ck : DY.Bytes) (n : UInt32) (k : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n k) := by
  induction k generalizing ck n with
  | zero => exact Preserves.pure _
  | succ k ih => exact Preserves.bind (preserves_pki_logTR _) fun _ => ih _ _

private theorem preserves_pki_dhRatchetStep (st : TRState) (pk : DY.Bytes) :
    Preserves PkiUnchanged (DY.Libsignal.TripleRatchet.dhRatchetStep st pk) := by
  unfold DY.Libsignal.TripleRatchet.dhRatchetStep
  rcases DY.Libsignal.TripleRatchet.recvHalfStep st.toDRState pk with _ | ⟨_, _⟩
  · exact Preserves.failure
  · exact Preserves.bind (preserves_pki_genRand 32) fun _ => Preserves.pure _

private theorem preserves_pki_ensureReceiverChain (st : TRState) (pk : DY.Bytes) :
    Preserves PkiUnchanged (ensureReceiverChain st pk) := by
  unfold ensureReceiverChain; split
  · exact Preserves.pure _
  · exact Preserves.bind (preserves_pki_dhRatchetStep st pk) fun _ => Preserves.pure _

private theorem preserves_pki_logMKAndStore (me : Participant)
    (s : DY.Libsignal.TripleRatchet.SessionInfo) (dir : DY.Libsignal.TripleRatchet.KeyDir)
    (seed pqSalt : DY.Bytes) (n : UInt32) (r par : Nat) (st : TRState) :
    Preserves PkiUnchanged
      (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
  Preserves.bind (preserves_pki_logTR _) fun _ => preserves_pki_storeTR me st

local macro "pki_tac" : tactic => `(tactic| repeat (first
  | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
  | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
  | with_reducible apply Preserves.failure | with_reducible apply preserves_pki_genRand
  | with_reducible apply preserves_pki_storeTR | with_reducible apply preserves_pki_sendMessage
  | with_reducible apply Preserves.getLocalState_tr | with_reducible apply Preserves.getLocalState_pq
  | with_reducible apply preserves_pki_getKey | with_reducible apply preserves_pki_lookupIdentity
  | with_reducible apply Preserves.receiveMessage | with_reducible apply Preserves.getEntry
  | with_reducible apply Preserves.receiveSignalMsg
  | with_reducible apply Preserves.verifyMacAndDecrypt
  | with_reducible apply preserves_pki_dhRatchetStep
  | with_reducible apply preserves_pki_ensureReceiverChain
  | with_reducible apply preserves_pki_logSkippedKeys | with_reducible apply Preserves.guardP
  | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
  | with_reducible apply Preserves.requireTracePredicate
  | with_reducible apply Preserves.traceLength
  | with_reducible apply preserves_pki_logMKAndStore
  | (apply preserves_pki_logPQ; intros; rintro ⟨⟩)
  | with_reducible apply preserves_pki_logC
  | with_reducible apply preserves_pki_logTR | split | with_reducible intro))

private theorem preserves_pki_decryptInMemory
    (st0 : TRState) (msg : DY.Libsignal.TripleRatchet.TRSignalMsg)
    (pqIdx : Nat) (spqrMsgIdx : UInt32) :
    Preserves PkiUnchanged
      (DY.Libsignal.TripleRatchet.decryptInMemory st0 msg pqIdx spqrMsgIdx) := by
  unfold DY.Libsignal.TripleRatchet.decryptInMemory; pki_tac

private theorem preserves_pki_logRatchet
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) (me : Participant) :
    Preserves PkiUnchanged (p.logRatchet me) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.logRatchet; pki_tac

private theorem preserves_pki_commit
    (p : DY.Libsignal.TripleRatchet.PendingDecrypt) (me : Participant)
    (par : Option Nat := none) :
    Preserves PkiUnchanged (p.commit me par) := by
  unfold DY.Libsignal.TripleRatchet.PendingDecrypt.commit
  cases par <;> (dsimp only; pki_tac)

private theorem preserves_pki_bobHandshake (b a : Participant)
    (kh : DY.Libsignal.PQXDH.BobKeyHandles) (regIdxA ekIdx ctIdx : Nat) :
    Preserves PkiUnchanged (DY.Libsignal.PQXDH.bobHandshake b a kh regIdxA ekIdx ctIdx) := by
  unfold DY.Libsignal.PQXDH.bobHandshake; pki_tac

theorem pkiUnchanged_runSteps_network :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) → PkiUnchanged tr → PkiUnchanged (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : PkiUnchanged ((Step.network m).next tr) := by
      rw [next_network]; exact pkiUnchanged_append_non h (NetE m) rfl rfl
    exact pkiUnchanged_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem pkiUnchanged_step_party {s : Step} {tr : ExecTrace}
    (hcls : s.cls = .party) (hpki : PkiUnchanged tr) : PkiUnchanged (s.next tr) := by
  cases s with
  | aliceStart a b idIdx regB bh =>
    have hact : Preserves PkiUnchanged (DY.Libsignal.Composed.aliceStart a b idIdx regB bh) := by
      unfold DY.Libsignal.Composed.aliceStart DY.Libsignal.PQXDH.aliceHandshake; pki_tac
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | bobStart b a kh regA mh pqIdx spqr =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.Composed.bobStart b a kh regA mh pqIdx spqr) := by
      unfold DY.Libsignal.Composed.bobStart
      refine Preserves.bind (preserves_pki_bobHandshake b a kh regA mh.ek mh.ct) fun o => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mh.msg) fun msg => ?_
      refine Preserves.bind (preserves_pki_decryptInMemory _ msg pqIdx spqr) fun pending => ?_
      cases o.opk with
      | none =>
        dsimp only
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_pki_logPQ _ (by intros; rintro ⟨⟩)) fun _ => ?_
        refine Preserves.bind (preserves_pki_logRatchet pending b) fun _ => ?_
        refine Preserves.bind (preserves_pki_logC _) fun _ => ?_
        exact preserves_pki_commit pending b
      | some _ =>
        dsimp only
        refine Preserves.bind (Preserves.guardTrace _) fun _ => ?_
        refine Preserves.bind (preserves_pki_logPQ _ (by intros; rintro ⟨⟩)) fun _ => ?_
        refine Preserves.bind Preserves.traceLength fun _ => ?_
        refine Preserves.bind (preserves_pki_logPQ _ (by intros; rintro ⟨⟩)) fun _ => ?_
        refine Preserves.bind (preserves_pki_logRatchet pending b) fun _ => ?_
        refine Preserves.bind (preserves_pki_logC _) fun _ => ?_
        exact preserves_pki_commit pending b
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | messageEncrypt me stateIdx cl pq =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
      unfold DY.Libsignal.TripleRatchet.messageEncrypt; pki_tac
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | messageEncryptAbort me stateIdx =>
    have hact : Preserves PkiUnchanged
        (DY.Libsignal.TripleRatchet.messageEncryptAbort me stateIdx) := by
      unfold DY.Libsignal.TripleRatchet.messageEncryptAbort; pki_tac
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | messageDecrypt me stateIdx mIdx pq spqr =>
    have hact : Preserves PkiUnchanged (messageDecrypt me stateIdx mIdx pq spqr) := by
      unfold messageDecrypt
      refine Preserves.bind (Preserves.getLocalState_tr me stateIdx) fun st => ?_
      refine Preserves.bind (Preserves.receiveSignalMsg mIdx) fun msg => ?_
      refine Preserves.bind (preserves_pki_decryptInMemory st msg pq spqr) fun pending => ?_
      refine Preserves.bind (preserves_pki_logRatchet pending me) fun _ => ?_
      exact preserves_pki_commit pending me (some stateIdx)
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | messageDecryptSkipped me stateIdx mIdx sk pq spqr =>
    have hact : Preserves PkiUnchanged (messageDecryptSkipped me stateIdx mIdx sk pq spqr) := by
      unfold messageDecryptSkipped; pki_tac
    dsimp only [Step.next, Step.toInput]
    erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr hpki
  | _ => simp [Step.cls] at hcls

theorem t1_t2_t3_t4_eq :
    t1 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr Trace.nil "alice" ∧
    t2 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr t1 "bob" ∧
    t3 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr t2 "bob" ikB ∧
    t4 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr t3 "bob" ikB := by
  have nil_len : (Trace.nil : ExecTrace).length = 0 := Symbolic.DYBridge.DY.Trace.length_eq_1
  have someEventB_nil : ∀ p : PQXDHEvent → Bool,
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent Trace.nil p = false := fun p => by
    rw [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?, nil_len]; rfl
  have someEventB_non : ∀ {E : Type} [ExecTraceTypes.Has E] (tr : ExecTrace) (x : E)
      (p : PQXDHEvent → Bool),
      (TraceEntryHas.proj (TraceEntryHas.inj x : ExecTrace.Entry) : Option PQEvEntry) = none →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent (tr.append x) p = false := by
    intro E _ tr x p hnone h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr x (List.mem_range.mp hi)]; exact h i hi
    · rw [at?_append_self_proj, hnone]
  have someEventB_ev : ∀ (tr : ExecTrace) (ev : PQXDHEvent) (p : PQXDHEvent → Bool),
      p ev = false → DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent tr p = false →
      DY.Libsignal.TripleRatchet.anyEventOnTrace PQXDHEvent
        (tr.append (Symbolic.Proofs.Tests.Shared.Composed.Runs.EvP ev)) p = false := by
    intro tr ev p hp h
    simp only [DY.Libsignal.TripleRatchet.anyEventOnTrace_eq_at?] at h ⊢
    rw [append_len, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · rw [List.any_eq_false] at h ⊢
      intro i hi
      rw [at?_append_of_lt tr _ (List.mem_range.mp hi)]; exact h i hi
    · rw [Trace.at?_append]; exact hp
  have ht1 : t1 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr Trace.nil "alice" :=
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.registerIdentity
      (by unfold DY.Libsignal.PQXDH.isRegisteredB; rw [someEventB_nil]; rfl)).2
  have ht2 : t2 = Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr t1 "bob" := by
    refine (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.registerIdentity ?_).2
    unfold DY.Libsignal.PQXDH.isRegisteredB; rw [ht1]
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [someEventB_non _ _ _ rfl (someEventB_non _ _ _ rfl
      (someEventB_non _ _ _ rfl (someEventB_ev _ _ _ rfl
        (someEventB_non _ _ _ rfl (someEventB_nil _)))))]
    rfl
  have hb2 : t2.at? 9 = some (Symbolic.Proofs.Tests.Shared.Composed.Runs.StP "bob"
      { kind := .identity, sk := ikB }) := by
    rw [ht2]; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr]
    rw [t1_length]
    exact at?_append_at _ _ (by simp only [append_len, t1_length])
  have ht3 : t3 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr t2 "bob" ikB :=
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.genSignedPrekey hb2).2
  have h23 : t2 ≤ t3 := by
    rw [ht3]; iterate 5 refine le_append_of_le ?_ _
    exact Trace.append_le _ _
  have ht4 : t4 = Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr t3 "bob" ikB :=
    (Symbolic.Proofs.Tests.Shared.Composed.Runs.Runs.genPQPrekey (at?_mono h23 hb2)).2
  exact ⟨ht1, ht2, ht3, ht4⟩

private theorem t4_pqSt_cases {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (t4.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t1_t2_t3_t4_eq
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQStEntry) = none →
      ((tr0.append e).at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ →
      (tr0.at? j : Option PQStEntry) = some ⟨⟨p, kst⟩⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  rw [ht4] at hat; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr] at hat
  replace hat := peel_non rfl (peel_non rfl hat)
  rcases at?_append_cases hat with ⟨_, hat3⟩ | ⟨_, hproj4⟩
  · replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
    rw [ht3] at hat3
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr] at hat3
    replace hat3 := peel_non rfl (peel_non rfl hat3)
    rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
    · replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
      rw [ht2] at hat2
      dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr] at hat2
      rcases at?_append_cases hat2 with ⟨_, hat2'⟩ | ⟨_, hproj2⟩
      · iterate 4 replace hat2' := peel_non rfl hat2'
        rw [ht1] at hat2'
        dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr] at hat2'
        rcases at?_append_cases hat2' with ⟨_, hat1'⟩ | ⟨_, hproj1⟩
        · iterate 4 replace hat1' := peel_non rfl hat1'
          have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQStEntry)
            (Trace.nil : ExecTrace) i
          rw [hat1', Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
        · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1
          cases hproj1; exact Or.inl ⟨rfl, rfl⟩
      · rw [t1_length] at hproj2
        cases hproj2; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rw [t2_length] at hproj3
      cases hproj3; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · rw [t3_length] at hproj4
    cases hproj4; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

private theorem t4_pqEv_cases {i : Nat} {ev0 : PQXDHEvent}
    (hat : (t4.at? i : Option PQEvEntry) = some ⟨ev0⟩) :
    ev0 = .IdentityRegistered "alice" (dhPk ikA) (DY.Signature.vk ikA) true ∨
    ev0 = .IdentityRegistered "bob" (dhPk ikB) (DY.Signature.vk ikB) true ∨
    (∃ p k, ev0 = .SignedPrekeyPublished p k) ∨
    (∃ p k, ev0 = .PQPrekeyPublished p k) := by
  obtain ⟨ht1, ht2, ht3, ht4⟩ := t1_t2_t3_t4_eq
  have peel_non : ∀ {E : Type} [ExecTraceTypes.Has E] {tr0 : ExecTrace} {e : E} {j : Nat},
      (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) : Option PQEvEntry) = none →
      ((tr0.append e).at? j : Option PQEvEntry) = some ⟨ev0⟩ →
      (tr0.at? j : Option PQEvEntry) = some ⟨ev0⟩ := by
    intro E _ tr0 e j hnone h
    rcases at?_append_cases h with ⟨_, h0⟩ | ⟨_, hp⟩
    · exact h0
    · rw [hnone] at hp; cases hp
  rw [ht4] at hat; dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genPQPrekeyTr] at hat
  replace hat := peel_non rfl (peel_non rfl (peel_non rfl hat))
  rcases at?_append_cases hat with ⟨_, hat3⟩ | ⟨_, hproj4⟩
  · replace hat3 := peel_non rfl (peel_non rfl hat3)
    rw [ht3] at hat3
    dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.genSignedPrekeyTr] at hat3
    replace hat3 := peel_non rfl (peel_non rfl (peel_non rfl hat3))
    rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hproj3⟩
    · replace hat2 := peel_non rfl (peel_non rfl hat2)
      rw [ht2] at hat2
      dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr] at hat2
      replace hat2 := peel_non rfl (peel_non rfl (peel_non rfl hat2))
      rcases at?_append_cases hat2 with ⟨_, hat1⟩ | ⟨_, hproj2⟩
      · replace hat1 := peel_non rfl hat1
        rw [ht1] at hat1
        dsimp only [Symbolic.Proofs.Tests.Shared.Composed.Runs.registerIdentityTr] at hat1
        replace hat1 := peel_non rfl (peel_non rfl (peel_non rfl hat1))
        rcases at?_append_cases hat1 with ⟨_, hat0⟩ | ⟨_, hproj1⟩
        · replace hat0 := peel_non rfl hat0
          have hlt := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry)
            (Trace.nil : ExecTrace) i
          rw [hat0, Symbolic.DYBridge.DY.Trace.length_eq_1] at hlt; simp at hlt
        · rw [Symbolic.DYBridge.DY.Trace.length_eq_1] at hproj1
          cases hproj1; exact Or.inl rfl
      · rw [t1_length] at hproj2
        cases hproj2; exact Or.inr (Or.inl rfl)
    · cases hproj3; exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · cases hproj4; exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))

private theorem t4_pqReg_cases {i : Nat} {p : Participant} {pk vk : DY.Bytes} {c : Bool}
    (hat : (t4.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  rcases t4_pqEv_cases hat with h1 | h2 | ⟨_, _, ⟨⟩⟩ | ⟨_, _, ⟨⟩⟩
  · cases h1; exact Or.inl ⟨rfl, rfl, rfl⟩
  · cases h2; exact Or.inr ⟨rfl, rfl, rfl⟩

theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem pki_pin_st {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {kst : PQXDHState}
    (hat : (tr.at? i : Option PQStEntry) = some ⟨⟨p, kst⟩⟩) :
    (p = "alice" ∧ kst = { kind := .identity, sk := ikA }) ∨
    (p = "bob" ∧ kst = { kind := .identity, sk := ikB }) ∨
    (p = "bob" ∧ kst = { kind := .signedPrekey, sk := spkB }) ∨
    (p = "bob" ∧ kst = { kind := .pqPrekey, sk := pqskB }) := by
  by_cases hlt : i < 22
  · rw [at?_of_le_lt hpki.1 (by rwa [t4_length])] at hat
    exact t4_pqSt_cases hat
  · exact False.elim (hpki.2.1 i p kst (by omega) hat)

theorem pki_pin_reg {tr : ExecTrace} (hpki : PkiUnchanged tr)
    {i : Nat} {p : Participant} {pk vk : DY.Bytes} {c : Bool}
    (hat : (tr.at? i : Option PQEvEntry) = some ⟨.IdentityRegistered p pk vk c⟩) :
    (p = "alice" ∧ pk = dhPk ikA ∧ vk = DY.Signature.vk ikA) ∨
    (p = "bob" ∧ pk = dhPk ikB ∧ vk = DY.Signature.vk ikB) := by
  by_cases hlt : i < 22
  · rw [at?_of_le_lt hpki.1 (by rwa [t4_length])] at hat
    exact t4_pqReg_cases hat
  · exact False.elim (hpki.2.2 i p pk vk c (by omega) hat)

/-- Every `AliceDone` event logged on `tr` carries `(ek0, ct0)`. -/
def OnlyAliceDone (ek0 ct0 : DY.Bytes) (tr : ExecTrace) : Prop :=
  ∀ d a b ik1 ik2 spk pq opk ek ct keys,
    tr.getEventAt PQXDHEvent d = some (.AliceDone a b ik1 ik2 spk pq opk ek ct keys) →
    ek = ek0 ∧ ct = ct0

theorem onlyAliceDone_t4 (ek0 ct0 : DY.Bytes) : OnlyAliceDone ek0 ct0 t4 := by
  intro d a b ik1 ik2 spk pq opk ek ct keys hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : (t4.at? d : Option PQEvEntry) with _ | ⟨⟨ev0⟩⟩
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; dsimp only at hget
    injection hget with hget'
    subst hget'
    rcases t4_pqEv_cases hat with h1 | h2 | ⟨_, _, h3⟩ | ⟨_, _, h4⟩ <;>
      first | cases h1 | cases h2 | cases h3 | cases h4

theorem onlyAliceDone_append_non {E : Type} [ExecTraceTypes.Has E]
    {ek0 ct0 : DY.Bytes} {tr : ExecTrace} (h : OnlyAliceDone ek0 ct0 tr) (e : E)
    (hnone : (TraceEntryHas.proj (TraceEntryHas.inj e : ExecTrace.Entry) :
      Option PQEvEntry) = none) :
    OnlyAliceDone ek0 ct0 (tr.append e) := by
  intro d a b ik1 ik2 spk pq opk ek ct keys hget
  simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
  rcases hat : ((tr.append e).at? d : Option PQEvEntry) with _ | ⟨⟨ev0⟩⟩
  · rw [hat] at hget; cases hget
  · rw [hat] at hget; dsimp only at hget
    injection hget with hget'
    subst hget'
    rcases at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
    · exact h d a b ik1 ik2 spk pq opk ek ct keys
        (by simp [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1, hat0])
    · rw [hnone] at hproj; cases hproj

theorem onlyAliceDone_runSteps_network {ek0 ct0 : DY.Bytes} :
    ∀ (pre : List Step) {tr : ExecTrace},
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      OnlyAliceDone ek0 ct0 tr → OnlyAliceDone ek0 ct0 (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have hm : OnlyAliceDone ek0 ct0 ((Step.network m).next tr) := by
      rw [next_network]; exact onlyAliceDone_append_non h (NetE m) rfl
    exact onlyAliceDone_runSteps_network pre (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) hm

theorem onlyAliceDone_iniAliceStartTr {tr : ExecTrace} {a b : Participant}
    {o : AliceHandshakeOut} (h0 : OnlyAliceDone o.ek o.ct tr) :
    OnlyAliceDone o.ek o.ct (iniAliceStartTr tr a b o) := by
  have hle : tr ≤ iniAliceStartTr tr a b o := by
    unfold iniAliceStartTr; dsimp only
    iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
    exact DY.Trace.append_le _ _
  obtain ⟨hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8⟩ := getEventAt_pq_iniAliceStartTr tr a b o
  intro d a' b' ik1 ik2 spk pq opk ek ct keys hget
  by_cases hlt : d < tr.length
  · rw [bks_getEventAt_of_le PQXDHEvent hle hlt] at hget
    exact h0 d a' b' ik1 ik2 spk pq opk ek ct keys hget
  · by_cases hgt : tr.length + 9 ≤ d
    · have hlen : (iniAliceStartTr tr a b o).length = tr.length + 9 :=
        Symbolic.Swarm.CREF.length_iniAliceStartTr tr a b o
      simp only [Symbolic.DYBridge.DY.Trace.getEventAt_eq_1] at hget
      rcases hat : ((iniAliceStartTr tr a b o).at? d : Option PQEvEntry) with _ | _
      · rw [hat] at hget; cases hget
      · have := DY.Trace.at?_eq_some_implies_length_le (EntryT := PQEvEntry)
          (iniAliceStartTr tr a b o) d
        rw [hat, hlen] at this; simp at this; omega
    · have hd : d = tr.length + 0 ∨ d = tr.length + 1 ∨ d = tr.length + 2 ∨
          d = tr.length + 3 ∨ d = tr.length + 4 ∨ d = tr.length + 5 ∨
          d = tr.length + 6 ∨ d = tr.length + 7 ∨ d = tr.length + 8 := by omega
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [Nat.add_zero, hp0] at hget; cases hget
      · rw [hp1] at hget; cases hget
      · rw [hp2] at hget; cases hget
      · rw [hp3] at hget; cases hget
      · rw [hp4] at hget; cases hget
      · rw [hp5] at hget
        injection hget with h1
        injection h1 with _ _ _ _ _ _ _ hek hct _
        exact ⟨hek.symm, hct.symm⟩
      · rw [hp6] at hget; cases hget
      · rw [hp7] at hget; cases hget
      · rw [hp8] at hget; cases hget

theorem onlyAliceDone_messageEncrypt {ek0 ct0 : DY.Bytes} {tr : ExecTrace}
    {me : Participant} {stateIdx cl pq : Nat}
    (h0 : OnlyAliceDone ek0 ct0 tr) :
    OnlyAliceDone ek0 ct0 ((Step.messageEncrypt me stateIdx cl pq).next tr) := by
  have hact : Preserves (OnlyAliceDone ek0 ct0)
      (DY.Libsignal.TripleRatchet.messageEncrypt me stateIdx cl pq) := by
    have hlogTR : ∀ ev : TREvent,
        Preserves (OnlyAliceDone ek0 ct0) (DY.ProtocolEvent.logEvent ev) :=
      fun ev t h => by rw [logEvent_snd_eq]; exact onlyAliceDone_append_non h (TREvE ev) rfl
    have hstoreTR : ∀ p (st : TRState),
        Preserves (OnlyAliceDone ek0 ct0) (DY.PersistentLocalState.storeLocalState p st) :=
      fun p st t h => by rw [storeLocalState_tr_snd_eq]; exact onlyAliceDone_append_non h (TRStE p st) rfl
    have hgen : ∀ n, Preserves (OnlyAliceDone ek0 ct0) (DY.Random.genRand n : Traceful DY.Bytes) :=
      fun n t h => (Symbolic.Swarm.CREF.TR.Runs.genRand t n).2.symm ▸
        onlyAliceDone_append_non h (RndE n) rfl
    have hsend : ∀ m, Preserves (OnlyAliceDone ek0 ct0) (DY.Network.sendMessage m) :=
      fun m t h => (Symbolic.Swarm.CREF.TR.Runs.sendMessage t m).2.symm ▸
        onlyAliceDone_append_non h (NetE m) rfl
    have hlmk : ∀ s dir seed pqSalt n r par st,
        Preserves (OnlyAliceDone ek0 ct0)
          (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n r par st) :=
      fun _ _ _ _ _ _ _ st => Preserves.bind (hlogTR _) fun _ => hstoreTR me st
    unfold DY.Libsignal.TripleRatchet.messageEncrypt
    dsimp only at *
    repeat (first
      | with_reducible apply Preserves.bind | with_reducible apply preserves_prodCasesOn
      | with_reducible apply preserves_optionCasesOn | with_reducible apply Preserves.pure
      | with_reducible apply Preserves.failure | with_reducible apply hgen
      | with_reducible apply hsend | with_reducible apply hlogTR
      | with_reducible apply Preserves.getLocalState_tr
      | with_reducible apply Preserves.receiveMessage
      | with_reducible apply Preserves.getEntry | with_reducible apply Preserves.guardP
      | with_reducible apply Preserves.monadLiftErr | with_reducible apply Preserves.guardTrace
      | with_reducible apply Preserves.requireTracePredicate | with_reducible apply Preserves.traceLength
      | with_reducible apply hlmk | split | with_reducible intro)
  dsimp only [Step.next, Step.toInput]
  erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]; exact hact tr h0

theorem pendingPreKey_eq_of_onlyAliceDone {ek0 ct0 : DY.Bytes} {tr : ExecTrace} {stateIdx : Nat}
    {ek ct : DY.Bytes}
    (honly : OnlyAliceDone ek0 ct0 tr)
    (hpend : pendingPreKey tr stateIdx = some (ek, ct)) :
    ek = ek0 ∧ ct = ct0 := by
  unfold pendingPreKey DY.ExecTrace.getLocalStateAt at hpend
  rcases hat : (tr.at? stateIdx : Option TRStEntry) with _ | e
  · simp [hat] at hpend
  · rw [hat] at hpend; dsimp only [Option.map] at hpend
    split at hpend
    · cases hpend
    · obtain ⟨l1, ev0, l2, hl_eq, hfind, _⟩ := List.findSome?_eq_some_iff.mp hpend
      have hev_mem : ev0 ∈ DY.Libsignal.Composed.Refinement.sessionHandshakeEvents tr
          (e.st.state.sessionInfo e.st.participant) := by
        rw [hl_eq]; exact List.mem_append_right _ List.mem_cons_self
      unfold DY.Libsignal.Composed.Refinement.sessionHandshakeEvents at hev_mem
      obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hev_mem
      rcases hce : tr.getEventAt ComposedEvent i with _ | ⟨s, d⟩
      · rw [hce] at hi; cases hi
      · rw [hce] at hi; dsimp only at hi
        split at hi
        · cases ev0 <;> simp at hfind
          obtain ⟨rfl, rfl⟩ := hfind
          exact honly d _ _ _ _ _ _ _ _ _ _ hi
        · cases hi

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
