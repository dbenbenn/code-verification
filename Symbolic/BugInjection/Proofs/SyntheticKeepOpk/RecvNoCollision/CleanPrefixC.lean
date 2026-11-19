/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixB
public import Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyStart
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux
import Symbolic.Proofs.Swarm.UA.XlateSteps
import DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean-Prefix Step Agreement and Clean `Explains` (`CleanPrefixC.lean`)

1. `alice_draws_pin`: pins the 3 fresh draws (`ek`, Kyber entropy `e`, `dhsA`) of `aliceStart`
   from `DrawsMatch` against 192-byte `.init` coins (`ev 0` and `ev 3`).
2. `alice_init_agree` (Calls 0 & 3), `alice_send_agree` (Calls 1 & 4), `bob_call2_preserve`.
3. Clean `DrawsMatch`, `RunMatches`, and `explains_ssClean_2` / `explains_ssClean_5`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixC

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful ExecTraceTypes)
open DY.DiffieHellman (dhPk)
open DY.PQKem (kemPk)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.PQXDH (BundleHandles AliceHandshakeOut PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState TREvent isCurrentSnapshot u32Max)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma clamp slice ecKey kyberKey pubBytes secretBytes preKeyWire parsePreKeyWire
   setupTrace setupPublic runTrace runSteps stepView aliceVis received
   pendingPreKey rngEntry kyberCoinEntries randTerm
   GhostAndSemMatchSetup GhostWF BytesMatchEntry DrawsMatch OutputsMatch
   ReadsFaithfully RunMatches MatchesEventsAt Explains
   runWrapped inputKind nextBundleIds preKeyRepresentationsOn)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry TRStE RndE NetE at?_append_cases)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState aliceStartState aliceStartTrOfOut length_aliceStartTrOfOut)
open Symbolic.Swarm.CREF.TR (Runs gamma_rand gamma_dhPk)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg encSig parse_encMsg aliceOutOpk aliceSt StT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB pqskB opkB spkNonce pqNonce bhOpk khOpk mhOpk oOpk dhsAOpk stA0Opk
   t4Opk t5Opk t7Opk t4Opk_length t7Opk_length)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.DefsI0
  (keepOpkI0 keepOpkHooks0 keepOpkCompFitsPinned keepOpkPubOfIdx)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.WitnessParse
  (w0 trace0 ev trace0_take_succ ev0_cmd_and_exit ev3_cmd_and_exit ev3_in_eq_ev0
   ev0_bundle_base nextBundleIds_ev1 nextBundleIds_ev2 nextBundleIds_ev4
   ev0KyberEnt ev0_coins_base ev3KyberEnt ev3_coins_base
   ev1_facts ev2_facts ev4_facts ev1_to_ev2 ev2_pt_eq_ev1 ev4_to_ev5
   ev2In_eq ev5In_eq p2 p5 parse_ev2 parse_ev5)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanTrace
  (ValidCoinLens setupTrace_eq_t4Opk encTrGen Runs.messageEncryptGen append_len at?_append_at
   cleanCallSteps cleanCallSteps_length ssClean ssClean_succ
   s0Clean s1Clean s2Clean s3Clean s4Clean
   pt0Clean coins0Clean key0Clean m0Clean trClean2
   trClean3 o2Clean dhsA2Clean stA2_0Clean trClean4
   pt1Clean coins1Clean key1Clean m1Clean
   s0_next_ok s1_next_ok s2_next_ok s3_next_ok s4_next_ok
   runTrace_ssClean_eqs modelRunWF_ssClean cleanPreKeyRep)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanVis
  (visClean visClean_succ stepView_s0 stepView_s1 stepView_s2 stepView_s3 stepView_s4
   encSendList encTrGen_stepView_ok)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanGhost
  (r_facts_of_fit setupRandomsAt_of_fit pqAddrBytes gClean gClean_addr
   gClean_sigma_lt26 gClean_sigma_26 gClean_sigma_27 gClean_sigma_28
   gClean_sigma_35 gClean_sigma_36 gClean_sigma_42
   gClean_sigma_52 gClean_sigma_53 gClean_sigma_54
   gClean_sigma_61 gClean_sigma_62
   ghostAndSemMatchSetup_gClean ghostWF_visClean gamma_KemPk gamma_randTerm_pos
   ev0_bundle_opk_spk gamma_dhPk_ts)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixA
  (StateBytesAgree stateBytesAgree_aliceStartOpk stateBytesAgree_encrypt
   PeeledCall preCond_of_stepIn sendCallOf stepCoinLen)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixB
  (PkiUnchanged pkiUnchanged_runSteps_network pkiUnchanged_step_party pki_pin_st pki_pin_reg
   NoNewPartyState noNewPartyState_runSteps_network noNewPartyState_step_other
   HSSidBound hsSidBound_runSteps_network hsSidBound_aliceStartTrOfOut
   hsSidBound_encTrGen hsSidBound_step_other
   SessionAliceDone sessionAliceDone_aliceStartTrOfOut pendingPreKey_eq_of_sessionAliceDone
   ActiveAliceSt activeAliceSt_pin_state activeAliceSt_init activeAliceSt_runSteps_network
   aliceAllInit_encTrGen at?_of_le_lt)
open Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.MemoCheck
  (cleanPreKeyRep_2_mem)

attribute [local irreducible] WitnessParse.ev

/-! ## 1. `alice_draws_pin` for 192-Byte `.init` Coins (`ev 0` and `ev 3`) -/

private theorem forall₂_append_inv {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys₁ ys₂ : List β}
    (h : List.Forall₂ R xs (ys₁ ++ ys₂)) :
    xs.take ys₁.length ++ xs.drop ys₁.length = xs ∧
    List.Forall₂ R (xs.take ys₁.length) ys₁ ∧
    List.Forall₂ R (xs.drop ys₁.length) ys₂ := by
  induction ys₁ generalizing xs with
  | nil => simpa using h
  | cons y ys₁ ih =>
    cases xs with
    | nil => cases h
    | cons x xs =>
      cases h with
      | cons hxy hrest =>
        obtain ⟨_, h1, h2⟩ := ih hrest
        exact ⟨List.take_append_drop _ _, .cons hxy h1, h2⟩

private theorem flatten_len_of_all_4 {xs : List HwBytes}
    (h : ∀ x ∈ xs, x.length = 4) :
    xs.flatten.length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons, List.length_append, List.length_cons, hx, hxs]
    omega

private theorem flatten_drop_4mul_head? {xs : List HwBytes}
    (h4 : ∀ x ∈ xs, x.length = 4) :
    ∀ {j : Nat} (hj : j < xs.length),
      (xs.flatten.drop (4 * j)).head? = xs[j].head? := by
  induction xs with
  | nil => intro j hj; simp at hj
  | cons x xs ih =>
    intro j hj
    have hx4 : x.length = 4 := h4 x List.mem_cons_self
    have hxs4 : ∀ y ∈ xs, y.length = 4 := fun y hy => h4 y (List.mem_cons_of_mem _ hy)
    cases j with
    | zero =>
      simp only [Nat.mul_zero, List.drop_zero, List.flatten_cons, List.getElem_cons_zero]
      cases x with
      | nil => simp at hx4
      | cons _ _ => rfl
    | succ j' =>
      have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [show 4 * (j' + 1) = x.length + 4 * j' by omega,
          List.drop_append, List.drop_of_length_le (Nat.le_add_right _ _),
          List.nil_append, Nat.add_sub_cancel_left]
      exact ih hxs4 hj'

theorem alice_draws_pin {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} {ts0 : Nat} {anc : Option Nat}
    {coins kyberEnt : HwBytes}
    (hcoins_len : coins.length = 192)
    (hent_len : kyberEnt.length = 32)
    (hent_idx : ∀ j < 32, kyberEnt[j]? = (coins.drop (32 + 4 * j)).head?)
    (hgwf : GhostWF g visAll)
    (hsub : ∀ w ∈ (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }]), w ∈ visAll)
    (hdr : DrawsMatch keepOpkI0 r S g
      (rngEntry (randTerm ts0 32) ::
        kyberCoinEntries (randTerm (ts0 + 1) 32) ++
        [{ rngEntry (randTerm (ts0 + 2) 32) with anchor := anc }])
      coins) :
    gamma keepOpkI0 S g (randTerm ts0 32) = slice coins 0 32 ∧
    gamma keepOpkI0 S g (randTerm (ts0 + 1) 32) = kyberEnt ∧
    gamma keepOpkI0 S g (randTerm (ts0 + 2) 32) = slice coins 160 32 := by
  obtain ⟨pieces, _, hpref, hrel⟩ := hdr
  simp only [List.cons_append] at hrel hsub
  cases pieces with
  | nil => cases hrel
  | cons p0 ps1 =>
    cases hrel with
    | cons h0 hrel1 =>
      have hp0_eq : gamma keepOpkI0 S g (randTerm ts0 32) = p0 := by
        simpa [rngEntry] using h0.2
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
            have hp33_eq : gamma keepOpkI0 S g (randTerm (ts0 + 2) 32) = p33 := by
              simpa [rngEntry] using hlast.2
            have hp33_len : p33.length = 32 := by
              have hmem33 : { rngEntry (randTerm (ts0 + 2) 32) with anchor := anc } ∈ visAll :=
                hsub _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _)))
              have hsig := hgwf.1 _ hmem33 rfl (ts0 + 2) 32 (by decide) (by simp [rngEntry])
              rw [← hp33_eq]; unfold randTerm; rw [gamma_rand]; simpa using hsig
            have hps_kem_len : ps_kem.length = 32 := hrel_kem.length_eq.trans hkem_len
            have hkem_item : ∀ (j : Nat) (hj : j < 32),
                (ps_kem[j]'(by omega)).length = 4 ∧
                (gamma keepOpkI0 S g (randTerm (ts0 + 1) 32)).length = 32 ∧
                (ps_kem[j]'(by omega)).head? =
                  (gamma keepOpkI0 S g (randTerm (ts0 + 1) 32))[j]? := by
              intro j hj
              have hget := (List.forall₂_iff_get.mp hrel_kem).2 j
                (by omega) (by rw [hkem_len]; exact hj)
              simp only [List.get_eq_getElem, kyberCoinEntries, List.getElem_map,
                List.getElem_range] at hget
              obtain ⟨_, hlen4, t, ht_eq, hlen32, hhead⟩ := hget
              simp only [List.cons.injEq, and_true] at ht_eq
              subst ht_eq
              exact ⟨hlen4, hlen32, hhead⟩
            have hall4 : ∀ q ∈ ps_kem, q.length = 4 := by
              intro q hq
              obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
              exact (hkem_item j (by omega)).1
            have hflat_kem_len : ps_kem.flatten.length = 128 := by
              rw [flatten_len_of_all_4 hall4, hps_kem_len]
            have hflat_eq : (p0 :: ps1).flatten = p0 ++ (ps_kem.flatten ++ p33) := by
              rw [← hps1_split]; simp [List.flatten_cons, List.flatten_append]
            obtain ⟨tail_rem, hcoins_eq⟩ := hpref
            rw [hflat_eq] at hcoins_eq
            have htail_nil : tail_rem = [] := by
              have hlen := congrArg List.length hcoins_eq
              simp only [List.length_append, hp0_len, hflat_kem_len, hp33_len,
                hcoins_len] at hlen
              exact List.eq_nil_of_length_eq_zero (by omega)
            rw [htail_nil, List.append_nil] at hcoins_eq
            have hs0 : slice coins 0 32 = p0 := by
              rw [← hcoins_eq]; unfold slice; simp only [List.drop_zero]
              exact List.take_left' hp0_len
            have hs160 : slice coins 160 32 = p33 := by
              rw [← hcoins_eq, ← List.append_assoc]; unfold slice
              have h160 : (p0 ++ ps_kem.flatten).length = 160 := by simp [hp0_len, hflat_kem_len]
              rw [List.drop_left' h160, List.take_of_length_le (by omega)]
            have he1_eq : gamma keepOpkI0 S g (randTerm (ts0 + 1) 32) = kyberEnt := by
              have hlen_e1 : (gamma keepOpkI0 S g (randTerm (ts0 + 1) 32)).length = 32 :=
                (hkem_item 0 (by decide)).2.1
              apply List.ext_getElem?
              intro j
              by_cases hj : j < 32
              · have hhead_j := (hkem_item j hj).2.2
                have hdrop_kem := flatten_drop_4mul_head? hall4 (j := j) (by omega)
                have hcoins_drop : (coins.drop (32 + 4 * j)).head? =
                    (ps_kem.flatten.drop (4 * j)).head? := by
                  rw [← hcoins_eq]
                  rw [show 32 + 4 * j = p0.length + 4 * j by omega,
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

/-! ## 2. Setup Key Agreement and Unified `alice_init_agree` (Calls 0 & 3) -/

theorem gamma_setup_rnd_eq {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (cls : Nat → Nat) {ts n : Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g)
    (hmem : (ts, n) ∈ [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64), (22, 32)])
    (hn : n ≠ 0) :
    gamma keepOpkI0 S g (rnd ts n) = gamma keepOpkI0 S (gClean r cls) (rnd ts n) := by
  have hmem' : (ts, n) ∈ DY.Libsignal.Composed.Refinement.setupRandomsAt r :=
    (setupRandomsAt_of_fit hfit) ▸ hmem
  have hlt : ts < 26 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      decide
  unfold rnd
  rw [gamma_rand, gamma_rand]
  simp only [hn, ↓reduceIte]
  exact (hCompat.1 (ts, n) hmem').trans (gClean_sigma_lt26 r cls hlt).symm

theorem gamma_kemPk_pqskB_gClean {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    (cls : Nat → Nat)
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g) :
    gamma keepOpkI0 S (gClean r cls) (kemPk pqskB) = w0.kyberPk := by
  have hf := r_facts_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hf.alice_eq, hf.bob_eq]; decide
  have hCompat' := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have h6 : r.opaqueBytes (setupPublic r 6) = gamma keepOpkI0 S (gClean r cls) (setupPublic r 6) :=
    (hCompat'.2.1 r.pqpkPubTerm (by simp)).symm
  rw [hf.pub6_eq, Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe] at h6
  exact h6.symm

theorem alice_init_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {callIdx : Nat} {tr trClean : ExecTrace} {dhsClean : Bytes} {kyberEnt : HwBytes}
    {initIds : Option BundlePreKeyIds} {c : PeeledCall}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hSid : HSSidBound tr)
    (hrole : ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true)
    (he_cmd : (ev callIdx).party = "alice" ∧
      (ev callIdx).cmd = .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle" ∧
      (ev callIdx).exit = some (0, []))
    (he_in : (ev callIdx).input = (ev 0).input)
    (he_ids : nextBundleIds initIds (ev callIdx) = some (some 3#32, 7#32, 9#32))
    (hcoins : (ev callIdx).coins.length = 192 ∧ kyberEnt.length = 32 ∧
      (∀ j < 32, kyberEnt[j]? = ((ev callIdx).coins.drop (32 + 4 * j)).head?))
    (hsig0 : (gClean r cls).σ trClean.length 32 = slice (ev callIdx).coins 0 32)
    (hsig1 : (gClean r cls).σ (trClean.length + 1) 32 = kyberEnt)
    (hdhs_eq : dhsClean = rnd (trClean.length + 2) 32)
    (hsig2 : (gClean r cls).σ (trClean.length + 2) 32 = slice (ev callIdx).coins 160 32)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s (ev callIdx) c.v initIds)
    (hsub : ∀ w ∈ c.v, w ∈ visAll) :
    let tr₁ := c.s.next (runSteps c.pre tr)
    let o_cl := aliceOutOpk trClean ikA (dhPk ikB) (dhPk spkB) (kemPk pqskB) (dhPk opkB)
    let st_cl := aliceSt "bob" o_cl dhsClean
    ∃ ek0 ct0 : Bytes,
      gamma keepOpkI0 S g ek0 = gamma keepOpkI0 S (gClean r cls) o_cl.ek ∧
      gamma keepOpkI0 S g ct0 = gamma keepOpkI0 S (gClean r cls) o_cl.ct ∧
      PkiUnchanged tr₁ ∧
      HSSidBound tr₁ ∧
      ActiveAliceSt S g (gClean r cls) ek0 ct0 st_cl tr₁ ∧
      nextBundleIds initIds (ev callIdx) = some (some 3#32, 7#32, 9#32) := by
  set tr₀ := runSteps c.pre tr
  have hf := r_facts_of_fit hfit
  have hpki₀ : PkiUnchanged tr₀ := pkiUnchanged_runSteps_network c.pre hnet hpki
  have hSid₀ : HSSidBound tr₀ := hsSidBound_runSteps_network c.pre hnet hSid
  have hnn₀ := noNewPartyState_runSteps_network (party := "alice") c.pre tr hnet
  have hrole₀ : ∀ i st, (tr₀.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true := by
    intro i st hat
    by_cases hlt : i < tr.length
    · rw [at?_of_le_lt hnn₀.1 hlt] at hat; exact hrole i st hat
    · exact False.elim (hnn₀.2 i st (Nat.le_of_not_lt hlt) hat)
  obtain ⟨hparty_e, hcmd_e, hexit_e⟩ := he_cmd
  obtain ⟨_, hparty, hfits, hpeer, hok, _, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_e] at hparty
  rw [hcmd_e] at hfits
  cases hs : c.s with
  | aliceStart a b idS regB bh =>
    rw [hs] at hparty hpeer hok hvis_eq
    rcases Option.some.inj hparty with rfl
    have hb_eq : b = "bob" := by simpa [Step.MatchesSetupPeer, hf.bob_eq] using hpeer
    subst hb_eq
    have hnext_mv : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
        (DY.Libsignal.Composed.Refinement.Move.aliceStart "alice" "bob" idS regB bh 35).next tr₀ := by
      dsimp only [DY.Libsignal.Composed.Refinement.Move.next,
        DY.Libsignal.Composed.Refinement.Move.act, Step.next, Step.toInput]
      erw [stepIn_next]
      exact (Symbolic.Proofs.Swarm.UA.XlateSteps.run_bind_pure_snd _ tr₀).symm
    obtain ⟨o0_ok, ho0_ok⟩ := Symbolic.Proofs.Swarm.UA.XlateSteps.aliceStart_ok_trOfOut hok
    have hlen_o0 : (aliceStartTrOfOut tr₀ "alice" "bob" o0_ok).length = tr₀.length + 9 :=
      length_aliceStartTrOfOut tr₀ "alice" "bob" o0_ok
    rcases Symbolic.Swarm.CREF.aliceStart_next_cases "alice" "bob" idS regB bh 35 tr₀ with
      h0 | h1 | ⟨ik_a, ik_b, vk_b, spk, spkSig, pqpk, pqpkSig, opk, honest,
        hstA, hregB, hspk, hspkSig, hpq, hpqSig, hopk, h3⟩
    · have := (congrArg DY.Trace.length (h0.symm.trans ho0_ok)).trans hlen_o0; omega
    · have := (append_len tr₀ (RndE 32)).symm.trans
        ((congrArg DY.Trace.length (h1.symm.trans ho0_ok)).trans hlen_o0); omega
    · have hikA_pin : ik_a = ikA := by
        rcases pki_pin_st hpki₀ hstA with ⟨_, hst_eq⟩ | ⟨hfb, _⟩ | ⟨hfb, _⟩ | ⟨hfb, _⟩ | ⟨hfb, _⟩
        · cases hst_eq; rfl
        · exact absurd hfb (by decide)
        · exact absurd hfb (by decide)
        · exact absurd hfb (by decide)
        · exact absurd hfb (by decide)
      subst hikA_pin
      have hregB_at : (tr₀.at? regB : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some ⟨.IdentityRegistered "bob" ik_b vk_b honest⟩ := by
        rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hregB
      have hikB_pin : ik_b = dhPk ikB := by
        rcases pki_pin_reg hpki₀ hregB_at with ⟨hfa, _⟩ | ⟨_, hpk, _⟩
        · exact absurd hfa (by decide)
        · exact hpk
      subst hikB_pin
      have hout_nil : outs = [] := by
        unfold OutputsMatch at hout
        rw [hexit_e, hcmd_e] at hout
        exact hout
      rw [hout_nil, List.append_nil] at hv_split
      let o_gen := Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr₀ ikA (dhPk ikB) spk pqpk opk
      have htr'_ofOut : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          aliceStartTrOfOut tr₀ "alice" "bob" o_gen :=
        hnext_mv.trans h3
      have hvis_full : c.v =
          { kind := .recv, terms := received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
            layout := .bundle, anchor := none } ::
          rngEntry (randTerm tr₀.length 32) ::
          (kyberCoinEntries (randTerm (tr₀.length + 1) 32) ++
            [{ rngEntry (randTerm (tr₀.length + 2) 32) with anchor := some (tr₀.length + 5) }]) := by
        rw [hvis_eq]; unfold stepView
        simp only [hok, ↓reduceIte, htr'_ofOut]
        rw [Symbolic.Swarm.CREF.exposures_aliceStartTrOfOut, List.append_nil]
        exact Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.aliceVis_iniAliceStartTr
          tr₀ "alice" "bob" o_gen bh
      have hinp_drs := hv_split.symm.trans hvis_full
      injection hinp_drs with hinp_eq hdrs_eq
      have hbun_b4 := ev0_bundle_base.2.1
      have hbun_pq := ev0_bundle_base.2.2.2.2.2.1
      obtain ⟨hbun_opk, hbun_spk⟩ := ev0_bundle_opk_spk
      obtain ⟨opkIdx, u, hbh_opk, hopk_eq, hu⟩ :
          ∃ idx u, bh.opk = some idx ∧ opk = some u ∧ Symbolic.Swarm.COMPOSED.CompTrace.NetMsgAt u idx tr₀ := by
        rcases hopk with ⟨h1, _⟩ | hsome
        · exfalso
          have hrec4 : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
              [spk, spkSig, pqpk, pqpkSig] := by
            rw [h1]
            change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] = _
            simp only [received, List.filterMap_cons, List.filterMap_nil,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspk,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspkSig,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpq,
              Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpqSig]
          rw [hinp_eq] at hbm_in
          have hplm := hbm_in.2
          dsimp only at hplm
          rw [hrec4, he_in] at hplm
          dsimp only [DY.Libsignal.Composed.Refinement.PreKeyBundleLayoutMatches,
            DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte] at hplm
          rw [hbun_b4] at hplm
          cases hplm.2
        · exact hsome
      subst hopk_eq
      have hrec5 : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig, u] := by
        rw [hbh_opk]
        change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig, opkIdx] = _
        simp only [received, List.filterMap_cons, List.filterMap_nil,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspk,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hspkSig,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpq,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hpqSig,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.getMessageSentAt_of_netMsgAt hu]
      rw [hinp_eq] at hbm_in
      have hplm := hbm_in.2
      dsimp only at hplm
      rw [hrec5, he_in] at hplm
      obtain ⟨⟨_, hspk_sl, _, hpq_sl, _⟩, _, hopk_sl⟩ := hplm
      have hspk_gam : gamma keepOpkI0 S g spk =
          gamma keepOpkI0 S (gClean r cls) (dhPk spkB) := by
        have h1 : ecKey (gamma keepOpkI0 S g spk) = ecKey (keepOpkPubOfIdx ⟨2, by decide⟩) :=
          hspk_sl.symm.trans hbun_spk
        exact ((List.cons.inj h1).2).trans
          (gamma_dhPk_ts (S := S) (cls := cls) (ts := 10) hfit (by decide)).symm
      have hopk_gam : gamma keepOpkI0 S g u =
          gamma keepOpkI0 S (gClean r cls) (dhPk opkB) := by
        have h1 : ecKey (gamma keepOpkI0 S g u) = ecKey (keepOpkPubOfIdx ⟨3, by decide⟩) :=
          hopk_sl.symm.trans hbun_opk
        exact ((List.cons.inj h1).2).trans
          (gamma_dhPk_ts (S := S) (cls := cls) (ts := 22) hfit (by decide)).symm
      have hpq_gam : gamma keepOpkI0 S g pqpk =
          gamma keepOpkI0 S (gClean r cls) (kemPk pqskB) := by
        have h1 : kyberKey (gamma keepOpkI0 S g pqpk) = kyberKey w0.kyberPk :=
          hpq_sl.symm.trans hbun_pq
        exact ((List.cons.inj h1).2).trans (gamma_kemPk_pqskB_gClean cls hfit hCompat).symm
      have hsub_drs : ∀ w ∈ drs, w ∈ visAll :=
        fun w hw => hsub w (hv_split ▸ List.mem_cons_of_mem _ hw)
      rw [hdrs_eq] at hdr hsub_drs
      obtain ⟨hek_coins, he_coins, hdhs_coins⟩ :=
        alice_draws_pin hcoins.1 hcoins.2.1 hcoins.2.2 hgwf hsub_drs hdr
      have hek_gam : gamma keepOpkI0 S g (rnd tr₀.length 32) =
          gamma keepOpkI0 S (gClean r cls) (rnd trClean.length 32) := by
        change gamma keepOpkI0 S g (randTerm tr₀.length 32) =
          gamma keepOpkI0 S (gClean r cls) (randTerm trClean.length 32)
        rw [hek_coins]; unfold randTerm; rw [gamma_rand]; simp [hsig0]
      have he_gam : gamma keepOpkI0 S g (rnd (tr₀.length + 1) 32) =
          gamma keepOpkI0 S (gClean r cls) (rnd (trClean.length + 1) 32) := by
        change gamma keepOpkI0 S g (randTerm (tr₀.length + 1) 32) =
          gamma keepOpkI0 S (gClean r cls) (randTerm (trClean.length + 1) 32)
        rw [he_coins]; unfold randTerm; rw [gamma_rand]; simp [hsig1]
      have hdhs_gam : gamma keepOpkI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma keepOpkI0 S (gClean r cls) dhsClean := by
        rw [hdhs_eq]
        change gamma keepOpkI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma keepOpkI0 S (gClean r cls) (randTerm (trClean.length + 2) 32)
        rw [hdhs_coins]; unfold randTerm; rw [gamma_rand]; simp [hsig2]
      have hikA_gam : gamma keepOpkI0 S g ikA = gamma keepOpkI0 S (gClean r cls) ikA :=
        gamma_setup_rnd_eq cls hfit hCompat (by decide) (by decide)
      have hikB_gam : gamma keepOpkI0 S g (dhPk ikB) =
          gamma keepOpkI0 S (gClean r cls) (dhPk ikB) := by
        rw [gamma_dhPk, gamma_dhPk,
            gamma_setup_rnd_eq cls hfit hCompat (ts := 5) (n := 32) (by decide) (by decide)]
      obtain ⟨hek_pk, hct_eq, hst_agree⟩ := stateBytesAgree_aliceStartOpk (tr := tr₀) (trClean := trClean)
        hikA_gam hikB_gam hspk_gam hpq_gam hopk_gam hek_gam he_gam hdhs_gam
      let o_ss := aliceOutOpk tr₀ ikA (dhPk ikB) spk pqpk u
      have htr₁_ofOut : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          aliceStartTrOfOut tr₀ "alice" "bob" o_ss := htr'_ofOut
      have htr₁_ini : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.iniAliceStartTr
            tr₀ "alice" "bob" o_ss := htr'_ofOut
      refine ⟨o_ss.ek, o_ss.ct, hek_pk, hct_eq,
        pkiUnchanged_step_party rfl hpki₀,
        htr₁_ofOut ▸ hsSidBound_aliceStartTrOfOut hSid₀, ?_, he_ids⟩
      have hle_tr₁ : tr₀ ≤ (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ := by
        rw [htr₁_ini]
        unfold Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.iniAliceStartTr
        dsimp only
        iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
        exact DY.Trace.append_le _ _
      let stA_ss := aliceStartState tr₀ "bob" o_ss
      have hat_stA : (((Step.aliceStart "alice" "bob" idS regB bh).next tr₀).at? (tr₀.length + 8) :
          Option TRStEntry) = some ⟨⟨"alice", stA_ss⟩⟩ := by
        rw [htr₁_ini,
            Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_trSt_iniAliceStartTr]
        simp only [↓reduceIte]; rfl
      refine activeAliceSt_init hrole₀ hle_tr₁ (by omega) hat_stA ?_ rfl hst_agree
        (htr₁_ofOut ▸ sessionAliceDone_aliceStartTrOfOut hSid₀)
      intro j st hj hat_j
      rw [htr₁_ini,
          Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice.at?_trSt_iniAliceStartTr] at hat_j
      by_cases hjeq : j = tr₀.length + 8
      · subst hjeq
        simp only [↓reduceIte, TRStE, Option.some.injEq] at hat_j
        injection hat_j with h1; injection h1 with _ h2
        exact ⟨rfl, h2.symm⟩
      · simp only [hjeq, ↓reduceIte] at hat_j
        have hlt_j : j < tr₀.length := by
          have h := DY.Trace.at?_eq_some_implies_length_le (EntryT := TRStEntry) tr₀ j
          rw [hat_j] at h; simpa using h
        omega
  | _ => rw [hs] at hfits; cases hfits

/-! ## 3. Unified `alice_send_agree` (Calls 1 & 4) and `bob_call2_preserve` (Call 2) -/

private theorem append_singleton_inj {α : Type} {xs₁ xs₂ : List α} {y₁ y₂ : α}
    (h : xs₁ ++ [y₁] = xs₂ ++ [y₂]) : xs₁ = xs₂ ∧ y₁ = y₂ := by
  induction xs₁ generalizing xs₂ with
  | nil =>
    cases xs₂ with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons _ _ => simp at h
  | cons x xs₁ ih =>
    cases xs₂ with
    | nil => simp at h
    | cons _ _ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hxs, hy⟩ := ih h.2
      exact ⟨congrArg₂ List.cons h.1 hxs, hy⟩

private theorem step_ok_encryptAbort_false (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.messageEncryptAbort me stateIdx).ok tr = false := by
  unfold Step.ok Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, stateIdx) tr]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability,
    DY.Libsignal.TripleRatchet.messageEncryptAbort]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst]
  rcases ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | _
  · rfl
  · dsimp only
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, (Runs.genRand _ 32).1]
    dsimp only; rw [DY.Traceful.run_failure]; rfl

theorem alice_send_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {oClean : AliceHandshakeOut} {stClean : TRState}
    {ek0 ct0 : Bytes} {sIdx tsPt tsCoins : Nat}
    {tr : ExecTrace} {c : PeeledCall}
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hSid : HSSidBound tr)
    (hek0 : gamma keepOpkI0 S g ek0 = gamma keepOpkI0 S (gClean r cls) oClean.ek)
    (hct0 : gamma keepOpkI0 S g ct0 = gamma keepOpkI0 S (gClean r cls) oClean.ct)
    (hAct : ActiveAliceSt S g (gClean r cls) ek0 ct0 stClean tr)
    (he_party : (ev (sendCallOf sIdx)).party = "alice" ∧
      (∃ peer, (ev (sendCallOf sIdx)).cmd = .send peer) ∧
      runWrapped (ev (sendCallOf sIdx)) = true)
    (hcl_eq : cls sIdx = stepCoinLen c.s)
    (hpt_clean : (gClean r cls).σ tsPt 32 = (ev (sendCallOf sIdx)).input)
    (hcoins_clean : ∀ n, (gClean r cls).σ tsCoins n = (ev (sendCallOf sIdx)).coins.take n)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hpre : c.s.PreCond (runSteps c.pre tr))
    (hlok : c.s.LocalOk (runSteps c.pre tr))
    (hrm : RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s (ev (sendCallOf sIdx)) c.v
      (some (some 3#32, 7#32, 9#32)))
    (hsub : ∀ w ∈ c.v, w ∈ visAll) :
    let tr' := c.s.next (runSteps c.pre tr)
    let coins' := rnd tsCoins (cls sIdx)
    let pt' := rnd tsPt 32
    let mClean := encMsg stClean coins' (DY.Spqr.spqrSend stClean.spqr coins').2.1 pt'
    PkiUnchanged tr' ∧
    HSSidBound tr' ∧
    (∀ i st, (tr'.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true) ∧
    (ev (sendCallOf sIdx)).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) oClean.ek)
      (gamma keepOpkI0 S (gClean r cls) oClean.ct)
      (gamma keepOpkI0 S (gClean r cls) mClean)) := by
  set e := ev (sendCallOf sIdx)
  set tr₁ := runSteps c.pre tr
  have hpki₁ : PkiUnchanged tr₁ := pkiUnchanged_runSteps_network c.pre hnet hpki
  have hSid₁ : HSSidBound tr₁ := hsSidBound_runSteps_network c.pre hnet hSid
  have hAct₁ : ActiveAliceSt S g (gClean r cls) ek0 ct0 stClean tr₁ :=
    activeAliceSt_runSteps_network hnet hAct
  obtain ⟨hparty_e, ⟨peer, hcmd_e⟩, hw_true⟩ := he_party
  obtain ⟨_, hparty, hfits, _, hok, hexit_some, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_e] at hparty
  rw [hcmd_e] at hfits
  cases hs : c.s with
  | messageEncryptAbort me stateIdx =>
    exfalso; rw [hs, step_ok_encryptAbort_false] at hok; cases hok
  | messageEncrypt me stateIdx cl pq =>
    rw [hs] at hparty hpre hlok hok hvis_eq hcl_eq
    dsimp only [stepCoinLen] at hcl_eq
    rcases Option.some.inj hparty.symm with rfl
    have hpq_eq : pq = tr₁.length + 2 := by
      rcases hlok.2 with hpq2 | hpq3
      · exact hpq2
      · exfalso
        dsimp only [DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx] at hpq3
        rw [hpq3, Symbolic.Proofs.Swarm.UA.XlateSteps.messageEncrypt_fail_not_ok] at hok
        cases hok
    subst hpq_eq
    have hcur : isCurrentSnapshot tr₁ stateIdx = true :=
      preCond_of_stepIn DY.Libsignal.TripleRatchet.messageEncrypt.reachability
        ("alice", stateIdx, cl, tr₁.length + 2) tr₁ hpre
    have hok_run : ((DY.Libsignal.TripleRatchet.messageEncrypt "alice" stateIdx cl (tr₁.length + 2)).run tr₁).1.isSome = true := by
      dsimp only [Step.ok, Step.toInput] at hok
      erw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ tr₁] at hok
      exact hok
    unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok_run
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst] at hok_run
    rcases hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx : Traceful TRState).run tr₁).1 with _ | st
    · simp [hst] at hok_run
    · obtain ⟨hinit, hagree, hsad⟩ := activeAliceSt_pin_state hAct₁ hst hcur
      have hat_st : tr₁.at? stateIdx = some (StT "alice" st) := bks_stored_of_getLocalState hst
      rw [hst, Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd] at hok_run
      dsimp only at hok_run
      have hns : st.ns ≠ u32Max := by
        intro hmax
        have hf0 : ((failure : Traceful Unit).run tr₁).1 = none := by rw [DY.Traceful.run_failure]
        simp [_root_.guard, hmax, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_fst, hf0] at hok_run
      let pqSalt := (DY.Spqr.spqrSend st.spqr (rnd (tr₁.length + 1) cl)).2.1
      have hpq_at : (((tr₁.append (RndE 32)).append (RndE cl)).append (NetE pqSalt)).at?
          (tr₁.length + 2) = some (NetE pqSalt) :=
        at?_append_at _ _ (by simp only [append_len])
      have hruns := Runs.messageEncryptGen hat_st hns hpq_at
      have hnext_eq : (Step.messageEncrypt "alice" stateIdx cl (tr₁.length + 2)).next tr₁ =
          encTrGen tr₁ "alice" stateIdx cl st pqSalt :=
        (stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability _ tr₁).trans hruns.2
      have hview := encTrGen_stepView_ok (wrapped := runWrapped e) hok hnext_eq
      obtain ⟨out, hexit_e⟩ := hexit_some
      unfold OutputsMatch at hout
      rw [hexit_e, hcmd_e] at hout
      obtain ⟨v_out, rfl, hbm_out⟩ := hout
      have hv_comb := hv_split.symm.trans (hvis_eq.trans hview)
      injection hv_comb with hinp_eq hdrs_out_eq
      have hpt_gam : gamma keepOpkI0 S g (rnd tr₁.length 32) =
          gamma keepOpkI0 S (gClean r cls) (rnd tsPt 32) := by
        have hin_k : inputKind e = .pt := by unfold inputKind; rw [hcmd_e]
        rw [hin_k, hinp_eq] at hbm_in
        have h1 : gamma keepOpkI0 S g (randTerm tr₁.length 32) = e.input := by simpa using hbm_in.2
        have h2 : gamma keepOpkI0 S (gClean r cls) (rnd tsPt 32) = e.input := by
          unfold rnd; rw [gamma_rand]; simp [hpt_clean]
        exact h1.trans h2.symm
      rw [hw_true] at hdrs_out_eq
      rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
      · exfalso
        rw [hppk] at hdrs_out_eq
        dsimp only [encSendList] at hdrs_out_eq
        rw [List.append_nil] at hdrs_out_eq
        have hmem : v_out ∈ (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) := by
          rw [← hdrs_out_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
        by_cases hcl0 : cl = 0 <;> simp [hcl0, rngEntry] at hmem
        subst hmem; cases hbm_out.1
      · rw [hppk] at hdrs_out_eq
        dsimp only [encSendList] at hdrs_out_eq
        obtain ⟨hdrs_eq, rfl⟩ := append_singleton_inj hdrs_out_eq
        obtain ⟨hek_eq, hct_eq⟩ := pendingPreKey_eq_of_sessionAliceDone hat_st hsad hppk
        subst ek; subst ct
        have hc_gam : gamma keepOpkI0 S g (rnd (tr₁.length + 1) cl) =
            gamma keepOpkI0 S (gClean r cls) (rnd tsCoins (cls sIdx)) := by
          rw [hcl_eq]
          by_cases hcl0 : cl = 0
          · subst hcl0; unfold rnd; rw [gamma_rand, gamma_rand]; simp
          · have hdrs_1 : drs = [rngEntry (randTerm (tr₁.length + 1) cl)] := by
              simpa [hcl0] using hdrs_eq
            rw [hdrs_1] at hdr
            have hmem_rng : rngEntry (randTerm (tr₁.length + 1) cl) ∈ visAll := by
              apply hsub; rw [hv_split, hdrs_1]; simp
            have hlen_c : (gamma keepOpkI0 S g (randTerm (tr₁.length + 1) cl)).length = cl := by
              have hsig := hgwf.1 _ hmem_rng rfl (tr₁.length + 1) cl hcl0 (by simp [rngEntry])
              unfold randTerm; rw [gamma_rand]; simpa [hcl0] using hsig
            obtain ⟨pieces, _, hpref, hrel⟩ := hdr
            cases pieces with
            | nil => cases hrel
            | cons p0 ps_tl =>
              cases hrel with
              | cons hp0 htl =>
                cases ps_tl with
                | cons _ _ => cases htl
                | nil =>
                  have hp0_eq : gamma keepOpkI0 S g (randTerm (tr₁.length + 1) cl) = p0 := by
                    simpa [rngEntry] using hp0.2
                  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
                  obtain ⟨_, hcoins_eq⟩ := hpref
                  have htake_c : e.coins.take cl = p0 := by
                    rw [← hcoins_eq]; exact List.take_left' (hp0_eq ▸ hlen_c)
                  have hg_clean : gamma keepOpkI0 S (gClean r cls) (rnd tsCoins cl) = e.coins.take cl := by
                    unfold rnd; rw [gamma_rand]; simp [hcl0, hcoins_clean]
                  exact hp0_eq.trans (htake_c.symm.trans hg_clean.symm)
        have hv_s_mem : (⟨.send, [ek0, ct0, encMsg st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32)],
            .preKeySend, none⟩ : VisEntry) ∈ visAll := by
          apply hsub; rw [hv_split]; simp
        have haddr_ss : g.addr (encSig st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32)).wire =
            pqAddrBytes :=
          (hgwf.2.2 _ hv_s_mem rfl).1 rfl _ _ _ _ rfl (parse_encMsg _ _ _ _)
        obtain ⟨_, hm_eq⟩ := stateBytesAgree_encrypt hagree hc_gam hpt_gam
          (haddr_ss.trans (gClean_addr r cls _).symm)
        obtain ⟨pkId, spkId, kpkId, hids_eq, hout_wire⟩ := hbm_out.2
        injection hids_eq with hprod
        obtain ⟨rfl, hprod2⟩ := Prod.mk.inj hprod
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hprod2
        rw [hek0, hct0, hm_eq] at hout_wire
        exact ⟨pkiUnchanged_step_party rfl hpki₁,
          hnext_eq ▸ hsSidBound_encTrGen hSid₁,
          hnext_eq ▸ aliceAllInit_encTrGen hAct₁.1 hinit,
          hexit_e.trans (congrArg (some ∘ (0, ·)) hout_wire)⟩
  | _ => rw [hs] at hfits; cases hfits

theorem bob_call2_preserve {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {initIds : Option BundlePreKeyIds} {c : PeeledCall}
    (hpki : PkiUnchanged tr)
    (hSid : HSSidBound tr)
    (hrole : ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true)
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches keepOpkI0 r S g (runSteps c.pre tr) c.s (ev 2) c.v initIds) :
    let tr' := c.s.next (runSteps c.pre tr)
    PkiUnchanged tr' ∧
    HSSidBound tr' ∧
    (∀ i st, (tr'.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → st.initiator = true) := by
  set tr₁ := runSteps c.pre tr
  have hcls : c.s.cls = .party := hrm.1
  have hparty : c.s.party? = some "bob" := by rw [hrm.2.1, ev2_facts.1]
  have hne : c.s.party? ≠ some "alice" := by rw [hparty]; decide
  have hnn₀ := noNewPartyState_runSteps_network (party := "alice") c.pre tr hnet
  have hnn₁ := noNewPartyState_step_other (party := "alice") tr₁ hcls hne
  refine ⟨pkiUnchanged_step_party hcls (pkiUnchanged_runSteps_network c.pre hnet hpki),
    hsSidBound_step_other hcls hne (hsSidBound_runSteps_network c.pre hnet hSid), ?_⟩
  intro i st hat
  by_cases hlt₁ : i < tr₁.length
  · rw [at?_of_le_lt hnn₁.1 hlt₁] at hat
    by_cases hlt₀ : i < tr.length
    · rw [at?_of_le_lt hnn₀.1 hlt₀] at hat; exact hrole i st hat
    · exact False.elim (hnn₀.2 i st (Nat.le_of_not_lt hlt₀) hat)
  · exact False.elim (hnn₁.2 i st (Nat.le_of_not_lt hlt₁) hat)

/-! ## 4. Clean `DrawsMatch`, `CleanStepsMatch`, `RunMatches`, and `Explains` on `ssClean` -/

private theorem forall2_append {α β : Type} {R : α → β → Prop}
    {xs₁ xs₂ : List α} {ys₁ ys₂ : List β}
    (h1 : List.Forall₂ R xs₁ ys₁) (h2 : List.Forall₂ R xs₂ ys₂) :
    List.Forall₂ R (xs₁ ++ xs₂) (ys₁ ++ ys₂) := by
  induction h1 with
  | nil => exact h2
  | cons hr _ ih => exact .cons hr ih

private theorem kyber_pieces_flatten :
    ∀ n ≤ 32, ∀ (b : HwBytes), b.length = 192 →
      ((List.range n).map fun j => slice b (32 + 4 * j) 4).flatten = slice b 32 (4 * n)
  | 0, _, b, _ => by simp [slice]
  | n + 1, hn, b, hlen => by
    rw [List.range_succ, List.map_append, List.flatten_append,
      kyber_pieces_flatten n (by omega) b hlen]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, slice]
    rw [show 4 * (n + 1) = 4 * n + 4 by omega, List.take_add, List.drop_drop]

private theorem kyber_pieces_forall2 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {tsE : Nat} {coins ent : HwBytes}
    (hlen192 : coins.length = 192) (hent_len : ent.length = 32)
    (hent_at : ∀ j < 32, ent[j]? = (coins.drop (32 + 4 * j)).head?)
    (hsig_e : (gClean r cls).σ tsE 32 = ent) :
    ∀ n ≤ 32,
      List.Forall₂
        (fun p v => BytesMatchEntry keepOpkI0 r S (gClean r cls) .rng p v)
        ((List.range n).map fun j => slice coins (32 + 4 * j) 4)
        ((List.range n).map fun j => ⟨.rng, [randTerm tsE 32], .kyberCoin j, none⟩)
  | 0, _ => .nil
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.map_append]
    refine forall2_append
      (kyber_pieces_forall2 r S cls hlen192 hent_len hent_at hsig_e n (by omega)) ?_
    refine List.Forall₂.cons ?_ .nil
    refine ⟨rfl, ?_, randTerm tsE 32, rfl, ?_, ?_⟩
    · simp only [slice, List.length_take, List.length_drop, hlen192]; omega
    · rw [gamma_randTerm_pos (by decide), hsig_e]; exact hent_len
    · rw [gamma_randTerm_pos (by decide), hsig_e, hent_at n (by omega)]
      dsimp only [slice]
      cases coins.drop (32 + 4 * n) <;> rfl

theorem drawsMatch_alice_init (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {tsEk tsE tsDhs anchor : Nat} {coins ent : HwBytes}
    (hlen192 : coins.length = 192) (hent_len : ent.length = 32)
    (hent_at : ∀ j < 32, ent[j]? = (coins.drop (32 + 4 * j)).head?)
    (hsig_ek : (gClean r cls).σ tsEk 32 = slice coins 0 32)
    (hsig_e : (gClean r cls).σ tsE 32 = ent)
    (hsig_dhs : (gClean r cls).σ tsDhs 32 = slice coins 160 32) :
    DrawsMatch keepOpkI0 r S (gClean r cls)
      (rngEntry (randTerm tsEk 32) ::
        (kyberCoinEntries (randTerm tsE 32) ++
          [{ rngEntry (randTerm tsDhs 32) with anchor := some anchor }]))
      coins := by
  let kpcs := (List.range 32).map fun j => slice coins (32 + 4 * j) 4
  refine ⟨slice coins 0 32 :: (kpcs ++ [slice coins 160 32]), ?_, ?_, ?_⟩
  · intro p hp
    dsimp only [kpcs] at hp
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | ⟨j, hj, rfl⟩ | rfl <;>
      (intro heq; have := congrArg List.length heq;
       simp only [slice, List.length_take, List.length_drop, hlen192, List.length_nil] at this; omega)
  · simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil]
    rw [kyber_pieces_flatten 32 (Nat.le_refl 32) coins hlen192]
    have hcat : slice coins 0 32 ++ (slice coins 32 128 ++ slice coins 160 32) = coins := by
      simp only [slice, List.drop_zero]
      rw [← List.append_assoc]
      have h1 : coins.take 32 ++ (coins.drop 32).take 128 = coins.take 160 := by
        simpa using (List.take_add (i := 32) (j := 128) (l := coins)).symm
      rw [h1]
      have h2 : coins.take 160 ++ (coins.drop 160).take 32 = coins.take 192 := by
        simpa using (List.take_add (i := 160) (j := 32) (l := coins)).symm
      rw [h2, List.take_of_length_le (Nat.le_of_eq hlen192)]
    rw [hcat]
  · refine List.Forall₂.cons ?_ (forall2_append
      (kyber_pieces_forall2 r S cls hlen192 hent_len hent_at hsig_e 32 (Nat.le_refl 32))
      (List.Forall₂.cons ?_ .nil))
    · exact ⟨rfl, by simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 32 ≠ 0), hsig_ek]⟩
    · exact ⟨rfl, by simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 32 ≠ 0), hsig_dhs]⟩

theorem drawsMatch_single32 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts : Nat} {coins : HwBytes}
    (hlen : 32 ≤ coins.length)
    (hsig : (gClean r cls).σ ts 32 = coins.take 32) :
    DrawsMatch keepOpkI0 r S (gClean r cls) [rngEntry (randTerm ts 32)] coins := by
  refine ⟨[coins.take 32], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; intro heq; have := congrArg List.length heq
    simp only [List.length_take, List.length_nil] at this; omega
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    exact List.take_prefix 32 coins
  · simp only [rngEntry, List.map_cons, List.map_nil,
      gamma_randTerm_pos (by decide : 32 ≠ 0), hsig]

theorem drawsMatch_enc (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (cls : Nat → Nat) {ts cl : Nat} {coins : HwBytes}
    (hcl : cl = 0 ∨ cl = 32 ∨ cl = 64)
    (hlen : 64 ≤ coins.length)
    (hsig : (gClean r cls).σ ts cl = coins.take cl) :
    DrawsMatch keepOpkI0 r S (gClean r cls)
      (if cl != 0 then [rngEntry (randTerm ts cl)] else []) coins := by
  rcases hcl with rfl | rfl | rfl
  · exact ⟨[], by simp, List.nil_prefix, .nil⟩
  · refine ⟨[coins.take 32], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; intro heq; have := congrArg List.length heq
      simp only [List.length_take, List.length_nil] at this; omega
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.take_prefix 32 coins
    · simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 32 ≠ 0), hsig]
  · refine ⟨[coins.take 64], ?_, ?_, List.Forall₂.cons ⟨rfl, ?_⟩ .nil⟩
    · intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp; intro heq; have := congrArg List.length heq
      simp only [List.length_take, List.length_nil] at this; omega
    · simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.take_prefix 64 coins
    · simp only [rngEntry, List.map_cons, List.map_nil,
        gamma_randTerm_pos (by decide : 64 ≠ 0), hsig]

private inductive CleanStepsMatch (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) :
    Option BundlePreKeyIds → Option BundlePreKeyIds → ExecTrace →
      List Step → List CliEvent → List VisEntry → Prop
  | nil (ids : Option BundlePreKeyIds) (tr : ExecTrace) :
      CleanStepsMatch r S g ids ids tr [] [] []
  | cons {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
      {s : Step} {ss : List Step} {e : RunEvent} {evs : List CliEvent}
      {v vs : List VisEntry} :
      mid = nextBundleIds ids e →
      RunMatches keepOpkI0 r S g tr s e v ids →
      CleanStepsMatch r S g mid outIds (s.next tr) ss evs vs →
      CleanStepsMatch r S g ids outIds tr (s :: ss) (.run e :: evs) (v ++ vs)

private theorem CleanStepsMatch.snoc {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ids mid outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    {s : Step} {e : RunEvent} {v : List VisEntry}
    (hm : CleanStepsMatch r S g ids mid tr ss evs vis)
    (hnext : outIds = nextBundleIds mid e)
    (hrm : RunMatches keepOpkI0 r S g (runSteps ss tr) s e v mid) :
    CleanStepsMatch r S g ids outIds tr (ss ++ [s]) (evs ++ [.run e]) (vis ++ v) := by
  induction hm with
  | nil =>
    rw [List.nil_append, List.nil_append, List.nil_append, ← List.append_nil v]
    exact CleanStepsMatch.cons hnext hrm (.nil outIds _)
  | cons hmid hrm0 hrest ih =>
    rw [List.cons_append, List.cons_append, List.append_assoc]
    exact CleanStepsMatch.cons hmid hrm0 (ih hnext hrm)

private theorem CleanStepsMatch.toMatchesEventsAt {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ids outIds : Option BundlePreKeyIds} {tr : ExecTrace}
    {ss : List Step} {evs : List CliEvent} {vis : List VisEntry}
    (hm : CleanStepsMatch r S g ids outIds tr ss evs vis) :
    MatchesEventsAt keepOpkI0 r S g ids tr ss evs vis := by
  induction hm with
  | nil => exact .nil (by simp)
  | cons hmid hrm _ ih =>
    subst hmid
    exact .run1 (pre := []) (by simp) hrm ih

private theorem bundleMatches_ev0 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S (gClean r cls)) :
    DY.Libsignal.Composed.Refinement.PreKeyBundleLayoutMatches keepOpkI0 S (gClean r cls)
      (ev 0).input
      [dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
       kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)),
       dhPk opkB] := by
  have hf := r_facts_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hf.alice_eq, hf.bob_eq]; decide
  obtain ⟨hlen_in, hbyte4, _, _, hsl79, hsl147, hsl1716⟩ := ev0_bundle_base
  obtain ⟨hsl9, hsl46⟩ := ev0_bundle_opk_spk
  have h5 : gamma keepOpkI0 S (gClean r cls) (setupPublic r 5) = r.opaqueBytes (setupPublic r 5) :=
    hCompat.2.1 r.spkSigTerm (by simp)
  have h6 : gamma keepOpkI0 S (gClean r cls) (setupPublic r 6) = r.opaqueBytes (setupPublic r 6) :=
    hCompat.2.1 r.pqpkPubTerm (by simp)
  have h7 : gamma keepOpkI0 S (gClean r cls) (setupPublic r 7) = r.opaqueBytes (setupPublic r 7) :=
    hCompat.2.1 r.pqpkSigTerm (by simp)
  refine ⟨⟨hlen_in, ?_, ?_, ?_, ?_⟩, hbyte4, ?_⟩
  · dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.spkPub]
    rw [hsl46, gamma_dhPk_ts (S := S) (cls := cls) hfit (by decide)]; rfl
  · dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.spkSig]
    rw [hsl79, ← hf.pub5_eq, ← h5, Symbolic.Swarm.CREF.b1_setupPublic_5 r hNe]; rfl
  · dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkPub]
    rw [hsl147, ← hf.pub6_eq, ← h6, Symbolic.Swarm.CREF.b1_setupPublic_6 r hNe]; rfl
  · dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.kpkSig]
    rw [hsl1716, ← hf.pub7_eq, ← h7, Symbolic.Swarm.CREF.b1_setupPublic_7 r hNe]; rfl
  · dsimp only [DY.Libsignal.PQXDH.Refinement.BundleBlob.opkPub]
    rw [hsl9, gamma_dhPk_ts (S := S) (cls := cls) hfit (by decide)]; rfl

private theorem runMatches_s0Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S (gClean r cls)) :
    RunMatches keepOpkI0 r S (gClean r cls) (setupTrace r)
      s0Clean (ev 0) (stepView s0Clean (setupTrace r) (runWrapped (ev 0))) none := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hp0, hcmd0, hex0, _⟩ := ev0_cmd_and_exit
  obtain ⟨hc0_len, hent0_len, _, hent0_at⟩ := ev0_coins_base
  rw [setupTrace_eq_t4Opk hf.alice_eq hf.bob_eq hf.withOpk_eq]
  refine ⟨rfl, by rw [hp0]; rfl, by rw [hcmd0]; trivial, hf.bob_eq.symm,
    s0_next_ok.2, ⟨[], hex0⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
      kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)),
      dhPk opkB], .bundle, none⟩,
    rngEntry (randTerm 26 32) ::
      (kyberCoinEntries (randTerm 27 32) ++
        [{ rngEntry (randTerm 28 32) with anchor := some 31 }]),
    [], by rw [stepView_s0, List.append_nil],
    ⟨by unfold inputKind; rw [hcmd0], bundleMatches_ev0 hfit hCompat⟩,
    drawsMatch_alice_init r S cls hc0_len hent0_len hent0_at
      (gClean_sigma_26 r cls 32) (gClean_sigma_27 r cls 32) (gClean_sigma_28 r cls 32),
    by unfold OutputsMatch; rw [hex0, hcmd0]; rfl,
    trivial, fun _ _ => trivial⟩

private theorem runMatches_s1Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hev1_out : (ev 1).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) oOpk.ek)
      (gamma keepOpkI0 S (gClean r cls) oOpk.ct)
      (gamma keepOpkI0 S (gClean r cls) (m0Clean cls)))) :
    RunMatches keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 1))
      (s1Clean cls) (ev 1)
      (stepView (s1Clean cls) (runTrace r (ssClean cls 1)) (runWrapped (ev 1)))
      (some (some 3#32, 7#32, 9#32)) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hp1, hcmd1, _, hc1_len, hw1⟩ := ev1_facts
  rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.1]
  refine ⟨rfl, by rw [hp1]; rfl, by rw [hcmd1]; trivial, trivial,
    (s1_next_ok cls).2, ⟨_, hev1_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [pt0Clean], .single, none⟩,
    if cls 0 != 0 then [rngEntry (randTerm 36 (cls 0))] else [],
    [⟨.send, [oOpk.ek, oOpk.ct, m0Clean cls], .preKeySend, none⟩],
    by rw [hw1]; exact stepView_s1 cls, ?_,
    drawsMatch_enc r S cls hv.1 (Nat.le_of_eq hc1_len.symm) (gClean_sigma_36 r cls (cls 0)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd1], ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt0Clean rnd; rw [gamma_rand]; simp [gClean_sigma_35]
  · unfold OutputsMatch; rw [hev1_out, hcmd1]
    exact ⟨_, rfl, rfl, some 3#32, 7#32, 9#32, rfl, rfl⟩

theorem explains_ssClean_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g)
    (hev1_out : (ev 1).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) oOpk.ek)
      (gamma keepOpkI0 S (gClean r cls) oOpk.ct)
      (gamma keepOpkI0 S (gClean r cls) (m0Clean cls)))) :
    Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2) (visClean r cls 2) (trace0.take 2) := by
  have hf := r_facts_of_fit hfit
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have csm0 : CleanStepsMatch r S (gClean r cls) none none (setupTrace r)
      (ssClean cls 0) (trace0.take 0) (visClean r cls 0) :=
    CleanStepsMatch.nil none (setupTrace r)
  have csm1 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 1) (trace0.take 1) (visClean r cls 1) := by
    rw [ssClean_succ (s := s0Clean) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s0Clean) rfl]
    exact csm0.snoc ev0_bundle_base.2.2.1.symm (runMatches_s0Clean hfit hCompatClean)
  have csm2 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 2) (trace0.take 2) (visClean r cls 2) := by
    rw [ssClean_succ (s := s1Clean cls) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s1Clean cls) rfl]
    exact csm1.snoc (nextBundleIds_ev1 _).symm (runMatches_s1Clean hfit hv hev1_out)
  exact ⟨hCompatClean, ghostWF_visClean hfit hv (by decide),
    modelRunWF_ssClean 2 hf.alice_eq hf.bob_eq hf.withOpk_eq hv,
    csm2.toMatchesEventsAt⟩

private theorem runMatches_s2Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hex2 : Explains keepOpkI0 r S (gClean r cls) (ssClean cls 2)
      (visClean r cls 2) (trace0.take 2)) :
    RunMatches keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 2))
      s2Clean (ev 2)
      (stepView s2Clean (runTrace r (ssClean cls 2)) (runWrapped (ev 2)))
      (some (some 3#32, 7#32, 9#32)) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hp2, hcmd2, hc2_len, _⟩ := ev2_facts
  have hrun2 := (runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.1
  have hrep2 := cleanPreKeyRep_2_mem hfit hv hex2
  have hopk2 : DY.Libsignal.Composed.Refinement.OpkNamed r (ev 2).input true :=
    ⟨p2, parse_ev2, by rw [hf.opkId_eq, hf.withOpk_eq]; exact ⟨WitnessParse.p2_fields_base.2.1, rfl⟩⟩
  have hbks_nil : DY.Libsignal.Composed.Refinement.bobDoneBaseKeys
      (runTrace r (ssClean cls 2)) = [] :=
    Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollisionAux.bobDoneBaseKeys_eq_nil_of_no_recv
      hfit.1.1.1 hex2 WitnessParse.noRecvEvent_take2
  refine ⟨rfl, by rw [hp2]; rfl, by rw [hcmd2]; trivial, hf.alice_eq.symm,
    by rw [hrun2]; exact (s2_next_ok cls).2, ⟨_, ev2_pt_eq_ev1⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [oOpk.ek, oOpk.ct, m0Clean cls, dhPk opkB], .preKeyRecv, none⟩,
    [rngEntry (randTerm 42 32)],
    [⟨.accept, [pt0Clean], .single, some 45⟩],
    by rw [hrun2]; exact stepView_s2 cls (runWrapped (ev 2)),
    ⟨by unfold inputKind; rw [hcmd2], hrep2.2.2.2.1, hopk2⟩,
    drawsMatch_single32 r S cls (Nat.le_of_eq hc2_len.symm) (gClean_sigma_42 r cls 32),
    ?_, hrep2, ?_⟩
  · unfold OutputsMatch; rw [ev2_pt_eq_ev1, hcmd2]
    refine ⟨_, rfl, rfl, ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt0Clean rnd; rw [gamma_rand]; simp [gClean_sigma_35]
  · unfold DY.Libsignal.Composed.Refinement.PathFaithfulAt
    intro p _; dsimp only; rw [hbks_nil]; rintro ⟨_, ⟨⟩, _⟩

private theorem runMatches_s3Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S (gClean r cls)) :
    RunMatches keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 3))
      s3Clean (ev 3)
      (stepView s3Clean (runTrace r (ssClean cls 3)) (runWrapped (ev 3)))
      (some (some 3#32, 7#32, 9#32)) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hp3, hcmd3, hex3, _⟩ := ev3_cmd_and_exit
  obtain ⟨hc3_len, hent3_len, hent3_at⟩ := ev3_coins_base
  rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.2.1]
  refine ⟨rfl, by rw [hp3]; rfl, by rw [hcmd3]; trivial, hf.bob_eq.symm,
    (s3_next_ok cls).2, ⟨[], hex3⟩, rfl, ?_⟩
  refine ⟨⟨.recv, [dhPk spkB, DY.Signature.sign ikB spkNonce (DY.Libsignal.PQXDH.encodeEC (dhPk spkB)),
      kemPk pqskB, DY.Signature.sign ikB pqNonce (DY.Libsignal.PQXDH.encodeKEM (kemPk pqskB)),
      dhPk opkB], .bundle, none⟩,
    rngEntry (randTerm 52 32) ::
      (kyberCoinEntries (randTerm 53 32) ++
        [{ rngEntry (randTerm 54 32) with anchor := some 57 }]),
    [], by rw [stepView_s3, List.append_nil],
    ⟨by unfold inputKind; rw [hcmd3], by rw [ev3_in_eq_ev0]; exact bundleMatches_ev0 hfit hCompat⟩,
    drawsMatch_alice_init r S cls hc3_len hent3_len hent3_at
      (gClean_sigma_52 r cls 32) (gClean_sigma_53 r cls 32) (gClean_sigma_54 r cls 32),
    by unfold OutputsMatch; rw [hex3, hcmd3]; rfl,
    trivial, fun _ _ => trivial⟩

private theorem runMatches_s4Clean {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hev4_out : (ev 4).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) o2Clean.ek)
      (gamma keepOpkI0 S (gClean r cls) o2Clean.ct)
      (gamma keepOpkI0 S (gClean r cls) (m1Clean cls)))) :
    RunMatches keepOpkI0 r S (gClean r cls) (runTrace r (ssClean cls 4))
      (s4Clean cls) (ev 4)
      (stepView (s4Clean cls) (runTrace r (ssClean cls 4)) (runWrapped (ev 4)))
      (some (some 3#32, 7#32, 9#32)) := by
  have hf := r_facts_of_fit hfit
  obtain ⟨hp4, hcmd4, _, hc4_len, hw4⟩ := ev4_facts
  rw [(runTrace_ssClean_eqs cls hf.alice_eq hf.bob_eq hf.withOpk_eq).2.2.2.2.1]
  refine ⟨rfl, by rw [hp4]; rfl, by rw [hcmd4]; trivial, trivial,
    (s4_next_ok cls).2, ⟨_, hev4_out⟩, rfl, ?_⟩
  refine ⟨⟨.pt, [pt1Clean], .single, none⟩,
    if cls 1 != 0 then [rngEntry (randTerm 62 (cls 1))] else [],
    [⟨.send, [o2Clean.ek, o2Clean.ct, m1Clean cls], .preKeySend, none⟩],
    by rw [hw4]; exact stepView_s4 cls, ?_,
    drawsMatch_enc r S cls hv.2 (Nat.le_of_eq hc4_len.symm) (gClean_sigma_62 r cls (cls 1)),
    ?_, trivial, fun _ _ => trivial⟩
  · refine ⟨by unfold inputKind; rw [hcmd4], ?_⟩
    simp only [List.map_cons, List.map_nil]
    unfold pt1Clean rnd; rw [gamma_rand]; simp [gClean_sigma_61]
  · unfold OutputsMatch; rw [hev4_out, hcmd4]
    exact ⟨_, rfl, rfl, some 3#32, 7#32, 9#32, rfl, rfl⟩

theorem explains_ssClean_5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {cls : Nat → Nat}
    (hfit : keepOpkCompFitsPinned (keepOpkI0, keepOpkHooks0) r)
    (hv : ValidCoinLens cls)
    (hCompat : GhostAndSemMatchSetup keepOpkI0 r S g)
    (hev1_out : (ev 1).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) oOpk.ek)
      (gamma keepOpkI0 S (gClean r cls) oOpk.ct)
      (gamma keepOpkI0 S (gClean r cls) (m0Clean cls))))
    (hev4_out : (ev 4).exit = some (0, preKeyWire (some 3#32) 7#32 9#32 r.regIdA
      (ecKey (pubBytes keepOpkI0 (secretBytes r 0)))
      (gamma keepOpkI0 S (gClean r cls) o2Clean.ek)
      (gamma keepOpkI0 S (gClean r cls) o2Clean.ct)
      (gamma keepOpkI0 S (gClean r cls) (m1Clean cls)))) :
    Explains keepOpkI0 r S (gClean r cls) (ssClean cls 5) (visClean r cls 5) (trace0.take 5) := by
  have hf := r_facts_of_fit hfit
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  have hex2 := explains_ssClean_2 hfit hv hCompat hev1_out
  have csm0 : CleanStepsMatch r S (gClean r cls) none none (setupTrace r)
      (ssClean cls 0) (trace0.take 0) (visClean r cls 0) :=
    CleanStepsMatch.nil none (setupTrace r)
  have csm1 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 1) (trace0.take 1) (visClean r cls 1) := by
    rw [ssClean_succ (s := s0Clean) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s0Clean) rfl]
    exact csm0.snoc ev0_bundle_base.2.2.1.symm (runMatches_s0Clean hfit hCompatClean)
  have csm2 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 2) (trace0.take 2) (visClean r cls 2) := by
    rw [ssClean_succ (s := s1Clean cls) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s1Clean cls) rfl]
    exact csm1.snoc (nextBundleIds_ev1 _).symm (runMatches_s1Clean hfit hv hev1_out)
  have csm3 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 3) (trace0.take 3) (visClean r cls 3) := by
    rw [ssClean_succ (s := s2Clean) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s2Clean) rfl]
    exact csm2.snoc (nextBundleIds_ev2 _).symm (runMatches_s2Clean hfit hv hex2)
  have csm4 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 4) (trace0.take 4) (visClean r cls 4) := by
    rw [ssClean_succ (s := s3Clean) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s3Clean) rfl]
    exact csm3.snoc ev0_bundle_base.2.2.2.1.symm (runMatches_s3Clean hfit hCompatClean)
  have csm5 : CleanStepsMatch r S (gClean r cls) none (some (some 3#32, 7#32, 9#32))
      (setupTrace r) (ssClean cls 5) (trace0.take 5) (visClean r cls 5) := by
    rw [ssClean_succ (s := s4Clean cls) rfl, trace0_take_succ (by decide),
        visClean_succ (by decide) (s := s4Clean cls) rfl]
    exact csm4.snoc (nextBundleIds_ev4 _).symm (runMatches_s4Clean hfit hv hev4_out)
  exact ⟨hCompatClean, ghostWF_visClean hfit hv (by decide),
    modelRunWF_ssClean 5 hf.alice_eq hf.bob_eq hf.withOpk_eq hv,
    csm5.toMatchesEventsAt⟩

end Symbolic.BugInjection.Proofs.SyntheticKeepOpk.RecvNoCollision.CleanPrefixC
