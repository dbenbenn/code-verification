/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4PrefixAux
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.Initiate.InitOk35Pure
import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import Symbolic.Proofs.Swarm.CREF.ModelBridge
import Symbolic.Proofs.Swarm.CREF.SendWire.ModelSteps
import Symbolic.Proofs.Swarm.UA.XlateSteps
import DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Clean-Run Prefix Inversion for Calls 0 & 1 (`Calls0to4Prefix/Inv0to1.lean`)

Proves:
1. `alice_call0_agree`: steps Call 0 (`ev 0`, Alice `.init`) on arbitrary network prefix `c0.pre`,
   establishing `PkiUnchanged`, `NoSkippedKeyStored`, `OnlyAliceDone`, `ActivePartySt "alice"`,
   and `NoPartyState "bob"`.
2. `party_send_agree`: generic `.send` step transition (`sIdx = 0` for Call 1 wrapped PreKey send
   and `sIdx = 1` for Call 3 unwrapped Whisper send), preserving `PkiUnchanged`,
   `NoSkippedKeyStored`, and `OnlyAliceDone` (when wrapped), advancing `ActivePartySt`, and pinning
   `(ev (sendCallOf sIdx)).exit` to the concrete wire bytes under `gClean r cls`.
3. `PrefixInv1` / `prefix_inv_1` (`k = 1`) and `PrefixInv2` / `prefix_inv_2` (`k = 2`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (PQXDHEvent)
open DY.Libsignal.TripleRatchet (TRState isCurrentSnapshot u32Max)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma clamp ecKey kyberKey pubBytes secretBytes preKeyWire setupTrace runTrace
   runSteps stepView pendingPreKey received rngEntry kyberCoinEntries randTerm
   GhostAndSemMatchSetup GhostWF OutputsMatch RunMatches MatchesEvents Explains
   runWrapped inputKind nextBundleIds)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry TRStE at?_append_cases proj_inj_eq run_bind_fst)
open Symbolic.Swarm.CREF (bks_stored_of_getLocalState)
open Symbolic.Swarm.CREF.TR (gamma_rand gamma_dhPk)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (Runs rnd encSt encMsg encSig parse_encMsg aliceOut RndE NetE StT)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB spkB pqskB dhsA o1 stA0 t4)
open Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
  (iniAliceStartTr iniAliceStartState aliceVis_iniAliceStartTr at?_trSt_iniAliceStartTr
   getMessageSentAt_of_netMsgAt)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned rcprPubOfIdx rcprSecretIdx)

attribute [local irreducible] ev

/-! ## 1. Call 0 (`ev 0` = Alice `.init`) Step Inversion (`alice_call0_agree`) -/

theorem alice_call0_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat) {c0 : PeeledCall}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hgwf : GhostWF g visAll)
    (hnet : ∀ x ∈ c0.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches rcprI0 r S g (runSteps c0.pre (setupTrace r)) c0.s (ev 0) c0.v none)
    (hsub : ∀ w ∈ c0.v, w ∈ visAll) :
    let tr₁ := c0.s.next (runSteps c0.pre (setupTrace r))
    ∃ ek0 ct0 : Bytes,
      gamma rcprI0 S g ek0 = gamma rcprI0 S (gClean r cls) o1.ek ∧
      gamma rcprI0 S g ct0 = gamma rcprI0 S (gClean r cls) o1.ct ∧
      PkiUnchanged tr₁ ∧
      NoSkippedKeyStored tr₁ ∧
      OnlyAliceDone ek0 ct0 tr₁ ∧
      ActivePartySt "alice" true S g (gClean r cls) [⟨2, by decide⟩] ⟨4, by decide⟩ stA0 tr₁ ∧
      NoPartyState "bob" tr₁ ∧
      nextBundleIds none (ev 0) = some (none, 7#32, 9#32) := by
  set tr₀ := runSteps c0.pre (setupTrace r)
  have hnames := r_names_of_fit hfit
  have hpki₀ : PkiUnchanged tr₀ :=
    pkiUnchanged_runSteps_network c0.pre hnet (setupTrace_eq_t4 hfit ▸ pkiUnchanged_t4)
  have hnskip₀ : NoSkippedKeyStored tr₀ :=
    noSkippedKeyStored_runSteps_network c0.pre hnet (setupTrace_eq_t4 hfit ▸ noSkippedKeyStored_t4)
  have hnoA₀ : NoPartyState "alice" tr₀ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c0.pre _ hnet)
      (noPartyState_setupTrace "alice" r)
  have hnoB₀ : NoPartyState "bob" tr₀ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c0.pre _ hnet)
      (noPartyState_setupTrace "bob" r)
  obtain ⟨hparty_ev0, hcmd_ev0, hexit_ev0, _⟩ := ev0_cmd_and_exit
  obtain ⟨_, hparty, hfits, hpeer, hok, _, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_ev0] at hparty
  rw [hcmd_ev0] at hfits
  cases hs : c0.s with
  | aliceStart a b idS regB bh =>
    rw [hs] at hparty hpeer hok hvis_eq
    rcases Option.some.inj hparty.symm with rfl
    have hb_eq : b = "bob" := by simpa [Step.MatchesSetupPeer, hnames.2] using hpeer
    subst hb_eq
    have hnext_mv : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
        (DY.Libsignal.Composed.Refinement.Move.aliceStart "alice" "bob" idS regB bh 35).next tr₀ := by
      rw [Symbolic.Swarm.CREF.b5_aliceStart_next]
      dsimp only [Step.next, Step.toInput]
      erw [Symbolic.Proofs.Swarm.UA.XlateSteps.stepIn_next]
    obtain ⟨o0_ok, ho0_ok⟩ := Symbolic.Proofs.Swarm.UA.XlateSteps.aliceStart_ok_trOfOut hok
    have hlen_o0 : (Symbolic.Swarm.CREF.aliceStartTrOfOut tr₀ "alice" "bob" o0_ok).length =
        tr₀.length + 9 :=
      Symbolic.Swarm.CREF.length_iniAliceStartTr tr₀ "alice" "bob" o0_ok
    rcases Symbolic.Swarm.CREF.aliceStart_next_cases "alice" "bob" idS regB bh 35 tr₀ with
      h0 | h1 | ⟨ik_a, ik_b, vk_b, spk, spkSig, pqpk, pqpkSig, opk, honest,
        hstA, hregB, hspk, hspkSig, hpq, hpqSig, hopk, h3⟩
    · have := (congrArg DY.Trace.length (h0.symm.trans ho0_ok)).trans hlen_o0; omega
    · have := (append_len tr₀ (RndE 32)).symm.trans
        ((congrArg DY.Trace.length (h1.symm.trans ho0_ok)).trans hlen_o0); omega
    · have hikA_pin : ik_a = ikA := by
        rcases pki_pin_st hpki₀ hstA with ⟨_, hst_eq⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩
        · cases hst_eq; rfl
        · exact absurd hf (by decide)
        · exact absurd hf (by decide)
        · exact absurd hf (by decide)
      subst hikA_pin
      have hregB_at : (tr₀.at? regB : Option (DY.ProtocolEvent.ExecEntryT PQXDHEvent)) =
          some ⟨.IdentityRegistered "bob" ik_b vk_b honest⟩ := by
        rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hregB
      have hikB_pin : ik_b = dhPk ikB := by
        rcases pki_pin_reg hpki₀ hregB_at with ⟨hf, _⟩ | ⟨_, hpk, _⟩
        · exact absurd hf (by decide)
        · exact hpk
      subst hikB_pin
      have hout_nil : outs = [] := by
        unfold OutputsMatch at hout
        rw [hexit_ev0, hcmd_ev0] at hout
        exact hout
      rw [hout_nil, List.append_nil] at hv_split
      let o_gen := Symbolic.Swarm.COMPOSED.CompTrace.aliceOut tr₀ ikA (dhPk ikB) spk pqpk opk
      have htr'_ofOut : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          Symbolic.Swarm.CREF.aliceStartTrOfOut tr₀ "alice" "bob" o_gen :=
        hnext_mv.trans h3
      have hvis_full : c0.v =
          { kind := .recv,
            terms := received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList),
            layout := .bundle, anchor := none } ::
          rngEntry (randTerm tr₀.length 32) ::
          (kyberCoinEntries (randTerm (tr₀.length + 1) 32) ++
            [{ rngEntry (randTerm (tr₀.length + 2) 32) with anchor := some (tr₀.length + 5) }]) := by
        rw [hvis_eq]; unfold stepView
        simp only [hok, ↓reduceIte, htr'_ofOut]
        rw [Symbolic.Swarm.CREF.exposures_aliceStartTrOfOut, List.append_nil]
        exact aliceVis_iniAliceStartTr tr₀ "alice" "bob" o_gen bh
      have hinp_drs := hv_split.symm.trans hvis_full
      injection hinp_drs with hinp_eq hdrs_eq
      obtain ⟨_, hbun_b4, hnext_ids, hbun_spk, _, hbun_pq, _, _⟩ := ev0_bundle_slices
      have hopk_none : bh.opk = none ∧ opk = none := by
        rcases hopk with ⟨h1, h2⟩ | ⟨idx, u, h1, _, hu⟩
        · exact ⟨h1, h2⟩
        · exfalso
          have hrec : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
              [spk, spkSig, pqpk, pqpkSig, u] := by
            rw [h1]
            change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig, idx] = _
            simp only [received, List.filterMap_cons, List.filterMap_nil,
              getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
              getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig,
              getMessageSentAt_of_netMsgAt hu]
          rw [hinp_eq] at hbm_in
          have hplm := hbm_in.2
          dsimp only at hplm
          rw [hrec] at hplm
          dsimp only [DY.Libsignal.Composed.Refinement.PreKeyBundleLayoutMatches,
            DY.Libsignal.PQXDH.Refinement.BundleBlob.hasOpkByte] at hplm
          rw [hbun_b4] at hplm
          cases hplm.2.1
      rcases hopk_none with ⟨hbh_opk, hopk_eq⟩
      subst hopk_eq
      have hrec4 : received tr₀ ([bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] ++ bh.opk.toList) =
          [spk, spkSig, pqpk, pqpkSig] := by
        rw [hbh_opk]
        change received tr₀ [bh.spk, bh.spkSig, bh.pqpk, bh.pqpkSig] = _
        simp only [received, List.filterMap_cons, List.filterMap_nil,
          getMessageSentAt_of_netMsgAt hspk, getMessageSentAt_of_netMsgAt hspkSig,
          getMessageSentAt_of_netMsgAt hpq, getMessageSentAt_of_netMsgAt hpqSig]
      rw [hinp_eq] at hbm_in
      have hplm := hbm_in.2
      dsimp only at hplm
      rw [hrec4] at hplm
      obtain ⟨⟨_, hspk_sl, _, hpq_sl, _⟩, _⟩ := hplm
      have hspk_gam : gamma rcprI0 S g spk =
          gamma rcprI0 S (gClean r cls) (dhPk spkB) := by
        have h1 : ecKey (gamma rcprI0 S g spk) = ecKey (rcprPubOfIdx ⟨2, by decide⟩) :=
          hspk_sl.symm.trans hbun_spk
        have h2 : gamma rcprI0 S g spk = rcprPubOfIdx ⟨2, by decide⟩ :=
          (List.cons.inj h1).2
        exact h2.trans (gamma_dhPk_spkB (S := S) (cls := cls) hfit).symm
      have hpq_gam : gamma rcprI0 S g pqpk =
          gamma rcprI0 S (gClean r cls) (DY.PQKem.kemPk pqskB) := by
        have h1 : kyberKey (gamma rcprI0 S g pqpk) = kyberKey rcprSetup.kyberPk :=
          hpq_sl.symm.trans hbun_pq
        have h2 : gamma rcprI0 S g pqpk = rcprSetup.kyberPk := (List.cons.inj h1).2
        exact h2.trans (gamma_kemPk_pqskB_gClean cls hfit hCompat).symm
      have hsub_drs : ∀ w ∈ drs, w ∈ visAll :=
        fun w hw => hsub w (hv_split ▸ List.mem_cons_of_mem _ hw)
      rw [hdrs_eq] at hdr hsub_drs
      obtain ⟨hek_coins, he_coins, hdhs_coins⟩ := ev0_draws_pin hgwf hsub_drs hdr
      have hek_gam : gamma rcprI0 S g (rnd tr₀.length 32) =
          gamma rcprI0 S (gClean r cls) (rnd 22 32) := by
        change gamma rcprI0 S g (randTerm tr₀.length 32) =
          gamma rcprI0 S (gClean r cls) (randTerm 22 32)
        rw [hek_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_22]
      have he_gam : gamma rcprI0 S g (rnd (tr₀.length + 1) 32) =
          gamma rcprI0 S (gClean r cls) (rnd 23 32) := by
        change gamma rcprI0 S g (randTerm (tr₀.length + 1) 32) =
          gamma rcprI0 S (gClean r cls) (randTerm 23 32)
        rw [he_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_23]
      have hdhs_gam : gamma rcprI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma rcprI0 S (gClean r cls) dhsA := by
        change gamma rcprI0 S g (randTerm (tr₀.length + 2) 32) =
          gamma rcprI0 S (gClean r cls) (randTerm 24 32)
        rw [hdhs_coins]; unfold randTerm; rw [gamma_rand]; simp [gClean_sigma_24]
      have hikA_gam : gamma rcprI0 S g ikA = gamma rcprI0 S (gClean r cls) ikA :=
        gamma_setup_rnd_eq cls hfit hCompat (ts := 0) (n := 32) (by decide) (by decide)
      have hikB_gam : gamma rcprI0 S g (dhPk ikB) =
          gamma rcprI0 S (gClean r cls) (dhPk ikB) := by
        rw [gamma_dhPk, gamma_dhPk,
            gamma_setup_rnd_eq cls hfit hCompat (ts := 5) (n := 32) (by decide) (by decide)]
      obtain ⟨hek_pk, hct_eq, hst_agree⟩ := stateBytesAgree_aliceStart (tr := tr₀)
        hikA_gam hikB_gam hspk_gam hpq_gam hek_gam he_gam hdhs_gam
      let o_ss := aliceOut tr₀ ikA (dhPk ikB) spk pqpk
      have htr₁_eq : (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ =
          iniAliceStartTr tr₀ "alice" "bob" o_ss :=
        htr'_ofOut
      refine ⟨o_ss.ek, o_ss.ct, hek_pk, hct_eq, ?_, ?_, ?_, ?_, ?_, hnext_ids⟩
      · exact pkiUnchanged_step_party rfl hpki₀
      · rw [htr₁_eq]
        exact noSkippedKeyStored_iniAliceStartTr hnskip₀
      · rw [htr₁_eq]
        exact onlyAliceDone_iniAliceStartTr
          (onlyAliceDone_runSteps_network c0.pre hnet
            (setupTrace_eq_t4 hfit ▸ onlyAliceDone_t4 o_ss.ek o_ss.ct))
      · have hle_tr₁ : tr₀ ≤ (Step.aliceStart "alice" "bob" idS regB bh).next tr₀ := by
          rw [htr₁_eq]
          unfold iniAliceStartTr
          dsimp only
          iterate 8 refine DY.Trace.le_trans _ _ _ ?_ (DY.Trace.append_le _ _)
          exact DY.Trace.append_le _ _
        let stA_ss := iniAliceStartState tr₀ "bob" o_ss
        have hat_stA : (((Step.aliceStart "alice" "bob" idS regB bh).next tr₀).at?
            (tr₀.length + 8) : Option TRStEntry) = some ⟨⟨"alice", stA_ss⟩⟩ := by
          rw [htr₁_eq, at?_trSt_iniAliceStartTr]
          simp only [↓reduceIte]; rfl
        refine activePartySt_init hnoA₀ hle_tr₁ hat_stA ?_ rfl hst_agree ?_ ?_
        · intro j st hj hat_j
          rw [htr₁_eq, at?_trSt_iniAliceStartTr] at hat_j
          by_cases hjeq : j = tr₀.length + 8
          · subst hjeq
            simp only [↓reduceIte, TRStE, Option.some.injEq] at hat_j
            injection hat_j with h1
            injection h1 with _ h2
            exact ⟨rfl, h2.symm⟩
          · simp only [hjeq, ↓reduceIte] at hat_j
            exact False.elim (hnoA₀ j st hat_j)
        · show [gamma rcprI0 S g spk] = [rcprPubOfIdx ⟨2, by decide⟩]
          have h1 : ecKey (gamma rcprI0 S g spk) = ecKey (rcprPubOfIdx ⟨2, by decide⟩) :=
            hspk_sl.symm.trans hbun_spk
          exact congrArg (· :: []) ((List.cons.inj h1).2)
        · show rcprSecretIdx (clamp (gamma rcprI0 S g (randTerm (tr₀.length + 2) 32))) =
              some ⟨4, by decide⟩
          rw [hdhs_coins]
          exact ev0_coins_facts.2.2.1
      · exact noPartyState_of_noNew
          (noNewPartyState_step_other tr₀ rfl (by simp [Step.party?])) hnoB₀
  | _ => rw [hs] at hfits; cases hfits

/-! ## 2. Generic `.send` Step Inversion (`party_send_agree`: Calls 1 & 3) -/

theorem party_send_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {party otherParty : Participant} {initRole : Bool}
    {recvIdxs : List (Fin 7)} {skIdx : Fin 7} {stClean : TRState}
    {ek0 ct0 : Bytes} {sIdx tsPt tsCoins : Nat}
    {tr : ExecTrace} {c : PeeledCall}
    (hne_other : otherParty ≠ party)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hnskip : NoSkippedKeyStored tr)
    (honly : runWrapped (ev (sendCallOf sIdx)) = true → OnlyAliceDone ek0 ct0 tr)
    (hek0 : gamma rcprI0 S g ek0 = gamma rcprI0 S (gClean r cls) o1.ek)
    (hct0 : gamma rcprI0 S g ct0 = gamma rcprI0 S (gClean r cls) o1.ct)
    (hAct : ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx stClean tr)
    (he_party : (ev (sendCallOf sIdx)).party = party ∧
      ∃ peer, (ev (sendCallOf sIdx)).cmd = .send peer)
    (hcl_eq : cls sIdx = stepCoinLen c.s)
    (hpt_clean : (gClean r cls).σ tsPt 32 = (ev (sendCallOf sIdx)).input)
    (hcoins_clean : ∀ n, (gClean r cls).σ tsCoins n = (ev (sendCallOf sIdx)).coins.take n)
    (hwrap_addr :
      (runWrapped (ev (sendCallOf sIdx)) = true ∧
       (gClean r cls).addr (encSig stClean (rnd tsCoins (cls sIdx))
         (DY.Spqr.spqrSend stClean.spqr (rnd tsCoins (cls sIdx))).2.1 (rnd tsPt 32)).wire =
         pqAddrBytes) ∨
      (runWrapped (ev (sendCallOf sIdx)) = false ∧
       (gClean r cls).addr (encSig stClean (rnd tsCoins (cls sIdx))
         (DY.Spqr.spqrSend stClean.spqr (rnd tsCoins (cls sIdx))).2.1 (rnd tsPt 32)).wire = []))
    (hnet : ∀ x ∈ c.pre, ∃ msg, x = .network msg)
    (hpre : c.s.PreCond (runSteps c.pre tr))
    (hlok : c.s.LocalOk (runSteps c.pre tr))
    (hrm : RunMatches rcprI0 r S g (runSteps c.pre tr) c.s (ev (sendCallOf sIdx)) c.v
      (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c.v, w ∈ visAll) :
    let tr' := c.s.next (runSteps c.pre tr)
    let coins' := rnd tsCoins (cls sIdx)
    let pt' := rnd tsPt 32
    let mClean := encMsg stClean coins' (DY.Spqr.spqrSend stClean.spqr coins').2.1 pt'
    PkiUnchanged tr' ∧
    NoSkippedKeyStored tr' ∧
    (runWrapped (ev (sendCallOf sIdx)) = true → OnlyAliceDone ek0 ct0 tr') ∧
    ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx (encSt stClean coins') tr' ∧
    NoNewPartyState otherParty tr tr' ∧
    (if runWrapped (ev (sendCallOf sIdx)) then
       (ev (sendCallOf sIdx)).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
         (ecKey (pubBytes rcprI0 (secretBytes r 0)))
         (gamma rcprI0 S (gClean r cls) o1.ek)
         (gamma rcprI0 S (gClean r cls) o1.ct)
         (gamma rcprI0 S (gClean r cls) mClean))
     else
       (ev (sendCallOf sIdx)).exit =
         some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) mClean)) := by
  set e := ev (sendCallOf sIdx)
  set tr₁ := runSteps c.pre tr
  have hpki₁ : PkiUnchanged tr₁ := pkiUnchanged_runSteps_network c.pre hnet hpki
  have hnskip₁ : NoSkippedKeyStored tr₁ := noSkippedKeyStored_runSteps_network c.pre hnet hnskip
  have honly₁ : runWrapped e = true → OnlyAliceDone ek0 ct0 tr₁ :=
    fun hw => onlyAliceDone_runSteps_network c.pre hnet (honly hw)
  have hAct₁ : ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx stClean tr₁ :=
    noNewPartyState_preserves_active (noNewPartyState_runSteps_network c.pre tr hnet) hAct
  obtain ⟨hparty_e, peer, hcmd_e⟩ := he_party
  obtain ⟨hcls_s, hparty, hfits, _, hok, hexit_some, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, _, _⟩ := hrm
  rw [hparty_e] at hparty
  rw [hcmd_e] at hfits
  cases hs : c.s with
  | messageEncryptAbort me stateIdx =>
    exfalso
    rw [hs, step_ok_encryptAbort_false] at hok
    cases hok
  | messageEncrypt me stateIdx cl pq =>
    rw [hs] at hparty hpre hlok hok hvis_eq hcl_eq hcls_s
    dsimp only [stepCoinLen] at hcl_eq
    rcases Option.some.inj hparty.symm with rfl
    have hpq_eq : pq = tr₁.length + 2 := by
      rcases hlok.2 with hpq2 | hpq3
      · exact hpq2
      · exfalso
        rw [hpq3] at hok
        unfold DY.Libsignal.Composed.Refinement.encryptAbortAfterSpqrIdx at hok
        rw [Symbolic.Proofs.Swarm.UA.XlateSteps.messageEncrypt_fail_not_ok] at hok
        cases hok
    subst hpq_eq
    have hcur : isCurrentSnapshot tr₁ stateIdx = true := preCond_messageEncrypt hpre
    have hok_run : ((DY.Libsignal.TripleRatchet.messageEncrypt party stateIdx cl
        (tr₁.length + 2)).run tr₁).1.isSome = true := by
      rwa [step_ok_encrypt] at hok
    unfold DY.Libsignal.TripleRatchet.messageEncrypt at hok_run
    rw [run_bind_fst] at hok_run
    rcases hst : ((DY.PersistentLocalState.getLocalState party stateIdx : Traceful TRState).run
        tr₁).1 with _ | st
    · simp [hst] at hok_run
    · obtain ⟨hinit, hagree, hrecv, hdhs⟩ := activePartySt_pin_state hAct₁ hst hcur
      have hat_st : tr₁.at? stateIdx = some (StT party st) :=
        bks_stored_of_getLocalState hst
      rw [hst, Symbolic.Swarm.COMPOSED.CompTrace.getLocalState_tr_snd] at hok_run
      dsimp only at hok_run
      have hns : st.ns ≠ u32Max := by
        intro hmax
        have hf : ((failure : Traceful Unit).run tr₁).1 = none := by rw [DY.Traceful.run_failure]
        simp [_root_.guard, hmax, run_bind_fst, hf] at hok_run
      let pqSalt := (DY.Spqr.spqrSend st.spqr (rnd (tr₁.length + 1) cl)).2.1
      have hpq_at : (((tr₁.append (RndE 32)).append (RndE cl)).append (NetE pqSalt)).at?
          (tr₁.length + 2) = some (NetE pqSalt) :=
        at?_append_at _ _ (by simp only [append_len])
      have hruns := Runs.messageEncryptGen hat_st hns hpq_at
      have hnext_eq : (Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁ =
          encTrGen tr₁ party stateIdx cl st pqSalt := by
        rw [step_next_encrypt]; exact hruns.2
      have hview := encTrGen_stepView_ok (wrapped := runWrapped e) hok hnext_eq
      obtain ⟨out, hexit_e⟩ := hexit_some
      unfold OutputsMatch at hout
      rw [hexit_e, hcmd_e] at hout
      obtain ⟨v_out, rfl, hbm_out⟩ := hout
      have hv_comb := hv_split.symm.trans (hvis_eq.trans hview)
      injection hv_comb with hinp_eq hdrs_out_eq
      have hpt_gam : gamma rcprI0 S g (rnd tr₁.length 32) =
          gamma rcprI0 S (gClean r cls) (rnd tsPt 32) := by
        have hin_k : inputKind e = .pt := by unfold inputKind; rw [hcmd_e]
        rw [hin_k, hinp_eq] at hbm_in
        have h1 : gamma rcprI0 S g (randTerm tr₁.length 32) = e.input := by
          simpa using hbm_in.2
        have h2 : gamma rcprI0 S (gClean r cls) (rnd tsPt 32) = e.input := by
          unfold rnd; rw [gamma_rand]; simp [hpt_clean]
        exact h1.trans h2.symm
      let encOpt : List VisEntry := encSendList (runWrapped e) (pendingPreKey tr₁ stateIdx)
        (encMsg st (rnd (tr₁.length + 1) cl) pqSalt (rnd tr₁.length 32))
      have hencOpt_nonempty : ∃ v_s, encOpt = [v_s] := by
        dsimp only [encOpt, encSendList]
        rcases hw : runWrapped e with _ | _ <;>
          rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · exact ⟨_, rfl⟩
        · exfalso
          rw [hw, hppk] at hdrs_out_eq; dsimp only [encSendList] at hdrs_out_eq
          rw [List.append_nil] at hdrs_out_eq
          have hmem : v_out ∈ (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) := by
            rw [← hdrs_out_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
          by_cases hcl0 : cl = 0 <;> simp [hcl0, rngEntry] at hmem
          subst hmem; cases hbm_out.1
        · exfalso
          rw [hw, hppk] at hdrs_out_eq; dsimp only [encSendList] at hdrs_out_eq
          rw [List.append_nil] at hdrs_out_eq
          have hmem : v_out ∈ (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) := by
            rw [← hdrs_out_eq]; exact List.mem_append_right _ (List.mem_singleton_self _)
          by_cases hcl0 : cl = 0 <;> simp [hcl0, rngEntry] at hmem
          subst hmem; cases hbm_out.1
        · exact ⟨_, rfl⟩
      obtain ⟨v_s, hv_s⟩ := hencOpt_nonempty
      change drs ++ [v_out] =
        (if cl != 0 then [rngEntry (randTerm (tr₁.length + 1) cl)] else []) ++ encOpt at hdrs_out_eq
      rw [hv_s] at hdrs_out_eq
      obtain ⟨hdrs_eq, rfl⟩ := append_singleton_inj hdrs_out_eq
      have hc_gam : gamma rcprI0 S g (rnd (tr₁.length + 1) cl) =
          gamma rcprI0 S (gClean r cls) (rnd tsCoins (cls sIdx)) := by
        rw [hcl_eq]
        by_cases hcl0 : cl = 0
        · subst hcl0; unfold rnd; rw [gamma_rand, gamma_rand]; simp
        · have hdrs_1 : drs = [rngEntry (randTerm (tr₁.length + 1) cl)] := by
            simpa [hcl0] using hdrs_eq
          rw [hdrs_1] at hdr
          have hmem_rng : rngEntry (randTerm (tr₁.length + 1) cl) ∈ visAll := by
            apply hsub; rw [hv_split, hdrs_1]; simp
          have hlen_c : (gamma rcprI0 S g (randTerm (tr₁.length + 1) cl)).length = cl := by
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
                have hp0_eq : gamma rcprI0 S g (randTerm (tr₁.length + 1) cl) = p0 := by
                  simpa [rngEntry] using hp0.2
                simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hpref
                obtain ⟨rem_c, hcoins_eq⟩ := hpref
                have htake_c : e.coins.take cl = p0 := by
                  rw [← hcoins_eq]; exact List.take_left' (hp0_eq ▸ hlen_c)
                have hg_clean : gamma rcprI0 S (gClean r cls) (rnd tsCoins cl) = e.coins.take cl := by
                  unfold rnd; rw [gamma_rand]; simp [hcl0, hcoins_clean]
                exact hp0_eq.trans (htake_c.symm.trans hg_clean.symm)
      have hv_s_mem : v_out ∈ visAll := by apply hsub; rw [hv_split]; simp
      have hpki₂ : PkiUnchanged ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        pkiUnchanged_step_party rfl hpki₁
      have hnskip₂ : NoSkippedKeyStored
          ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) := by
        rw [hnext_eq]; exact noSkippedKeyStored_encTrGen hnskip₁
      have honly₂ : runWrapped e = true →
          OnlyAliceDone ek0 ct0 ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        fun hw => onlyAliceDone_messageEncrypt (honly₁ hw)
      have hnoOther₂ : NoNewPartyState otherParty tr
          ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) :=
        noNewPartyState_trans (noNewPartyState_runSteps_network c.pre tr hnet)
          (noNewPartyState_step_other tr₁ rfl (by simp [Step.party?, Ne.symm hne_other]))
      have hst_upd : StateBytesAgree S g (gClean r cls)
          (encSt st (rnd (tr₁.length + 1) cl)) (encSt stClean (rnd tsCoins (cls sIdx))) →
          ActivePartySt party initRole S g (gClean r cls) recvIdxs skIdx
            (encSt stClean (rnd tsCoins (cls sIdx)))
            ((Step.messageEncrypt party stateIdx cl (tr₁.length + 2)).next tr₁) := by
        intro hst_ag'
        rw [hnext_eq]
        have hle_enc := encTrGen_le tr₁ party stateIdx cl st pqSalt
        have hge_idx : tr₁.length ≤ tr₁.length + 5 := by omega
        have hat_new : ((encTrGen tr₁ party stateIdx cl st pqSalt).at? (tr₁.length + 5) :
            Option TRStEntry) = some ⟨⟨party, encSt st (rnd (tr₁.length + 1) cl)⟩⟩ := by
          dsimp only [encTrGen]
          rw [at?_append_of_lt _ _ (by simp only [append_len]; omega)]
          exact at?_append_at _ _ (by simp only [append_len])
        refine activePartySt_of_unique_new hAct₁ hle_enc hge_idx hat_new ?_ hinit hst_ag' hrecv hdhs
        intro j s0 hj hat_j
        dsimp only [encTrGen] at hat_j
        rcases at?_append_cases hat_j with ⟨_, hat6⟩ | ⟨_, hp6⟩
        · rcases at?_append_cases hat6 with ⟨_, hat5⟩ | ⟨heq5, hp5⟩
          · rcases at?_append_cases hat5 with ⟨_, hat4⟩ | ⟨_, hp4⟩
            · rcases at?_append_cases hat4 with ⟨_, hat3⟩ | ⟨_, hp3⟩
              · rcases at?_append_cases hat3 with ⟨_, hat2⟩ | ⟨_, hp2⟩
                · rcases at?_append_cases hat2 with ⟨_, hat1⟩ | ⟨_, hp1⟩
                  · rcases at?_append_cases hat1 with ⟨_, _⟩ | ⟨_, hp0⟩
                    · omega
                    · cases hp0
                  · cases hp1
                · cases hp2
              · cases hp3
            · cases hp4
          · have hj5 : j = tr₁.length + 5 := by simp only [append_len] at heq5; omega
            subst hj5
            simp only [StT, proj_inj_eq, Option.some.injEq] at hp5
            injection hp5 with h1; injection h1 with _ hs0
            exact ⟨rfl, hs0.symm⟩
        · cases hp6
      rcases hwrap_addr with ⟨hw_true, haddr_clean⟩ | ⟨hw_false, haddr_clean⟩
      · dsimp only [encOpt] at hv_s
        rw [hw_true] at hv_s ⊢
        simp only [↓reduceIte]
        rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · rw [hppk] at hv_s; cases hv_s
        · rw [hppk] at hv_s
          dsimp only [encSendList] at hv_s
          simp only [List.cons.injEq, and_true] at hv_s
          subst hv_s
          obtain ⟨rfl, rfl⟩ := pendingPreKey_eq_of_onlyAliceDone (honly₁ hw_true) hppk
          have haddr_ss : g.addr (encSig st (rnd (tr₁.length + 1) cl) pqSalt
              (rnd tr₁.length 32)).wire = pqAddrBytes :=
            (hgwf.2.2 _ hv_s_mem rfl).1 rfl _ _ _ _ rfl (parse_encMsg _ _ _ _)
          obtain ⟨hst_ag', hm_eq⟩ := stateBytesAgree_encrypt hagree hc_gam hpt_gam
            (haddr_ss.trans haddr_clean.symm)
          have hsm := hbm_out.2
          dsimp only [DY.Libsignal.Composed.Refinement.SendMatches] at hsm
          obtain ⟨pkId, spkId, kpkId, hids_eq, hout_wire⟩ := hsm
          injection hids_eq with hprod
          obtain ⟨rfl, hprod2⟩ := Prod.mk.inj hprod
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hprod2
          rw [hek0, hct0, hm_eq] at hout_wire
          exact ⟨hpki₂, hnskip₂, fun _ => honly₂ hw_true, hst_upd hst_ag', hnoOther₂,
            hexit_e.trans (congrArg (some ∘ (0, ·)) hout_wire)⟩
      · dsimp only [encOpt] at hv_s
        rw [hw_false] at hv_s ⊢
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ek, ct⟩
        · rw [hppk] at hv_s
          dsimp only [encSendList] at hv_s
          simp only [List.cons.injEq, and_true] at hv_s
          subst hv_s
          have haddr_ss : g.addr (encSig st (rnd (tr₁.length + 1) cl) pqSalt
              (rnd tr₁.length 32)).wire = [] :=
            (hgwf.2.2 _ hv_s_mem rfl).2 rfl _ _ rfl (parse_encMsg _ _ _ _)
          obtain ⟨hst_ag', hm_eq⟩ := stateBytesAgree_encrypt hagree hc_gam hpt_gam
            (haddr_ss.trans haddr_clean.symm)
          obtain ⟨t_w, ht_eq, hout_wire⟩ := hbm_out.2
          simp only [List.cons.injEq, and_true] at ht_eq
          subst ht_eq
          rw [hm_eq] at hout_wire
          exact ⟨hpki₂, hnskip₂, False.elim, hst_upd hst_ag', hnoOther₂,
            hexit_e.trans (congrArg (some ∘ (0, ·)) hout_wire)⟩
        · rw [hppk] at hv_s; cases hv_s
  | _ => rw [hs] at hfits; cases hfits

/-! ## 3. Top-Level Prefix Inversion for `k = 1` & `k = 2` (`PrefixInv1`, `PrefixInv2`) -/

structure PrefixInv1 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)
  pki : PkiUnchanged (runTrace r ss)
  noSkip : NoSkippedKeyStored (runTrace r ss)
  onlyAlice : ∃ ek0 ct0 : Bytes,
    gamma rcprI0 S g ek0 = gamma rcprI0 S (gClean r cls) o1.ek ∧
    gamma rcprI0 S g ct0 = gamma rcprI0 S (gClean r cls) o1.ct ∧
    OnlyAliceDone ek0 ct0 (runTrace r ss)
  actAlice : ActivePartySt "alice" true S g (gClean r cls)
    [⟨2, by decide⟩] ⟨4, by decide⟩ stA0 (runTrace r ss)
  noBob : NoPartyState "bob" (runTrace r ss)

theorem prefix_inv_1 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 1)) :
    ∃ cls : Nat → Nat, PrefixInv1 r S g ss cls := by
  obtain ⟨hCompat, hgwf, hmwf, hm⟩ := hex
  rw [rcprTrace_take_eq_evsRange (by decide)] at hm
  unfold MatchesEvents at hm
  rw [← Nat.zero_add 1] at hm
  obtain ⟨csOrig, hcs_len, hpv0⟩ :=
    peel_evsRange 1 0 (by decide) hmwf.2.2.1 hm (fun _ hw => hw)
  let cls := clsOfCalls csOrig
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv0
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  rcases hcs_eq : csOrig with _ | ⟨c0, _ | _⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · rw [hcs_eq] at hpv0
    cases hpv0 with
    | @cons _ _ _ _ _ tail hnet0 _ _ hrm0 hsub0 hpv1 =>
      obtain ⟨ek0, ct0, hek0, hct0, hpki1, hnskip1, honly1, hActA1, hnoB1, _⟩ :=
        alice_call0_agree cls hfit hCompat hgwf hnet0 hrm0 hsub0
      cases hpv1 with
      | nil hnet_tail =>
        have hrt : runTrace r (c0.pre ++ c0.s :: tail) =
            runSteps tail (c0.s.next (runSteps c0.pre (setupTrace r))) := by
          unfold runTrace; simp only [runSteps_append, runSteps]
        exact ⟨cls,
          { validCls := hvCls
            compatClean := hCompatClean
            pki := hrt ▸ pkiUnchanged_runSteps_network tail hnet_tail hpki1
            noSkip := hrt ▸ noSkippedKeyStored_runSteps_network tail hnet_tail hnskip1
            onlyAlice := ⟨ek0, ct0, hek0, hct0,
              hrt ▸ onlyAliceDone_runSteps_network tail hnet_tail honly1⟩
            actAlice := hrt ▸ noNewPartyState_preserves_active
              (noNewPartyState_runSteps_network tail _ hnet_tail) hActA1
            noBob := hrt ▸ noPartyState_of_noNew
              (noNewPartyState_runSteps_network tail _ hnet_tail) hnoB1 }⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len

structure PrefixInv2 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)
  pki : PkiUnchanged (runTrace r ss)
  noSkip : NoSkippedKeyStored (runTrace r ss)
  onlyAlice : ∃ ek0 ct0 : Bytes,
    gamma rcprI0 S g ek0 = gamma rcprI0 S (gClean r cls) o1.ek ∧
    gamma rcprI0 S g ct0 = gamma rcprI0 S (gClean r cls) o1.ct ∧
    OnlyAliceDone ek0 ct0 (runTrace r ss)
  actAlice : ActivePartySt "alice" true S g (gClean r cls)
    [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) (runTrace r ss)
  noBob : NoPartyState "bob" (runTrace r ss)
  ev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes rcprI0 (secretBytes r 0)))
    (gamma rcprI0 S (gClean r cls) o1.ek)
    (gamma rcprI0 S (gClean r cls) o1.ct)
    (gamma rcprI0 S (gClean r cls) (m0Clean cls)))

theorem prefix_inv_2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 2)) :
    ∃ cls : Nat → Nat, PrefixInv2 r S g ss cls := by
  obtain ⟨hCompat, hgwf, hmwf, hm⟩ := hex
  rw [rcprTrace_take_eq_evsRange (by decide)] at hm
  unfold MatchesEvents at hm
  rw [← Nat.zero_add 2] at hm
  obtain ⟨csOrig, hcs_len, hpv0⟩ :=
    peel_evsRange 2 0 (by decide) hmwf.2.2.1 hm (fun _ hw => hw)
  let cls := clsOfCalls csOrig
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv0
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  rcases hcs_eq : csOrig with _ | ⟨c0, _ | ⟨c1, _ | _⟩⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · have hcl0 : cls 0 = stepCoinLen c1.s := by unfold cls clsOfCalls; rw [hcs_eq]; rfl
    rw [hcs_eq] at hpv0
    cases hpv0 with
    | cons hnet0 _ _ hrm0 hsub0 hpv1 =>
      obtain ⟨ek0, ct0, hek0, hct0, hpki1, hnskip1, honly1, hActA1, hnoB1, hids0⟩ :=
        alice_call0_agree cls hfit hCompat hgwf hnet0 hrm0 hsub0
      rw [hids0] at hpv1
      cases hpv1 with
      | @cons _ _ _ _ _ tail hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
        obtain ⟨hpki2, hnskip2, honly2, hActA2, hnoNewB2, hexit1⟩ :=
          party_send_agree cls (otherParty := "bob") (sIdx := 0) (tsPt := 31) (tsCoins := 32)
            (by decide) hgwf hpki1 hnskip1 (fun _ => honly1) hek0 hct0 hActA1
            ⟨ev1_party_cmd.1, _, ev1_party_cmd.2⟩ hcl0
            (gClean_sigma_31 r cls 32) (gClean_sigma_32 r cls)
            (Or.inl ⟨ev1_runWrapped, gClean_addr_m0 r cls⟩)
            hnet1 hpre1 hlok1 hrm1 hsub1
        have hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
            (ecKey (pubBytes rcprI0 (secretBytes r 0)))
            (gamma rcprI0 S (gClean r cls) o1.ek)
            (gamma rcprI0 S (gClean r cls) o1.ct)
            (gamma rcprI0 S (gClean r cls) (m0Clean cls))) := by
          have hw1 : runWrapped (ev (sendCallOf 0)) = true := ev1_runWrapped
          simp only [hw1, ↓reduceIte] at hexit1
          exact hexit1
        have hnoB2 : NoPartyState "bob" _ := noPartyState_of_noNew hnoNewB2 hnoB1
        cases hpv2 with
        | nil hnet_tail =>
          have hrt : runTrace r (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: tail)) =
              runSteps tail (c1.s.next (runSteps c1.pre
                (c0.s.next (runSteps c0.pre (setupTrace r))))) := by
            unfold runTrace; simp only [runSteps_append, runSteps]
          exact ⟨cls,
            { validCls := hvCls
              compatClean := hCompatClean
              pki := hrt ▸ pkiUnchanged_runSteps_network tail hnet_tail hpki2
              noSkip := hrt ▸ noSkippedKeyStored_runSteps_network tail hnet_tail hnskip2
              onlyAlice := ⟨ek0, ct0, hek0, hct0,
                hrt ▸ onlyAliceDone_runSteps_network tail hnet_tail (honly2 ev1_runWrapped)⟩
              actAlice := hrt ▸ noNewPartyState_preserves_active
                (noNewPartyState_runSteps_network tail _ hnet_tail) hActA2
              noBob := hrt ▸ noPartyState_of_noNew
                (noNewPartyState_runSteps_network tail _ hnet_tail) hnoB2
              ev1_out := hev1_out }⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
