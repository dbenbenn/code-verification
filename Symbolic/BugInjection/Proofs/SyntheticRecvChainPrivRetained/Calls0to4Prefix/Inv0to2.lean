/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Inv0to1
import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
import Symbolic.Proofs.Swarm.CREF.TRView
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptExplainPureA
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.HxplRep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation

/-!
# Clean-Run Prefix Inversion for Call 2 (`Calls0to4Prefix/Inv0to2.lean`)

Proves:
1. `consumeMessageKey_zero_inv`: unpacks `consumeMessageKey c counter = some (seed, c')` when
   `c.index = 0` and `counter.toNat = 0`.
2. `bob_call2_agree`: steps Call 2 (`ev 2`, Bob `.recv` `m0` via `bobStart`) on arbitrary network
   prefix `c2.pre`, establishing `PkiUnchanged`, `NoSkippedKeyStored`,
   `ActivePartySt "bob" false ... (stB2Clean cls)`, and `NoNewPartyState "alice"`.
3. `peeled_inv_0to2`: chains Calls 0, 1, 2 on any peeled prefix `c0 :: c1 :: c2 :: cs3` (`k ≥ 3`).
4. `PrefixInv3` / `prefix_inv_3` (`k = 3`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (agree pqxdhIkm pqxdhKdf errToOption)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain createChain setRecvChain kdfCk consumeMessageKey
   maxForwardJumps u32Max messageDecrypt messageDecryptSkipped spqrB2A)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry Move
   gamma clamp ecKey kyberKey pubBytes secretBytes preKeyWire setupTrace runTrace
   setupSecret runSteps stepView bobVis bobOpkPk received receivedPlaintext
   exposures rngEntry randTerm GhostAndSemMatchSetup GhostWF
   RunMatches ReadsFaithfully MatchesEvents Explains runWrapped)
open Symbolic.Swarm.COMPOSED.CompTrace (TRStEntry run_bind_fst)
open Symbolic.Swarm.CREF
  (StOpt BobStartOk rpkT_bobStart_inv rpkR_finalSt rpkR_bobStartTr_last
   rpkBH_trStateStoredAt_bobStartTr rpkT_getMessageSentAt_of_at?
   bobRatchetedSt bobRatchetedChain bobStartPreSkipTr bobStartTr
   bks_stored_of_getLocalState parsePreKeyWire_inner_tryFrom)
open Symbolic.Swarm.CREF.CliPure (newRandoms_bobStartTr receivedPlaintext_bobStartTr)
open Symbolic.Swarm.CREF.TR (gamma_rand gamma_dhPk setupSecret_eq gamma_kemSS_of_not_implicitReject ekBytes)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd bobSt0 ratchetState kemDecap_kemEncap)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession (ikA ikB spkB pqskB dhsA o1)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprSetup rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned rcprPubOfIdx rcprSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
  (encMsg_tryFrom_inv)

private theorem kyberCt0_len : (rcprSetup.kyberCts.headD []).length = 1568 := by
  decide +kernel

attribute [local irreducible] ev

/-! ## 1. `StOpt` & `consumeMessageKey` Counter-Zero Helpers -/

private theorem stOpt_opk_none_of_pkiUnchanged {tr : ExecTrace} {b : Participant}
    {opkIdx : Option Nat} {opk : Option Bytes}
    (hpki : PkiUnchanged tr)
    (hopk : StOpt tr b opkIdx opk) :
    opkIdx = none ∧ opk = none := by
  cases opkIdx with
  | none =>
    cases opk with
    | none => exact ⟨rfl, rfl⟩
    | some _ => cases hopk
  | some idx =>
    cases opk with
    | none => cases hopk
    | some k =>
      exfalso
      rcases pki_pin_st hpki hopk with ⟨_, h1⟩ | ⟨_, h2⟩ | ⟨_, h3⟩ | ⟨_, h4⟩
      · injection h1 with hk _; cases hk
      · injection h2 with hk _; cases hk
      · injection h3 with hk _; cases hk
      · injection h4 with hk _; cases hk

theorem consumeMessageKey_zero_inv {c c' : RecvChain} {counter : UInt32} {seed : Bytes}
    (hidx : c.index = 0) (hcnt : counter.toNat = 0)
    (hcons : consumeMessageKey c counter = some (seed, c')) :
    seed = (kdfCk c.chainKey).2 ∧
    c' = { c with chainKey := (kdfCk c.chainKey).1, index := 1 } := by
  have hcnt0 : counter = 0 :=
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by simpa using hcnt))
  subst hcnt0
  unfold consumeMessageKey at hcons
  rw [hidx] at hcons
  have hlt : ¬ ((0 : UInt32) < 0) := by decide
  have hjmp : ¬ (0 > maxForwardJumps) := by decide
  have hmax : (0 : UInt32) ≠ u32Max := by decide
  have hadd : (0 : UInt32) + 1 = 1 := rfl
  simp only [hlt, hmax, ↓reduceIte, Nat.sub_self, hjmp, hadd,
    DY.Libsignal.TripleRatchet.chainKeyAt, Option.some.injEq, Prod.mk.injEq] at hcons
  exact ⟨hcons.1.symm, hcons.2.symm⟩

/-! ## 2. Call 2 (`ev 2` = Bob `.recv` `m0` via `bobStart`) Step Inversion (`bob_call2_agree`) -/

theorem bob_call2_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {tr : ExecTrace} {c2 : PeeledCall}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hnskip : NoSkippedKeyStored tr)
    (hnoBob : NoPartyState "bob" tr)
    (hev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))))
    (hnet : ∀ x ∈ c2.pre, ∃ msg, x = .network msg)
    (hrm : RunMatches rcprI0 r S g (runSteps c2.pre tr) c2.s (ev 2) c2.v
      (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c2.v, w ∈ visAll) :
    let tr' := c2.s.next (runSteps c2.pre tr)
    PkiUnchanged tr' ∧
    NoSkippedKeyStored tr' ∧
    ActivePartySt "bob" false S g (gClean r cls) [⟨4, by decide⟩] ⟨5, by decide⟩
      (stB2Clean cls) tr' ∧
    NoNewPartyState "alice" tr tr' := by
  have hnames := r_names_of_fit hfit
  have hNe : r.alice ≠ r.bob := by rw [hnames.1, hnames.2]; decide
  set tr₂ := runSteps c2.pre tr
  have hpki₂ : PkiUnchanged tr₂ := pkiUnchanged_runSteps_network c2.pre hnet hpki
  have hnskip₂ : NoSkippedKeyStored tr₂ := noSkippedKeyStored_runSteps_network c2.pre hnet hnskip
  have hnoBob₂ : NoPartyState "bob" tr₂ :=
    noPartyState_of_noNew (noNewPartyState_runSteps_network c2.pre tr hnet) hnoBob
  obtain ⟨_, hparty, hfits, hpeer, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, _, hdr, hout, hrf, _⟩ := hrm
  have hbob : (ev 2).party = "bob" := ev2_party_cmd.1
  have hcmd₂ := ev2_party_cmd.2
  rw [hbob] at hparty
  rw [hcmd₂] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨_, hcmd₂⟩ hout
  cases hs : c2.s with
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    exfalso
    rw [hs] at hparty hok
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decrypt] at hok
    unfold messageDecrypt at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₂ stateIdx st (bks_stored_of_getLocalState hst)
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    rw [hs] at hparty hok
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    rw [step_ok_decryptSkipped] at hok
    unfold messageDecryptSkipped at hok
    rw [run_bind_fst] at hok
    rcases hst : ((DY.PersistentLocalState.getLocalState "bob" stateIdx :
        Traceful TRState).run tr₂).1 with _ | st
    · rw [hst] at hok; cases hok
    · exact hnoBob₂ stateIdx st (bks_stored_of_getLocalState hst)
  | bobStart b a kh regA mh pqIdx spqr =>
    rw [hs] at hparty hpeer hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have ha : a = "alice" := by simpa [Step.MatchesSetupPeer, hnames.1] using hpeer
    subst ha
    have hpki' : PkiUnchanged ((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂) :=
      pkiUnchanged_step_party rfl hpki₂
    have hnoNewA : NoNewPartyState "alice" tr
        ((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂) :=
      noNewPartyState_trans (noNewPartyState_runSteps_network c2.pre tr hnet)
        (noNewPartyState_step_other tr₂ rfl (by simp [Step.party?]))
    have hle_next := step_le_next (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₂
    have hnext_mv := step_next_bobStart "bob" "alice" kh regA mh pqIdx spqr tr₂
    have hview : stepView (.bobStart "bob" "alice" kh regA mh pqIdx spqr) tr₂
        (runWrapped (ev 2)) =
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
        have hw_mem : w_out ∈ c2.v := by rw [hv_split]; simp
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
        bobStartTr tr₂ "bob" "alice" w.out w.msg w.c'
          w.spqr' w.key w.seed w.pqSalt w.m :=
      hnext_mv.trans (w.next_eq 0)
    have hw_ikB : w.ikB = ikB := by
      rcases pki_pin_st hpki₂ w.hik with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with _ hsk
      · injection hk with hkind _; cases hkind
      · injection hk with hkind _; cases hkind
    have hw_spk : w.spk = spkB := by
      rcases pki_pin_st hpki₂ w.hspk with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with hkind _; cases hkind
      · injection hk with _ hsk
      · injection hk with hkind _; cases hkind
    have hw_pq : w.pqsk = pqskB := by
      rcases pki_pin_st hpki₂ w.hpq with ⟨hp, _⟩ | ⟨_, hk⟩ | ⟨_, hk⟩ | ⟨_, hk⟩
      · exact absurd hp (by decide)
      · injection hk with hkind _; cases hkind
      · injection hk with hkind _; cases hkind
      · injection hk with _ hsk
    obtain ⟨_, hw_opk⟩ := stOpt_opk_none_of_pkiUnchanged hpki₂ w.hopk
    have hw_ikA : w.ikAPk = dhPk ikA := by
      rcases pki_pin_reg hpki₂ w.hreg with ⟨_, hikA_eq, _⟩ | ⟨hp, _, _⟩
      · exact hikA_eq
      · exact absurd hp (by decide)
    have hrec_terms : received tr₂ [mh.ek, mh.ct, mh.msg] = [w.ek, w.ct, w.raw] := by
      simp only [received, List.filterMap_cons, List.filterMap_nil,
        rpkT_getMessageSentAt_of_at? w.hek, rpkT_getMessageSentAt_of_at? w.hct,
        rpkT_getMessageSentAt_of_at? w.hmsg]
    have hvis_full : c2.v =
        ⟨.recv, [w.ek, w.ct, w.raw] ++ (bobOpkPk "bob" kh tr₂).toList, .preKeyRecv, none⟩ ::
        rngEntry (randTerm tr₂.length 32) ::
        ⟨.accept, [w.m], .single,
          DY.Libsignal.Composed.Refinement.eventIdx DY.Libsignal.Composed.Refinement.isBobDone tr₂
            (bobStartTr tr₂ "bob" "alice"
              w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m)⟩ ::
        exposures tr₂ (bobStartTr tr₂ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m) := by
      rw [hvis_eq, hview, w.next_eq 0]
      unfold bobVis
      rw [hrec_terms, newRandoms_bobStartTr, receivedPlaintext_bobStartTr]
      rfl
    obtain ⟨hinp_eq, _, hdrs_eq⟩ :=
      split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
    have hrng_mem : rngEntry (randTerm tr₂.length 32) ∈ visAll := by
      apply hsub; rw [hv_split, hdrs_eq]; simp
    rw [hdrs_eq] at hdr
    have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
    have hdhs_idx : rcprSecretIdx
        (clamp (gamma rcprI0 S g (randTerm tr₂.length 32))) = some ⟨5, by decide⟩ := by
      rw [hdhs_bytes]; exact ev2_coins_idx
    have hdhsB_gam : gamma rcprI0 S g (randTerm tr₂.length 32) =
        gamma rcprI0 S (gClean r cls) dhsB1Clean := by
      rw [hdhs_bytes]; unfold dhsB1Clean rnd; rw [gamma_rand]; simp [gClean_sigma_38]
    obtain ⟨p₂, hp₂⟩ := ev2_has_preKey
    have hfull := ev2_full_fields hp₂
    have hev2_in : (ev 2).input = preKeyWire none 7#32 9#32 r.regIdA
        (ecKey (pubBytes rcprI0 (secretBytes r 0)))
        (gamma rcprI0 S (gClean r cls) o1.ek)
        (gamma rcprI0 S (gClean r cls) o1.ct)
        (gamma rcprI0 S (gClean r cls) (m0Clean cls)) := by
      have hcomb := ev1_to_ev2.symm.trans hev1_out
      injection hcomb with hpair
      exact (Prod.mk.inj hpair).2
    obtain ⟨_, hp₂_ct_clean, hp₂_bk_clean, hp₂_msg_clean⟩ :=
      parsePreKeyWire_preKeyWire_inv hev2_in ev2_input_len_lt_2pow63 hp₂
    rw [hinp_eq] at hrf
    dsimp only [ReadsFaithfully, List.cons_append] at hrf
    rcases hrf with ⟨_, _, _, ⟨p₁, hp₁, hbk₁, hct₁, _⟩, p₂', hp₂', hFaith⟩
    cases hp₂.symm.trans hp₁
    cases hp₂.symm.trans hp₂'
    have hek_g_ekb : gamma rcprI0 S g w.ek = ekBytes p₂ := by
      have hdrop := congrArg (List.drop 1) hbk₁
      rw [List.drop_take] at hdrop
      exact hdrop.symm
    have hct_g : gamma rcprI0 S g w.ct = rcprSetup.kyberCts.headD [] := by
      rw [hfull.2.2.2.2.1] at hct₁
      unfold kyberKey at hct₁
      injection hct₁ with hct₁
      injection hct₁ with _ heq
      exact heq.symm
    have hek_clean_val : gamma rcprI0 S (gClean r cls) o1.ek = rcprPubOfIdx ⟨3, by decide⟩ :=
      (List.cons.inj (hp₂_bk_clean.symm.trans hfull.2.2.2.2.2.1)).2
    have hekb_val : ekBytes p₂ = rcprPubOfIdx ⟨3, by decide⟩ := by
      unfold ekBytes
      rw [hfull.2.2.2.2.2.1]
      dsimp only [ecKey, List.drop]
      exact List.take_of_length_le (by decide)
    have hek_gam : gamma rcprI0 S g w.ek = gamma rcprI0 S (gClean r cls) o1.ek :=
      (hek_g_ekb.trans hekb_val).trans hek_clean_val.symm
    have hct_clean_val : gamma rcprI0 S (gClean r cls) o1.ct = rcprSetup.kyberCts.headD [] := by
      have h := hp₂_ct_clean.symm.trans hfull.2.2.2.2.1
      injection h with hkk
      exact (List.cons.inj hkk).2
    have hnk₂ := not_kyberMismatch_ev2 hfit hp₂
    have hs4_eq : setupSecret r 4 = pqskB := (setupSecret_eq r hNe).2.2.2.1
    have hagree_w := w.hagree
    rw [hw_ikB, hw_spk, hw_pq, hw_opk, hw_ikA] at hagree_w
    obtain ⟨ss_w, hdec_w, hss_w_gam⟩ :=
      gamma_kemSS_of_not_implicitReject rcprI0 r S g p₂ ⟨w.ek, w.ct, w.raw⟩
        (rcprSetup.kyberCts.headD []) hCompat hNe hnk₂ hfull.2.2.2.2.1 kyberCt0_len hct_g
    rw [hs4_eq] at hdec_w
    have hkeys_w : w.keys = pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB)
        (agree w.ek ikB) (agree w.ek spkB) none ss_w) := by
      unfold DY.Libsignal.PQXDH.bobAgreement at hagree_w
      dsimp only [Pure.pure] at hagree_w
      rw [hdec_w] at hagree_w
      injection hagree_w with hk_eq
      exact hk_eq.symm
    have hdec_clean : (errToOption (DY.PQKem.kemDecap (setupSecret r 4) o1.ct)).getD
        (DY.PQKem.kemRejKey (setupSecret r 4) o1.ct) =
        (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 := by
      rw [hs4_eq, o1_ct_eq, kemDecap_kemEncap pqskB (rnd 23 32)]
      rfl
    obtain ⟨ss_c, hdec_c, hss_c_gam⟩ :=
      gamma_kemSS_of_not_implicitReject rcprI0 r S (gClean r cls) p₂
        ⟨o1.ek, o1.ct, m0Clean cls⟩ (rcprSetup.kyberCts.headD [])
        (ghostAndSemMatchSetup_gClean cls hfit hCompat) hNe hnk₂
        hfull.2.2.2.2.1 kyberCt0_len hct_clean_val
    have hss_c_eq : ss_c = (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 :=
      hdec_c.symm.trans hdec_clean
    subst hss_c_eq
    have hss_gam : gamma rcprI0 S g ss_w =
        gamma rcprI0 S (gClean r cls) (DY.PQKem.kemEncap (DY.PQKem.kemPk pqskB) (rnd 23 32)).2 :=
      hss_w_gam.trans hss_c_gam.symm
    rcases hFaith with ⟨msg_f, hparse_f, _, _, _, _, hrk_w_p, hpq_w_p, hctr_w_p, _⟩
    rw [w.hparse] at hparse_f
    injection hparse_f with hmsg_eq; subst hmsg_eq
    have hcnt0 : w.msg.counter.toNat = 0 :=
      hctr_w_p.trans hfull.2.2.2.2.2.2.2.2.1
    have hnskip' : NoSkippedKeyStored
        ((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂) := by
      rw [htr']; exact noSkippedKeyStored_bobStartTr hnskip₂ hcnt0
    obtain ⟨_, hc'_eq⟩ := consumeMessageKey_zero_inv rfl hcnt0 w.hcons
    have hc'Rk : w.c'.ratchetKey = w.msg.ratchetKey := by
      rw [hc'_eq]; rfl
    have hc'Ck : w.c'.chainKey =
        (kdfCk (createChain (pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB)
          (agree w.ek ikB) (agree w.ek spkB) none ss_w)).rk
          w.msg.ratchetKey spkB).2).1 := by
      rw [hc'_eq]; dsimp only [bobRatchetedChain]; rw [hw_spk, hkeys_w]
    have hrk4 : gamma rcprI0 S g w.msg.ratchetKey = rcprPubOfIdx ⟨4, by decide⟩ :=
      hrk_w_p.trans hfull.2.2.2.2.2.2.2.1
    have hrk_dhsA_len : (gamma rcprI0 S (gClean r cls) (dhPk dhsA)).length = 32 := by
      rw [gamma_dhPk_dhsA hfit]; decide
    have htry_p₂ := parsePreKeyWire_inner_tryFrom hp₂
    obtain ⟨_, _, _, hrk_c_p, hpq_c_p, _, _⟩ :=
      encMsg_tryFrom_inv hp₂_msg_clean.symm hrk_dhsA_len htry_p₂
    have hrkMsg_gam : gamma rcprI0 S g w.msg.ratchetKey =
        gamma rcprI0 S (gClean r cls) (dhPk dhsA) :=
      hrk_w_p.trans hrk_c_p.symm
    have hpqMsg_gam : gamma rcprI0 S g w.msg.pqRatchet =
        gamma rcprI0 S (gClean r cls) (pqm0Clean cls) :=
      hpq_w_p.trans hpq_c_p.symm
    have hikB_gam : gamma rcprI0 S g ikB = gamma rcprI0 S (gClean r cls) ikB :=
      gamma_setup_rnd_eq cls hfit hCompat (ts := 5) (n := 32) (by decide) (by decide)
    have hspkB_gam : gamma rcprI0 S g spkB = gamma rcprI0 S (gClean r cls) spkB :=
      gamma_setup_rnd_eq cls hfit hCompat (ts := 10) (n := 32) (by decide) (by decide)
    have hikA_gam : gamma rcprI0 S g (dhPk ikA) =
        gamma rcprI0 S (gClean r cls) (dhPk ikA) := by
      rw [gamma_dhPk, gamma_dhPk,
          gamma_setup_rnd_eq cls hfit hCompat (ts := 0) (n := 32) (by decide) (by decide)]
    have hspqr_w := w.hspqr
    rw [hw_ikB, hw_spk, hw_ikA, hkeys_w] at hspqr_w
    have hst_agree := stateBytesAgree_bobStart (cls := cls) (c' := w.c')
      hikB_gam hspkB_gam hikA_gam hek_gam hss_gam hrkMsg_gam hdhsB_gam hpqMsg_gam
      hc'Rk hc'Ck hspqr_w
    have hfinal_eq : rpkR_finalSt w =
        (let keys_b := pqxdhKdf (pqxdhIkm (agree (dhPk ikA) spkB)
           (agree w.ek ikB) (agree w.ek spkB) none ss_w)
         let (stB_r, _) := ratchetState (bobSt0 "alice" ikB spkB (dhPk ikA) keys_b w.msg)
           w.msg.ratchetKey (randTerm tr₂.length 32)
         { stB_r with recv := setRecvChain stB_r.recv w.c', spqr := w.spqr' }) := by
      unfold rpkR_finalSt BobStartOk.out Symbolic.Swarm.CREF.bobOut
        bobRatchetedSt ratchetState bobSt0
      rw [hw_ikB, hw_spk, hw_ikA, hkeys_w]
      rfl
    have hst_agree' : StateBytesAgree S g (gClean r cls) (rpkR_finalSt w) (stB2Clean cls) := by
      rw [hfinal_eq]; exact hst_agree
    obtain ⟨tr_pre_last, hlast⟩ := rpkR_bobStartTr_last w
    have hat_final : (((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂).at?
        tr_pre_last.length : Option TRStEntry) = some ⟨⟨"bob", rpkR_finalSt w⟩⟩ := by
      rw [htr', hlast, Symbolic.Swarm.CREF.at?_append_length]; rfl
    have hchild_eq : tr_pre_last.length =
        (bobStartPreSkipTr tr₂ "bob" "alice" w.out w.msg w.key).length +
          (w.msg.counter.toNat -
            (bobRatchetedChain w.out.keys w.msg.ratchetKey w.out.spkSk).index.toNat) + 2 := by
      have hat_raw : ((bobStartTr tr₂ "bob" "alice"
          w.out w.msg w.c' w.spqr' w.key w.seed w.pqSalt w.m).at? tr_pre_last.length :
          Option TRStEntry) = some ⟨⟨"bob", rpkR_finalSt w⟩⟩ := by
        rw [hlast, Symbolic.Swarm.CREF.at?_append_length]; rfl
      rcases rpkBH_trStateStoredAt_bobStartTr w hat_raw with ⟨_, h0⟩ | ⟨heq, _, _⟩
      · exact False.elim (hnoBob₂ _ _ h0)
      · exact heq
    have huniq_all : ∀ j st, tr₂.length ≤ j →
        (((Step.bobStart "bob" "alice" kh regA mh pqIdx spqr).next tr₂).at? j :
          Option TRStEntry) = some ⟨⟨"bob", st⟩⟩ →
        j = tr_pre_last.length ∧ st = rpkR_finalSt w := by
      intro j st _ hat
      rw [htr'] at hat
      rcases rpkBH_trStateStoredAt_bobStartTr w hat with ⟨_, h0⟩ | ⟨hj, _, hst_eq⟩
      · exact False.elim (hnoBob₂ _ _ h0)
      · exact ⟨hj.trans hchild_eq.symm, hst_eq⟩
    have hrecv_map : (rpkR_finalSt w).recv.map (fun c => gamma rcprI0 S g c.ratchetKey) =
        [rcprPubOfIdx ⟨4, by decide⟩] := by
      unfold rpkR_finalSt
      dsimp only
      have hmap0 := congrArg (List.map (gamma rcprI0 S g))
        (setRecvChain_map_ratchetKey
          (bobRatchetedSt "alice" w.out.ikB w.out.ikA w.out.keys w.out.spkSk
            w.msg.ratchetKey (randTerm tr₂.length 32)).recv w.c')
      rw [List.map_map, List.map_map] at hmap0
      refine hmap0.trans ?_
      unfold bobRatchetedSt bobRatchetedChain
      dsimp only [List.map]
      exact congrArg (· :: []) hrk4
    exact ⟨hpki', hnskip',
      activePartySt_init hnoBob₂ hle_next hat_final huniq_all rfl hst_agree' hrecv_map hdhs_idx,
      hnoNewA⟩
  | _ => rw [hs] at hfits; cases hfits

/-! ## 3. Peeled Prefix Chaining (`peeled_inv_0to2`) & `PrefixInv3` / `prefix_inv_3` -/

theorem peeled_inv_0to2 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {c0 c1 c2 : PeeledCall} {cs3 : List PeeledCall} {rest2 : List Step}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hgwf : GhostWF g visAll)
    (hcl0 : cls 0 = stepCoinLen c1.s)
    (hpv : PeeledValid r S g visAll 0 none (setupTrace r) (c0 :: c1 :: c2 :: cs3)
      (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: rest2)))) :
    let tr₀ := c0.s.next (runSteps c0.pre (setupTrace r))
    let tr₁ := c1.s.next (runSteps c1.pre tr₀)
    let tr₂ := c2.s.next (runSteps c2.pre tr₁)
    ∃ ek0 ct0 : Bytes,
      gamma rcprI0 S g ek0 = gamma rcprI0 S (gClean r cls) o1.ek ∧
      gamma rcprI0 S g ct0 = gamma rcprI0 S (gClean r cls) o1.ct ∧
      PkiUnchanged tr₂ ∧
      NoSkippedKeyStored tr₂ ∧
      ActivePartySt "alice" true S g (gClean r cls) [⟨2, by decide⟩] ⟨4, by decide⟩
        (stA1Clean cls) tr₂ ∧
      ActivePartySt "bob" false S g (gClean r cls) [⟨4, by decide⟩] ⟨5, by decide⟩
        (stB2Clean cls) tr₂ ∧
      (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
        (ecKey (pubBytes rcprI0 (secretBytes r 0)))
        (gamma rcprI0 S (gClean r cls) o1.ek)
        (gamma rcprI0 S (gClean r cls) o1.ct)
        (gamma rcprI0 S (gClean r cls) (m0Clean cls))) ∧
      PeeledValid r S g visAll 3 (some (none, 7#32, 9#32)) tr₂ cs3 rest2 := by
  generalize hss0 : (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: rest2))) = ss0 at hpv
  cases hpv with
  | @cons _ _ _ _ _ rest0 hnet0 _ _ hrm0 hsub0 hpv1 =>
    have hrest0 : c1.pre ++ c1.s :: (c2.pre ++ c2.s :: rest2) = rest0 :=
      (List.cons.inj (List.append_cancel_left hss0)).2
    subst hrest0
    obtain ⟨ek0, ct0, hek0, hct0, hpki0, hnskip0, honly0, hActA0, hnoB0, hids0⟩ :=
      alice_call0_agree cls hfit hCompat hgwf hnet0 hrm0 hsub0
    rw [hids0] at hpv1
    generalize hss1 : (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: rest2)) = ss1 at hpv1
    cases hpv1 with
    | @cons _ _ _ _ _ rest1 hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
      have hrest1 : c2.pre ++ c2.s :: rest2 = rest1 :=
        (List.cons.inj (List.append_cancel_left hss1)).2
      subst hrest1
      obtain ⟨hpki1, hnskip1, _, hActA1, hnoNewB1, hexit1⟩ :=
        party_send_agree cls (otherParty := "bob") (sIdx := 0) (tsPt := 31) (tsCoins := 32)
          (by decide) hgwf hpki0 hnskip0 (fun _ => honly0) hek0 hct0 hActA0
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
      have hnoB1 : NoPartyState "bob" _ := noPartyState_of_noNew hnoNewB1 hnoB0
      rw [nextBundleIds_non_init (by decide) (by decide)] at hpv2
      generalize hss2 : (c2.pre ++ c2.s :: rest2) = ss2 at hpv2
      cases hpv2 with
      | @cons _ _ _ _ _ rest2' hnet2 _ _ hrm2 hsub2 hpv3 =>
        have hrest2 : rest2 = rest2' :=
          (List.cons.inj (List.append_cancel_left hss2)).2
        subst hrest2
        obtain ⟨hpki2, hnskip2, hActB2, hnoNewA2⟩ :=
          bob_call2_agree cls hfit hCompat hgwf hpki1 hnskip1 hnoB1 hev1_out hnet2 hrm2 hsub2
        rw [nextBundleIds_non_init (by decide) (by decide)] at hpv3
        exact ⟨ek0, ct0, hek0, hct0, hpki2, hnskip2,
          noNewPartyState_preserves_active hnoNewA2 hActA1,
          hActB2, hev1_out, hpv3⟩

structure PrefixInv3 (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ss : List Step) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)
  pki : PkiUnchanged (runTrace r ss)
  noSkip : NoSkippedKeyStored (runTrace r ss)
  actAlice : ActivePartySt "alice" true S g (gClean r cls)
    [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) (runTrace r ss)
  actBob : ActivePartySt "bob" false S g (gClean r cls)
    [⟨4, by decide⟩] ⟨5, by decide⟩ (stB2Clean cls) (runTrace r ss)
  ev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes rcprI0 (secretBytes r 0)))
    (gamma rcprI0 S (gClean r cls) o1.ek)
    (gamma rcprI0 S (gClean r cls) o1.ct)
    (gamma rcprI0 S (gClean r cls) (m0Clean cls)))

theorem prefix_inv_3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 3)) :
    ∃ cls : Nat → Nat, PrefixInv3 r S g ss cls := by
  obtain ⟨hCompat, hgwf, hmwf, hm⟩ := hex
  rw [rcprTrace_take_eq_evsRange (by decide)] at hm
  unfold MatchesEvents at hm
  rw [← Nat.zero_add 3] at hm
  obtain ⟨csOrig, hcs_len, hpv0⟩ :=
    peel_evsRange 3 0 (by decide) hmwf.2.2.1 hm (fun _ hw => hw)
  let cls := clsOfCalls csOrig
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv0
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  rcases hcs_eq : csOrig with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | _⟩⟩⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · rw [hcs_eq] at hcs_len; simp at hcs_len
  · have hcl0 : cls 0 = stepCoinLen c1.s := by unfold cls clsOfCalls; rw [hcs_eq]; rfl
    rw [hcs_eq] at hpv0
    cases hpv0 with
    | @cons _ _ _ _ _ rest0 hnet0 hpre0 hlok0 hrm0 hsub0 hpv1 =>
      cases hpv1 with
      | @cons _ _ _ _ _ rest1 hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
        cases hpv2 with
        | @cons _ _ _ _ _ tail hnet2 hpre2 hlok2 hrm2 hsub2 hpv3 =>
          have hpv0' : PeeledValid r S g vis 0 none (setupTrace r) [c0, c1, c2]
              (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: tail))) :=
            .cons hnet0 hpre0 hlok0 hrm0 hsub0
              (.cons hnet1 hpre1 hlok1 hrm1 hsub1
                (.cons hnet2 hpre2 hlok2 hrm2 hsub2 hpv3))
          obtain ⟨_, _, _, _, hpki2, hnskip2, hActA2, hActB2, hev1_out, hpv3'⟩ :=
            peeled_inv_0to2 cls hfit hCompat hgwf hcl0 hpv0'
          cases hpv3' with
          | nil hnet_tail =>
            have hrt : runTrace r (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: tail))) =
                runSteps tail (c2.s.next (runSteps c2.pre (c1.s.next (runSteps c1.pre
                  (c0.s.next (runSteps c0.pre (setupTrace r))))))) := by
              unfold runTrace; simp only [runSteps_append, runSteps]
            exact ⟨cls,
              { validCls := hvCls
                compatClean := hCompatClean
                pki := hrt ▸ pkiUnchanged_runSteps_network tail hnet_tail hpki2
                noSkip := hrt ▸ noSkippedKeyStored_runSteps_network tail hnet_tail hnskip2
                actAlice := hrt ▸ noNewPartyState_preserves_active
                  (noNewPartyState_runSteps_network tail _ hnet_tail) hActA2
                actBob := hrt ▸ noNewPartyState_preserves_active
                  (noNewPartyState_runSteps_network tail _ hnet_tail) hActB2
                ev1_out := hev1_out }⟩
  · rw [hcs_eq] at hcs_len; simp at hcs_len

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
