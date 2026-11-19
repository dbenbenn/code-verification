/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Inv0to2
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation

/-!
# Prefix Step Inversion for Calls 3 & 4 (`Calls0to4Prefix/Inv3to4.lean`)

Chains `Inv0to2.peeled_inv_0to2` and `Inv0to2.party_send_agree` across Call 3 (`ev 3`, Bob
Whisper `.send` `m1`) and proves `alice_call4_agree` across Call 4 (`ev 4`, Alice Whisper
`.recv` `m1`), establishing `PrefixInv4` (`k = 4`) and `PrefixInv5` (`k = 5`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained

open scoped DY.Libsignal.Composed
open DY (Bytes Participant ExecTrace Traceful)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet
  (TRState TREvent RecvChain findRecvChain setRecvChain consumeMessageKey kdfCk
   maxReceiverChains isCurrentSnapshot receiveSignalMsg
   messageDecrypt messageDecryptSkipped)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry
   gamma clamp ecKey pubBytes secretBytes preKeyWire nextBundleIds
   setupTrace runTrace runSteps stepView bobVis decVis bobOpkPk received
   exposures rngEntry randTerm runWrapped GhostWF GhostAndSemMatchSetup
   RunMatches ReadsFaithfully PreKeyRecvMatches PreKeyRecvOpkMatches Explains)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry TREvE run_bind_fst)
open Symbolic.Swarm.CREF
  (rpkT_getMessageSentAt_of_at? rpkT_receiveSignalMsg_some)
open Symbolic.Swarm.CREF.TR (gamma_rand)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd at?_append_of_lt at?_eq_none_of_le at?_append_non_entry
   at?_stEntry_logSkippedKeysTr trDhRatchetState decRatchetPreTr decRatchetPreTr_length
   decTailTr decrypt_next_ratchet_eq newRandoms_decRatchet
   receivedPlaintext_decTailTr receivedPlaintext_decRatchetPreTr)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg ratchetState recvSt recvKey)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (spkB o1 stA0)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprTrace rcprI0 rcprHooks0 rcprCompFitsPinned rcprPubOfIdx rcprSecretIdx)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.Rep
  (encMsg_tryFrom_inv)

attribute [local irreducible] ev

/-! ## 1. `consumeMessageKey` Pinning at `(index = 0, counter = 0)` -/

private theorem consumeMessageKey_zero_of_index_zero {c c' : RecvChain} {cnt : UInt32}
    {seed : Bytes} (hc0 : c.index = 0) (hcnt0 : cnt.toNat = 0)
    (hcons : consumeMessageKey c cnt = some (seed, c')) :
    c' = { c with chainKey := (kdfCk c.chainKey).1, index := 1 } ∧
    cnt.toNat - c.index.toNat = 0 := by
  have hsub : cnt.toNat - c.index.toNat = 0 := by rw [hcnt0, hc0]; rfl
  have hcnt_eq : cnt = 0 := by
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    exact hcnt0
  unfold consumeMessageKey at hcons
  split at hcons
  · cases hcons
  · split at hcons
    · cases hcons
    · split at hcons
      · cases hcons
      · dsimp only at hcons
        rw [hsub, hcnt_eq, DY.Libsignal.TripleRatchet.chainKeyAt] at hcons
        exact ⟨(Prod.mk.inj (Option.some.inj hcons)).2.symm, hsub⟩

/-! ## 2. Call 4 (`ev 4` = Alice Whisper `.recv` `m1`) Step Inversion -/

theorem alice_call4_agree {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat) {tr : ExecTrace} {c4 : PeeledCall}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hgwf : GhostWF g visAll)
    (hpki : PkiUnchanged tr)
    (hnskip : NoSkippedKeyStored tr)
    (hActA : ActivePartySt "alice" true S g (gClean r cls)
      [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) tr)
    (hev3_out : (ev 3).exit =
      some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls)))
    (hnet : ∀ x ∈ c4.pre, ∃ msg, x = .network msg)
    (hpre : c4.s.PreCond (runSteps c4.pre tr))
    (hrm : RunMatches rcprI0 r S g (runSteps c4.pre tr) c4.s (ev 4) c4.v
      (some (none, 7#32, 9#32)))
    (hsub : ∀ w ∈ c4.v, w ∈ visAll) :
    let tr' := c4.s.next (runSteps c4.pre tr)
    PkiUnchanged tr' ∧
    NoSkippedKeyStored tr' ∧
    ActivePartySt "alice" true S g (gClean r cls)
      [⟨2, by decide⟩, ⟨5, by decide⟩] ⟨6, by decide⟩ (stA4Clean cls) tr' ∧
    NoNewPartyState "bob" tr tr' := by
  set tr₁ := runSteps c4.pre tr
  have hpki₁ : PkiUnchanged tr₁ := pkiUnchanged_runSteps_network c4.pre hnet hpki
  have hnskip₁ : NoSkippedKeyStored tr₁ := noSkippedKeyStored_runSteps_network c4.pre hnet hnskip
  have hAct₁ : ActivePartySt "alice" true S g (gClean r cls)
      [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) tr₁ :=
    noNewPartyState_preserves_active (noNewPartyState_runSteps_network c4.pre tr hnet) hActA
  obtain ⟨_, hparty, hfits, _, hok, hexit, hvis_eq,
    inp, drs, outs, hv_split, hbm_in, hdr, hout, hrf, _⟩ := hrm
  obtain ⟨hparty4, hcmd4⟩ := ev4_party_cmd
  obtain ⟨hwrap, hnpk, body, m_wire, hin_eq, htry, hm_rk, hm_cnt⟩ := ev4_whisper
  rw [hparty4] at hparty
  rw [hcmd4] at hfits
  obtain ⟨w_out, rfl, hw_accept⟩ := recv_outputs_accept hexit ⟨_, hcmd4⟩ hout
  have hnotMem : (⟨5, by decide⟩ : Fin 7) ∉ ([⟨2, by decide⟩] : List (Fin 7)) := by decide
  cases hs : c4.s with
  | bobStart b a kh regA mh pqIdx spqr =>
    exfalso
    rw [hs] at hok hvis_eq
    have hinp : inp = ⟨.recv, received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList,
        .preKeyRecv, none⟩ := by
      have hv0 := hv_split.symm.trans hvis_eq
      unfold stepView bobVis at hv0
      simp only [hok, ↓reduceIte, List.cons_append] at hv0
      injection hv0
    rw [hinp] at hbm_in
    have hpk_opk : PreKeyRecvOpkMatches rcprI0 r S g (ev 4).input
        (received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList) := hbm_in.2
    have hpk_rec : ∃ x y z, PreKeyRecvMatches rcprI0 r S g (ev 4).input [x, y, z] := by
      unfold PreKeyRecvOpkMatches at hpk_opk
      rcases hts : received tr₁ [mh.ek, mh.ct, mh.msg] ++ (bobOpkPk b kh tr₁).toList with
        _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _ | _⟩⟩⟩⟩ <;> rw [hts] at hpk_opk
      · exact False.elim hpk_opk
      · exact False.elim hpk_opk
      · exact False.elim hpk_opk
      · exact ⟨x, y, z, hpk_opk.1⟩
      · exact ⟨x, y, z, hpk_opk.1⟩
      · exact False.elim hpk_opk
    obtain ⟨_, _, _, p, hp, _⟩ := hpk_rec
    rw [hnpk] at hp; cases hp
  | messageDecryptSkipped me stateIdx msgIdx sk pq spqr =>
    exfalso
    rw [hs] at hparty hpre hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst me
    have hcur := preCond_messageDecryptSkipped hpre
    have hok_copy := hok
    rw [step_ok_decryptSkipped] at hok_copy
    unfold messageDecryptSkipped at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · simp [hst] at hok_copy
    · rw [hst, getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · simp [hmsg_run] at hok_copy
      · obtain ⟨_, _, hrecv_map, _⟩ := activePartySt_pin_state hAct₁ hst hcur
        obtain ⟨t, hat, hparse, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t], .whisper, none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true,
            rpkT_getMessageSentAt_of_at? hat, Option.map_some, Option.toList_some,
            List.cons_append] at hv0
          injection hv0
        rw [hinp, hin_eq] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have hrk_eq := ((hrf.2.2.2 msg hparse).2.2.2 m_wire htry).2.1.trans hm_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk_eq hnotMem
        rw [not_decryptSkipped_of_find_none hst hmsg_run hfind] at hok
        cases hok
  | messageDecrypt me stateIdx msgIdx pq spqr =>
    rw [hs] at hparty hpre hok hvis_eq
    simp only [Step.party?, Option.some.injEq] at hparty; subst me
    have hpki' : PkiUnchanged ((Step.messageDecrypt "alice" stateIdx msgIdx pq spqr).next tr₁) :=
      pkiUnchanged_step_party rfl hpki₁
    have hnoNewBob : NoNewPartyState "bob" tr
        ((Step.messageDecrypt "alice" stateIdx msgIdx pq spqr).next tr₁) :=
      noNewPartyState_trans (noNewPartyState_runSteps_network c4.pre tr hnet)
        (noNewPartyState_step_other tr₁ rfl (by simp [Step.party?]))
    have hcur := preCond_messageDecrypt hpre
    have hle_next := step_le_next (.messageDecrypt "alice" stateIdx msgIdx pq spqr) tr₁
    have hok_copy := hok
    rw [step_ok_decrypt] at hok_copy
    unfold messageDecrypt at hok_copy
    rw [run_bind_fst] at hok_copy
    rcases hst : ((DY.PersistentLocalState.getLocalState "alice" stateIdx :
        Traceful TRState).run tr₁).1 with _ | st
    · simp [hst] at hok_copy
    · rw [hst, getLocalState_snd] at hok_copy; dsimp only at hok_copy
      rw [run_bind_fst] at hok_copy
      rcases hmsg_run : ((receiveSignalMsg msgIdx).run tr₁).1 with _ | msg
      · simp [hmsg_run] at hok_copy
      · obtain ⟨hinit, hagree_st, hrecv_map, _⟩ := activePartySt_pin_state hAct₁ hst hcur
        obtain ⟨t₀, hat₀, hparse₀, _⟩ := rpkT_receiveSignalMsg_some hmsg_run
        have hinp : inp = ⟨.recv, [t₀], .whisper, none⟩ := by
          have hv0 := hv_split.symm.trans hvis_eq
          unfold stepView decVis at hv0
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true,
            rpkT_getMessageSentAt_of_at? hat₀, Option.map_some, Option.toList_some,
            List.cons_append] at hv0
          injection hv0
        rw [hinp, hin_eq] at hrf
        dsimp only [ReadsFaithfully] at hrf
        have hrf_fields := (hrf.2.2.2 msg hparse₀).2.2.2 m_wire htry
        have hrk_eq : gamma rcprI0 S g msg.ratchetKey = rcprPubOfIdx ⟨5, by decide⟩ :=
          hrf_fields.2.1.trans hm_rk
        have hfind := findRecvChain_none_of_not_mem hrecv_map hrk_eq hnotMem
        obtain ⟨w, hw_msg⟩ := decrypt_ratchet_inv hok hst hmsg_run hfind
        have hrk_w : gamma rcprI0 S g w.msg.ratchetKey = rcprPubOfIdx ⟨5, by decide⟩ := by
          rw [hw_msg]; exact hrk_eq
        have hrk_w_wire : gamma rcprI0 S g w.msg.ratchetKey =
            m_wire.senderRatchetKey.bytes.toList := by
          rw [hw_msg]; exact hrf_fields.2.1
        have hpq_w_wire : gamma rcprI0 S g w.msg.pqRatchet = m_wire.pqRatchet := by
          rw [hw_msg]; exact hrf_fields.2.2.1
        have hcnt_w : w.msg.counter.toNat = 0 := by
          rw [hw_msg]; exact hrf_fields.2.2.2.1.trans hm_cnt
        have hfind_w : findRecvChain st.recv w.msg.ratchetKey = none := by
          rw [hw_msg]; exact hfind
        let st1 := (trDhRatchetState st w.msg.ratchetKey tr₁.length).1
        let cChain := (trDhRatchetState st w.msg.ratchetKey tr₁.length).2
        let tr_pre := decRatchetPreTr tr₁ "alice" st1 w.msg.ratchetKey w.key
        have htr' : (Step.messageDecrypt "alice" stateIdx msgIdx pq spqr).next tr₁ =
            decTailTr tr_pre "alice" stateIdx st1 cChain w.c' w.msg.ratchetKey w.seed
              w.pqSalt w.ptTerm w.spqr' w.msg.counter :=
          (step_next_decrypt "alice" stateIdx msgIdx pq spqr tr₁).trans
            (decrypt_next_ratchet_eq hst w.hmsg w.hparse w.hver hfind_w w.hlow
              w.hcons w.hspqr w.hpqSalt w.hmac_eq w.hdec)
        obtain ⟨hwc', hskip0⟩ := consumeMessageKey_zero_of_index_zero rfl hcnt_w w.hcons
        have hnskip' : NoSkippedKeyStored
            ((Step.messageDecrypt "alice" stateIdx msgIdx pq spqr).next tr₁) := by
          rw [htr']
          exact noSkippedKeyStored_decRatchet hnskip₁ hskip0
        have hvis_full : c4.v =
            ⟨.recv, [w.t], .whisper, none⟩ ::
            rngEntry (randTerm tr₁.length 32) ::
            ⟨.accept, [w.ptTerm], .single, none⟩ ::
            exposures tr₁ (decTailTr tr_pre "alice" stateIdx st1 cChain w.c' w.msg.ratchetKey
              w.seed w.pqSalt w.ptTerm w.spqr' w.msg.counter) := by
          rw [hvis_eq]
          unfold stepView decVis
          simp only [hok, ↓reduceIte, hwrap, Bool.false_eq_true, w.hmsg, htr']
          dsimp only [tr_pre]
          rw [newRandoms_decRatchet,
            receivedPlaintext_decTailTr
              (by rw [decRatchetPreTr_length]; omega)
              (receivedPlaintext_decRatchetPreTr ..)]
          rfl
        obtain ⟨_, _, hdrs_eq⟩ :=
          split_vis_recv_rng (hv_split.symm.trans hvis_full) hw_accept
        have hrng_mem : rngEntry (randTerm tr₁.length 32) ∈ visAll := by
          apply hsub; rw [hv_split, hdrs_eq]; simp
        rw [hdrs_eq] at hdr
        have hdhs_bytes := drawsMatch_single_pin hgwf hrng_mem hdr
        have hdhs_idx : rcprSecretIdx (clamp (gamma rcprI0 S g st1.dhs)) =
            some ⟨6, by decide⟩ := by
          change rcprSecretIdx (clamp (gamma rcprI0 S g (randTerm tr₁.length 32))) =
            some ⟨6, by decide⟩
          rw [hdhs_bytes]; exact ev4_coins_idx
        have hdhsNew_gam : gamma rcprI0 S g (randTerm tr₁.length 32) =
            gamma rcprI0 S (gClean r cls) dhsA1Clean := by
          rw [hdhs_bytes]; show _ = gamma rcprI0 S (gClean r cls) (rnd 54 32)
          unfold rnd; rw [gamma_rand]; simp [gClean_sigma_54]
        have hsent_wire : (ev 4).input =
            wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls) :=
          (Prod.mk.inj (Option.some.inj (ev3_to_ev4.symm.trans hev3_out))).2
        have hb_clean : gamma rcprI0 S (gClean r cls)
            (encMsg (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean) = body :=
          (List.cons.inj (hsent_wire.symm.trans hin_eq)).2
        have hrk_len_clean :
            (gamma rcprI0 S (gClean r cls) (dhPk (stB2Clean cls).dhs)).length = 32 := by
          have hdhs_b : (stB2Clean cls).dhs = dhsB1Clean := rfl
          rw [hdhs_b, gamma_dhPk_dhsB1 hfit]; decide
        obtain ⟨_, _, _, hrk_clean_wire, hpq_clean_wire, _, _⟩ :=
          encMsg_tryFrom_inv hb_clean hrk_len_clean htry
        have hrkMsg_gam : gamma rcprI0 S g w.msg.ratchetKey =
            gamma rcprI0 S (gClean r cls) (dhPk dhsB1Clean) :=
          hrk_w_wire.trans hrk_clean_wire.symm
        have hpqMsg_gam : gamma rcprI0 S g w.msg.pqRatchet =
            gamma rcprI0 S (gClean r cls) (pqm1Clean cls) :=
          hpq_w_wire.trans hpq_clean_wire.symm
        have hc0_ex : ∃ c0, st.recv = [c0] := by
          have hlen := congrArg List.length hrecv_map
          rcases hsr : st.recv with _ | ⟨c0, _ | _⟩
          · rw [hsr] at hlen; simp at hlen
          · exact ⟨c0, rfl⟩
          · rw [hsr] at hlen; simp at hlen
        obtain ⟨c0, hrecv1⟩ := hc0_ex
        have hne1 : c0.ratchetKey ≠ w.msg.ratchetKey := by
          intro heq
          simp [findRecvChain, hrecv1, heq] at hfind_w
        have hne_spk : dhPk spkB ≠ dhPk dhsB1Clean := fun heq =>
          absurd (dhPk_rnd_inj heq) (by decide)
        have hne2 : cA0Clean.ratchetKey ≠ dhPk dhsB1Clean := hne_spk
        have hspqr_clean : DY.Spqr.spqrRecv (stA1Clean cls).spqr (pqm1Clean cls) 1 =
            some (recvSt (stA1Clean cls).spqr (pqm1Clean cls),
                  recvKey (stA1Clean cls).spqr (pqm1Clean cls)) := by
          unfold DY.Spqr.spqrRecv DY.Spqr.spqrEmptyMsg pqm1Clean
          rw [bytesToLiteral_spqrSendMsg]
          dsimp only [stA1Clean, encSt]
          rw [spqrSend_st_not_init]; rfl
        have hsetA4 : setRecvChain (stA3'Clean cls).recv cA1Clean = [cA0Clean, cA1Clean] := by
          have ho1 : o1.spk = dhPk spkB := rfl
          simp [setRecvChain, stA3'Clean, ratchetState, cA1Clean, cA1RawClean, stA1Clean, encSt,
            stA0, Symbolic.Proofs.Tests.Shared.Composed.Runs.aliceSt, cA0Clean, ho1, hne_spk,
            maxReceiverChains]
        have hst_agree0 := stateBytesAgree_decrypt_ratchet
          (c0 := c0) (c0' := cA0Clean) (c' := w.c') (c'' := cA1Clean)
          (dhsNew := randTerm tr₁.length 32) (dhsNew' := dhsA1Clean)
          hagree_st hrecv1 rfl hne1 hne2 hrkMsg_gam hdhsNew_gam hpqMsg_gam
          (by rw [hwc']; rfl) rfl (by rw [hwc']; rfl) rfl w.hspqr hspqr_clean
        have hst_clean_eq :
            { (ratchetState (stA1Clean cls) (dhPk dhsB1Clean) dhsA1Clean).1 with
                recv := setRecvChain
                  (ratchetState (stA1Clean cls) (dhPk dhsB1Clean) dhsA1Clean).1.recv cA1Clean,
                spqr := recvSt (stA1Clean cls).spqr (pqm1Clean cls) } = stA4Clean cls := by
          change { stA3'Clean cls with
              recv := setRecvChain (stA3'Clean cls).recv cA1Clean,
              spqr := recvSt (stA1Clean cls).spqr (pqm1Clean cls) } = stA4Clean cls
          rw [hsetA4]; rfl
        have hst_agree' : StateBytesAgree S g (gClean r cls)
            { st1 with recv := setRecvChain st1.recv w.c', spqr := w.spqr' } (stA4Clean cls) := by
          rw [← hst_clean_eq]; exact hst_agree0
        refine ⟨hpki', hnskip', ?_, hnoNewBob⟩
        rw [htr'] at hle_next ⊢
        unfold decTailTr at hle_next ⊢
        dsimp only at hle_next ⊢
        let tr_sk := Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr
          (st1.sessionInfo "alice") w.msg.ratchetKey cChain.rIdx stateIdx cChain.chainKey
          cChain.index (w.msg.counter.toNat - cChain.index.toNat) tr_pre
        let tr_rec := tr_sk.append
          (TREvE (TREvent.Received "alice" st1.peer w.msg.ratchetKey w.msg.counter w.ptTerm))
        let tr_mk := tr_rec.append
          (TREvE (TREvent.MessageKey (st1.sessionInfo "alice") .receiver
            w.seed w.pqSalt w.msg.counter cChain.rIdx stateIdx))
        let stOut : TRState := { st1 with recv := setRecvChain st1.recv w.c', spqr := w.spqr' }
        have hge : tr₁.length ≤ tr_mk.length := by
          dsimp only [tr_mk, tr_rec, tr_sk]
          rw [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2,
              Symbolic.Swarm.CREF.TR.RecvDec.logSkippedKeysTr_length, decRatchetPreTr_length]
          omega
        have hat_new : ((tr_mk.append (⟨⟨"alice", stOut⟩⟩ : TRStEntry)).at? tr_mk.length :
            Option TRStEntry) = some ⟨⟨"alice", stOut⟩⟩ := by
          rw [Symbolic.Swarm.CREF.at?_append_length]; rfl
        have hmk_none : ∀ j, tr₁.length ≤ j → (tr_mk.at? j : Option TRStEntry) = none := by
          intro j hj
          dsimp only [tr_mk, tr_rec, tr_sk, tr_pre]
          rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_stEntry_logSkippedKeysTr]
          unfold decRatchetPreTr
          rw [at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_append_non_entry _ _ rfl, at?_append_non_entry _ _ rfl,
              at?_eq_none_of_le tr₁ hj]
        have hrecv_new : stOut.recv.map (fun x => gamma rcprI0 S g x.ratchetKey) =
            ([⟨2, by decide⟩, ⟨5, by decide⟩] : List (Fin 7)).map rcprPubOfIdx := by
          have hmap0 := congrArg (List.map (gamma rcprI0 S g))
            (setRecvChain_map_ratchetKey st1.recv w.c')
          rw [List.map_map, List.map_map] at hmap0
          refine hmap0.trans ?_
          have hlen : st.recv.length = 1 := by simp [hrecv1]
          dsimp only [st1, trDhRatchetState, maxReceiverChains]
          simp only [Function.comp_def]
          rw [hlen]; dsimp only [Nat.reduceAdd, Nat.reduceSub, List.drop]
          rw [List.map_append, hrecv_map]; dsimp only [List.map]
          rw [hrk_w]; rfl
        refine activePartySt_of_unique_new hAct₁ hle_next hge hat_new ?_ hinit
          hst_agree' hrecv_new hdhs_idx
        intro j s0 hj hat
        by_cases hlt : j < tr_mk.length
        · rw [at?_append_of_lt _ _ hlt, hmk_none j hj] at hat; cases hat
        · by_cases heq : j = tr_mk.length
          · subst heq
            rw [Symbolic.Swarm.CREF.at?_append_length] at hat
            injection hat with h1; injection h1 with h2; injection h2 with _ hs0
            exact ⟨rfl, hs0.symm⟩
          · rw [at?_eq_none_of_le (tr_mk.append (⟨⟨"alice", stOut⟩⟩ : TRStEntry))
                (by simp only [Symbolic.DYBridge.DY.Trace.append_eq_1,
                      Symbolic.DYBridge.DY.Trace.length_eq_2]; omega)] at hat
            cases hat
  | _ => rw [hs] at hfits; cases hfits

/-! ## 3. Peeled Chain `0..3` & Prefix Invariants for `k = 4, 5` -/

theorem peeled_inv_0to3 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {visAll : List VisEntry} (cls : Nat → Nat)
    {c0 c1 c2 c3 : PeeledCall} {cs4 : List PeeledCall} {rest3 : List Step}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hCompat : GhostAndSemMatchSetup rcprI0 r S g)
    (hgwf : GhostWF g visAll)
    (hcl0 : cls 0 = stepCoinLen c1.s)
    (hcl1 : cls 1 = stepCoinLen c3.s)
    (hpv : PeeledValid r S g visAll 0 none (setupTrace r) (c0 :: c1 :: c2 :: c3 :: cs4)
      (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: (c3.pre ++ c3.s :: rest3))))) :
    let tr₀ := c0.s.next (runSteps c0.pre (setupTrace r))
    let tr₁ := c1.s.next (runSteps c1.pre tr₀)
    let tr₂ := c2.s.next (runSteps c2.pre tr₁)
    let tr₃ := c3.s.next (runSteps c3.pre tr₂)
    PkiUnchanged tr₃ ∧
    NoSkippedKeyStored tr₃ ∧
    ActivePartySt "alice" true S g (gClean r cls)
      [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) tr₃ ∧
    ActivePartySt "bob" false S g (gClean r cls)
      [⟨4, by decide⟩] ⟨5, by decide⟩ (stB3Clean cls) tr₃ ∧
    (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
      (ecKey (pubBytes rcprI0 (secretBytes r 0)))
      (gamma rcprI0 S (gClean r cls) o1.ek)
      (gamma rcprI0 S (gClean r cls) o1.ct)
      (gamma rcprI0 S (gClean r cls) (m0Clean cls))) ∧
    (ev 3).exit =
      some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls)) ∧
    PeeledValid r S g visAll 4 (some (none, 7#32, 9#32)) tr₃ cs4 rest3 := by
  obtain ⟨ek0, ct0, hek0, hct0, hpki2, hnskip2, hActA2, hActB2, hev1_out, hpv3⟩ :=
    peeled_inv_0to2 cls hfit hCompat hgwf hcl0 hpv
  generalize hss3 : (c3.pre ++ c3.s :: rest3) = ss3 at hpv3
  cases hpv3 with
  | @cons _ _ _ _ _ rest3' hnet3 hpre3 hlok3 hrm3 hsub3 hpv4 =>
    have hrest3 : rest3 = rest3' :=
      (List.cons.inj (List.append_cancel_left hss3)).2
    subst hrest3
    have hw3 : runWrapped (ev (sendCallOf 1)) = false := ev3_runWrapped
    obtain ⟨hpki3, hnskip3, _, hActB3, hnoNewA3, hexit3⟩ :=
      party_send_agree cls (party := "bob") (otherParty := "alice")
        (sIdx := 1) (tsPt := 47) (tsCoins := 48)
        (by decide) hgwf hpki2 hnskip2
        (fun hw => by rw [hw3] at hw; cases hw)
        hek0 hct0 hActB2
        ⟨ev3_party_cmd.1, _, ev3_party_cmd.2⟩
        hcl1
        (gClean_sigma_47 r cls 32)
        (gClean_sigma_48 r cls)
        (Or.inr ⟨hw3, gClean_addr_m1 r cls⟩)
        hnet3 hpre3 hlok3 hrm3 hsub3
    have hev3_out : (ev 3).exit =
        some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls)) := by
      simp only [hw3, Bool.false_eq_true, ↓reduceIte] at hexit3
      rw [show sendCallOf 1 = 3 from rfl] at hexit3
      unfold m1Clean coins1Clean key1Clean pt1Clean
      exact hexit3
    rw [nextBundleIds_non_init (by decide) (by decide)] at hpv4
    exact ⟨hpki3, hnskip3, noNewPartyState_preserves_active hnoNewA3 hActA2,
      hActB3, hev1_out, hev3_out, hpv4⟩

structure PrefixInv4 (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)
  pki : PkiUnchanged (runTrace r ss)
  noSkip : NoSkippedKeyStored (runTrace r ss)
  actAlice : ActivePartySt "alice" true S g (gClean r cls)
    [⟨2, by decide⟩] ⟨4, by decide⟩ (stA1Clean cls) (runTrace r ss)
  actBob : ActivePartySt "bob" false S g (gClean r cls)
    [⟨4, by decide⟩] ⟨5, by decide⟩ (stB3Clean cls) (runTrace r ss)
  ev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes rcprI0 (secretBytes r 0)))
    (gamma rcprI0 S (gClean r cls) o1.ek)
    (gamma rcprI0 S (gClean r cls) o1.ct)
    (gamma rcprI0 S (gClean r cls) (m0Clean cls)))
  ev3_out : (ev 3).exit =
    some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))

structure PrefixInv5 (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (cls : Nat → Nat) : Prop where
  validCls : ValidCoinLens cls
  compatClean : GhostAndSemMatchSetup rcprI0 r S (gClean r cls)
  pki : PkiUnchanged (runTrace r ss)
  noSkip : NoSkippedKeyStored (runTrace r ss)
  actAlice : ActivePartySt "alice" true S g (gClean r cls)
    [⟨2, by decide⟩, ⟨5, by decide⟩] ⟨6, by decide⟩ (stA4Clean cls) (runTrace r ss)
  actBob : ActivePartySt "bob" false S g (gClean r cls)
    [⟨4, by decide⟩] ⟨5, by decide⟩ (stB3Clean cls) (runTrace r ss)
  ev1_out : (ev 1).exit = some (0, preKeyWire none 7#32 9#32 r.regIdA
    (ecKey (pubBytes rcprI0 (secretBytes r 0)))
    (gamma rcprI0 S (gClean r cls) o1.ek)
    (gamma rcprI0 S (gClean r cls) o1.ct)
    (gamma rcprI0 S (gClean r cls) (m0Clean cls)))
  ev3_out : (ev 3).exit =
    some (0, wireWhisperTag :: gamma rcprI0 S (gClean r cls) (m1Clean cls))

theorem prefix_inv_4 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 4)) :
    ∃ cls, PrefixInv4 r S g ss cls := by
  obtain ⟨hCompat, hgwf, hmrwf, hm⟩ := hex
  rw [rcprTrace_take_eq_evsRange (by decide)] at hm
  obtain ⟨cs, hlen, hpv⟩ := peel_evsRange 4 0 (by decide) hmrwf.2.2.1 hm (fun _ h => h)
  rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | _⟩⟩⟩⟩ <;> simp at hlen
  let cls := clsOfCalls [c0, c1, c2, c3]
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  cases hpv with
  | @cons _ _ _ _ _ r0 hnet0 hpre0 hlok0 hrm0 hsub0 hpv1 =>
    cases hpv1 with
    | @cons _ _ _ _ _ r1 hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
      cases hpv2 with
      | @cons _ _ _ _ _ r2 hnet2 hpre2 hlok2 hrm2 hsub2 hpv3 =>
        cases hpv3 with
        | @cons _ _ _ _ _ tail hnet3 hpre3 hlok3 hrm3 hsub3 hpv4 =>
          have hpv_full : PeeledValid r S g vis 0 none (setupTrace r) [c0, c1, c2, c3]
              (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: (c3.pre ++ c3.s :: tail)))) :=
            .cons hnet0 hpre0 hlok0 hrm0 hsub0
              (.cons hnet1 hpre1 hlok1 hrm1 hsub1
                (.cons hnet2 hpre2 hlok2 hrm2 hsub2
                  (.cons hnet3 hpre3 hlok3 hrm3 hsub3 hpv4)))
          obtain ⟨hpki3, hnskip3, hActA3, hActB3, hev1_out, hev3_out, hpv_tail⟩ :=
            peeled_inv_0to3 cls hfit hCompat hgwf rfl rfl hpv_full
          cases hpv_tail with
          | nil hnet_tail =>
            refine ⟨cls, hvCls, hCompatClean, ?_, ?_, ?_, ?_, hev1_out, hev3_out⟩
            · unfold runTrace; simp only [runSteps_append, runSteps]
              exact pkiUnchanged_runSteps_network tail hnet_tail hpki3
            · unfold runTrace; simp only [runSteps_append, runSteps]
              exact noSkippedKeyStored_runSteps_network tail hnet_tail hnskip3
            · unfold runTrace; simp only [runSteps_append, runSteps]
              exact noNewPartyState_preserves_active
                (noNewPartyState_runSteps_network tail _ hnet_tail) hActA3
            · unfold runTrace; simp only [runSteps_append, runSteps]
              exact noNewPartyState_preserves_active
                (noNewPartyState_runSteps_network tail _ hnet_tail) hActB3

theorem prefix_inv_5 {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ss : List Step} {vis : List VisEntry}
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hex : Explains rcprI0 r S g ss vis (rcprTrace.take 5)) :
    ∃ cls, PrefixInv5 r S g ss cls := by
  obtain ⟨hCompat, hgwf, hmrwf, hm⟩ := hex
  rw [rcprTrace_take_eq_evsRange (by decide)] at hm
  obtain ⟨cs, hlen, hpv⟩ := peel_evsRange 5 0 (by decide) hmrwf.2.2.1 hm (fun _ h => h)
  rcases cs with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | _⟩⟩⟩⟩⟩ <;> simp at hlen
  let cls := clsOfCalls [c0, c1, c2, c3, c4]
  have hvCls : ValidCoinLens cls := validCoinLens_clsOfCalls hpv
  have hCompatClean := ghostAndSemMatchSetup_gClean cls hfit hCompat
  cases hpv with
  | @cons _ _ _ _ _ r0 hnet0 hpre0 hlok0 hrm0 hsub0 hpv1 =>
    cases hpv1 with
    | @cons _ _ _ _ _ r1 hnet1 hpre1 hlok1 hrm1 hsub1 hpv2 =>
      cases hpv2 with
      | @cons _ _ _ _ _ r2 hnet2 hpre2 hlok2 hrm2 hsub2 hpv3 =>
        cases hpv3 with
        | @cons _ _ _ _ _ r3 hnet3 hpre3 hlok3 hrm3 hsub3 hpv4 =>
          have hpv_full : PeeledValid r S g vis 0 none (setupTrace r) [c0, c1, c2, c3, c4]
              (c0.pre ++ c0.s :: (c1.pre ++ c1.s :: (c2.pre ++ c2.s :: (c3.pre ++ c3.s :: r3)))) :=
            .cons hnet0 hpre0 hlok0 hrm0 hsub0
              (.cons hnet1 hpre1 hlok1 hrm1 hsub1
                (.cons hnet2 hpre2 hlok2 hrm2 hsub2
                  (.cons hnet3 hpre3 hlok3 hrm3 hsub3 hpv4)))
          obtain ⟨hpki3, hnskip3, hActA3, hActB3, hev1_out, hev3_out, hpv_c4⟩ :=
            peeled_inv_0to3 cls hfit hCompat hgwf rfl rfl hpv_full
          cases hpv_c4 with
          | @cons _ _ _ _ _ tail hnet4 hpre4 _ hrm4 hsub4 hpv_tail =>
            obtain ⟨hpki4, hnskip4, hActA4, hnoNewB4⟩ :=
              alice_call4_agree cls hfit hgwf hpki3 hnskip3 hActA3 hev3_out
                hnet4 hpre4 hrm4 hsub4
            have hActB4 := noNewPartyState_preserves_active hnoNewB4 hActB3
            cases hpv_tail with
            | nil hnet_tail =>
              refine ⟨cls, hvCls, hCompatClean, ?_, ?_, ?_, ?_, hev1_out, hev3_out⟩
              · unfold runTrace; simp only [runSteps_append, runSteps]
                exact pkiUnchanged_runSteps_network tail hnet_tail hpki4
              · unfold runTrace; simp only [runSteps_append, runSteps]
                exact noSkippedKeyStored_runSteps_network tail hnet_tail hnskip4
              · unfold runTrace; simp only [runSteps_append, runSteps]
                exact noNewPartyState_preserves_active
                  (noNewPartyState_runSteps_network tail _ hnet_tail) hActA4
              · unfold runTrace; simp only [runSteps_append, runSteps]
                exact noNewPartyState_preserves_active
                  (noNewPartyState_runSteps_network tail _ hnet_tail) hActB4

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
