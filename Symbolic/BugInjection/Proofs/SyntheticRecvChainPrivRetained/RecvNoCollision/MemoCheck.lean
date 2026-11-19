/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.SendTrials
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.TraceSummary
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.StateSafe

/-!
# Memo & MAC Collision Dischargers at Calls 2 and 4 (`MemoCheck.lean`)

Combines `walk_calls_0_to_3` (`SendTrials.lean`), `summary_at_2` / `summary_at_4`
(`TraceSummary.lean`), and `not_memoCollisionOn_of_safeMemo2` (`StateSafe.lean`) to prove:
- `not_bobStartCollides_of_pinned` (Call 2 PreKey `recv`),
- `not_recvCollisionOn_of_pinned` (Call 4 Whisper `recv`),
- `not_reselectCollisionOn_of_pinned` (Call 4 Whisper `recv`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.MemoCheck

open scoped DY.Libsignal.Composed
attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.PQXDH (serializedIk)
open DY.Libsignal.TripleRatchet
  (TRState parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry PreKeyFields
   runTrace honestSaltsOf principalTerms plaintextTerms prefixTerms trialTerms
   RecvCollisionOn ReselectCollisionOn BobSessionStartCollidesOrImplicitRejectsOn
   randTerm gamma)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (encMsg encSig parse_encMsg)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (ikA ikB spkB o1 keys1 dhsA stA0)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
  (rcprI0 rcprHooks0 rcprCompFitsPinned)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (ValidCoinLens pt0Clean coins0Clean key0Clean stA1Clean m0Clean
   dhsB1Clean cB'Clean stB2Clean pt1Clean coins1Clean key1Clean stB3Clean m1Clean
   cA0Clean ssClean)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs
  (SafeMemo safeMemo_plaintext safeMemo_lit_short)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagTermAt
  (safeMemo_spqrInit)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
  (dagSize dagOp dagBytes sendPtTs)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
  (runTrace_eq_r0 honestSaltsOf_eq_r0 bobSessionStartCollides_eq_r0 recvCollisionOn_eq_r0
   termAt_lit_b HandshakeAt handshake_termAt pqSecrets_safeMemo)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.StateSafe
  (SafeMemo2 safeMemo_toSafeMemo2 not_memoCollisionOn_of_safeMemo2 safeMemo2_trState_of_dr)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.SendTrials
  (pqKeyOf sendPtBytes_len_lt8 PrefixPinned mem_pts_of_lt
   SendStepOut send_step_at not_macTagForgery_of_sendStep
   allSeedTuples safeMemo_of_seedTrialOk walk_calls_0_to_3)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision
  (summary_at_2 summary_at_4 bobCtx2 bobTrials_at_2
   not_reselectCollisionOn_trClean4 whisperTrials_trClean4_cases)

/-! ## 1. `SafeMemo2` Helpers for Alice's and Bob's Stored `TRState`s -/

private theorem safeMemo2_alice_state
    {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {st : TRState}
    (hh : HandshakeAt S g pts)
    (hpeer : st.peer = "bob")
    (hcore : st.myIk = serializedIk (dhPk ikA) ∧
             st.peerIk = serializedIk (dhPk ikB) ∧
             st.rk = stA0.rk ∧
             st.dhs = dhsA ∧
             st.sid = stA0.sid)
    (hrecv : st.recv = [cA0Clean])
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts st.spqr)
    (hcks : SafeMemo dagSize dagOp dagBytes S g pts st.cks) :
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"alice", st⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  refine safeMemo2_trState_of_dr (ls₀ := ⟨"alice", st⟩) (cLast := cA0Clean)
    rfl rfl (Or.inl rfl) (Or.inr hpeer) hspqr ?_ ?_ ?_ (by decide)
  · intro u hu
    dsimp only at hu
    rw [hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hh.ik0s.safeMemo
    · exact hh.ik1s.safeMemo
    · exact hh.stA0_rk.safeMemo
    · exact hh.t_dhsA.safeMemo
    · exact hcks
    · exact hh.stA0_sid.safeMemo
  · intro c hc
    dsimp only at hc
    rw [hrecv, List.mem_singleton] at hc
    subst hc
    exact ⟨hh.pk2.safeMemo, hh.ck_init.safeMemo⟩
  · dsimp only; rw [hrecv]; rfl

private theorem safeMemo2_bob_state
    {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {st : TRState}
    (hh : HandshakeAt S g pts)
    (h_dhsB1 : SafeMemo dagSize dagOp dagBytes S g pts dhsB1Clean)
    (h_rkB : SafeMemo dagSize dagOp dagBytes S g pts (stB2Clean cls).rk)
    (h_sidB : SafeMemo dagSize dagOp dagBytes S g pts (stB2Clean cls).sid)
    (h_cB'_ck : SafeMemo dagSize dagOp dagBytes S g pts cB'Clean.chainKey)
    (hpeer : st.peer = "alice")
    (hcore : st.myIk = serializedIk (dhPk ikB) ∧
             st.peerIk = serializedIk (dhPk ikA) ∧
             st.rk = (stB2Clean cls).rk ∧
             st.dhs = dhsB1Clean ∧
             st.sid = (stB2Clean cls).sid)
    (hrecv : st.recv = [cB'Clean])
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts st.spqr)
    (hcks : SafeMemo dagSize dagOp dagBytes S g pts st.cks) :
    SafeMemo2 S g pts (DY.Comparse.serialize (⟨"bob", st⟩ : DY.PersistentLocalState.LocalState TRState)) := by
  refine safeMemo2_trState_of_dr (ls₀ := ⟨"bob", st⟩) (cLast := cB'Clean)
    rfl rfl (Or.inr rfl) (Or.inl hpeer) hspqr ?_ ?_ ?_ (by decide)
  · intro u hu
    dsimp only at hu
    rw [hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hh.ik1s.safeMemo
    · exact hh.ik0s.safeMemo
    · exact h_rkB
    · exact h_dhsB1
    · exact hcks
    · exact h_sidB
  · intro c hc
    dsimp only at hc
    rw [hrecv, List.mem_singleton] at hc
    subst hc
    exact ⟨hh.pk4.safeMemo, h_cB'_ck⟩
  · dsimp only; rw [hrecv]; rfl

/-! ## 2. Call 2 (`bobStart`) Non-Collision -/

theorem not_bobStartCollides_of_pinned
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (vis : List VisEntry)
    (cls : Nat → Nat) (p : PreKeyFields)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hcls : ValidCoinLens cls)
    (hp : PrefixPinned cls S g vis 1)
    (hpId : p.preKeyId = none) :
    ¬ BobSessionStartCollidesOrImplicitRejectsOn rcprI0 r S g
        (runTrace r (ssClean cls 2)) vis
        (honestSaltsOf r (ssClean cls 2)) p
        ⟨o1.ek, o1.ct, m0Clean cls⟩ := by
  rw [bobSessionStartCollides_eq_r0 hfit, runTrace_eq_r0 hfit, honestSaltsOf_eq_r0 hfit]
  obtain ⟨htr2, hst2, hsec2, hsalts2⟩ := summary_at_2 cls
  rw [htr2, hsalts2]
  set pts := plaintextTerms vis
  have hpts_eq : pts = [randTerm (sendPtTs 0) 32] := hp.vis_pts
  have hpt0_mem : randTerm (sendPtTs 0) 32 ∈ pts := mem_pts_of_lt hp (by decide)
  have hh := handshake_termAt (pts := pts) hp.base
  have hspqr0 : SafeMemo dagSize dagOp dagBytes S g pts stA0.spqr :=
    safeMemo_spqrInit hh.pqr.safeMemo (safeMemo_lit_short (by decide))
  have hs0 : SendStepOut (cls := cls) S g pts stA0 0 :=
    send_step_at hp hcls (by decide) (by decide) hpt0_mem
      rfl hspqr0 hh.pk4 hh.ik0s hh.ik1s hh.stA0_cks rfl rfl
  have hparse0 : parseTrSignalMsg (m0Clean cls) =
      some (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean) :=
    parse_encMsg _ _ _ _
  unfold BobSessionStartCollidesOrImplicitRejectsOn
  dsimp only
  rw [hparse0]
  dsimp only
  rintro (hmemo | hmac_forg)
  · have hbt2 := bobTrials_at_2 cls (Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.trClean2 cls) p hpId
    refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g pts t
      unfold prefixTerms principalTerms at ht
      simp only [List.mem_append] at ht
      rcases ht with ((hsend | hstate) | hsec) | hpt
      · rcases hp.vis_sends t hsend with rfl | rfl | ⟨j, hj, rfl⟩
        · exact safeMemo_toSafeMemo2 hh.ek.safeMemo
        · exact safeMemo_toSafeMemo2 hh.ct.safeMemo
        · obtain rfl : j = 0 := by omega
          exact safeMemo_toSafeMemo2 hs0.wmac.safeMemo
      · rw [hst2] at hstate
        simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hstate
        rcases hstate with rfl | rfl
        · exact safeMemo2_alice_state hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            hspqr0 hh.stA0_cks.safeMemo
        · exact safeMemo2_alice_state hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            hs0.spqr_sm hs0.cks_next.safeMemo
      · rw [hsec2] at hsec
        exact safeMemo_toSafeMemo2 (pqSecrets_safeMemo hh t hsec)
      · have hpt' : t ∈ [randTerm (sendPtTs 0) 32] := by rw [← hpts_eq]; exact hpt
        rw [List.mem_singleton] at hpt'
        subst hpt'
        exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt0_mem
          (by rw [hp.send_pt 0 (by decide)]; exact sendPtBytes_len_lt8 (by decide)))
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g pts t
      have ht_full : t ∈ [o1.ek, o1.ct, m0Clean cls] ++
          ([bobCtx2 cls p]).flatMap (trialTerms [DY.Spqr.zeroKey, key0Clean cls]
            (encSig stA0 (coins0Clean cls) (key0Clean cls) pt0Clean)) := by
        rcases hbt2 with hbt | hbt <;> rw [hbt] at ht
        · simp only [List.flatMap_nil, List.append_nil] at ht
          exact List.mem_append_left _ ht
        · exact ht
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        List.flatMap_cons, List.flatMap_nil] at ht_full
      rcases ht_full with (rfl | rfl | rfl) | htrial
      · exact safeMemo_toSafeMemo2 hh.ek.safeMemo
      · exact safeMemo_toSafeMemo2 hh.ct.safeMemo
      · exact safeMemo_toSafeMemo2 hs0.wmac.safeMemo
      · refine safeMemo_toSafeMemo2 (safeMemo_of_seedTrialOk
          (salts := [DY.Spqr.zeroKey, key0Clean cls]) (ctx := bobCtx2 cls p)
          (nSalts := 2) (seed_id := 98) (pIk_id := 30) (mIk_id := 31) (wire_id := 109)
          (by decide) ?_ ?_ hs0.ct.safeMemo hh.ik0s hh.ik1s hs0.wire ?_ t htrial)
        · intro salt hsalt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
          rcases hsalt with rfl | rfl
          · exact ⟨8, by decide, termAt_lit_b (by decide +kernel)⟩
          · exact ⟨100, by decide, hs0.pqKey⟩
        · intro u hu
          dsimp only [bobCtx2] at hu
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl
          · exact hh.rk_init.safeMemo
          · exact hh.ck_init.safeMemo
          · exact hh.pqr.safeMemo
          · exact hh.stA0_cks.safeMemo
          · exact hs0.cks_next.safeMemo
        · intro seed hseed
          dsimp only [bobCtx2] at hseed
          cases hseed
          exact hs0.seed
  · have hsalt0_mem : pqKeyOf stA0 (cls 0) (sendPtTs 0) ∈ [DY.Spqr.zeroKey, key0Clean cls] :=
      List.mem_cons_of_mem _ List.mem_cons_self
    exact not_macTagForgery_of_sendStep (j := 0) (by decide) hs0 hsalt0_mem hmac_forg

/-! ## 3. Call 4 (`messageDecrypt`) `RecvCollisionOn` & `ReselectCollisionOn` Dischargers -/

private theorem pk29_pk69_ne_pk116 :
    dagBytes 29 ≠ dagBytes 116 ∧ dagBytes 69 ≠ dagBytes 116 := by
  decide +kernel

theorem not_reselectCollisionOn_of_pinned
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (vis : List VisEntry)
    (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hcls : ValidCoinLens cls)
    (hp : PrefixPinned cls S g vis 2) :
    ¬ ReselectCollisionOn rcprI0 r S g
        (runTrace r (ssClean cls 4)) vis
        (honestSaltsOf r (ssClean cls 4)) (m1Clean cls) := by
  rw [runTrace_eq_r0 hfit, (summary_at_4 cls).1]
  have w := walk_calls_0_to_3 hp hcls
  have hne29 : gamma rcprI0 S g (dhPk spkB) ≠ gamma rcprI0 S g (dhPk dhsB1Clean) := by
    rw [w.hh.pk2.gamma_eq, w.t_pk5.gamma_eq]; exact pk29_pk69_ne_pk116.1
  have hne69 : gamma rcprI0 S g (dhPk dhsA) ≠ gamma rcprI0 S g (dhPk dhsB1Clean) := by
    rw [w.hh.pk4.gamma_eq, w.t_pk5.gamma_eq]; exact pk29_pk69_ne_pk116.2
  exact not_reselectCollisionOn_trClean4 hfit hne29 hne69

theorem not_recvCollisionOn_of_pinned
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (vis : List VisEntry)
    (cls : Nat → Nat)
    (hfit : rcprCompFitsPinned (rcprI0, rcprHooks0) r)
    (hcls : ValidCoinLens cls)
    (hp : PrefixPinned cls S g vis 2) :
    ¬ RecvCollisionOn rcprI0 r S g
        (runTrace r (ssClean cls 4)) vis
        (honestSaltsOf r (ssClean cls 4)) (m1Clean cls) := by
  rw [recvCollisionOn_eq_r0 hfit, runTrace_eq_r0 hfit, honestSaltsOf_eq_r0 hfit]
  obtain ⟨htr4, hst4, hsec4, _, hsalts4⟩ := summary_at_4 cls
  rw [htr4, hsalts4]
  set pts := plaintextTerms vis
  have hpts_eq : pts = [randTerm (sendPtTs 0) 32, randTerm (sendPtTs 1) 32] := hp.vis_pts
  have hpt0_mem : randTerm (sendPtTs 0) 32 ∈ pts := mem_pts_of_lt hp (by decide)
  have hpt1_mem : randTerm (sendPtTs 1) 32 ∈ pts := mem_pts_of_lt hp (by decide)
  have w := walk_calls_0_to_3 hp hcls
  have hne29 : gamma rcprI0 S g (dhPk spkB) ≠ gamma rcprI0 S g (dhPk dhsB1Clean) := by
    rw [w.hh.pk2.gamma_eq, w.t_pk5.gamma_eq]; exact pk29_pk69_ne_pk116.1
  have hne69 : gamma rcprI0 S g (dhPk dhsA) ≠ gamma rcprI0 S g (dhPk dhsB1Clean) := by
    rw [w.hh.pk4.gamma_eq, w.t_pk5.gamma_eq]; exact pk29_pk69_ne_pk116.2
  have hparse1 : parseTrSignalMsg (m1Clean cls) =
      some (encSig (stB2Clean cls) (coins1Clean cls) (key1Clean cls) pt1Clean) :=
    parse_encMsg _ _ _ _
  unfold RecvCollisionOn
  rw [hparse1]
  dsimp only
  rintro (hmemo | hmac_forg)
  · refine not_memoCollisionOn_of_safeMemo2 ?_ ?_ hmemo
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g pts t
      unfold prefixTerms principalTerms at ht
      simp only [List.mem_append] at ht
      rcases ht with ((hsend | hstate) | hsec) | hpt
      · rcases hp.vis_sends t hsend with rfl | rfl | ⟨j, hj, rfl⟩
        · exact safeMemo_toSafeMemo2 w.hh.ek.safeMemo
        · exact safeMemo_toSafeMemo2 w.hh.ct.safeMemo
        · rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
          · exact safeMemo_toSafeMemo2 w.out0.wmac.safeMemo
          · exact safeMemo_toSafeMemo2 w.out1.wmac.safeMemo
      · rw [hst4] at hstate
        simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hstate
        rcases hstate with rfl | rfl | rfl | rfl
        · exact safeMemo2_alice_state w.hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            w.spqr_stA0 w.hh.stA0_cks.safeMemo
        · exact safeMemo2_alice_state w.hh rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            w.out0.spqr_sm w.out0.cks_next.safeMemo
        · exact safeMemo2_bob_state w.hh w.t_dhsB1.safeMemo w.t_stB2_rk.safeMemo
            w.t_stB2_sid.safeMemo w.t_cB'_ck.safeMemo rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            w.spqr_stB2 w.t_stB2_cks.safeMemo
        · exact safeMemo2_bob_state w.hh w.t_dhsB1.safeMemo w.t_stB2_rk.safeMemo
            w.t_stB2_sid.safeMemo w.t_cB'_ck.safeMemo rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
            w.out1.spqr_sm w.out1.cks_next.safeMemo
      · rw [hsec4] at hsec
        exact safeMemo_toSafeMemo2 (pqSecrets_safeMemo w.hh t hsec)
      · have hpt' : t ∈ [randTerm (sendPtTs 0) 32, randTerm (sendPtTs 1) 32] := by
          rw [← hpts_eq]; exact hpt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hpt'
        rcases hpt' with rfl | rfl
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt0_mem
            (by rw [hp.send_pt 0 (by decide)]; exact sendPtBytes_len_lt8 (by decide)))
        · exact safeMemo_toSafeMemo2 (safeMemo_plaintext hpt1_mem
            (by rw [hp.send_pt 1 (by decide)]; exact sendPtBytes_len_lt8 (by decide)))
    · intro t ht
      rw [List.append_nil]
      change SafeMemo2 S g pts t
      simp only [List.mem_cons] at ht
      rcases ht with rfl | hflat
      · exact safeMemo_toSafeMemo2 w.out1.wmac.safeMemo
      · obtain ⟨ctx, hctx, htrial⟩ := List.mem_flatMap.mp hflat
        have hsalts_ok : ∀ salt ∈ [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls],
            ∃ s_id ∈ [8, 100, 126],
              Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs.TermAt
                dagSize dagOp dagBytes S g pts salt s_id := by
          intro salt hsalt
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsalt
          rcases hsalt with rfl | rfl | rfl
          · exact ⟨8, by decide, termAt_lit_b (by decide +kernel)⟩
          · exact ⟨100, by decide, w.out0.pqKey⟩
          · exact ⟨126, by decide, w.out1.pqKey⟩
        rcases whisperTrials_trClean4_cases hne29 hne69 hctx with
          ⟨hpIk, hmIk, hextra, hseed⟩ | ⟨hpIk, hmIk, hextra, hseed⟩
        · refine safeMemo_toSafeMemo2 (safeMemo_of_seedTrialOk
            (salts := [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls]) (ctx := ctx)
            (nSalts := 3) (seed_id := 124) (pIk_id := 31) (mIk_id := 30) (wire_id := 135)
            (by decide) hsalts_ok ?_ w.out1.ct.safeMemo
            (hpIk ▸ w.hh.ik1s) (hmIk ▸ w.hh.ik0s) w.out1.wire ?_ t htrial)
          · intro u hu; rw [hextra] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact w.t_aliceNew_ck.safeMemo
            · exact w.t_aliceNew_nck.safeMemo
          · intro seed hs; rw [hseed] at hs; cases hs; exact w.t_aliceNew_seed
        · refine safeMemo_toSafeMemo2 (safeMemo_of_seedTrialOk
            (salts := [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls]) (ctx := ctx)
            (nSalts := 3) (seed_id := 146) (pIk_id := 30) (mIk_id := 31) (wire_id := 135)
            (by decide) hsalts_ok ?_ w.out1.ct.safeMemo
            (hpIk ▸ w.hh.ik0s) (hmIk ▸ w.hh.ik1s) w.out1.wire ?_ t htrial)
          · intro u hu; rw [hextra] at hu
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
            rcases hu with rfl | rfl
            · exact w.t_selfB_ck.safeMemo
            · exact w.t_selfB_nck.safeMemo
          · intro seed hs; rw [hseed] at hs; cases hs; exact w.t_selfB_seed
  · have hsalt1_mem : pqKeyOf (stB2Clean cls) (cls 1) (sendPtTs 1) ∈
        [DY.Spqr.zeroKey, key0Clean cls, key1Clean cls] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    exact not_macTagForgery_of_sendStep (j := 1) (by decide) w.out1 hsalt1_mem hmac_forg

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.MemoCheck
