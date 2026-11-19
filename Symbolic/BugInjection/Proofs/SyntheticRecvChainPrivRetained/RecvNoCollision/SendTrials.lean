/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.Calls0to4Prefix.Schedule
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.ShaMacLaws
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk

/-!
# Send-Step Pinning, Receiver Trial Tables, and 4-Call DAG Walk (`SendTrials.lean`)

Provides:
1. `PrefixPinned` and the universal 1-step send theorem `send_step_at` +
   `not_macTagForgery_of_sendStep`.
2. Certified trial-row / seed-entry combinators `safeMemo_of_trialRowMatches` and
   `safeMemo_of_seedTrialOk`.
3. `walk_calls_0_to_3`: complete DAG `TermAt` and `SafeMemo` witnesses for Calls `0..3`,
   including Alice's Call 4 ratchet chain and Bob's Call 4 self-DH trial chain.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.SendTrials

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
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg lit litByte messageVersion hmac kdfCk createChain
   trMsgKeys computeMac parseTrSignalMsg)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry TrialCtx MacTagForgeryOrCollision
   trialTerms plaintextTerms randTerm litOf gamma' gamma gamma_litOf)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compTag4)
open Symbolic.BugInjection.Proofs.Common443.Census443Memo (memoOK_spqrRecvState_pack)
open Symbolic.Proofs.Tests.Shared.Composed.Runs
  (rnd encSt encMsg encSig parse_encMsg createChain_comm)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (spkB o1 keys1 dhsA stA0)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0 (rcprI0)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained
  (ValidCoinLens m0Clean m1Clean stA1Clean dhsB1Clean cBClean cB'Clean stB2Clean stB3Clean)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.ShaMacLaws
  (gamma_hmacE gamma_computeMacE gamma_trMsgKeys_congr_prk
   encMsg_pins_pqKey_and_pqMsg not_macTagForgeryOrCollision_of_honest_mac)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagDefs
  (DagOp dagOpBytesOk SafeMemo TermAt safeMemo_randTerm_zero safeMemo_lit_short)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagTermAt
  (termAt_concat termAt_symEncPt termAt_trWire termAt_of_opaque
   safeMemo_spqrInit safeMemo_spqrSend termAt_computeMac termAt_trMsgKeys safeMemo_trialTerms)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.DagData
  (dagSize dagOp dagBytes dag_nodes_ok wmkInfo1Id wmkInfo2Id wmkInfo3Id
   dhsB1Id honestSaltIds aliceBobAddrBytes sendPtTs sendPtBytes
   sendC32Id sendC64Id sendWmacId SendRow getSendRow
   TrialRow getTrialRow SeedEntry allSeedEntries)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.HandshakeWalk
  (dag_bytes_ok isKdfOp isConcatOp isTrunc8Op isLitOp isRandOp isSymEncPtOp isTrWireOp
   checkDhRand kdf_of_isKdfOp concat_of_isConcatOp trunc8_of_isTrunc8Op
   termAt_strLit wmkInfo_termAt termAt_lit_b termAt_litOf_b termAt_rand_b
   termAt_concat_b termAt_dhPk_b termAt_dh_b termAt_kdf_b
   norm_dhPk createChain_dhPk SetupAndCall0Pinned HandshakeAt handshake_termAt)

/-! ## 1. Send-Step Helpers and `PrefixPinned` -/

def pqKeyOf (st : TRState) (cl ptTs : Nat) : Bytes :=
  (DY.Spqr.spqrSend st.spqr (rnd (ptTs + 1) cl)).2.1

def pqMsgOf (st : TRState) (cl ptTs : Nat) : Bytes :=
  (DY.Spqr.spqrSend st.spqr (rnd (ptTs + 1) cl)).2.2

def sendStOf (st : TRState) (cl ptTs : Nat) : TRState :=
  encSt st (rnd (ptTs + 1) cl)

def sendMsgOf (st : TRState) (cl ptTs : Nat) : Bytes :=
  encMsg st (rnd (ptTs + 1) cl) (pqKeyOf st cl ptTs) (rnd ptTs 32)

def cleanSendSt (cls : Nat → Nat) : Nat → TRState
  | 0 => stA0
  | _ => stB2Clean cls

def cleanSendMsg (cls : Nat → Nat) : Nat → Bytes
  | 0 => m0Clean cls
  | _ => m1Clean cls

theorem sendPtBytes_len_lt8 {j : Nat} (hj : j < 2) : (sendPtBytes j).length < 8 := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide

/-- Ghost coins, wire addresses, concretized ciphertexts, and visible terms pinned on a clean
prefix with `nSends` `.send` steps (`nSends = 1` at `k = 2`, `nSends = 2` at `k = 4`). -/
structure PrefixPinned (cls : Nat → Nat) (S : OpaqueSymbolSemantics) (g : Ghost)
    (vis : List VisEntry) (nSends : Nat) : Prop where
  base : SetupAndCall0Pinned S g
  dhsB1 : nSends = 2 → g.σ 38 32 = dagBytes dhsB1Id
  send_pt : ∀ j < nSends, g.σ (sendPtTs j) 32 = sendPtBytes j
  send_c32 : ∀ j < nSends, cls j = 32 → g.σ (sendPtTs j + 1) 32 = dagBytes (sendC32Id j)
  send_c64 : ∀ j < nSends, cls j = 64 → g.σ (sendPtTs j + 1) 64 = dagBytes (sendC64Id j)
  send_msg : ∀ j < nSends, gamma rcprI0 S g (cleanSendMsg cls j) = dagBytes (sendWmacId j)
  send_addr : ∀ j < nSends, ∀ msg, parseTrSignalMsg (cleanSendMsg cls j) = some msg →
    g.addr msg.wire = (if j = 0 then aliceBobAddrBytes else [])
  vis_pts : plaintextTerms vis = (List.range nSends).map (fun j => randTerm (sendPtTs j) 32)
  vis_sends : ∀ t ∈ (vis.filter (·.kind == .send)).flatMap (·.terms),
    t = o1.ek ∨ t = o1.ct ∨ ∃ j < nSends, t = cleanSendMsg cls j

theorem mem_pts_of_lt {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {nSends j : Nat}
    (hp : PrefixPinned cls S g vis nSends) (hj : j < nSends) :
    randTerm (sendPtTs j) 32 ∈ plaintextTerms vis := by
  rw [hp.vis_pts]
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

/-! ## 2. Universal 1-Step Send Theorem (`send_step_at`) & MAC Non-Forgery -/

theorem spqrSend_shapes (S : OpaqueSymbolSemantics) (g : Ghost) (spqr coins : Bytes) :
    (gamma' rcprI0 S g (DY.Spqr.spqrSend spqr coins).2.1).shape =
      litOf (gamma rcprI0 S g (DY.Spqr.spqrSend spqr coins).2.1) ∧
    (gamma' rcprI0 S g (DY.Spqr.spqrSend spqr coins).2.2).shape =
      litOf (gamma rcprI0 S g (DY.Spqr.spqrSend spqr coins).2.2) := by
  unfold DY.Spqr.spqrSend; dsimp only
  split
  · constructor
    · unfold gamma gamma'
      dsimp only [DY.Spqr.spqrChainKey]
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrChainKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll rcprI0 S g)]
      rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll rcprI0 S g)]
      rfl
  · constructor
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendKey S)
        (DY.Libsignal.Composed.Refinement.concretizeAll rcprI0 S g)]
      rfl
    · unfold gamma gamma'
      rw [DY.Bytes.rec_eq (DY.Libsignal.Composed.Refinement.concretizeSpqrSendMsg S)
        (DY.Libsignal.Composed.Refinement.concretizeAll rcprI0 S g)]
      rfl

def sendRowOk (j : Nat) (r : SendRow) : Bool :=
  let wmac_id := sendWmacId j
  let ptTs := sendPtTs j
  let ptBs := sendPtBytes j
  let addr := if j = 0 then aliceBobAddrBytes else []
  let c2_id := r.mkey_id - 1
  let c3_id := r.iv_id - 1
  decide (j < 2) &&
  decide (r.pk_id < dagSize) && decide (r.myIk_id < dagSize) && decide (r.peerIk_id < dagSize) &&
  decide (r.seed_id < dagSize) && decide (r.nck_id < dagSize) &&
  decide (r.salt_id < dagSize) && decide (r.pq_id < dagSize) &&
  decide (r.prk_id < dagSize) && decide (r.ckey_id < dagSize) && decide (c2_id < dagSize) &&
  decide (r.mkey_id < dagSize) && decide (c3_id < dagSize) && decide (r.iv_id < dagSize) &&
  decide (r.ct_id < dagSize) && decide (r.wire_id < dagSize) &&
  decide (r.mi_r_id < dagSize) && decide (r.mi_id < dagSize) &&
  decide (r.fmac_id < dagSize) && decide (r.mac_id < dagSize) && decide (wmac_id < dagSize) &&
  isKdfOp (dagOp r.seed_id) r.old_cks_id 2 &&
  isKdfOp (dagOp r.nck_id) r.old_cks_id 3 &&
  isLitOp (dagOp r.salt_id) (dagBytes r.salt_id) &&
  decide ((dagBytes r.salt_id).length = 32) &&
  isLitOp (dagOp r.pq_id) (dagBytes r.pq_id) &&
  isKdfOp (dagOp r.prk_id) r.salt_id r.seed_id &&
  isKdfOp (dagOp r.ckey_id) r.prk_id 13 &&
  isConcatOp (dagOp c2_id) r.ckey_id 14 &&
  isKdfOp (dagOp r.mkey_id) r.prk_id c2_id &&
  isConcatOp (dagOp c3_id) r.mkey_id 15 &&
  isKdfOp (dagOp r.iv_id) r.prk_id c3_id &&
  isSymEncPtOp (dagOp r.ct_id) r.ckey_id r.iv_id ptTs ptBs &&
  isTrWireOp (dagOp r.wire_id) messageVersion r.pk_id r.ctr r.prev r.ct_id r.pq_id addr &&
  isConcatOp (dagOp r.mi_r_id) r.peerIk_id r.wire_id &&
  isConcatOp (dagOp r.mi_id) r.myIk_id r.mi_r_id &&
  isKdfOp (dagOp r.fmac_id) r.mkey_id r.mi_id &&
  isTrunc8Op (dagOp r.mac_id) r.fmac_id &&
  isConcatOp (dagOp wmac_id) r.wire_id r.mac_id &&
  decide ((dagBytes r.mac_id).length = 8) &&
  decide ((dagBytes r.mac_id).take 4 ≠ compTag4) &&
  decide ((dagBytes r.wire_id).length < 2048)

theorem all_send_rows_ok : (List.range 2).all (fun j => sendRowOk j (getSendRow j)) = true := by
  decide +kernel

structure SendStepOut {cls : Nat → Nat} (S : OpaqueSymbolSemantics) (g : Ghost) (pts : List Bytes)
    (st : TRState) (j : Nat) : Prop where
  spqr_sm : SafeMemo dagSize dagOp dagBytes S g pts (sendStOf st (cls j) (sendPtTs j)).spqr
  pqKey : TermAt dagSize dagOp dagBytes S g pts (pqKeyOf st (cls j) (sendPtTs j)) (getSendRow j).salt_id
  pqMsg : TermAt dagSize dagOp dagBytes S g pts (pqMsgOf st (cls j) (sendPtTs j)) (getSendRow j).pq_id
  cks_next : TermAt dagSize dagOp dagBytes S g pts (sendStOf st (cls j) (sendPtTs j)).cks (getSendRow j).nck_id
  seed : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).2 (getSendRow j).seed_id
  ct : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).ciphertext
    (getSendRow j).ct_id
  wire : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).wire
    (getSendRow j).wire_id
  mac : TermAt dagSize dagOp dagBytes S g pts
    (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).mac
    (getSendRow j).mac_id
  wmac : TermAt dagSize dagOp dagBytes S g pts (cleanSendMsg cls j) (sendWmacId j)

theorem send_step_at {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry} {pts : List Bytes} {nSends j : Nat} {st : TRState}
    (hp : PrefixPinned cls S g vis nSends)
    (hcls : ValidCoinLens cls)
    (hj : j < nSends) (hj2 : j < 2)
    (hpt_mem : randTerm (sendPtTs j) 32 ∈ pts)
    (hclean : cleanSendMsg cls j = sendMsgOf st (cls j) (sendPtTs j))
    (hspqr : SafeMemo dagSize dagOp dagBytes S g pts st.spqr)
    (tpk : TermAt dagSize dagOp dagBytes S g pts (dhPk st.dhs) (getSendRow j).pk_id)
    (tmyIk : TermAt dagSize dagOp dagBytes S g pts st.myIk (getSendRow j).myIk_id)
    (tpeerIk : TermAt dagSize dagOp dagBytes S g pts st.peerIk (getSendRow j).peerIk_id)
    (tcks : TermAt dagSize dagOp dagBytes S g pts st.cks (getSendRow j).old_cks_id)
    (hns : st.ns = (getSendRow j).ctr)
    (hpn : st.pn = (getSendRow j).prev) :
    SendStepOut (cls := cls) S g pts st j := by
  have hrow := List.all_eq_true.mp all_send_rows_ok j (List.mem_range.mpr hj2)
  set r := getSendRow j
  unfold sendRowOk at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩,
    hseed_lt⟩, hnck_lt⟩, hsalt_lt⟩, hpq_lt⟩, hprk_lt⟩, hckey_lt⟩, hc2_lt⟩,
    hmkey_lt⟩, hc3_lt⟩, hiv_lt⟩, hct_lt⟩, hwire_lt⟩, hmir_lt⟩, hmi_lt⟩,
    hfmac_lt⟩, hmac_lt⟩, hwmac_lt⟩,
    hseed_op⟩, hnck_op⟩, hsalt_op⟩, hsalt_len⟩, hpq_op⟩, hprk_op⟩, hckey_op⟩, hc2_op⟩,
    hmkey_op⟩, hc3_op⟩, hiv_op⟩, hct_op⟩, hwire_op⟩, hmir_op⟩, hmi_op⟩, hfmac_op⟩,
    hmac_op⟩, hwmac_op⟩, hmac_len⟩, huntag⟩, hwire_len_lt⟩ := hrow
  have hcoins_sm : SafeMemo dagSize dagOp dagBytes S g pts (rnd (sendPtTs j + 1) (cls j)) := by
    rcases hcls j hj2 with h0 | h32 | h64
    · rw [h0]; exact safeMemo_randTerm_zero (sendPtTs j + 1)
    · rw [h32]
      have hcok : (decide (sendC32Id j < dagSize) &&
          isRandOp (dagOp (sendC32Id j)) (sendPtTs j + 1) 32) = true := by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide +kernel
      exact (termAt_rand_b (pts := pts) (hp.send_c32 j hj h32) hcok).safeMemo
    · rw [h64]
      have hcok : (decide (sendC64Id j < dagSize) &&
          isRandOp (dagOp (sendC64Id j)) (sendPtTs j + 1) 64) = true := by
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide +kernel
      exact (termAt_rand_b (pts := pts) (hp.send_c64 j hj h64) hcok).safeMemo
  obtain ⟨hspqr_next, hpqKey_sm, hpqMsg_sm⟩ := safeMemo_spqrSend hspqr hcoins_sm
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (by decide +kernel)
  have tseed : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).2 r.seed_id := by
    change TermAt dagSize dagOp dagBytes S g pts (hmac st.cks (litByte 1)) r.seed_id
    exact termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hseed_lt, hseed_op⟩) tcks tb01
  have tnck : TermAt dagSize dagOp dagBytes S g pts (kdfCk st.cks).1 r.nck_id := by
    change TermAt dagSize dagOp dagBytes S g pts (hmac st.cks (litByte 2)) r.nck_id
    exact termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hnck_lt, hnck_op⟩) tcks tb02
  obtain ⟨hi1, hi2, hi3⟩ := wmkInfo_termAt S g pts
  have tsalt_lit := termAt_litOf_b (S := S) (g := g) (pts := pts) hsalt_lt hsalt_op
  have hse_op : ∀ {x c i t : Nat} {p : HwBytes},
      isSymEncPtOp (dagOp x) c i t p = true → dagOp x = .symEncPt c i t p := by
    intro x c i t p h; cases hd : dagOp x <;> simp [isSymEncPtOp, hd] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  have htw_op : ∀ {x rk ct pq : Nat} {v : UInt8} {c p : UInt32} {ad : HwBytes},
      isTrWireOp (dagOp x) v rk c p ct pq ad = true → dagOp x = .trWire v rk c p ct pq ad := by
    intro x rk ct pq v c p ad h; cases hd : dagOp x <;> simp [isTrWireOp, hd] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h; rfl
  obtain ⟨tck0, tmk0, tiv0⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, kdf_of_isKdfOp hprk_op⟩ ⟨hckey_lt, kdf_of_isKdfOp hckey_op⟩
    ⟨hc2_lt, concat_of_isConcatOp hc2_op⟩ ⟨hmkey_lt, kdf_of_isKdfOp hmkey_op⟩
    ⟨hc3_lt, concat_of_isConcatOp hc3_op⟩ ⟨hiv_lt, kdf_of_isKdfOp hiv_op⟩ tsalt_lit tseed
  have hprk_lit : gamma rcprI0 S g (hmac (litOf (dagBytes r.salt_id)) (litOf (dagBytes r.seed_id))) =
      gamma rcprI0 S g (hmac (litOf (dagBytes r.salt_id)) (kdfCk st.cks).2) := by
    simp only [gamma_hmacE, gamma_litOf, tseed.gamma_eq]
  obtain ⟨hck_c, hmk_c, hiv_c⟩ := gamma_trMsgKeys_congr_prk hprk_lit
  have twire_lit_dummy : gamma rcprI0 S g
      (computeMac (trMsgKeys (litOf (dagBytes r.salt_id)) (litOf (dagBytes r.seed_id))).macKey
        (litOf (dagBytes r.myIk_id)) (litOf (dagBytes r.peerIk_id)) (litOf (dagBytes r.wire_id))) =
      dagBytes r.mac_id := by
    simp only [gamma_computeMacE, hmk_c, tmk0.gamma_eq, gamma_litOf]
    have hb_mir := dag_bytes_ok hmir_lt; rw [concat_of_isConcatOp hmir_op] at hb_mir
    simp only [dagOpBytesOk, beq_iff_eq] at hb_mir
    have hb_mi := dag_bytes_ok hmi_lt; rw [concat_of_isConcatOp hmi_op] at hb_mi
    simp only [dagOpBytesOk, beq_iff_eq] at hb_mi
    have hb_fm := dag_bytes_ok hfmac_lt; rw [kdf_of_isKdfOp hfmac_op] at hb_fm
    simp only [dagOpBytesOk, beq_iff_eq] at hb_fm
    have hb_m := dag_bytes_ok hmac_lt; rw [trunc8_of_isTrunc8Op hmac_op] at hb_m
    simp only [dagOpBytesOk, beq_iff_eq] at hb_m
    rw [← hb_mir, ← hb_mi, ← hb_fm, ← hb_m]
  have hb_ct := dag_bytes_ok hct_lt; rw [hse_op hct_op] at hb_ct
  simp only [dagOpBytesOk, beq_iff_eq] at hb_ct
  have hb_w := dag_bytes_ok hwire_lt; rw [htw_op hwire_op] at hb_w
  simp only [dagOpBytesOk, beq_iff_eq] at hb_w
  have hb_wm := dag_bytes_ok hwmac_lt; rw [concat_of_isConcatOp hwmac_op] at hb_wm
  simp only [dagOpBytesOk, beq_iff_eq] at hb_wm
  have hmsg_bytes : gamma rcprI0 S g
      (encMsg st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)) =
      dagBytes r.wire_id ++ dagBytes r.mac_id := by
    have h1 := hp.send_msg j hj
    rw [hclean] at h1
    exact h1.trans hb_wm
  have hparse : parseTrSignalMsg (cleanSendMsg cls j) =
      some (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)) := by
    rw [hclean]; exact parse_encMsg _ _ _ _
  have haddr := hp.send_addr j hj _ hparse
  obtain ⟨hpqKey_bs, hpqMsg_bs⟩ := encMsg_pins_pqKey_and_pqMsg rfl hmsg_bytes hmac_len hsalt_len
    huntag tseed.gamma_eq tpk.gamma_eq tmyIk.gamma_eq tpeerIk.gamma_eq (hp.send_pt j hj) haddr
    twire_lit_dummy.symm (hck_c.trans tck0.gamma_eq) (hiv_c.trans tiv0.gamma_eq)
    hb_ct.symm (by rw [hns, hpn]; exact hb_w.symm) hwire_len_lt
  obtain ⟨hpqKey_sh, hpqMsg_sh⟩ := spqrSend_shapes S g st.spqr (rnd (sendPtTs j + 1) (cls j))
  have hs_lit_eq : dagOp r.salt_id = .lit (dagBytes r.salt_id) := by
    cases hd : dagOp r.salt_id <;> simp [isLitOp, hd] at hsalt_op; exact congrArg DagOp.lit hsalt_op
  have hp_lit_eq : dagOp r.pq_id = .lit (dagBytes r.pq_id) := by
    cases hd : dagOp r.pq_id <;> simp [isLitOp, hd] at hpq_op; exact congrArg DagOp.lit hpq_op
  have tpqKey : TermAt dagSize dagOp dagBytes S g pts (pqKeyOf st (cls j) (sendPtTs j)) r.salt_id :=
    termAt_of_opaque dag_nodes_ok hsalt_lt hs_lit_eq hpqKey_bs
      (hpqKey_sh.trans (congrArg litOf hpqKey_bs)) hpqKey_sm
  have tpqMsg : TermAt dagSize dagOp dagBytes S g pts (pqMsgOf st (cls j) (sendPtTs j)) r.pq_id :=
    termAt_of_opaque dag_nodes_ok hpq_lt hp_lit_eq hpqMsg_bs
      (hpqMsg_sh.trans (congrArg litOf hpqMsg_bs)) hpqMsg_sm
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, kdf_of_isKdfOp hprk_op⟩ ⟨hckey_lt, kdf_of_isKdfOp hckey_op⟩
    ⟨hc2_lt, concat_of_isConcatOp hc2_op⟩ ⟨hmkey_lt, kdf_of_isKdfOp hmkey_op⟩
    ⟨hc3_lt, concat_of_isConcatOp hc3_op⟩ ⟨hiv_lt, kdf_of_isKdfOp hiv_op⟩ tpqKey tseed
  have tct := termAt_symEncPt dag_nodes_ok hct_lt (hse_op hct_op) tck tiv hpt_mem
    (hp.send_pt j hj) (sendPtBytes_len_lt8 hj2)
  have twire : TermAt dagSize dagOp dagBytes S g pts
      (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).wire
      r.wire_id := by
    dsimp only [encSig]
    exact termAt_trWire dag_nodes_ok hwire_lt (by rw [hns, hpn]; exact htw_op hwire_op) tpk tct tpqMsg haddr
  have tmac : TermAt dagSize dagOp dagBytes S g pts
      (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)).mac
      r.mac_id :=
    termAt_computeMac dag_nodes_ok ⟨hmir_lt, concat_of_isConcatOp hmir_op⟩
      ⟨hmi_lt, concat_of_isConcatOp hmi_op⟩ ⟨hfmac_lt, kdf_of_isKdfOp hfmac_op⟩
      ⟨hmac_lt, trunc8_of_isTrunc8Op hmac_op⟩ tmk tmyIk tpeerIk twire
  have twmac : TermAt dagSize dagOp dagBytes S g pts (cleanSendMsg cls j) (sendWmacId j) := by
    rw [hclean]; unfold sendMsgOf encMsg
    exact termAt_concat dag_nodes_ok hwmac_lt (concat_of_isConcatOp hwmac_op) twire tmac
  exact ⟨hspqr_next, tpqKey, tpqMsg, tnck, tseed, tct, twire, tmac, twmac⟩

theorem not_macTagForgery_of_sendStep
    {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {known : Bytes → Prop} {honest : List Bytes} {ctxs : List TrialCtx}
    {st : TRState} {j : Nat}
    (hj2 : j < 2)
    (hs : SendStepOut (cls := cls) S g pts st j)
    (hmem : pqKeyOf st (cls j) (sendPtTs j) ∈ honest) :
    ¬ MacTagForgeryOrCollision rcprI0 S g known honest
        (encSig st (rnd (sendPtTs j + 1) (cls j)) (pqKeyOf st (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32))
        ctxs := by
  have huntag_row : (dagBytes (getSendRow j).mac_id).take 4 ≠ compTag4 := by
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> decide +kernel
  refine not_macTagForgeryOrCollision_of_honest_mac hmem rfl ?_
  rw [hs.mac.gamma_eq]
  exact huntag_row

/-! ## 3. Receiver Trial Table Checkers & `safeMemo_of_seedTrialOk` -/

def trialRowMatches (salt seed pIk mIk wire : Nat) (r : TrialRow) : Bool :=
  decide (r.salt = salt) && decide (r.seed = seed) &&
  decide (r.pIk = pIk) && decide (r.mIk = mIk) && decide (r.wire = wire) &&
  decide (r.prk < dagSize) && isKdfOp (dagOp r.prk) salt seed &&
  decide (r.ck < dagSize) && isKdfOp (dagOp r.ck) r.prk wmkInfo1Id &&
  decide (r.c2 < dagSize) && isConcatOp (dagOp r.c2) r.ck wmkInfo2Id &&
  decide (r.mkId < dagSize) && isKdfOp (dagOp r.mkId) r.prk r.c2 &&
  decide (r.c3 < dagSize) && isConcatOp (dagOp r.c3) r.mkId wmkInfo3Id &&
  decide (r.iv < dagSize) && isKdfOp (dagOp r.iv) r.prk r.c3 &&
  decide (r.miR < dagSize) && isConcatOp (dagOp r.miR) mIk wire &&
  decide (r.mi < dagSize) && isConcatOp (dagOp r.mi) pIk r.miR &&
  decide (r.fmac < dagSize) && isKdfOp (dagOp r.fmac) r.mkId r.mi &&
  decide (r.mac < dagSize) && isTrunc8Op (dagOp r.mac) r.fmac

def seedEntryOk (e : SeedEntry) : Bool :=
  let (nSalts, seed, pIk, mIk, wire, ris) := e
  decide (ris.map (fun ri => (getTrialRow ri).salt) = honestSaltIds.take nSalts) &&
  ris.all (fun ri => trialRowMatches (getTrialRow ri).salt seed pIk mIk wire (getTrialRow ri))

def allSeedTuples : List (Nat × Nat × Nat × Nat × Nat) :=
  allSeedEntries.map fun (n, sd, p, m, w, _) => (n, sd, p, m, w)

private theorem allSeedEntries_ok_bool : allSeedEntries.all seedEntryOk = true := by
  decide +kernel

theorem all_seed_entries_ok : ∀ e ∈ allSeedEntries, seedEntryOk e = true :=
  List.all_eq_true.mp allSeedEntries_ok_bool

theorem safeMemo_of_trialRowMatches {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salt seed pIk mIk wire : Bytes} {salt_id seed_id pIk_id mIk_id wire_id : Nat}
    {row : TrialRow}
    (hrow : trialRowMatches salt_id seed_id pIk_id mIk_id wire_id row = true)
    (hsalt : TermAt dagSize dagOp dagBytes S g pts salt salt_id)
    (hseed : TermAt dagSize dagOp dagBytes S g pts seed seed_id)
    (hpIk : TermAt dagSize dagOp dagBytes S g pts pIk pIk_id)
    (hmIk : TermAt dagSize dagOp dagBytes S g pts mIk mIk_id)
    (hwire : TermAt dagSize dagOp dagBytes S g pts wire wire_id) :
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).cipherKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).macKey ∧
    SafeMemo dagSize dagOp dagBytes S g pts (trMsgKeys salt seed).iv ∧
    SafeMemo dagSize dagOp dagBytes S g pts
      (computeMac (trMsgKeys salt seed).macKey pIk mIk wire) := by
  unfold trialRowMatches at hrow
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hrow
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩,
    hprk_lt⟩, hprk_op⟩, hck_lt⟩, hck_op⟩, hc2_lt⟩, hc2_op⟩, hmk_lt⟩, hmk_op⟩,
    hc3_lt⟩, hc3_op⟩, hiv_lt⟩, hiv_op⟩, hmiR_lt⟩, hmiR_op⟩, hmi_lt⟩, hmi_op⟩,
    hfmac_lt⟩, hfmac_op⟩, hmac_lt⟩, hmac_op⟩ := hrow
  obtain ⟨hi1, hi2, hi3⟩ := wmkInfo_termAt S g pts
  obtain ⟨tck, tmk, tiv⟩ := termAt_trMsgKeys dag_nodes_ok hi1 hi2 hi3
    ⟨hprk_lt, kdf_of_isKdfOp hprk_op⟩ ⟨hck_lt, kdf_of_isKdfOp hck_op⟩
    ⟨hc2_lt, concat_of_isConcatOp hc2_op⟩ ⟨hmk_lt, kdf_of_isKdfOp hmk_op⟩
    ⟨hc3_lt, concat_of_isConcatOp hc3_op⟩ ⟨hiv_lt, kdf_of_isKdfOp hiv_op⟩ hsalt hseed
  have tmac := termAt_computeMac dag_nodes_ok
    ⟨hmiR_lt, concat_of_isConcatOp hmiR_op⟩ ⟨hmi_lt, concat_of_isConcatOp hmi_op⟩
    ⟨hfmac_lt, kdf_of_isKdfOp hfmac_op⟩ ⟨hmac_lt, trunc8_of_isTrunc8Op hmac_op⟩
    tmk hpIk hmIk hwire
  exact ⟨tck.safeMemo, tmk.safeMemo, tiv.safeMemo, tmac.safeMemo⟩

theorem safeMemo_of_seedTrialOk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {salts : List Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    {nSalts seed_id pIk_id mIk_id wire_id : Nat}
    (htup : (nSalts, seed_id, pIk_id, mIk_id, wire_id) ∈ allSeedTuples)
    (hsalts : ∀ salt ∈ salts, ∃ s_id ∈ honestSaltIds.take nSalts,
      TermAt dagSize dagOp dagBytes S g pts salt s_id)
    (hextra : ∀ t ∈ ctx.extra, SafeMemo dagSize dagOp dagBytes S g pts t)
    (hct : SafeMemo dagSize dagOp dagBytes S g pts msg.ciphertext)
    (hpIk : TermAt dagSize dagOp dagBytes S g pts ctx.peerIk pIk_id)
    (hmIk : TermAt dagSize dagOp dagBytes S g pts ctx.myIk mIk_id)
    (hwire : TermAt dagSize dagOp dagBytes S g pts msg.wire wire_id)
    (hseed : ∀ seed, ctx.seed? = some seed →
      TermAt dagSize dagOp dagBytes S g pts seed seed_id) :
    ∀ t ∈ trialTerms salts msg ctx, SafeMemo dagSize dagOp dagBytes S g pts t := by
  unfold allSeedTuples at htup
  obtain ⟨⟨n', sd', p', m', w', ris⟩, hent, heq⟩ := List.mem_map.mp htup
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
  have hok := all_seed_entries_ok _ hent
  unfold seedEntryOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hmap, hall⟩ := hok
  refine safeMemo_trialTerms hextra hct (fun seed hs salt hsalt_mem => ?_)
  obtain ⟨s_id, hs_mem, tsalt⟩ := hsalts salt hsalt_mem
  rw [← hmap] at hs_mem
  obtain ⟨ri, hri_mem, rfl⟩ := List.mem_map.mp hs_mem
  have hrow := List.all_eq_true.mp hall ri hri_mem
  exact safeMemo_of_trialRowMatches hrow tsalt (hseed seed hs) hpIk hmIk hwire

/-! ## 4. Certified `createChain` Combinator & Calls `0..3` Ratchet/Self-DH Walk -/

def checkCreateChain (rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id : Nat) : Bool :=
  decide (prk_id < dagSize) && decide (rk2_id < dagSize) &&
  decide (c2_id < dagSize) && decide (cks_id < dagSize) &&
  checkDhRand s1 pk1 s2 pk2 dh_id ts1 ts2 &&
  isKdfOp (dagOp prk_id) rk_id dh_id &&
  isKdfOp (dagOp rk2_id) prk_id 16 &&
  isConcatOp (dagOp c2_id) rk2_id 17 &&
  isKdfOp (dagOp cks_id) prk_id c2_id

theorem termAt_createChain_dhPk {S : OpaqueSymbolSemantics} {g : Ghost} {pts : List Bytes}
    {rk : Bytes}
    {rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id : Nat}
    (hok : checkCreateChain rk_id s1 pk1 ts1 s2 pk2 ts2 dh_id prk_id rk2_id c2_id cks_id = true)
    (trk : TermAt dagSize dagOp dagBytes S g pts rk rk_id)
    (tsk1 : TermAt dagSize dagOp dagBytes S g pts (rnd ts1 32) s1)
    (tpk1 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts1 32)) pk1)
    (tsk2 : TermAt dagSize dagOp dagBytes S g pts (rnd ts2 32) s2)
    (tpk2 : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd ts2 32)) pk2) :
    TermAt dagSize dagOp dagBytes S g pts (DY.DiffieHellman.dh (dhPk (rnd ts1 32)) (rnd ts2 32)) dh_id ∧
    TermAt dagSize dagOp dagBytes S g pts (hmac rk (DY.DiffieHellman.dh (dhPk (rnd ts1 32)) (rnd ts2 32))) prk_id ∧
    TermAt dagSize dagOp dagBytes S g pts (createChain rk (dhPk (rnd ts1 32)) (rnd ts2 32)).1 rk2_id ∧
    TermAt dagSize dagOp dagBytes S g pts (createChain rk (dhPk (rnd ts1 32)) (rnd ts2 32)).2 cks_id := by
  unfold checkCreateChain at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hprk_lt, hrk2_lt⟩, hc2_lt⟩, hcks_lt⟩,
    hdh_op⟩, hprk_op⟩, hrk2_op⟩, hc2_op⟩, hcks_op⟩ := hok
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (id := 2) (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (id := 3) (by decide +kernel)
  have twrlbl : TermAt dagSize dagOp dagBytes S g pts (lit "WhisperRatchet") 10 :=
    termAt_strLit (by decide) (by decide +kernel)
  have twri1 := termAt_concat_b (id := 16) (by decide +kernel) twrlbl tb01
  have twri2 := termAt_concat_b (id := 17) (by decide +kernel) twrlbl tb02
  have tdh := termAt_dh_b hdh_op tsk1 tpk1 tsk2 tpk2
  have tprk := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hprk_lt, hprk_op⟩) trk tdh
  have trk2 := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hrk2_lt, hrk2_op⟩) tprk twri1
  have tc2 := termAt_concat_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hc2_lt, hc2_op⟩) trk2 twri2
  have tcks := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hcks_lt, hcks_op⟩) tprk tc2
  rw [createChain_dhPk rk (rnd ts1 32) (rnd ts2 32)]
  exact ⟨tdh, tprk, trk2, tcks⟩

/-- Certified DAG witnesses for Calls `0..3`, Alice's Call 4 new chain, and Bob's Call 4 self-DH
trial chain. -/
structure Calls0to3At (cls : Nat → Nat) (S : OpaqueSymbolSemantics) (g : Ghost)
    (pts : List Bytes) : Prop where
  hh : HandshakeAt S g pts
  spqr_stA0 : SafeMemo dagSize dagOp dagBytes S g pts stA0.spqr
  out0 : SendStepOut (cls := cls) S g pts stA0 0
  t_dhsB1 : TermAt dagSize dagOp dagBytes S g pts dhsB1Clean 115
  t_pk5 : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsB1Clean) 116
  t_stB2_rk : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).rk 119
  t_stB2_cks : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).cks 121
  t_stB2_sid : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).sid 88
  t_cB_ck : TermAt dagSize dagOp dagBytes S g pts cBClean.chainKey 95
  t_cB'_ck : TermAt dagSize dagOp dagBytes S g pts cB'Clean.chainKey 99
  spqr_stB2 : SafeMemo dagSize dagOp dagBytes S g pts (stB2Clean cls).spqr
  out1 : SendStepOut (cls := cls) S g pts (stB2Clean cls) 1
  t_aliceNew_ck : TermAt dagSize dagOp dagBytes S g pts
    (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2 121
  t_aliceNew_nck : TermAt dagSize dagOp dagBytes S g pts
    (kdfCk (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2).1 125
  t_aliceNew_seed : TermAt dagSize dagOp dagBytes S g pts
    (kdfCk (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2).2 124
  t_selfB_ck : TermAt dagSize dagOp dagBytes S g pts
    (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2 145
  t_selfB_seed : TermAt dagSize dagOp dagBytes S g pts
    (kdfCk (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2).2 146
  t_selfB_nck : TermAt dagSize dagOp dagBytes S g pts
    (kdfCk (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2).1 147

theorem walk_calls_0_to_3 {cls : Nat → Nat} {S : OpaqueSymbolSemantics} {g : Ghost}
    {vis : List VisEntry}
    (hp : PrefixPinned cls S g vis 2) (hcls : ValidCoinLens cls) :
    Calls0to3At cls S g (plaintextTerms vis) := by
  set pts := plaintextTerms vis
  have hh := handshake_termAt (pts := pts) hp.base
  have hspqr0 : SafeMemo dagSize dagOp dagBytes S g pts stA0.spqr :=
    safeMemo_spqrInit hh.pqr.safeMemo (safeMemo_lit_short (by decide))
  have out0 : SendStepOut (cls := cls) S g pts stA0 0 :=
    send_step_at hp hcls (by decide) (by decide) (mem_pts_of_lt hp (by decide))
      rfl hspqr0 hh.pk4 hh.ik0s hh.ik1s hh.stA0_cks rfl rfl
  have t_dhsB1 : TermAt dagSize dagOp dagBytes S g pts dhsB1Clean 115 :=
    termAt_rand_b (hp.dhsB1 rfl) (by decide +kernel)
  have t_pk5 : TermAt dagSize dagOp dagBytes S g pts (dhPk dhsB1Clean) 116 :=
    termAt_dhPk_b (by decide +kernel) t_dhsB1
  have hcc1 : createChain keys1.rk (dhPk dhsA) spkB = (stA0.rk, stA0.cks) :=
    createChain_comm keys1.rk dhsA spkB
  obtain ⟨_, _, t_rkB0, t_cksB0⟩ :=
    termAt_createChain_dhPk (rk_id := 93) (s1 := 67) (pk1 := 69) (ts1 := 24)
      (s2 := 115) (pk2 := 116) (ts2 := 38)
      (dh_id := 117) (prk_id := 118) (rk2_id := 119) (c2_id := 120) (cks_id := 121)
      (by decide +kernel) hh.stA0_rk hh.t_dhsA hh.pk4 t_dhsB1 t_pk5
  have hrkB_eq : (stB2Clean cls).rk = (createChain stA0.rk (dhPk dhsA) dhsB1Clean).1 := by
    show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1Clean).1 = _
    rw [hcc1]
  have hcksB_eq : (stB2Clean cls).cks = (createChain stA0.rk (dhPk dhsA) dhsB1Clean).2 := by
    show (createChain (createChain keys1.rk (dhPk dhsA) spkB).1 (dhPk dhsA) dhsB1Clean).2 = _
    rw [hcc1]
  have t_stB2_rk : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).rk 119 :=
    hrkB_eq ▸ t_rkB0
  have t_stB2_cks : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).cks 121 :=
    hcksB_eq ▸ t_cksB0
  have hsidB_eq : (stB2Clean cls).sid = stA0.sid := by
    show DY.Concat.concat (DY.X25519.normalizeX25519Key (dhPk dhsA)) keys1.rk = _
    rw [norm_dhPk dhsA]; rfl
  have t_stB2_sid : TermAt dagSize dagOp dagBytes S g pts (stB2Clean cls).sid 88 :=
    hsidB_eq ▸ hh.stA0_sid
  have hcB_eq : cBClean.chainKey = stA0.cks := by
    show (createChain keys1.rk (dhPk dhsA) spkB).2 = _
    rw [hcc1]
  have hcB'_eq : cB'Clean.chainKey = (stA1Clean cls).cks := by
    show (kdfCk cBClean.chainKey).1 = (kdfCk stA0.cks).1
    rw [hcB_eq]
  have hspqr_b2 : SafeMemo dagSize dagOp dagBytes S g pts (stB2Clean cls).spqr :=
    memoOK_spqrRecvState_pack
      (safeMemo_spqrInit hh.pqr.safeMemo (safeMemo_lit_short (by decide))) out0.pqMsg.safeMemo
  have out1 : SendStepOut (cls := cls) S g pts (stB2Clean cls) 1 :=
    send_step_at hp hcls (by decide) (by decide) (mem_pts_of_lt hp (by decide))
      rfl hspqr_b2 t_pk5 hh.ik1s hh.ik0s t_stB2_cks rfl rfl
  have haliceNew_eq : (createChain stA0.rk (dhPk dhsB1Clean) dhsA).2 = (stB2Clean cls).cks := by
    rw [hcksB_eq, createChain_comm stA0.rk dhsB1Clean dhsA]
  obtain ⟨_, _, _, t_selfB_ck⟩ :=
    termAt_createChain_dhPk (rk_id := 119) (s1 := 115) (pk1 := 116) (ts1 := 38)
      (s2 := 115) (pk2 := 116) (ts2 := 38)
      (dh_id := 141) (prk_id := 142) (rk2_id := 143) (c2_id := 144) (cks_id := 145)
      (by decide +kernel) t_stB2_rk t_dhsB1 t_pk5 t_dhsB1 t_pk5
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 := termAt_lit_b (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 := termAt_lit_b (by decide +kernel)
  have t_selfB_seed : TermAt dagSize dagOp dagBytes S g pts
      (kdfCk (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2).2 146 :=
    termAt_kdf_b (by decide +kernel) t_selfB_ck tb01
  have t_selfB_nck : TermAt dagSize dagOp dagBytes S g pts
      (kdfCk (createChain (stB2Clean cls).rk (dhPk dhsB1Clean) dhsB1Clean).2).1 147 :=
    termAt_kdf_b (by decide +kernel) t_selfB_ck tb02
  exact ⟨hh, hspqr0, out0, t_dhsB1, t_pk5, t_stB2_rk, t_stB2_cks, t_stB2_sid,
    hcB_eq ▸ hh.stA0_cks, hcB'_eq ▸ out0.cks_next, hspqr_b2, out1,
    haliceNew_eq ▸ t_stB2_cks, haliceNew_eq ▸ out1.cks_next, haliceNew_eq ▸ out1.seed,
    t_selfB_ck, t_selfB_seed, t_selfB_nck⟩

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.RecvNoCollision.SendTrials
