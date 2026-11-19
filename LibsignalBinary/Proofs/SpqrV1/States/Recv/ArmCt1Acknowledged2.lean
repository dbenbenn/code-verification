/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Acknowledged` Arm, Part 2

**Checked by Lean.** Shared `Ok(V1Recv)` tail (`+4924 -> +18996`), no-op Branch B
(`+4516 -> +4924 -> s0.x30`), pure `Ct1Acknowledged.recv_ek_chunk` classification, and Branch C
`recv_ek_chunk` call (`+4448 -> +4468`), error path, and `.stillReceiving` path.
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## 1. Shared Tail (`+4924 -> +18996`) and Branch B (`+4516 -> +4924 -> s0.x30`) -/

/-- Updated `SendEkSpills` after `+4924..+5056` (`0x56790..0x56810 -> 0x59e88`). -/
@[expose] def ct1AckSpills4924 (s : State) (sp : SendEkSpills) : SendEkSpills :=
  { sp with
    b2 := { sp.b2 with w8 := noneCap }
    b3 := { sp.b3 with w4 := s.readReg64 .x15 }
    b4 := { sp.b4 with w2 := s.readReg64 .x7, w5 := s.readReg64 .x26 }
    b5 := { sp.b5 with w5 := s.readReg64 .x6, w9 := s.readReg64 .x11 } }

/-- Updated `SendEkSpills` after `+4516..+4924` (`0x565f8..0x56790`). -/
@[expose] def ct1AckSpills4516 (sp : SendEkSpills) (w : Words66) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w1 := w.b3.w5, w4 := w.b3.w2, w5 := w.b4.w1, w7 := w.b3.w8, w8 := w.b3.w4, w9 := w.b3.w3 }
    b1 := { sp.b1 with w3 := w.b3.w6, w5 := w.b3.w7, w8 := w.b1.w5 }
    b2 := { sp.b2 with w3 := w.b4.w3, w5 := w.b0.w1, w7 := 11#64, w9 := w.b4.w2 }
    b3 := { sp.b3 with w0 := w.b5.w8, w1 := w.w62, w2 := w.b1.w8, w3 := w.b2.w1, w5 := w.b0.w7, w6 := w.b1.w3, w7 := w.b2.w5, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w1 := w.b1.w2, w3 := w.b1.w0, w4 := w.b2.w2, w6 := w.b0.w4, w7 := w.b1.w1, w8 := w.b2.w0, w9 := w.b2.w3 }
    b5 := { sp.b5 with w0 := w.b0.w9, w1 := w.b4.w4, w2 := w.b1.w4, w3 := w.b0.w8, w4 := w.b1.w7, w6 := w.b0.w3, w7 := w.b2.w4, w8 := w.b4.w6 }
    w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6
    q3c0 := w.q60 }

theorem writebackWords63_ct1Ack_noop (s2 s3 : State) (sp : SendEkSpills) (w : Words66)
    (h2_x0 : s2.readReg64 .x0 = w.b5.w5) (h2_x1 : s2.readReg64 .x1 = w.b0.w0) (h2_x2 : s2.readReg64 .x2 = w.b5.w7)
    (h2_x3 : s2.readReg64 .x3 = w.b2.w9) (h2_x4 : s2.readReg64 .x4 = w.b4.w9) (h2_x5 : s2.readReg64 .x5 = w.b4.w8)
    (h2_x6 : s2.readReg64 .x6 = w.b5.w0) (h2_x7 : s2.readReg64 .x7 = w.b1.w9) (h2_x10 : s2.readReg64 .x10 = w.b1.w6)
    (h2_x11 : s2.readReg64 .x11 = w.b5.w4) (h2_x12 : s2.readReg64 .x12 = w.b4.w0) (h2_x13 : s2.readReg64 .x13 = w.b5.w1)
    (h2_x15 : s2.readReg64 .x15 = w.b2.w7) (h2_x16 : s2.readReg64 .x16 = w.b4.w7) (h2_x17 : s2.readReg64 .x17 = w.b4.w5)
    (h2_x18 : s2.readReg64 .x18 = w.b5.w3) (h2_x22 : s2.readReg64 .x22 = w.b5.w2) (h2_x24 : s2.readReg64 .x24 = w.b3.w1)
    (h2_x25 : s2.readReg64 .x25 = w.b3.w9) (h2_x26 : s2.readReg64 .x26 = w.b0.w5) (h2_x30 : s2.readReg64 .x30 = w.b5.w9)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x25) (h3_x1 : s3.readReg64 .x1 = s2.readReg64 .x1)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x2) (h3_x3 : s3.readReg64 .x3 = s2.readReg64 .x3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = s2.readReg64 .x5)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x12) (h3_x7 : s3.readReg64 .x7 = (ct1AckSpills4516 sp w).b0.w7)
    (h3_x8 : s3.readReg64 .x8 = (ct1AckSpills4516 sp w).b2.w5) (h3_x9 : s3.readReg64 .x9 = (ct1AckSpills4516 sp w).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = (ct1AckSpills4516 sp w).b0.w1) (h3_x11 : s3.readReg64 .x11 = (ct1AckSpills4516 sp w).b0.w8)
    (h3_x12 : s3.readReg64 .x12 = (ct1AckSpills4516 sp w).b0.w9) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x22)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x18) (h3_x15 : s3.readReg64 .x15 = (ct1AckSpills4516 sp w).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x0) (h3_x17 : s3.readReg64 .x17 = s2.readReg64 .x17)
    (h3_x20 : s3.readReg64 .x20 = s2.readReg64 .x30) (h3_x21 : s3.readReg64 .x21 = (ct1AckSpills4516 sp w).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = s2.readReg64 .x13) (h3_x23 : s3.readReg64 .x23 = (ct1AckSpills4516 sp w).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = s2.readReg64 .x24) (h3_x25 : s3.readReg64 .x25 = (ct1AckSpills4516 sp w).b0.w4)
    (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x16) (h3_x27 : s3.readReg64 .x27 = s2.readReg64 .x10)
    (h3_x28 : s3.readReg64 .x28 = (ct1AckSpills4516 sp w).b1.w5) (h3_x30 : s3.readReg64 .x30 = (ct1AckSpills4516 sp w).b0.w5) :
    writebackWords63 s3 (ct1AckSpills4924 s2 (ct1AckSpills4516 sp w)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5, q60 := w.q60, w62 := w.w62 } := by
  dsimp only [writebackWords63, ct1AckSpills4924, ct1AckSpills4516]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9,
    h3_x10, h3_x11, h3_x12, h3_x13, h3_x14, h3_x15, h3_x16, h3_x17, h3_x20,
    h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30, ct1AckSpills4516,
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x10, h2_x11,
    h2_x12, h2_x13, h2_x15, h2_x16, h2_x17, h2_x18, h2_x22, h2_x24, h2_x25, h2_x26, h2_x30]

theorem chunkedCt1AcknowledgedAt_dup_pts_len (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1AcknowledgedAt A a st ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗ chunkedCt1AcknowledgedAt A a st := by
  unfold chunkedCt1AcknowledgedAt
  refine Entails.trans (sepConj_mono_right (polyDecoderAt_dup_pts_len A (a + 128#64) st.receiving_ek)) ?_
  exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] addChunkTotal decodedMessageTotal in
theorem ct1Acknowledged_recv_ek_chunk_cases_of_preInv {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (hlen : st.receiving_ek.pts.length = 16)
    (hinv : statesRecvPreInv (.ct1Acknowledged st)) :
    ∃ res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)),
      st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res ∧
      (∀ e, res = .error e → e = .erroneousDataReceived) := by
  rcases hinv with ⟨hsort, hes, hct1, hmac⟩
  have hadd : spqrPolyApi.add_chunk st.receiving_ek chunk =
      .ok (addChunkTotal st.receiving_ek chunk) := by
    dsimp only [spqrPolyApi, liftSpqrPanic]
    rw [addChunk_eq_ok st.receiving_ek chunk hlen]; rfl
  have hlen' := addChunkTotal_pts_length st.receiving_ek chunk hlen
  have hsort' := (addChunkBsearch_eq_addChunkTotal st.receiving_ek chunk hlen hsort).2
  have hdec : spqrPolyApi.decoded_message (addChunkTotal st.receiving_ek chunk) =
      .ok (decodedMessageTotal (addChunkTotal st.receiving_ek chunk)) := by
    change ((addChunkTotal st.receiving_ek chunk).decodedMessage).mapError PolyPanic.toSpqrPanic = _
    rw [decodedMessage_eq_ok (addChunkTotal st.receiving_ek chunk) hlen' hsort']; rfl
  unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hadd]; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind]
  rw [hdec]; dsimp only [StatesResult.ofPanic, Bind.bind, Except.bind]
  cases hdm : decodedMessageTotal (addChunkTotal st.receiving_ek chunk) with
  | none =>
    exact ⟨.ok (.stillReceiving { uc := st.uc, receiving_ek := addChunkTotal st.receiving_ek chunk }),
      rfl, fun _ h => by cases h⟩
  | some ek =>
    dsimp only []
    unfold Unchunked.SendCt.Ct1Sent.recv_ek
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    cases hmatch : ek_matches_header K ek st.uc.hdr
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨.error .erroneousDataReceived, rfl, fun _ h => (Except.error.inj h).symm⟩
    · simp only [↓reduceIte]
      have hek : ek.length = 1152 := by
        unfold ek_matches_header MlKem.validPkBytes at hmatch
        simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
        exact hmatch.1.2
      let uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F) :=
        { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := ek, ct1 := st.uc.ct1 }
      obtain ⟨uc2, ct2, mac, enc2, hsend, henc2⟩ :=
        send_ct2_and_encoder_eq_ok_of_lengths K uc_ek hes hek hct1 hmac
      rw [show ({ epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := ek, ct1 := st.uc.ct1 } :
            Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) = uc_ek from rfl,
          hsend]
      dsimp only []
      rw [henc2]
      exact ⟨.ok (.done { uc := uc2, sending_ct2 := enc2 }), rfl, fun _ h => by cases h⟩

/-! ## 3. Branch C Call (`+4448 -> +4468`) and Error Path (`+4468 -> +19324 -> s0.x30`) -/

theorem stackAt_statesRecvCallee_split_ct1AckRecvEkChunk (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 336 ∗ stackAt fsp ct1AcknowledgedRecvEkChunkStack :=
  stackAt_statesRecvCallee_eq_ct1AcknowledgedRecvEkChunk fsp

/-- Framed call rule for `ct1AcknowledgedRecvEkChunkSpec A F K b` (`0x5e9c8`), bridging from `SepWP`
    before the call to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to `SepWP` after the call. -/
theorem call_ct1AcknowledgedRecvEkChunk {A : RustAlloc} {F : ShaCompress} {K : MlKem} {b : BitVec 64}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry (ct1AcknowledgedRecvEkChunkSpec A F K b))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hstrict : PolyDecoderStrictSorted st.receiving_ek)
    (hrecv : st.recv_ek_chunk K st.uc.epoch chunk = StatesResult.ofError res)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA 528 ∗
      chunkedCt1AcknowledgedAt A stA st ∗ chunkAt chunkA chunk ∗
      unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((ct1AcknowledgedRecvEkChunkResAt A outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, res⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [ct1AcknowledgedRecvEkChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hstrict, hrecv⟩, hm⟩
  · dsimp only [ct1AcknowledgedRecvEkChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [ct1AcknowledgedRecvEkChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (ct1AcknowledgedRecvEkChunkResAt A outA res ∗
          memRegion stA 528 ∗ chunkAt chunkA chunk ∗
          unchunkedSendCt2RoAt b ∗ tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack) ∗ Frame =
        (ct1AcknowledgedRecvEkChunkResAt A outA res ∗
          (memRegion stA 528 ∗
            (chunkAt chunkA chunk ∗
              (unchunkedSendCt2RoAt b ∗
                (tokenInitAt b ∗ (reduceTableAt b ∗ (A.pool ∗ stackAt sp_call ct1AcknowledgedRecvEkChunkStack))))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

theorem ct1Ack_byte_memRegion7_extract_word (a : BitVec 64) (b0 : BitVec 8) :
    (a ↦₈ b0) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ w : BitVec 64,
        ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ b0 :: bs = unpack64 w⌝ ∗ (a ↦₆₄ w) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [← sepConj_assoc, sepConj_comm (a ↦₈ b0), sepConj_assoc]
  apply Entails.pure_left; intro hbs
  obtain ⟨w, hw⟩ := exists_word_of_length_8 (b0 :: bs) (by simp [hbs])
  refine Entails.sepExists_right w (Entails.pure_right ⟨bs, hbs, hw⟩ ?_)
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, sepConj_comm]
  exact Entails.refl _

theorem ct1Ack_byte_memRegion7_recompose_word (dst : BitVec 64) (b0 : BitVec 8) (w : BitVec 64)
    (hw : ∃ bs : List (BitVec 8), bs.length = 7 ∧ b0 :: bs = unpack64 w) :
    (dst ↦₆₄ w) ⊢ (dst ↦₈ b0) ∗ memRegion (dst + 1#64) 7 := by
  rcases hw with ⟨bs, hbs, hw⟩
  rw [pointsTo64_eq_pointsToBytes, ← hw, pointsToBytes_cons, ← hbs]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (dst + 1#64) bs)

theorem ct1Ack_memRegion_out_960_split_4words (outA : BitVec 64) :
    memRegion outA v1RecvSize ⊢
      ∃∗ o0 : BitVec 64, ∃∗ o1 : BitVec 64, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
        (outA ↦₆₄ o0) ∗ ((outA + 8#64) ↦₆₄ o1) ∗ ((outA + 16#64) ↦₆₄ o2) ∗ ((outA + 24#64) ↦₆₄ o3) ∗
        memRegion (outA + 32#64) 928 := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split' (b := outA) (n := 8) (k := 952) (b' := outA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 8) (k := 944) (b' := outA + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936) (b' := outA + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928) (b' := outA + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA, ProofLib.memRegion_eight (outA + 8#64),
      ProofLib.memRegion_eight (outA + 16#64), ProofLib.memRegion_eight (outA + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro o3; apply Entails.sepExists_elim; intro o2
  apply Entails.sepExists_elim; intro o1; apply Entails.sepExists_elim; intro o0
  exact Entails.sepExists_right o0 (Entails.sepExists_right o1 (Entails.sepExists_right o2
    (Entails.sepExists_right o3 (Entails.refl _))))

theorem ct1Ack_err_1856_split {A : RustAlloc} {F : ShaCompress} (fsp : BitVec 64) (err : Error) :
    ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.error err) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ⌜∃ bs : List (BitVec 8), bs.length = 7 ∧ 12#8 :: bs = unpack64 w1⌝ ∗
        ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
        ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗ memRegion (fsp + 1888#64) 496 := by
  dsimp only [ct1AcknowledgedRecvEkChunkResAt, none2Cap]
  rw [ProofLib.memRegion_split' (b := (fsp + 1856#64) + 9#64) (n := 7) (k := 512)
        (b' := fsp + 1872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1872#64) (n := 8) (k := 504)
        (b' := fsp + 1880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1880#64) (n := 8) (k := 496)
        (b' := fsp + 1888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 1872#64), ProofLib.memRegion_eight (fsp + 1880#64)]
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1865 : (fsp + 1856#64) + 9#64 = (fsp + 1864#64) + 1#64 := by bv_omega
  rw [h1864, h1865]
  refine Entails.trans (Entails.of_eq (show _ =
    (((fsp + 1864#64) ↦₈ 12#8) ∗ memRegion ((fsp + 1864#64) + 1#64) 7) ∗
    ((fsp + 1856#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
    (∃∗ w2 : BitVec 64, ((fsp + 1872#64) ↦₆₄ w2)) ∗
    (∃∗ w3 : BitVec 64, ((fsp + 1880#64) ↦₆₄ w3)) ∗ memRegion (fsp + 1888#64) 496 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (ct1Ack_byte_memRegion7_extract_word (fsp + 1864#64) 12#8)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3; apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w1
  exact Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.of_eq (by ac_rfl))))

@[expose] def ct1AckSpillsRestAt (fsp : BitVec 64) (sp : SendEkSpills) : SepProp :=
  words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗ words10At (fsp + 168#64) sp.b2 ∗
  words10At (fsp + 248#64) sp.b3 ∗ words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
  ((fsp + 488#64) ↦₆₄ sp.w60) ∗ ((fsp + 504#64) ↦₆₄ sp.w62) ∗
  ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗
  ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗ ((fsp + 560#64) ↦₆₄ sp.w230) ∗ ((fsp + 960#64) ↦₁₂₈ sp.q3c0)

theorem ct1AckSpillsAt_split_w61 (fsp : BitVec 64) (sp : SendEkSpills) :
    sendEkSpillsAt fsp sp = ((fsp + 496#64) ↦₆₄ sp.w61) ∗ ct1AckSpillsRestAt fsp sp := by
  dsimp only [sendEkSpillsAt, ct1AckSpillsRestAt]; ac_rfl

theorem ct1AckSpillsAt_rejoin_w61 (fsp : BitVec 64) (sp : SendEkSpills) (w3 : BitVec 64) :
    ((fsp + 496#64) ↦₆₄ w3) ∗ ct1AckSpillsRestAt fsp sp = sendEkSpillsAt fsp { sp with w61 := w3 } := by
  dsimp only [sendEkSpillsAt, ct1AckSpillsRestAt]; ac_rfl

theorem ct1Ack_err_1856_rejoin_880 (fsp w0 w1 w2 w3 : BitVec 64) :
    ((fsp + 1856#64) ↦₆₄ w0) ∗ ((fsp + 1864#64) ↦₆₄ w1) ∗
      ((fsp + 1872#64) ↦₆₄ w2) ∗ ((fsp + 1880#64) ↦₆₄ w3) ∗
      memRegion (fsp + 1888#64) 496 ∗ memRegion (fsp + 2384#64) 352 ⊢
      memRegion (fsp + 1856#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 8) (k := 872) (b' := fsp + 1864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1864#64) (n := 8) (k := 864) (b' := fsp + 1872#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1872#64) (n := 8) (k := 856) (b' := fsp + 1880#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1880#64) (n := 8) (k := 848) (b' := fsp + 1888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1888#64) (n := 496) (k := 352) (b' := fsp + 2384#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 1856#64) w0)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 1864#64) w1)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 1872#64) w2)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 1880#64) w3))))

theorem ct1Ack_err_out_recompose (A : RustAlloc) {F : ShaCompress} (outA w1 w2 w3 : BitVec 64)
    (hw1 : ∃ bs : List (BitVec 8), bs.length = 7 ∧ 12#8 :: bs = unpack64 w1) :
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₆₄ w1) ∗
      ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928 ⊢
      resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  rw [ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944) (b' := outA + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936) (b' := outA + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928) (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (ct1Ack_byte_memRegion7_recompose_word (outA + 8#64) 12#8 w1 hw1))) ?_
  rw [show (outA + 8#64) + 1#64 = outA + 9#64 from by bv_omega]
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 12#8) ∗
    (memRegion (outA + 9#64) 7 ∗ ((outA + 16#64) ↦₆₄ w2) ∗ ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (outA + 16#64) w2)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (outA + 24#64) w3)))))

theorem ct1Ack_cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  apply beq_false_of_ne; intro heq
  have h1 : (cap + 2#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  omega

theorem ct1Ack_cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  apply beq_false_of_ne; intro heq
  have h1 : (cap + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  omega

@[expose] def ct1AckUnusedRestAt (fsp : BitVec 64) : SepProp :=
  memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
  memRegion (fsp + 2736#64) 912 ∗ memRegion (fsp + 3672#64) 8 ∗ memRegion (fsp + 3696#64) 448

theorem sendEkUnusedAt_split_e40 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qe40 : BitVec 128, ∃∗ we50 : BitVec 64, ∃∗ qe60 : BitVec 128,
        ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗
        ((fsp + 3680#64) ↦₁₂₈ qe60) ∗ ct1AckUnusedRestAt fsp := by
  dsimp only [sendEkUnusedAt, ct1AckUnusedRestAt]
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 912) (k := 496) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 16) (k := 480) (b' := fsp + 3664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 8) (k := 472) (b' := fsp + 3672#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3672#64) (n := 8) (k := 464) (b' := fsp + 3680#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3680#64) (n := 16) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 3664#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono (memRegion_16_entails_128_recv (fsp + 3648#64))
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 3680#64)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro qe60; apply Entails.sepExists_elim; intro we50
  apply Entails.sepExists_elim; intro qe40
  exact Entails.sepExists_right qe40 (Entails.sepExists_right we50
    (Entails.sepExists_right qe60 (Entails.of_eq (by ac_rfl))))

theorem ct1AckUnusedRest_entails_sendEkUnusedAt (fsp : BitVec 64) (qe40 : BitVec 128) (we50 : BitVec 64) (qe60 : BitVec 128) :
    ((fsp + 3648#64) ↦₁₂₈ qe40) ∗ ((fsp + 3664#64) ↦₆₄ we50) ∗
      ((fsp + 3680#64) ↦₁₂₈ qe60) ∗ ct1AckUnusedRestAt fsp ⊢
      sendEkUnusedAt fsp := by
  dsimp only [sendEkUnusedAt, ct1AckUnusedRestAt]
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 912) (k := 496) (b' := fsp + 3648#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3648#64) (n := 16) (k := 480) (b' := fsp + 3664#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3664#64) (n := 8) (k := 472) (b' := fsp + 3672#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3672#64) (n := 8) (k := 464) (b' := fsp + 3680#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3680#64) (n := 16) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2736#64) 912 ∗ ((fsp + 3648#64) ↦₁₂₈ qe40) ∗
    (((fsp + 3664#64) ↦₆₄ we50) ∗ memRegion (fsp + 3672#64) 8 ∗
     ((fsp + 3680#64) ↦₁₂₈ qe60) ∗ memRegion (fsp + 3696#64) 448) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 3648#64) qe40)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 3664#64) we50)
        (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 3680#64) qe60))))))))

@[expose] def ct1AckSpillsStill4924 (sp : SendEkSpills) (w : Words66) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w1 := w.b3.w5, w2 := w.b3.w2, w4 := w.b3.w2, w5 := w.b4.w1, w7 := w.b3.w8, w8 := w.b3.w4, w9 := w.b3.w3 }
    b1 := { sp.b1 with w0 := w.b5.w7, w1 := w.b5.w5, w3 := w.b3.w6, w5 := w.b3.w7, w6 := w.b0.w1, w7 := w.b5.w9, w8 := w.b1.w5, w9 := w.b1.w6 }
    b2 := { sp.b2 with w3 := w.b4.w3, w5 := w.b0.w1, w7 := 11#64, w8 := w.b2.w0, w9 := w.b4.w2 }
    b3 := { sp.b3 with w0 := w.b5.w8, w1 := w.w62, w2 := w.b1.w8, w3 := w.b2.w1, w4 := w.b2.w8, w5 := w.b0.w7, w6 := w.b1.w3, w7 := w.b2.w5, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w1 := w.b1.w2, w2 := w.b1.w9, w3 := w.b1.w0, w4 := w.b2.w2, w5 := w.b0.w6, w6 := w.b0.w4, w7 := w.b1.w1, w8 := w.b2.w0, w9 := w.b2.w3 }
    b5 := { sp.b5 with w0 := w.b0.w9, w1 := w.b4.w4, w2 := w.b1.w4, w3 := w.b0.w8, w4 := w.b1.w7, w6 := w.b0.w3, w7 := w.b2.w4, w8 := w.b4.w6 }
    w60 := w.b5.w6, w61 := w.b0.w2, w62 := w.b0.w6, q3c0 := w.q60 }

theorem writebackWords63_ct1Ack_still (s2 s3 : State) (sp : SendEkSpills) (w : Words66)
    (h2_x0 : s2.readReg64 .x0 = w.b5.w5) (h2_x1 : s2.readReg64 .x1 = w.b0.w0) (h2_x2 : s2.readReg64 .x2 = w.b5.w7)
    (h2_x3 : s2.readReg64 .x3 = w.b2.w9) (h2_x4 : s2.readReg64 .x4 = w.b4.w9) (h2_x5 : s2.readReg64 .x5 = w.b4.w8)
    (h2_x6 : s2.readReg64 .x6 = w.b5.w0) (h2_x7 : s2.readReg64 .x7 = w.b1.w9) (h2_x10 : s2.readReg64 .x10 = w.b1.w6)
    (h2_x11 : s2.readReg64 .x11 = w.b5.w4) (h2_x12 : s2.readReg64 .x12 = w.b4.w0) (h2_x13 : s2.readReg64 .x13 = w.b5.w1)
    (h2_x15 : s2.readReg64 .x15 = w.b2.w7) (h2_x16 : s2.readReg64 .x16 = w.b4.w7) (h2_x17 : s2.readReg64 .x17 = w.b4.w5)
    (h2_x18 : s2.readReg64 .x18 = w.b5.w3) (h2_x22 : s2.readReg64 .x22 = w.b5.w2) (h2_x24 : s2.readReg64 .x24 = w.b3.w1)
    (h2_x25 : s2.readReg64 .x25 = w.b3.w9) (h2_x26 : s2.readReg64 .x26 = w.b0.w5) (h2_x30 : s2.readReg64 .x30 = w.b5.w9)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x25) (h3_x1 : s3.readReg64 .x1 = s2.readReg64 .x1)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x2) (h3_x3 : s3.readReg64 .x3 = s2.readReg64 .x3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = s2.readReg64 .x5)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x12) (h3_x7 : s3.readReg64 .x7 = (ct1AckSpillsStill4924 sp w).b0.w7)
    (h3_x8 : s3.readReg64 .x8 = (ct1AckSpillsStill4924 sp w).b2.w5) (h3_x9 : s3.readReg64 .x9 = (ct1AckSpillsStill4924 sp w).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = (ct1AckSpillsStill4924 sp w).b0.w1) (h3_x11 : s3.readReg64 .x11 = (ct1AckSpillsStill4924 sp w).b0.w8)
    (h3_x12 : s3.readReg64 .x12 = (ct1AckSpillsStill4924 sp w).b0.w9) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x22)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x18) (h3_x15 : s3.readReg64 .x15 = (ct1AckSpillsStill4924 sp w).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x0) (h3_x17 : s3.readReg64 .x17 = s2.readReg64 .x17)
    (h3_x20 : s3.readReg64 .x20 = s2.readReg64 .x30) (h3_x21 : s3.readReg64 .x21 = (ct1AckSpillsStill4924 sp w).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = s2.readReg64 .x13) (h3_x23 : s3.readReg64 .x23 = (ct1AckSpillsStill4924 sp w).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = s2.readReg64 .x24) (h3_x25 : s3.readReg64 .x25 = (ct1AckSpillsStill4924 sp w).b0.w4)
    (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x16) (h3_x27 : s3.readReg64 .x27 = s2.readReg64 .x10)
    (h3_x28 : s3.readReg64 .x28 = (ct1AckSpillsStill4924 sp w).b1.w5) (h3_x30 : s3.readReg64 .x30 = (ct1AckSpillsStill4924 sp w).b0.w5) :
    writebackWords63 s3 (ct1AckSpills4924 s2 (ct1AckSpillsStill4924 sp w)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5, q60 := w.q60, w62 := w.w62 } := by
  dsimp only [writebackWords63, ct1AckSpills4924, ct1AckSpillsStill4924]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9,
    h3_x10, h3_x11, h3_x12, h3_x13, h3_x14, h3_x15, h3_x16, h3_x17, h3_x20,
    h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30, ct1AckSpillsStill4924,
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x10, h2_x11,
    h2_x12, h2_x13, h2_x15, h2_x16, h2_x17, h2_x18, h2_x22, h2_x24, h2_x25, h2_x26, h2_x30]

end CryptoVerification.SpqrV1.States.Recv

