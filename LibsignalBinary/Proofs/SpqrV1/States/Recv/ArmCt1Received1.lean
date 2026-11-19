/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Received` Arm, Part 1

**Checked by Lean.** Stack/writeback helpers, pure `Ct1Received::recv_ct2_chunk` unfolding,
post-call writeback blocks, and the `msg.epoch > st.uc.epoch` and `msg.epoch < st.uc.epoch` paths
of `.ct1Received` (`0x55908`, `+1204`).
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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48

/-! ## 1. Stack & Writeback Entailment Helpers -/

theorem sendEkUnusedAt_split_ac0 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qac0 : BitVec 128,
        ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2736#64) 16 ∗
        memRegion (fsp + 2768#64) 1376 := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376)
        (b' := fsp + 2768#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 2752#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qac0
  refine Entails.sepExists_right qac0 ?_
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_ac0 (fsp : BitVec 64) (qac0 : BitVec 128) :
    ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2736#64) 16 ∗
    memRegion (fsp + 2768#64) 1376 ⊢
      sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 16) (k := 1392)
        (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 16) (k := 1376)
        (b' := fsp + 2768#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
    (memRegion (fsp + 2736#64) 16 ∗ (((fsp + 2752#64) ↦₁₂₈ qac0) ∗ memRegion (fsp + 2768#64) 1376)) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 2752#64) qac0)))))

theorem none_tail_entails_optEpochSecretAt_none (A : RustAlloc) (a w1 : BitVec 64) (q2 : BitVec 128) :
    (a ↦₆₄ noneCap) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₁₂₈ q2) ⊢
      optEpochSecretAt A a none := by
  dsimp only [optEpochSecretAt]
  rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono
    (ProofLib.pointsTo64_entails_memRegion (a + 8#64) w1)
    (pointsTo128_entails_memRegion_16 (a + 16#64) q2))

theorem self_504_416_entails_memRegion_928 (selfA tag : BitVec 64) :
    (selfA ↦₆₄ tag) ∗ memRegion (selfA + 8#64) 504 ∗ memRegion (selfA + 512#64) 416 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 504) (k := 416)
        (b' := selfA + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA tag)

theorem writeback_ct1Received_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (w : Words63) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 5#64) ∗
    words63At (outA + 8#64) w ∗
    relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Received st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have h416 : memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 512#64) 416 := by
    rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 5#64) ∗
     (words63At (outA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
     (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono (recompose63 (outA + 8#64) w) h416))
    hnone

theorem writeback_ekSentCt1Received_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (w : Words63) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 6#64) ∗
    words63At (outA + 8#64) w ∗
    relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ noneCap) ∗
    ((outA + 936#64) ↦₆₄ w936) ∗
    ((outA + 944#64) ↦₁₂₈ q944) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ekSentCt1Received st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  have h416 : memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 512#64) 416 := by
    rw [ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
      (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  have hnone := none_tail_entails_optEpochSecretAt_none A (outA + 928#64) w936 q944
  have h936 : (outA + 928#64) + 8#64 = outA + 936#64 := by bv_omega
  have h944 : (outA + 928#64) + 16#64 = outA + 944#64 := by bv_omega
  rw [h936, h944] at hnone
  refine Entails.trans (Entails.of_eq (show _ =
    ((outA ↦₆₄ 6#64) ∗
     (words63At (outA + 8#64) w ∗
      relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w))) ∗
     (memRegion (outA + 512#64) 376 ∗ memRegion (outA + 888#64) 40)) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono (recompose63 (outA + 8#64) w) h416))
    hnone

/-! ## 2. Pure Model Unfolding for `Ct1Received::recv_ct2_chunk` -/

attribute [local irreducible] addChunkTotal decodedMessageTotal

theorem spqrPolyApi_add_chunk_eq_ok2 (self : PolyDecoder) (chunk : Chunk)
    (hpts_len : self.pts.length = 16) :
    spqrPolyApi.add_chunk self chunk = .ok (addChunkTotal self chunk) := by
  dsimp only [spqrPolyApi]
  rw [addChunk_eq_ok self chunk hpts_len]
  rfl

theorem except_bind_ok2 {ε α β : Type} {x : Except ε α} {v : α}
    (h : x = .ok v) (f : α → Except ε β) :
    Bind.bind x f = f v := by
  rw [h]; rfl

theorem except_lift_bind_ok2 {α β : Type} {x : Except SpqrPanic α} {v : α}
    (h : x = .ok v) (f : α → Except StatesPanic β) :
    Bind.bind (liftM x) f = f v := by
  rw [h]; rfl

def polyDecoderNew80 : PolyDecoder :=
  { pts := List.replicate NUM_POLYS SortedSetPt.new
    ptsNeeded := 80
    isComplete := false }

theorem expectDecoderNew_160 :
    expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:174" 160 = .ok polyDecoderNew80 := by
  rfl

theorem polyDecoderNew80_strictSorted :
    PolyDecoderStrictSorted polyDecoderNew80 := by
  intro s hs
  rw [polyDecoderNew80, List.mem_replicate] at hs
  rcases hs with ⟨_, rfl⟩
  exact List.Pairwise.nil

theorem ct1Received_recv_ct2_chunk_eq_ok {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk) :
    ∃ outSt,
      st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt ∧
      PolyDecoderStrictSorted outSt.receiving_ct2 := by
  have hlen0 : polyDecoderNew80.pts.length = 16 := rfl
  have hadd := spqrPolyApi_add_chunk_eq_ok2 polyDecoderNew80 chunk hlen0
  have hsort' := (addChunkBsearch_eq_addChunkTotal polyDecoderNew80 chunk hlen0 polyDecoderNew80_strictSorted).2
  let outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F) :=
    { uc := st.uc, receiving_ct2 := addChunkTotal polyDecoderNew80 chunk }
  refine ⟨outSt, ?_, hsort'⟩
  have hstep : st.recv_ct2_chunk st.uc.epoch chunk =
      (do
        let receivingCt2 ← expectDecoderNew spqrPolyApi "v1/chunked/send_ek.rs:174" 160
        let receivingCt2 ← liftM (spqrPolyApi.add_chunk receivingCt2 chunk)
        Except.ok { uc := st.uc, receiving_ct2 := receivingCt2 }) := by
    unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk
    rw [bne_self_eq_false, ite_eq_right_iff.mpr (fun h => nomatch h)]
    rfl
  rw [hstep, except_bind_ok2 expectDecoderNew_160, except_lift_bind_ok2 hadd]

open CryptoVerification.SpqrV1.States.Leaves (sub_ok_of_addr_eq)

theorem fnAddr_bwd_eq_recv {c : Program} {f1 f2 : String} {o1 o2 d k : Nat}
    {b : BitVec 64} {X : String → Option (State → State)}
    (ho1 : c.fnOff f1 = o1) (ho2 : c.fnOff f2 = o2) (hd : o2 + d = o1)
    (hk : BitVec.ofNat 64 k = -BitVec.ofNat 64 d) :
    (c.rebase b X).fnAddr f1 + BitVec.ofNat 64 k = (c.rebase b X).fnAddr f2 := by
  have hback : (c.rebase b X).fnAddr f2 = (c.rebase b X).fnAddr f1 - BitVec.ofNat 64 d :=
    Program.fnAddr_back (d := d) (b := b) (X := X) ho1 ho2 hd
  rw [hback, hk]
  bv_omega

theorem stackAt_statesRecvCallee_split_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX) (statesRecvCalleeStackX - dropStack32) ∗
      stackAt sp dropStack32 := by
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - dropStack32) (k := dropStack32)
    (b' := sp - BitVec.ofNat 64 dropStack32) rfl
    (by change sp - 4128#64 = (sp - 19552#64) + 15424#64; bv_omega)
    (by decide)

theorem stackAt_statesRecvCallee_split_ct1RecvCt2 (sp : BitVec 64) :
    stackAt sp statesRecvCalleeStackX =
      memRegion (sp - BitVec.ofNat 64 statesRecvCalleeStackX)
        (statesRecvCalleeStackX - ct1ReceivedRecvCt2ChunkStack) ∗
      stackAt sp ct1ReceivedRecvCt2ChunkStack := by
  simp only [stackAt]
  exact ProofLib.memRegion_split'
    (b := sp - BitVec.ofNat 64 statesRecvCalleeStackX)
    (n := statesRecvCalleeStackX - ct1ReceivedRecvCt2ChunkStack) (k := ct1ReceivedRecvCt2ChunkStack)
    (b' := sp - BitVec.ofNat 64 ct1ReceivedRecvCt2ChunkStack) rfl
    (by change sp - 16976#64 = (sp - 19552#64) + 2576#64; bv_omega)
    (by decide)

theorem memRegion_880_split_504_376 (a a' : BitVec 64) (h : a + 504#64 = a') :
    memRegion a 880 = memRegion a 504 ∗ memRegion a' 376 :=
  ProofLib.memRegion_split' (b := a) (n := 504) (k := 376) (b' := a') rfl h.symm (by decide)

theorem words63At_376_entails_memRegion_880 (a a' : BitVec 64) (w : Words63) (h : a + 504#64 = a') :
    words63At a w ∗ memRegion a' 376 ⊢ memRegion a 880 := by
  rw [memRegion_880_split_504_376 a a' h]
  exact sepConj_mono_left (words63At_entails_memRegion a w)

/-! ## 3. `.ct1Received` (`0x55908`, `+1204`) Helper Blocks -/

theorem states_recv_ct1Received_gt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.ct1Received st) msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hgt' : msg.epoch > st.epoch := hgt
  dsimp only [States.recv]
  rw [ite_eq_left_iff.mpr (fun h => absurd hgt' h)]

theorem states_recv_ct1Received_lt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ct1Received st } := by
  have hlt' : msg.epoch < st.epoch := hlt
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    change ¬ (st.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt')
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_left_iff.mpr (fun h => absurd hlt' h)]

theorem states_recv_ct1Received_eq_other (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (heq : msg.epoch = st.uc.epoch)
    (hct2 : ∀ c, msg.payload ≠ .ct2 c) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ct1Received st } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt')]
  cases hpay : msg.payload with
  | ct2 c => exact absurd hpay (hct2 c)
  | _ => rfl

theorem states_recv_ct1Received_eq_ct2 (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ct2 chunk)
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt) :
    States.recv K (.ct1Received st) msg =
      .ok { key := none, state := .ekSentCt1Received outSt } := by
  have heq' : msg.epoch = st.epoch := heq
  have hnot_gt' : ¬ (msg.epoch > st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  have hnot_lt' : ¬ (msg.epoch < st.epoch) := by
    rw [heq']; exact BitVec.lt_irrefl _
  dsimp only [States.recv]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hnot_gt'),
      ite_eq_right_iff.mpr (fun h => absurd h hnot_lt'),
      hpay, heq]
  change Except.bind (StatesResult.ofPanic (st.recv_ct2_chunk st.uc.epoch chunk)) _ = _
  rw [hrecv]
  rfl

/-! ## 4. Full `.ct1Received` Arm (`+1204 -> s0.x30`, `0x55908 -> 0x59ff0`) -/

theorem epoch_cmp_ct1r_eq_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_eq_1_of_gt {st_ep msg_ep : BitVec 64} (hgt : msg_ep.toNat > st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 1#32) = true := by
  have h1 : st_ep.ule msg_ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]; omega
  have h2 : msg_ep.ule st_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1, h2]

theorem epoch_cmp_ct1r_eq_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_ct1r_eq_1_of_lt {st_ep msg_ep : BitVec 64} (hlt : msg_ep.toNat < st_ep.toNat) :
    (BitVec.truncate 32 ((if st_ep.ule msg_ep = true then if msg_ep.ule st_ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 1#32) = false := by
  have h1 : st_ep.ule msg_ep = false := by rw [BitVec.ule_eq_decide, decide_eq_false_iff_not]; omega
  simp [h1]

theorem epoch_cmp_ct1r_eq_of_eq (ep : BitVec 64) :
    (BitVec.truncate 32 ((if ep.ule ep = true then if ep.ule ep = true then 0#64 else 1#64 else 4294967295#64) &&& 1095216660735#64) == 0#32) = true := by
  have h1 : ep.ule ep = true := by rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp [h1]

theorem words63At_self_entails_memRegion_928 (selfA tag : BitVec 64) (w : Words63) :
    (selfA ↦₆₄ tag) ∗ words63At (selfA + 8#64) w ∗ memRegion (selfA + 512#64) 416 ⊢
      memRegion selfA chunkedStatesSize := by
  refine Entails.trans ?_ (self_504_416_entails_memRegion_928 selfA tag)
  exact sepConj_mono_right (sepConj_mono_left (words63At_entails_memRegion (selfA + 8#64) w))

end CryptoVerification.SpqrV1.States.Recv
