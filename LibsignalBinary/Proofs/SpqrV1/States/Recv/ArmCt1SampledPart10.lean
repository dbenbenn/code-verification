/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart6
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart9
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 10 (Top-Level Arm)

**Checked by Lean.** Composes all paths of the `.ct1Sampled` arm (`0x55a4c`, `entry + 1528`) into
`states_recv_ct1Sampled_ok_ext`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.States

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144

theorem states_recv_ct1Sampled_eq_gt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch.toNat > st.uc.epoch.toNat) :
    (States.ct1Sampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  have hlt : st.uc.epoch < msg.epoch := BitVec.lt_def.mpr hgt
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    gt_iff_lt, hlt, ↓reduceIte]

theorem states_recv_ct1Sampled_eq_lt {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch.toNat < st.uc.epoch.toNat) :
    (States.ct1Sampled st).recv K msg = .ok { key := none, state := .ct1Sampled st } := by
  have hlt' : msg.epoch < st.uc.epoch := BitVec.lt_def.mpr hlt
  have hnot_gt : ¬ (st.uc.epoch < msg.epoch) := by
    rw [BitVec.lt_def]; omega
  simp only [States.recv, Chunked.SendCt.Ct1Sampled.epoch, Unchunked.SendCt.Ct1Sent.epoch,
    gt_iff_lt, hnot_gt, hlt', Bool.false_eq_true, ↓reduceIte]

theorem messagePayloadAt_other_expose (msgA : BitVec 64) (p : MessagePayload spqrPolyApi)
    (hnot_ek : ∀ c, p ≠ .ek c) (hnot_ack : ∀ c, p ≠ .ekCt1Ack c) :
    ∃ (tag : BitVec 8) (Rest_msg : SepProp),
      (BitVec.zeroExtend 32 tag == 2#32) = false ∧
      (BitVec.zeroExtend 32 tag != 3#32) = true ∧
      messagePayloadAt spqrPolyApi msgA p = (((msgA + 8#64) ↦₈ tag) ∗ Rest_msg) := by
  cases p with
  | none =>
    exact ⟨0#8, memRegion (msgA + 9#64) 39, rfl, rfl, rfl⟩
  | hdr c =>
    exact ⟨1#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩
  | ek c => exact False.elim (hnot_ek c rfl)
  | ekCt1Ack c => exact False.elim (hnot_ack c rfl)
  | ct1Ack b =>
    exact ⟨4#8, ((msgA + 9#64) ↦₈ (if b then 1#8 else 0#8)) ∗ memRegion (msgA + 10#64) 38,
      rfl, rfl, rfl⟩
  | ct1 c =>
    exact ⟨5#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩
  | ct2 c =>
    exact ⟨6#8, memRegion (msgA + 9#64) 1 ∗ chunkAt (msgA + 10#64) c ∗ memRegion (msgA + 44#64) 4,
      rfl, rfl, rfl⟩

theorem messageAt_ek_eq (msgA : BitVec 64) (msg : Message spqrPolyApi) (chunk : Chunk)
    (hpay : msg.payload = .ek chunk) :
    messageAt spqrPolyApi msgA msg =
      (msgA ↦₆₄ msg.epoch) ∗
      ((msgA + 8#64) ↦₈ 2#8) ∗
      memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗
      memRegion (msgA + 44#64) 4 := by
  dsimp only [messageAt, messagePayloadAt]
  rw [hpay]

theorem messageAt_ekCt1Ack_eq (msgA : BitVec 64) (msg : Message spqrPolyApi) (chunk : Chunk)
    (hpay : msg.payload = .ekCt1Ack chunk) :
    messageAt spqrPolyApi msgA msg =
      (msgA ↦₆₄ msg.epoch) ∗
      ((msgA + 8#64) ↦₈ 3#8) ∗
      memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗
      memRegion (msgA + 44#64) 4 := by
  dsimp only [messageAt, messagePayloadAt]
  rw [hpay]

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre0 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder) (decoded : Bytes)
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
      polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
      wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
      memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗ A.pool ∗
      stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
      messageAt spqrPolyApi msgA msg ⊢
    optVecU8At A (fsp + 3832#64) (some decoded) ∗ wordsAt (fsp + 3696#64) c_uc.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
      memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) :=
  Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre1 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) (.ok uc_ek) ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) ⊢
    ∃∗ c_ek : Words16,
      ⌜c_ek.w0.toNat < 2 ^ 63⌝ ∗
      wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
      copyScratchStackAt fsp sc ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 128) (k := 160) (b' := fsp + 3984#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_left
    (unchunkedCt1SentEkReceivedAt_extract_words16 A (fsp + 1856#64) uc_ek)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro c_ek
  exact Entails.sepExists_right c_ek (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 800000 in
theorem ct1Sampled_some_ok_ack_pre3 {A : RustAlloc} {F : ShaCompress}
    (b fsp selfA outA msgA : BitVec 64) (s0 : State)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (dec' : PolyDecoder)
    (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (c_uc c_ek : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack) :
    wordsAt (fsp + 1856#64) c_ek.toList ∗
      wordsAt (fsp + 3856#64) c_ek.toList ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
      (relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList) ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3984#64) 160 ∗ memRegion outA v1RecvSize ∗ statesRecvRoAt b ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗
        messageAt spqrPolyApi msgA msg) ⊢
    (memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗
      unchunkedCt1SentEkReceivedAt A (fsp + 3856#64) uc_ek ∗
      memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
    (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 2312#64) 440 ∗
      memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
      memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
      memRegion (fsp + 3984#64) 8 ∗ memRegion (fsp + 4096#64) 48 ∗
      memRegion outA v1RecvSize ∗
      (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) := by
  refine Entails.trans (sepConj_mono_left (words16_entails_memRegion_128 (fsp + 1856#64) c_ek)) ?_
  have hek := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (fsp + 3856#64) c_ek
  have h1856_join :
      memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768 =
      memRegion (fsp + 1856#64) 400 ∗ memRegion (fsp + 2256#64) 56 ∗ memRegion (fsp + 2312#64) 440 := by
    rw [← ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 400) (k := 496) (b' := fsp + 2256#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 2256#64) (n := 56) (k := 440) (b' := fsp + 2312#64) rfl (by bv_omega) (by decide)]
  rw [ProofLib.memRegion_split' (b := fsp + 3984#64) (n := 8) (k := 152) (b' := fsp + 3992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3992#64) (n := 104) (k := 48) (b' := fsp + 4096#64) rfl (by bv_omega) (by decide),
      statesRecvRoAt_eq_unchunkedSendCt2 b]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (fsp + 1856#64) 128 ∗ memRegion (fsp + 1984#64) 768) ∗
    (wordsAt (fsp + 3856#64) c_ek.toList ∗
      relocatedHeap (fun a => unchunkedCt1SentEkReceivedAt A a uc_ek) (wordsBytes c_ek.toList)) ∗
    (memRegion (fsp + 3992#64) 104 ∗ unchunkedSendCt2RoAt b ∗
      A.pool ∗ stackAt fsp statesRecvCalleeStackX) ∗
    (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
      wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
      copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗ epilogueStoreStackPart1At fsp k ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
      memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
      memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 3152#64) 544 ∗
      memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3824#64) 8 ∗
      memRegion (fsp + 3832#64) 24 ∗ memRegion (fsp + 3984#64) 8 ∗
      memRegion (fsp + 4096#64) 48 ∗ memRegion outA v1RecvSize ∗
      (statesRecvJumpTableAt b ∗ tokenInitAt b ∗ reduceTableAt b) ∗
      statesRecvSavedCells s0 ∗ messageAt spqrPolyApi msgA msg) by ac_rfl)) ?_
  rw [h1856_join]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hek)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem ct1Sampled_send_ct2_ok_of_recv_ek_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (decoded : Bytes) (uc_ek : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (hes : st.uc.es.length = 2080) (hct1 : st.uc.ct1.length = 960)
    (hmac : st.uc.auth.macKey.length < 2 ^ 32)
    (hrek : st.uc.recv_ek K st.uc.epoch decoded = .ok uc_ek) :
    ∃ outUc ct2 mac outEnc,
      uc_ek.send_ct2 K = .ok (outUc, ct2, mac) ∧
      Chunked.SendCt.send_ct2_encoder spqrPolyApi ct2 mac = .ok outEnc := by
  unfold Unchunked.SendCt.Ct1Sent.recv_ek ek_matches_header MlKem.validPkBytes at hrek
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hrek
  split_ifs at hrek with hval
  have huc : uc_ek = { epoch := st.uc.epoch, auth := st.uc.auth, es := st.uc.es, ek := decoded, ct1 := st.uc.ct1 } :=
    (Except.ok.inj hrek).symm
  simp only [Bool.and_eq_true, beq_iff_eq] at hval
  subst huc
  exact send_ct2_and_encoder_eq_ok_of_lengths K _ hes hval.1.2 hct1 hmac

end CryptoVerification.SpqrV1.States.Recv
