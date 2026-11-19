/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkReceivedCt1SampledSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Acknowledged` Arm, Part 1

Pure unfolding lemmas, `66`-word (`528`B) state extraction helpers, jump-table dispatch
(`+36 -> +588`), entry epoch/payload branch dispatch, and the `msg.epoch > st.uc.epoch`
(`EpochOutOfRange`) exit path of `.ct1Acknowledged` (`0x556a0`, tag `11#64`).
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
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff /-! ## 1. Pure Unfolding Lemmas for `States.recv (.ct1Acknowledged st) msg` -/
theorem states_recv_ct1Acknowledged_gt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) :
    States.recv K (.ct1Acknowledged st) msg =
      .error (.err (.epochOutOfRange msg.epoch)) := by
  simp only [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, hgt, ↓reduceIte]

theorem states_recv_ct1Acknowledged_lt (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hlt : msg.epoch < st.uc.epoch) :
    States.recv K (.ct1Acknowledged st) msg =
      .ok { key := none, state := .ct1Acknowledged st } := by
  have hnot_gt : ¬ (msg.epoch > st.uc.epoch) := by
    change ¬ (st.uc.epoch < msg.epoch)
    exact BitVec.not_lt.mpr (BitVec.le_of_lt hlt)
  simp only [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, hnot_gt, hlt, ↓reduceIte]

theorem states_recv_ct1Acknowledged_eq_other (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (heq : msg.epoch = st.uc.epoch)
    (hek : ∀ c, msg.payload ≠ .ek c)
    (hekAck : ∀ c, msg.payload ≠ .ekCt1Ack c) :
    States.recv K (.ct1Acknowledged st) msg =
      .ok { key := none, state := .ct1Acknowledged st } := by
  cases hpay : msg.payload with
  | ek c => exact absurd hpay (hek c)
  | ekCt1Ack c => exact absurd hpay (hekAck c)
  | _ =>
    simp only [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, heq, BitVec.lt_irrefl, ↓reduceIte]

theorem states_recv_ct1Acknowledged_eq_ek (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ek chunk) :
    States.recv K (.ct1Acknowledged st) msg =
      Except.bind (st.recv_ek_chunk K st.uc.epoch chunk) (fun res =>
        match res with
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }) := by
  simp only [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, heq, BitVec.lt_irrefl, hpay, ↓reduceIte, Bind.bind]
  congr 1; ext res; cases res <;> rfl

theorem states_recv_ct1Acknowledged_eq_ekCt1Ack (K : MlKem) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch)
    (hpay : msg.payload = .ekCt1Ack chunk) :
    States.recv K (.ct1Acknowledged st) msg =
      Except.bind (st.recv_ek_chunk K st.uc.epoch chunk) (fun res =>
        match res with
        | .stillReceiving s' => .ok { key := none, state := .ct1Acknowledged s' }
        | .done s' => .ok { key := none, state := .ct2Sampled s' }) := by
  simp only [States.recv, Chunked.SendCt.Ct1Acknowledged.epoch, heq, BitVec.lt_irrefl, hpay, ↓reduceIte, Bind.bind]
  congr 1; ext res; cases res <;> rfl

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 2. Word-Level Extraction for `chunkedCt1AcknowledgedAt` (`528`B = 66 words) -/

theorem vecU8_extract_cap_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ _)]
  apply Entails.pure_left; intro ⟨hlen, hcap_lt, hptr_ne⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hcap_lt ?_)
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst
    simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [hhdr dst, wordsAt_eq_pointsToBytes]
  rw [sepConj_left_comm (dst ↦ₛ _)]
  exact Entails.pure_right ⟨hlen, hcap_lt, hptr_ne⟩ (Entails.refl _)

theorem unchunkedCt1SentAt_extract_cap_lt (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A a st ⊢
      ∃∗ g : FiveVecWords,
        ⌜g.v1.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (fiveVecWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedCt1SentAt A dst st)
          (wordsBytes (fiveVecWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.hdr⟩, st.es, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.hdr) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.es ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.hdr ∗
        vecU8 A (dst + 72#64) st.es ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_cap_lt A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.sepExists_right ⟨v1, rest⟩ (Entails.pure_right hlt ?_)
  exact wordsExtract_sepConj rfl heq

def mkWords66_16_50 (g : FiveVecWords) (ep : BitVec 64) (p : Words5x10) : Words66 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
           g.rest.rest.v1.w0, g.rest.rest.v1.w1, g.rest.rest.v1.w2, g.rest.rest.auth.v1.w0⟩
    b1 := ⟨g.rest.rest.auth.v1.w1, g.rest.rest.auth.v1.w2, g.rest.rest.auth.v2.w0,
           g.rest.rest.auth.v2.w1, g.rest.rest.auth.v2.w2, ep,
           p.b0.w0, p.b0.w1, p.b0.w2, p.b0.w3⟩
    b2 := ⟨p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9,
           p.b1.w0, p.b1.w1, p.b1.w2, p.b1.w3⟩
    b3 := ⟨p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9,
           p.b2.w0, p.b2.w1, p.b2.w2, p.b2.w3⟩
    b4 := ⟨p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9,
           p.b3.w0, p.b3.w1, p.b3.w2, p.b3.w3⟩
    b5 := ⟨p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9,
           p.b4.w0, p.b4.w1, p.b4.w2, p.b4.w3⟩
    q60 := p.b4.w5 ++ p.b4.w4
    w62 := p.b4.w6
    q63 := p.b4.w8 ++ p.b4.w7
    w65 := p.b4.w9 }

theorem words66List_mkWords66_16_50 (g : FiveVecWords) (ep : BitVec 64) (p : Words5x10) :
    fiveVecWordsList g ep ++ words5x10List p = words66List (mkWords66_16_50 g ep p) := by
  simp only [words66List, mkWords66_16_50, words5x10List, words10List,
    fiveVecWordsList, ekSentCt1ReceivedWordsList, ekSentWordsList, ct2SentWordsList,
    authWordsList, vecWordsList, Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append,
    List.append_assoc, List.cons_append, List.nil_append]

theorem chunkedCt1AcknowledgedAt_extract66 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1AcknowledgedAt A a st ⊢
      ∃∗ w : Words66,
        ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w5 = st.uc.epoch⌝ ∗
        words66At a w ∗
        relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) := by
  unfold chunkedCt1AcknowledgedAt
  refine Entails.trans (sepConj_mono
    (unchunkedCt1SentAt_extract_cap_lt A a st.uc)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ek) (a + 128#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hlt
  let w := mkWords66_16_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right ⟨hlt, rfl⟩ ?_)
  rw [words66At_eq_wordsAt, ← words66List_mkWords66_16_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem recompose66_ct1Acknowledged (A : RustAlloc) {F : ShaCompress}
    (dst : BitVec 64) (w : Words66)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    words66At dst w ∗
      relocatedHeap (fun d => chunkedCt1AcknowledgedAt A d st) (wordsBytes (words66List w)) ⊢
    chunkedCt1AcknowledgedAt A dst st :=
  recompose66 (F_pred := fun d => chunkedCt1AcknowledgedAt A d st) dst w

theorem words66At_392_entails_memRegion_920 (a a' : BitVec 64) (w : Words66) (h : a + 528#64 = a') :
    words66At a w ∗ memRegion a' 392 ⊢ memRegion a 920 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 528) (k := 392) (b' := a') rfl h.symm (by decide)]
  exact sepConj_mono_left (words66At_entails_memRegion a w)

theorem memRegion_976_880_split_528_352 (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 880 =
      memRegion (fsp + 976#64) 528 ∗ memRegion (fsp + 1504#64) 352 :=
  ProofLib.memRegion_split' (b := fsp + 976#64) (n := 528) (k := 352)
    (b' := fsp + 1504#64) rfl (by bv_omega) (by decide)

theorem words66At_976_352_entails_memRegion_880 (fsp : BitVec 64) (w : Words66) :
    words66At (fsp + 976#64) w ∗ memRegion (fsp + 1504#64) 352 ⊢
      memRegion (fsp + 976#64) 880 := by
  rw [memRegion_976_880_split_528_352 fsp]
  exact sepConj_mono_left (words66At_entails_memRegion (fsp + 976#64) w)

theorem selfA_ct1Acknowledged_entails_memRegion (selfA : BitVec 64) (w : Words66) :
    (selfA ↦₆₄ 11#64) ∗ words66At (selfA + 8#64) w ∗ memRegion (selfA + 536#64) 392 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 528) (k := 392)
        (b' := selfA + 536#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion selfA 11#64)
    (sepConj_mono_left (words66At_entails_memRegion (selfA + 8#64) w))

theorem selfA_11_528_entails_memRegion (selfA : BitVec 64) :
    (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 528) (k := 392)
        (b' := selfA + 536#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 11#64)

theorem ct1Ack_noop_out_entails_resultV1RecvAt (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (w : Words66) (w936 : BitVec 64) (q944 : BitVec 128) :
    (outA ↦₆₄ 11#64) ∗
      words63At (outA + 8#64)
        { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
          q60 := w.q60, w62 := w.w62 } ∗
      ekTail376 w.q63 w.w65 (outA + 512#64) ∗
      memRegion (outA + 888#64) 40 ∗
      ((outA + 928#64) ↦₆₄ noneCap) ∗
      ((outA + 936#64) ↦₆₄ w936) ∗
      ((outA + 944#64) ↦₁₂₈ q944) ∗
      relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged st }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt]
  rw [ProofLib.memRegion_split' (b := outA + 536#64) (n := 352) (k := 40)
        (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
  have h66 := words63At_ekTail376_eq_words66At outA w
  have hrec := recompose66 (F_pred := fun dst => chunkedCt1AcknowledgedAt A dst st) (outA + 8#64) w
  have hopt := optEpochSecretAt_none_of_parts A (outA + 928#64) w936 q944
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd] at hopt
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 11#64) ∗
    (words63At (outA + 8#64)
       { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4, b5 := w.b5,
         q60 := w.q60, w62 := w.w62 } ∗
     ekTail376 w.q63 w.w65 (outA + 512#64)) ∗
    relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w)) ∗
    memRegion (outA + 888#64) 40 ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  rw [h66]
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ 11#64) ∗
    (words66At (outA + 8#64) w ∗
     relocatedHeap (fun dst => chunkedCt1AcknowledgedAt A dst st) (wordsBytes (words66List w))) ∗
    (memRegion (outA + 536#64) 352 ∗ memRegion (outA + 888#64) 40) ∗
    (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_right hopt))) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Discriminant byte at `msgA + 8#64` of `MessagePayload spqrPolyApi`. -/
@[expose] def ct1AckPayloadTag (p : MessagePayload spqrPolyApi) : BitVec 8 :=
  match p with
  | .none => 0#8
  | .hdr _ => 1#8
  | .ek _ => 2#8
  | .ekCt1Ack _ => 3#8
  | .ct1Ack _ => 4#8
  | .ct1 _ => 5#8
  | .ct2 _ => 6#8

/-- Tail (`39` bytes at `msgA + 9#64`) of `messageAt spqrPolyApi msgA msg`. -/
@[expose] def ct1AckPayloadTailAt (a : BitVec 64) (p : MessagePayload spqrPolyApi) : SepProp :=
  match p with
  | .none => memRegion (a + 0x09#64) 39
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c =>
      memRegion (a + 0x09#64) 1 ∗ chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4
  | .ct1Ack b =>
      ((a + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗ memRegion (a + 0x0a#64) 38

theorem messageAt_eq_epoch_ct1AckTag_tail (a : BitVec 64) (msg : Message spqrPolyApi) :
    messageAt spqrPolyApi a msg =
      (a ↦₆₄ msg.epoch) ∗ ((a + 8#64) ↦₈ ct1AckPayloadTag msg.payload) ∗ ct1AckPayloadTailAt a msg.payload := by
  dsimp only [messageAt, messagePayloadAt]
  cases msg.payload <;>
    (dsimp only [ct1AckPayloadTag, ct1AckPayloadTailAt, spqrPolyApi]; try ac_rfl)

theorem messagePayloadTag_and6_eq_2_of_not_ek {p : MessagePayload spqrPolyApi}
    (hek : ∀ c, p ≠ .ek c) (hekAck : ∀ c, p ≠ .ekCt1Ack c) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag p) &&& 25769803782#64) == 2#32) = false := by
  cases p with
  | ek c => exact absurd rfl (hek c)
  | ekCt1Ack c => exact absurd rfl (hekAck c)
  | _ => dsimp only [ct1AckPayloadTag]; decide

theorem messagePayloadTag_and6_bne_2_of_not_ek {p : MessagePayload spqrPolyApi}
    (hek : ∀ c, p ≠ .ek c) (hekAck : ∀ c, p ≠ .ekCt1Ack c) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag p) &&& 25769803782#64) != 2#32) = true := by
  cases p with
  | ek c => exact absurd rfl (hek c)
  | ekCt1Ack c => exact absurd rfl (hekAck c)
  | _ => dsimp only [ct1AckPayloadTag]; decide

theorem messagePayloadTag_and6_eq_2_of_ek (c : Chunk) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag (.ek c)) &&& 25769803782#64) == 2#32) = true := by
  dsimp only [ct1AckPayloadTag]; decide

theorem messagePayloadTag_and6_bne_2_of_ek (c : Chunk) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag (.ek c)) &&& 25769803782#64) != 2#32) = false := by
  dsimp only [ct1AckPayloadTag]; decide

theorem messagePayloadTag_and6_eq_2_of_ekCt1Ack (c : Chunk) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag (.ekCt1Ack c)) &&& 25769803782#64) == 2#32) = true := by
  dsimp only [ct1AckPayloadTag]; decide

theorem messagePayloadTag_and6_bne_2_of_ekCt1Ack (c : Chunk) :
    (BitVec.truncate 32 (BitVec.zeroExtend 64 (ct1AckPayloadTag (.ekCt1Ack c)) &&& 25769803782#64) != 2#32) = false := by
  dsimp only [ct1AckPayloadTag]; decide

/-! ## 3. Dispatch (`+36 -> +588`, `0x55478 -> 0x556a0`) -/

theorem words66At_eq_pointsToBytes (a : BitVec 64) (w : Words66) :
    words66At a w = (a ↦ₛ wordsBytes (words66List w)) := by
  rw [words66At_eq_wordsAt, wordsAt_eq_pointsToBytes]

theorem length_wordsBytes_words66List (w : Words66) :
    (wordsBytes (words66List w)).length = 528 := by
  rw [length_wordsBytes, length_words66List]

/-- Framed `memcpy` call rule that copies `words66At src w` (`528`B) into `memRegion dst 528`,
    producing `words66At dst w ∗ words66At src w` and forwarding `CalleeSavedPreserved s sf`. -/
theorem call_memcpy_words66_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) (w : Words66)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = 528)
    (hsplit : P = (memRegion dst 528 ∗ words66At src w) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog target_pc sf ((words66At dst w ∗ words66At src w) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  let bs := wordsBytes (words66List w)
  have hlen : bs.length = 528 := length_wordsBytes_words66List w
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, ← words66At_eq_pointsToBytes src w, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    rw [← words66At_eq_pointsToBytes dst w, ← words66At_eq_pointsToBytes src w]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr.trans htrace)

/-- Flat-offset 5-Vec headers at `fsp + 976#64` (`128` bytes = `0x3d0..0x450`). -/
@[expose] def fiveVec976HeadersAt (fsp : BitVec 64) (g : FiveVecGhost) : SepProp :=
  ((fsp + 976#64) ↦₆₄ g.v1.cap) ∗ ((fsp + 984#64) ↦₆₄ g.v1.ptr) ∗ memRegion (fsp + 992#64) 8 ∗
  ((fsp + 1000#64) ↦₆₄ g.v2.cap) ∗ ((fsp + 1008#64) ↦₆₄ g.v2.ptr) ∗ memRegion (fsp + 1016#64) 8 ∗
  ((fsp + 1024#64) ↦₆₄ g.v3.cap) ∗ ((fsp + 1032#64) ↦₆₄ g.v3.ptr) ∗ memRegion (fsp + 1040#64) 8 ∗
  ((fsp + 1048#64) ↦₆₄ g.v4.cap) ∗ ((fsp + 1056#64) ↦₆₄ g.v4.ptr) ∗ memRegion (fsp + 1064#64) 8 ∗
  ((fsp + 1072#64) ↦₆₄ g.v5.cap) ∗ ((fsp + 1080#64) ↦₆₄ g.v5.ptr) ∗ memRegion (fsp + 1088#64) 16

theorem fiveVec128HeadersAt_976_eq (fsp : BitVec 64) (g : FiveVecGhost) :
    fiveVec128HeadersAt (fsp + 976#64) g = fiveVec976HeadersAt fsp g := by
  unfold fiveVec128HeadersAt fiveVec976HeadersAt
  simp only [bv_add_lit_add_lit_recv, Nat.reduceAdd]

theorem unchunkedCt1Sent976_entails_dealloc (A : RustAlloc) {F : ShaCompress} (fsp : BitVec 64)
    (st : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)) :
    unchunkedCt1SentAt A (fsp + 976#64) st ⊢
      ∃∗ g : FiveVecGhost,
        fiveVec976HeadersAt fsp g ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗
        vecCapPtrDealloc A g.v2.cap g.v2.ptr ∗
        vecCapPtrDealloc A g.v3.cap g.v3.ptr ∗
        vecCapPtrDealloc A g.v4.cap g.v4.ptr ∗
        vecCapPtrDealloc A g.v5.cap g.v5.ptr := by
  refine Entails.trans (unchunkedCt1SentAt_entails_dealloc A (fsp + 976#64) st) ?_
  apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g ?_
  rw [fiveVec128HeadersAt_976_eq]
  exact Entails.refl _

theorem fiveVec976HeadersAt_entails_memRegion_128 (fsp : BitVec 64) (g : FiveVecGhost) :
    fiveVec976HeadersAt fsp g ⊢ memRegion (fsp + 976#64) 128 := by
  rw [← fiveVec128HeadersAt_976_eq]
  exact fiveVec128HeadersAt_entails_memRegion_128 (fsp + 976#64) g

end CryptoVerification.SpqrV1.States.Recv
