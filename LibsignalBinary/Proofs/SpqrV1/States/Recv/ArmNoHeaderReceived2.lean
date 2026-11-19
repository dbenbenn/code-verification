/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceived1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree -- shake: keep

/-!
# `<States>::recv` — `.noHeaderReceived` Arm, Part 2

**Checked by Lean.** Verifies the `<NoHeaderReceived>::recv_hdr_chunk` call bridge (`+8568 ->
+8616`) and top-level variant contract `states_recv_noHeaderReceived_ok_ext`.
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
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  sp_sub_4240_add_4144 bv_add_lit_add_lit_recv
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48

/-! ## 1. Call to `NoHeaderReceived::recv_hdr_chunk` (`+8612 -> +8616`) & Helpers -/

theorem sepWPp_intro_ex_nhr {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {P : α → SepProp} {Q Q_panic : State → SepProp → Prop} (hrun : s.status = .Running)
    (h : ∀ x, SepWPp prog target_pc s (P x) Q Q_panic) :
    SepWPp prog target_pc s (∃∗ x, P x) Q Q_panic := by
  apply SepWPp.of_sepWP
  rw [← emp_sepConj (∃∗ x, P x), sepExists_sepConj_right]
  apply ProofLib.SepWP.exists_left
  intro x; rw [emp_sepConj]
  exact SepWP.done rfl hrun (h x)

theorem states_recv_noHeaderReceived_isPanic_hdr {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (heq : msg.epoch = st.uc.epoch) (hp : msg.payload = .hdr chunk)
    (hpan : (st.recv_hdr_chunk st.uc.epoch chunk).isPanic = true) :
    ((States.noHeaderReceived st).recv K msg).isPanic = true := by
  rw [states_recv_noHeaderReceived_eq_hdr K st msg chunk heq hp]
  cases h : st.recv_hdr_chunk st.uc.epoch chunk with
  | error e => rw [h] at hpan; exact hpan
  | ok res => rw [h] at hpan; cases hpan

theorem memRegion_880_split_456_424_nhr (fsp : BitVec 64) :
    memRegion (fsp + 976#64) 880 =
      memRegion (fsp + 976#64) 456 ∗ memRegion (fsp + 1432#64) 424 :=
  ProofLib.memRegion_split' (b := fsp + 976#64) (n := 456) (k := 424)
    (b' := fsp + 1432#64) rfl (by bv_omega) (by decide)

theorem memRegion_880_split_480_400_1856_nhr (fsp : BitVec 64) :
    memRegion (fsp + 1856#64) 880 =
      memRegion (fsp + 1856#64) 480 ∗ memRegion (fsp + 2336#64) 400 :=
  ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 400)
    (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)

theorem nhr_still_1856_split {A : RustAlloc} {F : ShaCompress} (fsp : BitVec 64)
    (outSt : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    noHeaderReceivedRecvChunkResultAt A (F := F) (fsp + 1856#64) (.ok (.stillReceiving outSt)) ⊢
      ∃∗ w_out : Words57, ∃∗ w58 : BitVec 64, ∃∗ w59 : BitVec 64,
        words60At (fsp + 1856#64) (mkWords60_still w_out w58 w59) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst outSt) (wordsBytes (words57List w_out)) := by
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt]
  apply Entails.pure_left; intro _
  rw [ProofLib.memRegion_split' (b := (fsp + 1856#64) + 464#64) (n := 8) (k := 8)
        (b' := (fsp + 1856#64) + 472#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ((fsp + 1856#64) + 464#64),
      ProofLib.memRegion_eight ((fsp + 1856#64) + 472#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (chunkedNoHeaderReceivedAt_extract57 A ((fsp + 1856#64) + 8#64) outSt))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w59
  apply Entails.sepExists_elim; intro w58
  apply Entails.sepExists_elim; intro w_out
  rw [← sepConj_assoc, sepConj_comm ((fsp + 1856#64) ↦₆₄ noneCap), sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro _
  refine Entails.sepExists_right w_out (Entails.sepExists_right w58 (Entails.sepExists_right w59 ?_))
  rw [← words60At_mkWords60_still (fsp + 1856#64) w_out w58 w59]
  exact Entails.of_eq (by ac_rfl)

theorem messagePayloadAt_hdr_eq (msgA : BitVec 64) (chunk : Chunk) :
    messagePayloadAt spqrPolyApi msgA (.hdr chunk) =
      ((msgA + 8#64) ↦₈ 1#8) ∗ memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 := rfl

theorem nhr_hdr_pre_call_entails (A : RustAlloc) {F : ShaCompress} (fsp selfA : BitVec 64)
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) (w : Words57) :
    (words57At (fsp + 976#64) w ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst st) (wordsBytes (words57List w))) ∗
    ((selfA ↦₆₄ 7#64) ∗ words57At (selfA + 8#64) w ∗ memRegion (selfA + 464#64) 464) ∗
    (words57At (fsp + 2752#64) w ∗ nhrUnusedRestAt fsp) ⊢
      chunkedNoHeaderReceivedAt A (fsp + 976#64) st ∗
      memRegion selfA chunkedStatesSize ∗
      sendEkUnusedAt fsp :=
  sepConj_mono
    (recompose57 (F_pred := fun dst => chunkedNoHeaderReceivedAt A dst st) (fsp + 976#64) w)
    (sepConj_mono
      (selfA_noHeaderReceived_entails_memRegion selfA w)
      (words57At_nhrUnusedRest_entails_sendEkUnusedAt fsp w))

theorem messageAt_hdr_recompose (msgA : BitVec 64) (msg : Message spqrPolyApi) (chunk : Chunk)
    (hp : msg.payload = .hdr chunk) :
    (msgA ↦₆₄ msg.epoch) ∗ ((msgA + 8#64) ↦₈ 1#8) ∗ memRegion (msgA + 9#64) 1 ∗
      chunkAt (msgA + 10#64) chunk ∗ memRegion (msgA + 44#64) 4 =
      messageAt spqrPolyApi msgA msg := by
  unfold messageAt
  rw [hp, messagePayloadAt_hdr_eq]

theorem vecU8_extract_niche (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0 ≠ 0xfffffffffffffffe#64 ∧ v.w0 ≠ noneCap⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [← sepConj_assoc, sepConj_comm (vecHeader _ _ _ _), sepConj_assoc]
  apply Entails.pure_left; intro ⟨hlen, hcap, hptr⟩
  have hne : cap ≠ 0xfffffffffffffffe#64 ∧ cap ≠ noneCap := by
    unfold noneCap; constructor <;> bv_omega
  unfold vecHeader
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hne ?_)
  have hhdr : ∀ dst : BitVec 64,
      ((dst ↦₆₄ cap) ∗ ((dst + 8#64) ↦₆₄ ptr) ∗ ((dst + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length)) =
      wordsAt dst (vecWordsList v) := by
    intro dst; simp only [vecWordsList, wordsAt, sepConj_emp]
    have h16 : (dst + 8#64) + 8#64 = dst + 16#64 := by bv_omega
    rw [h16]
  rw [hhdr a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [hhdr dst, wordsAt_eq_pointsToBytes]
  exact sepConj_mono_right (Entails.pure_right ⟨hlen, hcap, hptr⟩ (Entails.refl _))

theorem unchunkedEkSentAt_extract_niche (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSent (spqrAuthApi F)) :
    unchunkedEkSentAt A a st ⊢
      ∃∗ g : ThreeVecWords,
        ⌜g.v1.w0 ≠ 0xfffffffffffffffe#64 ∧ g.v1.w0 ≠ noneCap⌝ ∗
        wordsAt a (ekSentWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedEkSentAt A dst st)
          (wordsBytes (ekSentWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st2 : Unchunked.SendCt.Ct2Sent (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.dk⟩⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedCt2SentAt A (dst + 24#64) st2 = unchunkedEkSentAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.dk) ∗
        (((dst + 24#64) + 48#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.dk ∗ ((dst + 72#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64]; ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_niche A a r0) (unchunkedCt2SentAt_extract A (a + 24#64) st2)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro auth
  rw [sepConj_assoc (⌜_⌝)]; apply Entails.pure_left; intro hne
  refine Entails.sepExists_right ⟨v1, auth⟩ (Entails.pure_right hne ?_)
  exact wordsExtract_sepConj rfl heq

theorem chunkedHeaderReceivedAt_extract60_niche (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A a st ⊢
      ∃∗ w : Words60,
        ⌜w.b0.w0 ≠ 0xfffffffffffffffe#64 ∧ w.b0.w0 ≠ noneCap⌝ ∗
        words60At a w ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst st) (wordsBytes (words60List w)) := by
  unfold chunkedHeaderReceivedAt
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine Entails.trans (sepConj_mono
    (unchunkedEkSentAt_extract_niche A a { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ek) (a + 80#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  rw [sepConj_assoc (⌜_⌝)]; apply Entails.pure_left; intro hne
  let w := mkWords60_10_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right hne ?_)
  rw [words60At_eq_wordsAt, ← words60List_mkWords60_10_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem nhr_done_1856_split {A : RustAlloc} {F : ShaCompress} (fsp : BitVec 64)
    (outSt : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    noHeaderReceivedRecvChunkResultAt A (F := F) (fsp + 1856#64) (.ok (.done outSt)) ⊢
      ∃∗ w_out : Words60,
        ⌜w_out.b0.w0 ≠ 0xfffffffffffffffe#64 ∧ w_out.b0.w0 ≠ noneCap⌝ ∗
        words60At (fsp + 1856#64) w_out ∗
        relocatedHeap (fun dst => chunkedHeaderReceivedAt A dst outSt) (wordsBytes (words60List w_out)) := by
  dsimp only [noHeaderReceivedRecvChunkResultAt, noHeaderReceivedRecvChunkAt]
  apply Entails.pure_left; intro _
  exact chunkedHeaderReceivedAt_extract60_niche A (fsp + 1856#64) outSt

end CryptoVerification.SpqrV1.States.Recv

