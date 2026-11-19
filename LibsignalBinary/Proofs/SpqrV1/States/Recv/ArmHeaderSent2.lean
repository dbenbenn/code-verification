/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.headerSent` Arm, Part 2

**Checked by Lean.** Post-call `.done` / `.stillReceiving` writeback blocks, the
`<HeaderSent>::recv_ct1_chunk` (`eq_ct1`) branch, and the complete `.headerSent` arm
`states_recv_arm_headerSent` (`0x55760`, `+780`).
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
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
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
  bv376_toNat_hs

@[local arm64_norm, local wp_norm]
theorem bv880_toNat_hs : (880#64 : BitVec 64).toNat = 880 := rfl

/-! ## 1. Stack, Relocation, and Tag-Extraction Helpers for `.headerSent` -/

theorem sendEkUnusedAt_split_f10 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qf10 : BitVec 128,
        ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2736#64) 1120 ∗
        memRegion (fsp + 3872#64) 272 := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 1120) (k := 288)
        (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272)
        (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 3856#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qf10
  refine Entails.sepExists_right qf10 ?_
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_f10 (fsp : BitVec 64) (qf10 : BitVec 128) :
    ((fsp + 3856#64) ↦₁₂₈ qf10) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2736#64) 1120 ∗
    memRegion (fsp + 3872#64) 272 ⊢
      sendEkUnusedAt fsp := by
  unfold sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp + 2736#64) (n := 1120) (k := 288)
        (b' := fsp + 3856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 3856#64) (n := 16) (k := 272)
        (b' := fsp + 3872#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
    (memRegion (fsp + 2736#64) 1120 ∗ (((fsp + 3856#64) ↦₁₂₈ qf10) ∗ memRegion (fsp + 3872#64) 272)) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 3856#64) qf10)))))

theorem done_976_entails_memRegion_880 (a : BitVec 64) (w : Words63) :
    (a ↦₆₄ 2#64) ∗ words63At (a + 8#64) w ∗ memRegion (a + 512#64) 368 ⊢
      memRegion a 880 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 872) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 504) (k := 368)
        (b' := a + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a 2#64)
    (sepConj_mono_left (words63At_entails_memRegion (a + 8#64) w))

theorem Relocatable.of_chunkedHeaderSentAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    Relocatable 880 (fun a => chunkedHeaderSentAt A a st) := by
  intro src; dsimp only
  refine Entails.trans (chunkedHeaderSentAt_extract63_376 A src st) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.sepExists_elim; intro tailBytes
  apply Entails.pure_left; intro ⟨_, htail⟩
  let bs := wordsBytes (words63List w) ++ tailBytes
  have hlen : bs.length = 880 := by
    simp only [bs, List.length_append, length_wordsBytes, length_words63List, htail]
  have hbs : ∀ dst : BitVec 64,
      words63At dst w ∗ ((dst + 504#64) ↦ₛ tailBytes) = (dst ↦ₛ bs) := by
    intro dst
    rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes,
        pointsToBytes_append dst (wordsBytes (words63List w)) tailBytes,
        length_wordsBytes, length_words63List]
  refine Entails.sepExists_right bs (Entails.pure_right hlen ?_)
  rw [← sepConj_assoc, hbs src]
  exact Entails.refl _

@[expose] def polyEncoderTag : EncoderState → BitVec 64
  | .points _ => 0#64
  | .polys _ => 1#64

theorem polyEncoderTag_bne_2 (s : EncoderState) : (polyEncoderTag s != 2#64) = true := by
  cases s <;> rfl

@[expose] def polyEncoderTailAt (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) : SepProp :=
  (match enc.s with
   | .points pts =>
     ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
       pointListOf A a pts
   | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A a ps) ∗
  ((a + 384#64) ↦₃₂ enc.idx) ∗
  memRegion (a + 388#64) 4

theorem polyEncoderAt_eq_tag_tail (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc =
      (a ↦₆₄ polyEncoderTag enc.s) ∗ polyEncoderTailAt A (a + 8#64) enc := by
  unfold polyEncoderAt polyEncoderTailAt encoderStateAt polyEncoderTag
    polyEncoderPointsTag polyEncoderPolysTag polyEncoderVecsOff
    polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  have h1 : (a + 8#64) + 384#64 = a + 0x188#64 := by bv_omega
  have h2 : (a + 8#64) + 388#64 = a + 0x18c#64 := by bv_omega
  rw [h1, h2]
  cases enc.s <;> · dsimp only; ac_rfl

theorem Relocatable.of_polyEncoderTailAt (A : RustAlloc) (enc : PolyEncoder) :
    Relocatable 392 (fun a => polyEncoderTailAt A a enc) := by
  have hstate : Relocatable 384 (fun a =>
      match enc.s with
      | .points pts =>
        ⌜pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)⌝ ∗
          pointListOf A a pts
      | .polys ps => ⌜ps.length = NUM_POLYS⌝ ∗ polyListOf A a ps) := by
    cases hs : enc.s with
    | points pts =>
      dsimp only
      refine Relocatable.pure_left
        (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555))
        fun ⟨hlen, _⟩ => ?_
      exact Relocatable.arrayAt (elem := fun pt addr => pointOf A addr pt)
        (fun pt => Relocatable.vecOf A gf16Stride gf16Align gf16At pt.value)
        pts 384 (by rw [hlen]; rfl)
    | polys ps =>
      dsimp only
      refine Relocatable.pure_left (ps.length = NUM_POLYS) fun hlen => ?_
      exact Relocatable.arrayAt (elem := fun p addr => polyOf A addr p)
        (fun p => Relocatable.vecOf A gf16Stride gf16Align gf16At p.coefficients)
        ps 384 (by rw [hlen]; rfl)
  have hfull := Relocatable.sepConj (off := 384#64) (m := 392) rfl rfl hstate
    (Relocatable.sepConj (off := 4#64) (m := 8) rfl rfl
      (Relocatable.pointsTo32 enc.idx) (Relocatable.of_memRegion 4))
  refine Relocatable.congr rfl (fun a => ?_) hfull
  unfold polyEncoderTailAt
  have h2 : (a + 384#64) + 4#64 = a + 388#64 := by bv_omega
  rw [h2]

theorem exists_words5x10_cons_of_length_392 (w0 : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 392) :
    ∃ p : Words5x10, p.b0.w0 = w0 ∧ unpack64 w0 ++ bs = wordsBytes (words5x10List p) := by
  obtain ⟨w1, r2, hr2, h1⟩ := exists_word_cons_of_length_add_8 (k := 384) bs h
  obtain ⟨w2, r3, hr3, h2⟩ := exists_word_cons_of_length_add_8 (k := 376) r2 hr2
  obtain ⟨w3, r4, hr4, h3⟩ := exists_word_cons_of_length_add_8 (k := 368) r3 hr3
  obtain ⟨w4, r5, hr5, h4⟩ := exists_word_cons_of_length_add_8 (k := 360) r4 hr4
  obtain ⟨w5, r6, hr6, h5⟩ := exists_word_cons_of_length_add_8 (k := 352) r5 hr5
  obtain ⟨w6, r7, hr7, h6⟩ := exists_word_cons_of_length_add_8 (k := 344) r6 hr6
  obtain ⟨w7, r8, hr8, h7⟩ := exists_word_cons_of_length_add_8 (k := 336) r7 hr7
  obtain ⟨w8, r9, hr9, h8⟩ := exists_word_cons_of_length_add_8 (k := 328) r8 hr8
  obtain ⟨w9, r10, hr10, h9⟩ := exists_word_cons_of_length_add_8 (k := 320) r9 hr9
  obtain ⟨b1, r20, hr20, hb1⟩ := exists_words10_of_length_add_80 (k := 240) r10 hr10
  obtain ⟨b2, r30, hr30, hb2⟩ := exists_words10_of_length_add_80 (k := 160) r20 hr20
  obtain ⟨b3, r40, hr40, hb3⟩ := exists_words10_of_length_add_80 (k := 80) r30 hr30
  obtain ⟨b4, r50, hr50, hb4⟩ := exists_words10_of_length_add_80 (k := 0) r40 hr40
  have hr50_nil : r50 = [] := List.length_eq_zero_iff.mp hr50
  refine ⟨⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9⟩, b1, b2, b3, b4⟩, rfl, ?_⟩
  simp only [words5x10List, words10List, wordsBytes_append, wordsBytes_cons, wordsBytes_nil,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, hb1, hb2, hb3, hb4, hr50_nil,
    List.append_assoc, List.append_nil, List.nil_append]

theorem polyEncoderAt_extract_words5x10_tag (A : RustAlloc) (a : BitVec 64) (enc : PolyEncoder) :
    polyEncoderAt A a enc ⊢
      ∃∗ p : Words5x10,
        ⌜(p.b0.w0 != 2#64) = true⌝ ∗
        wordsAt a (words5x10List p) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst enc) (wordsBytes (words5x10List p)) := by
  let w0 := polyEncoderTag enc.s
  have h1 : polyEncoderAt A a enc ⊢
      (a ↦₆₄ w0) ∗ (∃∗ bs : List (BitVec 8),
        ⌜bs.length = 392⌝ ∗ ((a + 8#64) ↦ₛ bs) ∗
        relocatedHeap (fun dst => polyEncoderTailAt A dst enc) bs) := by
    rw [polyEncoderAt_eq_tag_tail A a enc]
    exact sepConj_mono_right (Relocatable.of_polyEncoderTailAt A enc (a + 8#64))
  refine Entails.trans h1 ?_
  rw [sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro bs
  rw [sepConj_left_comm (a ↦₆₄ w0)]
  apply Entails.pure_left; intro hlen
  obtain ⟨p, hp0, hbs⟩ := exists_words5x10_cons_of_length_392 w0 bs hlen
  refine Entails.sepExists_right p ?_
  have htag : (p.b0.w0 != 2#64) = true := hp0 ▸ polyEncoderTag_bne_2 enc.s
  refine Entails.pure_right htag ?_
  have hslice : ∀ dst : BitVec 64,
      (dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦ₛ bs) = wordsAt dst (words5x10List p) := by
    intro dst
    rw [wordsAt_eq_pointsToBytes, ← hbs, pointsToBytes_append dst (unpack64 w0) bs,
        unpack64_length, ← pointsTo64_eq_pointsToBytes dst w0]
  rw [← sepConj_assoc, hslice a]
  refine sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_)
  rw [← wordsAt_eq_pointsToBytes, ← hslice dst, polyEncoderAt_eq_tag_tail A dst enc, sepConj_assoc]
  exact sepConj_mono_right (relocatedHeap_recompose (fun d => polyEncoderTailAt A d enc) bs (dst + 8#64))

theorem chunkedHeaderSentAt_extract63_376_tag (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderSentAt A a st ⊢
      ∃∗ w : Words63, ∃∗ tailBytes : List (BitVec 8),
        ⌜(w.b0.w0 != 2#64) = true ∧ w.b5.w9 = st.uc.epoch ∧ tailBytes.length = 376⌝ ∗
        words63At a w ∗
        ((a + 504#64) ↦ₛ tailBytes) ∗
        relocatedHeap (fun dst => chunkedHeaderSentAt A dst st)
          (wordsBytes (words63List w) ++ tailBytes) := by
  unfold chunkedHeaderSentAt
  have h12 : polyEncoderAt A a st.sending_ek ∗ unchunkedEkSentAt A (a + 400#64) st.uc ⊢
      ∃∗ p : Words5x10, ∃∗ g : ThreeVecWords,
        ⌜(p.b0.w0 != 2#64) = true⌝ ∗
        wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) := by
    refine Entails.trans (sepConj_mono
      (polyEncoderAt_extract_words5x10_tag A a st.sending_ek)
      (unchunkedEkSentAt_extract A (a + 400#64) st.uc)) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc (⌜(p.b0.w0 != 2#64) = true⌝)]
    apply Entails.pure_left; intro htag
    exact Entails.sepExists_right p (Entails.sepExists_right g
      (Entails.pure_right htag (wordsExtract_sepConj rfl (fun _ => rfl))))
  refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ _).symm) ?_
  refine Entails.trans (sepConj_mono h12
    (relocatable_400_extract_words3_376 (Relocatable.of_polyDecoderAt A st.receiving_ct1) (a + 480#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro v
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro tailBytes
  rw [sepConj_assoc (⌜(p.b0.w0 != 2#64) = true⌝)]
  apply Entails.pure_left; intro htag
  rw [sepConj_left_comm (wordsAt a _ ∗ _)]
  apply Entails.pure_left; intro htail
  let w := mkWords63_50_10_3 p g st.uc.epoch v
  refine Entails.sepExists_right w (Entails.sepExists_right tailBytes ?_)
  refine Entails.pure_right ⟨htag, rfl, htail⟩ ?_
  have hw_eq := words63List_mkWords63_50_10_3 p g st.uc.epoch v
  have hwords_a :
      wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v) =
      words63At a w := by
    rw [words63At_eq_wordsAt a w, ← hw_eq,
        wordsAt_append (words5x10List p ++ ekSentWordsList g st.uc.epoch) (vecWordsList v)]
    simp only [List.length_append, length_words5x10List, length_ekSentWordsList]
  have ha504 : (a + 480#64) + 24#64 = a + 504#64 := by bv_omega
  rw [ha504]
  have hreord :
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      wordsAt (a + 480#64) (vecWordsList v) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
        (wordsBytes (vecWordsList v) ++ tailBytes) =
      (wordsAt a (words5x10List p ++ ekSentWordsList g st.uc.epoch) ∗ wordsAt (a + 480#64) (vecWordsList v)) ∗
      ((a + 504#64) ↦ₛ tailBytes) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hreord, hwords_a]
  refine sepConj_mono_right (sepConj_mono_right (relocatedHeap_intro _ fun dst => ?_))
  have hsplit_dst :
      (dst ↦ₛ (wordsBytes (words63List w) ++ tailBytes)) =
      (dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
      ((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes)) := by
    rw [← hw_eq, wordsBytes_append, List.append_assoc,
        pointsToBytes_append dst (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))
          (wordsBytes (vecWordsList v) ++ tailBytes)]
    simp only [length_wordsBytes, List.length_append, length_words5x10List, length_ekSentWordsList]
  have hreord_dst :
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
        ((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes))) ∗
      (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) =
      ((dst ↦ₛ wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch)) ∗
        relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ek ∗ unchunkedEkSentAt A (dst + 400#64) st.uc)
          (wordsBytes (words5x10List p ++ ekSentWordsList g st.uc.epoch))) ∗
      (((dst + 480#64) ↦ₛ (wordsBytes (vecWordsList v) ++ tailBytes)) ∗
        relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ct1)
          (wordsBytes (vecWordsList v) ++ tailBytes)) := by ac_rfl
  rw [hsplit_dst, hreord_dst, ← sepConj_assoc (polyEncoderAt A dst st.sending_ek)]
  exact sepConj_mono (relocatedHeap_recompose _ _ dst) (relocatedHeap_recompose _ _ (dst + 480#64))

/-! ## 2. Post-Call Writeback Blocks (`0x56848..0x56ad4` and `0x58cac..0x58ecc`) -/

theorem stackAt_statesRecvCallee_split_headerSentRecvCt1 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 928 ∗ stackAt fsp headerSentRecvCt1ChunkStack :=
  stackAt_split_bottom fsp headerSentRecvCt1ChunkStack 928 (by decide)

/-- Framed call rule for `headerSentRecvCt1ChunkSpec A F b` (`0x5d8fc`). -/
theorem call_headerSentRecvCt1Chunk {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (hcall : subroutine_ok prog entry (headerSentRecvCt1ChunkSpec A F b))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outRes : Chunked.SendEk.HeaderSentRecvChunk spqrPolyApi (spqrAuthApi F))
    (hsort : PolyDecoderStrictSorted st.receiving_ct1)
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outRes)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post Q_panic : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = outA)
    (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch)
    (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedHeaderSentAt A stA st ∗ chunkAt chunkA chunk ∗
      tokenInitAt b ∗ reduceTableAt b ∗
      A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, outRes⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [headerSentRecvCt1ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hb, hx0, hx1, hx2, hx3, hsort, hrecv⟩, hm⟩
  · dsimp only [headerSentRecvCt1ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [headerSentRecvCt1ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (headerSentRecvChunkAt A outA outRes ∗
          memRegion stA chunkedHeaderSentSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗
          A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack) ∗ Frame =
        (headerSentRecvChunkAt A outA outRes ∗
          (memRegion stA chunkedHeaderSentSize ∗
            (chunkAt chunkA chunk ∗ (tokenInitAt b ∗ (reduceTableAt b ∗
              (A.pool ∗ stackAt sp_call headerSentRecvCt1ChunkStack)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end CryptoVerification.SpqrV1.States.Recv
