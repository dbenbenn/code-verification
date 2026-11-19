/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm, Part 1

**Checked by Lean.** Verifies the `msg.epoch > st.uc.epoch`, `msg.epoch < st.uc.epoch`,
`msg.epoch = st.uc.epoch ∧ msg.payload ≠ .ct2 _`, and post-call `.error` paths of
`.ekSentCt1Received` (`0x55538`, `+228`).
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
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

theorem stackAt_statesRecvStackX_split_dropStack32 (sp : BitVec 64) :
    stackAt sp statesRecvStackX =
      memRegion (sp - 23792#64) 19664 ∗ stackAt sp dropStack32 :=
  stackAt_split_bottom sp dropStack32 19664 (by decide)

/-! ## 1. `.ekSentCt1Received` (`0x55538`, `+228`): `msg.epoch > st.uc.epoch` -/

@[expose] def errMacVerifyTag8At (a : BitVec 64) : SepProp :=
  (a ↦₈ 3#8) ∗ memRegion (a + 1#64) 7

@[expose] def errMacVerifyTag8Split : SplitBytes 8 errMacVerifyTag8At :=
  have h : ∀ a, ((a ↦₈ 3#8) ∗ memRegion (a + BitVec.ofNat 64 1) 7) = errMacVerifyTag8At a :=
    fun _ => rfl
  SplitBytes.congr h ((SplitBytes.pointsTo8 3#8).seq (SplitBytes.region 7 (by decide)) (by decide))

theorem extract_errMacVerifyTag8_word (a : BitVec 64) :
    errMacVerifyTag8At a ⊢ ∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ errMacVerifyTag8Split.heap (unpack64 w) := by
  refine Entails.trans (errMacVerifyTag8Split.to_bytes a) ?_
  apply Entails.sepExists_elim; intro bs
  apply Entails.pure_left; intro hlen
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 hlen
  subst hw
  rw [← pointsTo64_eq_pointsToBytes a w]
  exact Entails.sepExists_right w (Entails.refl _)

theorem recompose_errMacVerifyTag8_word (a : BitVec 64) (w : BitVec 64) :
    (a ↦₆₄ w) ∗ errMacVerifyTag8Split.heap (unpack64 w) ⊢ errMacVerifyTag8At a := by
  rw [pointsTo64_eq_pointsToBytes a w]
  exact errMacVerifyTag8Split.of_bytes a (unpack64 w) (unpack64_length w)

theorem err_result_976_extract (A : RustAlloc) {F : ShaCompress} (fsp : BitVec 64) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) (fsp + 976#64) (.error (.err .macVerifyFailed)) ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((fsp + 976#64) ↦₆₄ none2Cap) ∗
        ((fsp + 984#64) ↦₆₄ w1) ∗
        ((fsp + 992#64) ↦₆₄ w2) ∗
        ((fsp + 1000#64) ↦₆₄ w3) ∗
        errMacVerifyTag8Split.heap (unpack64 w1) ∗
        memRegion (fsp + 1008#64) 472 := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, spqrErrorByte]
  rw [show (fsp + 976#64) + 8#64 = fsp + 984#64 by bv_omega,
      show (fsp + 976#64) + 9#64 = fsp + 985#64 by bv_omega,
      ProofLib.memRegion_split' (b := fsp + 985#64) (n := 7) (k := 488)
        (b' := fsp + 992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 992#64) (n := 8) (k := 480)
        (b' := fsp + 1000#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1000#64) (n := 8) (k := 472)
        (b' := fsp + 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 992#64),
      ProofLib.memRegion_eight (fsp + 1000#64)]
  have htag : ((fsp + 984#64) ↦₈ 3#8) ∗ memRegion (fsp + 985#64) 7 ⊢
      ∃∗ w1 : BitVec 64, ((fsp + 984#64) ↦₆₄ w1) ∗ errMacVerifyTag8Split.heap (unpack64 w1) := by
    rw [show fsp + 985#64 = (fsp + 984#64) + 1#64 by bv_omega]
    exact extract_errMacVerifyTag8_word (fsp + 984#64)
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 976#64) ↦₆₄ none2Cap) ∗
    (((fsp + 984#64) ↦₈ 3#8) ∗ memRegion (fsp + 985#64) 7) ∗
    (∃∗ v : BitVec 64, (fsp + 992#64) ↦₆₄ v) ∗
    (∃∗ v : BitVec 64, (fsp + 1000#64) ↦₆₄ v) ∗
    memRegion (fsp + 1008#64) 472 by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left htag)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w3
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3 ?_))
  exact Entails.of_eq (by ac_rfl)

theorem err_result_976_fold_880 (fsp w1 w2 w3 : BitVec 64) :
    ((fsp + 976#64) ↦₆₄ none2Cap) ∗
    ((fsp + 984#64) ↦₆₄ w1) ∗
    ((fsp + 992#64) ↦₆₄ w2) ∗
    ((fsp + 1000#64) ↦₆₄ w3) ∗
    memRegion (fsp + 1008#64) 472 ∗
    memRegion (fsp + 1480#64) 376 ⊢
      memRegion (fsp + 976#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 8) (k := 872)
        (b' := fsp + 984#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 984#64) (n := 8) (k := 864)
        (b' := fsp + 992#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 992#64) (n := 8) (k := 856)
        (b' := fsp + 1000#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1000#64) (n := 8) (k := 848)
        (b' := fsp + 1008#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1008#64) (n := 472) (k := 376)
        (b' := fsp + 1480#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))

theorem memRegion_960_split_err4 (outA : BitVec 64) :
    memRegion outA v1RecvSize ⊢
      ∃∗ v0 : BitVec 64, ∃∗ v8 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v24 : BitVec 64,
        (outA ↦₆₄ v0) ∗ ((outA + 8#64) ↦₆₄ v8) ∗
        ((outA + 16#64) ↦₆₄ v16) ∗ ((outA + 24#64) ↦₆₄ v24) ∗
        memRegion (outA + 32#64) 928 := by
  unfold v1RecvSize
  rw [ProofLib.memRegion_split outA 8 952 (by decide),
      ProofLib.memRegion_split' (b := outA + 8#64) (n := 8) (k := 944)
        (b' := outA + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
        (b' := outA + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
        (b' := outA + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight outA,
      ProofLib.memRegion_eight (outA + 8#64),
      ProofLib.memRegion_eight (outA + 16#64),
      ProofLib.memRegion_eight (outA + 24#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro v24
  apply Entails.sepExists_elim; intro v16
  apply Entails.sepExists_elim; intro v8
  apply Entails.sepExists_elim; intro v0
  refine Entails.sepExists_right v0 (Entails.sepExists_right v8
    (Entails.sepExists_right v16 (Entails.sepExists_right v24 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem err4_entails_resultV1RecvAt_macVerifyFailed (A : RustAlloc) {F : ShaCompress}
    (outA w1 w2 w3 : BitVec 64) :
    (outA ↦₆₄ noneCap) ∗
    ((outA + 8#64) ↦₆₄ w1) ∗
    errMacVerifyTag8Split.heap (unpack64 w1) ∗
    ((outA + 16#64) ↦₆₄ w2) ∗
    ((outA + 24#64) ↦₆₄ w3) ∗
    memRegion (outA + 32#64) 928 ⊢
      resultV1RecvAt A (F := F) outA (.error (.err .macVerifyFailed)) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  have hrec := recompose_errMacVerifyTag8_word (outA + 8#64) w1
  unfold errMacVerifyTag8At at hrec
  rw [show (outA + 8#64) + 1#64 = outA + 9#64 by bv_omega] at hrec
  have h951 :
      memRegion (outA + 9#64) 7 ∗
      ((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗
      memRegion (outA + 32#64) 928 ⊢
        memRegion (outA + 9#64) 951 := by
    rw [ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944)
          (b' := outA + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
          (b' := outA + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
          (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (outA + 9#64) 7 ∗
      (((outA + 16#64) ↦₆₄ w2) ∗ (((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928)) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗
    (((outA + 8#64) ↦₆₄ w1) ∗ errMacVerifyTag8Split.heap (unpack64 w1)) ∗
    (((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left hrec)) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    (outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 3#8) ∗
    (memRegion (outA + 9#64) 7 ∗ ((outA + 16#64) ↦₆₄ w2) ∗
      ((outA + 24#64) ↦₆₄ w3) ∗ memRegion (outA + 32#64) 928) by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right h951)

theorem messagePayloadTag_ct2 (chunk : Chunk) :
    messagePayloadTag (.ct2 chunk) = 6#8 := rfl

@[expose] def mkWords63_done (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (v_sec : VecWords) (sec_ep w_pad : BitVec 64) : Words63 :=
  { b0 := ⟨noneCap, g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2, ep, p.b0.w0, p.b0.w1⟩
    b1 := ⟨p.b0.w2, p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9, p.b1.w0, p.b1.w1⟩
    b2 := ⟨p.b1.w2, p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9, p.b2.w0, p.b2.w1⟩
    b3 := ⟨p.b2.w2, p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9, p.b3.w0, p.b3.w1⟩
    b4 := ⟨p.b3.w2, p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9, p.b4.w0, p.b4.w1⟩
    b5 := ⟨p.b4.w2, p.b4.w3, p.b4.w4, p.b4.w5, p.b4.w6, p.b4.w7, p.b4.w8, p.b4.w9, v_sec.w0, v_sec.w1⟩
    q60 := sec_ep ++ v_sec.w2
    w62 := w_pad }

theorem words63List_mkWords63_done (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (v_sec : VecWords) (sec_ep w_pad : BitVec 64) :
    ([noneCap] ++ (ct2SentWordsList g ep ++ words5x10List p)) ++
      (vecWordsList v_sec ++ [sec_ep, w_pad]) =
      words63List (mkWords63_done g ep p v_sec sec_ep w_pad) := by
  simp only [words63List, mkWords63_done, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList,
    Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append, List.append_assoc,
    List.cons_append, List.nil_append]

theorem chunkedNoHeaderReceivedAt_extract57_ct2 (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedNoHeaderReceivedAt A a nhr ⊢
      ∃∗ g : AuthWords, ∃∗ p : Words5x10,
        wordsAt a (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) := by
  unfold chunkedNoHeaderReceivedAt
  refine Entails.trans (sepConj_mono
    (unchunkedCt2SentAt_extract A a ⟨nhr.uc.epoch, nhr.uc.auth⟩)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A nhr.receiving_hdr) (a + 56#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  refine Entails.sepExists_right g (Entails.sepExists_right p ?_)
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem done_result_976_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) a (.ok (.done (nhr, sec))) ⊢
      ∃∗ g : AuthWords, ∃∗ p : Words5x10, ∃∗ v_sec : VecWords, ∃∗ w_pad : BitVec 64,
        words63At a (mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
        relocatedHeap (fun dst => vecU8 A dst sec.secret)
          (wordsBytes (vecWordsList v_sec)) := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt, epochSecretAt]
  apply Entails.pure_left; intro _
  rw [ProofLib.memRegion_eight (a + 496#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono
    (chunkedNoHeaderReceivedAt_extract57_ct2 A (a + 8#64) nhr)
    (sepConj_mono_left (sepConj_mono_left (vecU8_extract A (a + 464#64) sec.secret))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro w_pad
  apply Entails.sepExists_elim; intro v_sec
  apply Entails.sepExists_elim; intro g
  apply Entails.sepExists_elim; intro p
  refine Entails.sepExists_right g (Entails.sepExists_right p
    (Entails.sepExists_right v_sec (Entails.sepExists_right w_pad ?_)))
  have hw_eq :
      words63At a (mkWords63_done g nhr.uc.epoch p v_sec sec.epoch w_pad) =
      (a ↦₆₄ noneCap) ∗
      wordsAt (a + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      wordsAt (a + 464#64) (vecWordsList v_sec) ∗
      ((a + 488#64) ↦₆₄ sec.epoch) ∗
      ((a + 496#64) ↦₆₄ w_pad) := by
    rw [words63At_eq_wordsAt, ← words63List_mkWords63_done,
        wordsAt_append ([noneCap] ++ (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p))
          (vecWordsList v_sec ++ [sec.epoch, w_pad]),
        wordsAt_append [noneCap] (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p),
        wordsAt_append (vecWordsList v_sec) [sec.epoch, w_pad]]
    simp only [List.length_append, List.length_singleton, length_ct2SentWordsList,
      length_words5x10List, length_vecWordsList, wordsAt, sepConj_emp,
      bv_add_lit_add_lit_recv, sepConj_assoc]
  simp only [hw_eq, bv_add_lit_add_lit_recv, arm64_norm]
  exact Entails.of_eq (by ac_rfl)

@[expose] def mkWords63_nhr_tail (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) : Words63 :=
  { b0 := ⟨g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2, ep, p.b0.w0, p.b0.w1, p.b0.w2⟩
    b1 := ⟨p.b0.w3, p.b0.w4, p.b0.w5, p.b0.w6, p.b0.w7, p.b0.w8, p.b0.w9, p.b1.w0, p.b1.w1, p.b1.w2⟩
    b2 := ⟨p.b1.w3, p.b1.w4, p.b1.w5, p.b1.w6, p.b1.w7, p.b1.w8, p.b1.w9, p.b2.w0, p.b2.w1, p.b2.w2⟩
    b3 := ⟨p.b2.w3, p.b2.w4, p.b2.w5, p.b2.w6, p.b2.w7, p.b2.w8, p.b2.w9, p.b3.w0, p.b3.w1, p.b3.w2⟩
    b4 := ⟨p.b3.w3, p.b3.w4, p.b3.w5, p.b3.w6, p.b3.w7, p.b3.w8, p.b3.w9, p.b4.w0, p.b4.w1, p.b4.w2⟩
    b5 := ⟨p.b4.w3, p.b4.w4, p.b4.w5, p.b4.w6, p.b4.w7, p.b4.w8, p.b4.w9, u57, u58, u59⟩
    q60 := q60
    w62 := w62 }

theorem words63List_mkWords63_nhr_tail (g : AuthWords) (ep : BitVec 64) (p : Words5x10)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) :
    words63List (mkWords63_nhr_tail g ep p u57 u58 u59 q60 w62) =
      (ct2SentWordsList g ep ++ words5x10List p) ++
      [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] := by
  simp only [words63List, mkWords63_nhr_tail, words5x10List, words10List,
    ct2SentWordsList, authWordsList, vecWordsList, List.append_assoc,
    List.cons_append, List.nil_append]

theorem writeback_noHeaderReceived_some_entails_resultV1RecvAt
    (A : RustAlloc) {F : ShaCompress} (outA : BitVec 64)
    (nhr : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F))
    (sec : EpochSecret)
    (g : AuthWords) (p : Words5x10) (v_sec : VecWords)
    (u57 u58 u59 : BitVec 64) (q60 : BitVec 128) (w62 : BitVec 64) :
    relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
      (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
    relocatedHeap (fun dst => vecU8 A dst sec.secret)
      (wordsBytes (vecWordsList v_sec)) ∗
    (outA ↦₆₄ 7#64) ∗
    words63At (outA + 8#64) (mkWords63_nhr_tail g nhr.uc.epoch p u57 u58 u59 q60 w62) ∗
    memRegion (outA + 512#64) 376 ∗
    memRegion (outA + 888#64) 40 ∗
    ((outA + 928#64) ↦₆₄ v_sec.w0) ∗
    ((outA + 936#64) ↦₆₄ v_sec.w1) ∗
    ((outA + 944#64) ↦₁₂₈ (sec.epoch ++ v_sec.w2)) ⊢
      resultV1RecvAt A (F := F) outA (.ok { key := some sec, state := .noHeaderReceived nhr }) := by
  dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt, optEpochSecretAt, epochSecretAt]
  have hw63 :
      words63At (outA + 8#64) (mkWords63_nhr_tail g nhr.uc.epoch p u57 u58 u59 q60 w62) =
      wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] := by
    rw [words63At_eq_wordsAt, words63List_mkWords63_nhr_tail,
        wordsAt_append (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)]
    simp only [List.length_append, length_ct2SentWordsList, length_words5x10List,
      bv_add_lit_add_lit_recv]
  have hsec_words :
      ((outA + 928#64) ↦₆₄ v_sec.w0) ∗
      ((outA + 936#64) ↦₆₄ v_sec.w1) ∗
      ((outA + 944#64) ↦₁₂₈ (sec.epoch ++ v_sec.w2)) =
      wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
      ((outA + 952#64) ↦₆₄ sec.epoch) := by
    simp only [vecWordsList, wordsAt, sepConj_emp, pointsTo128_eq_pair64_recv,
      Leaves.extractLsb'_0_64_append, Leaves.extractLsb'_64_64_append,
      bv_add_lit_add_lit_recv, sepConj_assoc]
  have hnhr_rec :
      wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ⊢
      chunkedNoHeaderReceivedAt A (outA + 8#64) nhr := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose _ _ (outA + 8#64)
  have hsec_rec :
      wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ⊢
      vecU8 A (outA + 928#64) sec.secret := by
    rw [wordsAt_eq_pointsToBytes]
    exact relocatedHeap_recompose _ _ (outA + 928#64)
  have h464 :
      wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ⊢
      memRegion (outA + 464#64) 464 := by
    rw [ProofLib.memRegion_split' (b := outA + 464#64) (n := 48) (k := 416)
          (b' := outA + 512#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 512#64) (n := 376) (k := 40)
          (b' := outA + 888#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (wordsAt_entails_memRegion _ (outA + 464#64) 48 rfl)
  rw [hw63, hsec_words, bv_add_lit_add_lit_recv]
  have hreord :
      relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
        (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p)) ∗
      relocatedHeap (fun dst => vecU8 A dst sec.secret)
        (wordsBytes (vecWordsList v_sec)) ∗
      (outA ↦₆₄ 7#64) ∗
      (wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
       wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62]) ∗
      memRegion (outA + 512#64) 376 ∗
      memRegion (outA + 888#64) 40 ∗
      (wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
       ((outA + 952#64) ↦₆₄ sec.epoch)) =
      ((outA ↦₆₄ 7#64) ∗
       (wordsAt (outA + 8#64) (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p) ∗
        relocatedHeap (fun dst => chunkedNoHeaderReceivedAt A dst nhr)
          (wordsBytes (ct2SentWordsList g nhr.uc.epoch ++ words5x10List p))) ∗
       (wordsAt (outA + 464#64) [u57, u58, u59, q60.extractLsb' 0 64, q60.extractLsb' 64 64, w62] ∗
        memRegion (outA + 512#64) 376 ∗
        memRegion (outA + 888#64) 40)) ∗
      ((wordsAt (outA + 928#64) (vecWordsList v_sec) ∗
        relocatedHeap (fun dst => vecU8 A dst sec.secret)
          (wordsBytes (vecWordsList v_sec))) ∗
       ((outA + 952#64) ↦₆₄ sec.epoch)) := by ac_rfl
  rw [hreord]
  exact sepConj_mono
    (sepConj_mono_right (sepConj_mono hnhr_rec h464))
    (sepConj_mono_left hsec_rec)

theorem memRegion_880_split_504_376_ct2 (a a504 : BitVec 64) (ha : a + 504#64 = a504) :
    memRegion a 880 = memRegion a 504 ∗ memRegion a504 376 :=
  ProofLib.memRegion_split' rfl ha.symm (by decide)

end CryptoVerification.SpqrV1.States.Recv
