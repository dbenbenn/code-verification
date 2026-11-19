/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunkSym -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2Encoder
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::send_ct::Ct1Acknowledged>::recv_ek_chunk` (`0x5e9c8`)

**Checked by Lean.**

Verifies `ct1_acknowledged_recv_ek_chunk_ok_ext` (`0x5e9c8`, 153 instructions) against
`ct1AcknowledgedRecvEkChunkSpec A F K b`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff addChunkTotal
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

@[simp, local arm64_norm] theorem ct1AckEk_trace_writeVReg128 (s : State) (r : BitVec 5)
    (v : BitVec 128) : (s.writeVReg128 r v).trace = s.trace := rfl

@[local arm64_norm, local wp_norm]
private theorem hsp_add_8 (s₀ : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 8#64 = s₀.sp - 680#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem hsp_592_add_8 (s₀ : State) :
    (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s₀ + 592#64) + 8#64 = s₀.sp - 88#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm]
private theorem esp_add_8 (s₀ : State) :
    CryptoVerification.LibsignalTripleRatchet.Expand.esp s₀ + 8#64 = s₀.sp - 488#64 := by
  unfold CryptoVerification.LibsignalTripleRatchet.Expand.esp; bv_omega

/-! ## 1. Done Branch (`+0x098..+0x184`) -/

theorem wordsAt_sp1176_fiveVec (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 1176#64) (fiveVecWordsList g ep) =
      ((sp - 1176#64) ↦₆₄ g.v1.w0) ∗ ((sp - 1168#64) ↦₆₄ g.v1.w1) ∗
      ((sp - 1160#64) ↦₆₄ g.v1.w2) ∗ ((sp - 1152#64) ↦₆₄ g.rest.v1.w0) ∗
      ((sp - 1144#64) ↦₆₄ g.rest.v1.w1) ∗ ((sp - 1136#64) ↦₆₄ g.rest.v1.w2) ∗
      ((sp - 1128#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((sp - 1120#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((sp - 1112#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((sp - 1104#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((sp - 1096#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((sp - 1088#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((sp - 1080#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((sp - 1072#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((sp - 1064#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((sp - 1056#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVec]; simp only [arm64_norm]

theorem wordsAt_sp592_fiveVec (sp : BitVec 64) (g : FiveVecWords) (ep : BitVec 64) :
    wordsAt (sp - 592#64) (fiveVecWordsList g ep) =
      ((sp - 592#64) ↦₆₄ g.v1.w0) ∗ ((sp - 584#64) ↦₆₄ g.v1.w1) ∗
      ((sp - 576#64) ↦₆₄ g.v1.w2) ∗ ((sp - 568#64) ↦₆₄ g.rest.v1.w0) ∗
      ((sp - 560#64) ↦₆₄ g.rest.v1.w1) ∗ ((sp - 552#64) ↦₆₄ g.rest.v1.w2) ∗
      ((sp - 544#64) ↦₆₄ g.rest.rest.v1.w0) ∗ ((sp - 536#64) ↦₆₄ g.rest.rest.v1.w1) ∗
      ((sp - 528#64) ↦₆₄ g.rest.rest.v1.w2) ∗ ((sp - 520#64) ↦₆₄ g.rest.rest.auth.v1.w0) ∗
      ((sp - 512#64) ↦₆₄ g.rest.rest.auth.v1.w1) ∗ ((sp - 504#64) ↦₆₄ g.rest.rest.auth.v1.w2) ∗
      ((sp - 496#64) ↦₆₄ g.rest.rest.auth.v2.w0) ∗ ((sp - 488#64) ↦₆₄ g.rest.rest.auth.v2.w1) ∗
      ((sp - 480#64) ↦₆₄ g.rest.rest.auth.v2.w2) ∗ ((sp - 472#64) ↦₆₄ ep) := by
  rw [wordsAt_fiveVec]; simp only [arm64_norm]

/-- Callee-saved registers preserved across `__rust_dealloc` calls in `ct1_ack_recv_ek_done_branch`. -/
@[expose] def Ct1AckDoneSaved (s0 s : State) (sp1760 outA ct2Cap ct2Ptr : BitVec 64) : Prop :=
  s.readReg64 .x19 = outA ∧ s.readReg64 .x20 = ct2Cap ∧ s.readReg64 .x21 = ct2Ptr ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.sp = sp1760 ∧ s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

theorem ct1Ack_done_uc1_copy_recompose {A : RustAlloc} {F : ShaCompress}
    (sp : BitVec 64) (uc1 : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F))
    (g : FiveVecWords) (u0 u1 u2 : BitVec 64) :
    wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch)) ∗
      (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ⊢
    unchunkedCt1SentEkReceivedAt A (sp - 1176#64) uc1 ∗
      memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 := by
  have h1 : wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch)) ⊢
      unchunkedCt1SentEkReceivedAt A (sp - 1176#64) uc1 :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1176#64)
  have h2 : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ⊢
      memRegion (sp - 1200#64) 24 := by
    have heq : (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) =
        wordsAt (sp - 1200#64) [u0, u1, u2] := by
      simp only [wordsAt, wordsAt_cons_off, wordsAt_nil, sepConj_emp,
        show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion _ (sp - 1200#64) 24 rfl
  have h3 : wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) ⊢
      memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 := by
    rw [← ProofLib.memRegion_split' (b := sp - 592#64) (n := 104) (k := 24) (b' := sp - 488#64) rfl (by bv_omega) (by decide)]
    exact wordsAt_entails_memRegion _ (sp - 592#64) 128 rfl
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (sp - 1176#64) (fiveVecWordsList g uc1.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst uc1)
        (wordsBytes (fiveVecWordsList g uc1.epoch))) ∗
    (((sp - 1200#64) ↦₆₄ u0) ∗ ((sp - 1192#64) ↦₆₄ u1) ∗ ((sp - 1184#64) ↦₆₄ u2)) ∗
    wordsAt (sp - 592#64) (fiveVecWordsList g uc1.epoch) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 h3)

theorem ct1Ack_done_uc56_and_headers_recompose {A : RustAlloc} {F : ShaCompress}
    (sp : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (g : AuthWords) (c0 c1 c2 m0 m1 m2 : BitVec 64) :
    wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ∗
      ((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
      ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2) ⊢
    unchunkedCt2SentAt A (sp - 648#64) outUc ∗ memRegion (sp - 592#64) 104 := by
  have h1 : wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (sp - 648#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (sp - 648#64)
  have h2_sp : wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ⊢
      memRegion (sp - 592#64) 56 :=
    wordsAt_entails_memRegion (ct2SentWordsList g outUc.epoch) (sp - 592#64) 56 rfl
  have h2_hdr :
      ((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
      ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2) ⊢
      memRegion (sp - 536#64) 48 := by
    have heq :
        (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
         ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2)) =
        wordsAt (sp - 536#64) [c0, c1, c2, m0, m1, m2] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [c0, c1, c2, m0, m1, m2] (sp - 536#64) 48 rfl
  have h2 :
      wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
       ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2)) ⊢
      memRegion (sp - 592#64) 104 := by
    refine Entails.trans (sepConj_mono h2_sp h2_hdr) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 592#64) (n := 56) (k := 48) (b' := sp - 536#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (sp - 648#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch))) ∗
    (wordsAt (sp - 592#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 536#64) ↦₆₄ c0) ∗ ((sp - 528#64) ↦₆₄ c1) ∗ ((sp - 520#64) ↦₆₄ c2) ∗
       ((sp - 512#64) ↦₆₄ m0) ∗ ((sp - 504#64) ↦₆₄ m1) ∗ ((sp - 496#64) ↦₆₄ m2))) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem ct1Ack_done_scratch_join (sp : BitVec 64) :
    memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 1176#64) 128 ∗
      memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 ∗ memRegion (sp - 464#64) 400 ⊢
    memRegion (sp - 1224#64) 176 ∗ memRegion (sp - 592#64) 528 := by
  have h1 : memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 24 ∗ memRegion (sp - 1176#64) 128 =
      memRegion (sp - 1224#64) 176 := by
    rw [← ProofLib.memRegion_split' (b := sp - 1200#64) (n := 24) (k := 128) (b' := sp - 1176#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 152) (b' := sp - 1200#64) rfl (by bv_omega) (by decide)]
  have h2 : memRegion (sp - 592#64) 104 ∗ memRegion (sp - 488#64) 24 ∗ memRegion (sp - 464#64) 400 =
      memRegion (sp - 592#64) 528 := by
    rw [← ProofLib.memRegion_split' (b := sp - 488#64) (n := 24) (k := 400) (b' := sp - 464#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 592#64) (n := 104) (k := 424) (b' := sp - 488#64) rfl (by bv_omega) (by decide)]
  rw [← h1, ← h2]; exact Entails.of_eq (by ac_rfl)

theorem ct1Ack_done_stack_1160_rejoin (sp : BitVec 64) :
    memRegion (sp - 1224#64) 176 ∗ memRegion (sp - 1048#64) 456 ∗ memRegion (sp - 592#64) 528 ⊢
    memRegion (sp - 1224#64) 1160 := by
  rw [← ProofLib.memRegion_split' (b := sp - 1048#64) (n := 456) (k := 528) (b' := sp - 592#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 1224#64) (n := 176) (k := 984) (b' := sp - 1048#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem ct1Ack_done_outA_recompose (A : RustAlloc) {F : ShaCompress}
    (outA : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (sendingCt2 : PolyEncoder)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (hres : res = .ok (.done { uc := outUc, sending_ct2 := sendingCt2 })) :
    (outA ↦₆₄ 0xffffffffffffffff#64) ∗
      chunkedCt2SampledAt A (outA + 8#64) { uc := outUc, sending_ct2 := sendingCt2 } ∗
      memRegion (outA + 464#64) 64 ⊢
    ct1AcknowledgedRecvEkChunkResAt A outA res := by
  subst hres; exact Entails.refl _

theorem ct1AckEk_sepWPp_congr_pre {prog : Program} {pc : BitVec 64} {s : State} {P1 P2 : SepProp}
    {post1 post2 fail1 fail2 : State → SepProp → Prop}
    (h : SepWPp prog pc s P1 post1 fail1) (hP : P1 = P2) (hpost : post1 = post2)
    (hfail : fail1 = fail2) :
    SepWPp prog pc s P2 post2 fail2 := by
  subst hP hpost hfail; exact h

theorem ct1Ack_some_pre_recvEk (A : RustAlloc) {F : ShaCompress}
    (sp stA : BitVec 64) (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (decoded : Bytes) (g_uc : FiveVecWords) (v_dec : VecWords) :
    wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ∗
      wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ∗
      wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec)) ∗
      memRegion (sp - 1200#64) 1136 ⊢
    memRegion stA 528 ∗ unchunkedCt1SentAt A (sp - 1760#64) uc ∗
      vecU8 A (sp - 1224#64) decoded ∗ memRegion (sp - 1200#64) 608 ∗
      memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400 := by
  have h1 : wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400 ⊢
      memRegion stA 528 := by
    refine Entails.trans (sepConj_mono_left (wordsAt_entails_memRegion _ stA 128 rfl)) ?_
    rw [← ProofLib.memRegion_split' (b := stA) (n := 128) (k := 400) (b' := stA + 128#64) rfl rfl (by decide)]
    exact Entails.refl _
  have h2 : wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch)) ⊢
      unchunkedCt1SentAt A (sp - 1760#64) uc :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1760#64)
  have h3 : wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec)) ⊢
      vecU8 A (sp - 1224#64) decoded :=
    recompose_wordsAt_relocatedHeap _ _ (sp - 1224#64)
  have h4 : memRegion (sp - 1200#64) 1136 =
      memRegion (sp - 1200#64) 608 ∗ memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400 := by
    rw [ProofLib.memRegion_split' (b := sp - 1200#64) (n := 608) (k := 528) (b' := sp - 592#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := sp - 592#64) (n := 128) (k := 400) (b' := sp - 464#64) rfl (by bv_omega) (by decide)]
  rw [h4]
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt stA (fiveVecWordsList g_uc uc.epoch) ∗ memRegion (stA + 128#64) 400) ∗
    (wordsAt (sp - 1760#64) (fiveVecWordsList g_uc uc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt1SentAt A dst uc)
        (wordsBytes (fiveVecWordsList g_uc uc.epoch))) ∗
    (wordsAt (sp - 1224#64) (vecWordsList v_dec) ∗
      relocatedHeap (fun dst => vecU8 A dst decoded) (wordsBytes (vecWordsList v_dec))) ∗
    (memRegion (sp - 1200#64) 608 ∗ memRegion (sp - 592#64) 128 ∗ memRegion (sp - 464#64) 400) by ac_rfl)) ?_
  exact sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))

theorem ct1Ack_some_post_recvEk (sp : BitVec 64) :
    memRegion (sp - 1760#64) 128 ∗ memRegion (sp - 1632#64) 8 ∗
      memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 608 ⊢
    memRegion (sp - 1760#64) 136 ∗ memRegion (sp - 1224#64) 632 := by
  have h1 : memRegion (sp - 1760#64) 128 ∗ memRegion (sp - 1632#64) 8 = memRegion (sp - 1760#64) 136 :=
    (ProofLib.memRegion_split' (b := sp - 1760#64) (n := 128) (k := 8) (b' := sp - 1632#64) rfl (by bv_omega) (by decide)).symm
  have h2 : memRegion (sp - 1224#64) 24 ∗ memRegion (sp - 1200#64) 608 = memRegion (sp - 1224#64) 632 :=
    (ProofLib.memRegion_split' (b := sp - 1224#64) (n := 24) (k := 608) (b' := sp - 1200#64) rfl (by bv_omega) (by decide)).symm
  rw [← sepConj_assoc, h1, h2]
  exact Entails.refl _

end CryptoVerification.SpqrV1.States.Leaves
