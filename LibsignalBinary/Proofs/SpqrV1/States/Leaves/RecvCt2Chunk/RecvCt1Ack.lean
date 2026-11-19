/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2Defs
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::v1::chunked::send_ct::EkReceivedCt1Sampled>::recv_ct1_ack` (`0x58c20`)

Verifies `<EkReceivedCt1Sampled>::recv_ct1_ack` (`0x58c20`, 53 instructions) against
`ekReceivedCt1SampledRecvCt1AckSpec A F K b`.
-/

public section

namespace CryptoVerification.SpqrV1.States.Leaves

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_sub BitVec.sub_add_cancel BitVec.toNat_zero

theorem unchunkedCt1SentEkReceivedAt_400_eq (A : RustAlloc) {F : ShaCompress}
    (stA : BitVec 64) (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A (stA + 400#64) st =
      (authenticatorAt A (stA + 400#64) st.auth ∗
       vecU8 A (stA + 448#64) st.es ∗
       vecU8 A (stA + 472#64) st.ek ∗
       vecU8 A (stA + 496#64) st.ct1) ∗
      ((stA + 520#64) ↦₆₄ st.epoch) := by
  unfold unchunkedCt1SentEkReceivedAt
  simp only [BitVec.add_assoc, arm64_norm]

theorem stackAt_176_split (sp : BitVec 64) :
    stackAt sp ekReceivedCt1SampledRecvCt1AckStack =
      memRegion (sp - 17632#64) 736 ∗
      stackAt (sp - 176#64) unchunkedSendCt2Stack ∗
      memRegion (sp - 176#64) 8 ∗
      memRegion (sp - 168#64) 104 ∗
      memRegion (sp - 64#64) 64 := by
  change memRegion (sp - 17632#64) 17632 =
    memRegion (sp - 17632#64) 736 ∗ memRegion (sp - 176#64 - 16720#64) 16720 ∗ _
  have hsub : sp - 176#64 - 16720#64 = sp - 16896#64 := by bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - 17632#64) (n := 736) (k := 16896) (b' := sp - 16896#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 16896#64) (n := 16720) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 168) (b' := sp - 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 168#64) (n := 104) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide)]

theorem stackAt_176_to_sendCt2Encoder (sp : BitVec 64) :
    memRegion (sp - 17632#64) 736 ∗ stackAt (sp - 176#64) unchunkedSendCt2Stack ⊢
    stackAt (sp - 176#64) sendCt2EncoderStack := by
  change memRegion (sp - 17632#64) 736 ∗ memRegion (sp - 176#64 - 16720#64) 16720 ⊢
    memRegion (sp - 176#64 - 17456#64) 17456
  have h1 : sp - 176#64 - 16720#64 = sp - 16896#64 := by bv_omega
  have h2 : sp - 176#64 - 17456#64 = sp - 17632#64 := by bv_omega
  rw [h1, h2, ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 736) (k := 16720) (b' := sp - 16896#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_176_to_allocHook (sp : BitVec 64) :
    stackAt (sp - 176#64) sendCt2EncoderStack ⊢
    memRegion (sp - 17632#64) 13360 ∗ stackAt (sp - 176#64) allocHookStack := by
  change memRegion (sp - 176#64 - 17456#64) 17456 ⊢
    memRegion (sp - 17632#64) 13360 ∗ memRegion (sp - 176#64 - 4096#64) 4096
  have h1 : sp - 176#64 - 17456#64 = sp - 17632#64 := by bv_omega
  have h2 : sp - 176#64 - 4096#64 = sp - 4272#64 := by bv_omega
  rw [h1, h2, ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13360) (k := 4096) (b' := sp - 4272#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem uc_56_and_headers_recompose {A : RustAlloc} {F : ShaCompress}
    (outA sp : BitVec 64) (outUc : Unchunked.SendCt.Ct2Sent (spqrAuthApi F))
    (g : AuthWords) (w0 c0 c1 c2 m0 m1 m2 : BitVec 64) :
    wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ∗
      ((sp - 176#64) ↦₆₄ w0) ∗
      ((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
      ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2) ⊢
    unchunkedCt2SentAt A (outA + 400#64) outUc ∗ memRegion (sp - 176#64) 112 := by
  have h1 : wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch)) ⊢
      unchunkedCt2SentAt A (outA + 400#64) outUc := by
    rw [wordsAt_eq_pointsToBytes]; exact relocatedHeap_recompose _ _ (outA + 400#64)
  have h2_sp : wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ⊢
      memRegion (sp - 168#64) 56 :=
    wordsAt_entails_memRegion (ct2SentWordsList g outUc.epoch) (sp - 168#64) 56 rfl
  have h2_hdr :
      ((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
      ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2) ⊢
      memRegion (sp - 112#64) 48 := by
    have heq :
        (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
         ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2)) =
        wordsAt (sp - 112#64) [c0, c1, c2, m0, m1, m2] := by simp only [wordsAt_6, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [c0, c1, c2, m0, m1, m2] (sp - 112#64) 48 rfl
  have h2_w0 : ((sp - 176#64) ↦₆₄ w0) ⊢ memRegion (sp - 176#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion (sp - 176#64) w0
  have h2 :
      ((sp - 176#64) ↦₆₄ w0) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
       ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2)) ⊢
      memRegion (sp - 176#64) 112 := by
    refine Entails.trans (sepConj_mono h2_w0 (sepConj_mono h2_sp h2_hdr)) ?_
    rw [← ProofLib.memRegion_split' (b := sp - 168#64) (n := 56) (k := 48) (b' := sp - 112#64) rfl (by bv_omega) (by decide),
        ← ProofLib.memRegion_split' (b := sp - 176#64) (n := 8) (k := 104) (b' := sp - 168#64) rfl (by bv_omega) (by decide)]
    exact Entails.refl _
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAt (outA + 400#64) (ct2SentWordsList g outUc.epoch) ∗
      relocatedHeap (fun dst => unchunkedCt2SentAt A dst outUc)
        (wordsBytes (ct2SentWordsList g outUc.epoch))) ∗
    (((sp - 176#64) ↦₆₄ w0) ∗
      wordsAt (sp - 168#64) (ct2SentWordsList g outUc.epoch) ∗
      (((sp - 112#64) ↦₆₄ c0) ∗ ((sp - 104#64) ↦₆₄ c1) ∗ ((sp - 96#64) ↦₆₄ c2) ∗
       ((sp - 88#64) ↦₆₄ m0) ∗ ((sp - 80#64) ↦₆₄ m1) ∗ ((sp - 72#64) ↦₆₄ m2))) by ac_rfl)) ?_
  exact sepConj_mono h1 h2

theorem stackAt_176_to_dropPoly16 (sp w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    memRegion (sp - 17632#64) 13360 ∗ stackAt (sp - 176#64) allocHookStack ∗ memRegion (sp - 176#64) 112 ∗
      (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
       ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
       ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ⊢
    memRegion (sp - 17632#64) 13504 ∗ stackAt sp dropGluePoly16Stack := by
  have h8 :
      (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
       ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
       ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) ⊢
      memRegion (sp - 64#64) 64 := by
    have heq :
        (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
         ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
         ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) =
        wordsAt (sp - 64#64) [w0, w1, w2, w3, w4, w5, w6, w7] := by simp only [wordsAt_8, arm64_norm]
    rw [heq]; exact wordsAt_entails_memRegion [w0, w1, w2, w3, w4, w5, w6, w7] (sp - 64#64) 64 rfl
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h8))) ?_
  change memRegion (sp - 17632#64) 13360 ∗
      (memRegion (sp - 176#64 - 4096#64) 4096 ∗ (memRegion (sp - 176#64) 112 ∗ memRegion (sp - 64#64) 64)) ⊢
    memRegion (sp - 17632#64) 13504 ∗ memRegion (sp - 4128#64) 4128
  have hsub : sp - 176#64 - 4096#64 = sp - 4272#64 := by bv_omega
  rw [hsub,
      ← ProofLib.memRegion_split' (b := sp - 176#64) (n := 112) (k := 64) (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 4272#64) (n := 4096) (k := 176) (b' := sp - 176#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13360) (k := 4272) (b' := sp - 4272#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13504) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem stackAt_176_from_dropPoly16 (sp : BitVec 64) :
    memRegion (sp - 17632#64) 13504 ∗ stackAt sp dropGluePoly16Stack ⊢
    stackAt sp ekReceivedCt1SampledRecvCt1AckStack := by
  change memRegion (sp - 17632#64) 13504 ∗ memRegion (sp - 4128#64) 4128 ⊢ memRegion (sp - 17632#64) 17632
  rw [← ProofLib.memRegion_split' (b := sp - 17632#64) (n := 13504) (k := 4128) (b' := sp - 4128#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Callee-saved registers preserved across `__rust_dealloc` calls in `recv_ct1_ack`. -/
@[expose] def RecvCt1AckSaved (s0 s : State) (sp176 stA ct2Cap ct2Ptr : BitVec 64) : Prop :=
  s.readReg64 .x19 = stA ∧ s.readReg64 .x20 = ct2Cap ∧ s.readReg64 .x21 = ct2Ptr ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = sp176 ∧ s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0

end CryptoVerification.SpqrV1.States.Leaves

