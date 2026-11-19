/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Acknowledged1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Acknowledged` Arm, Part 3

**Checked by Lean.** Verifies the `.done` path (`+4468 -> +13292 -> +18148 -> +19360 -> +4924 ->
s0.x30`), Branch C composition, and top-level `.ct1Acknowledged` theorem
`states_recv_ct1Acknowledged_ok_ext`.
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
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
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

/-! ## 1. `.done` Path (`+4468 -> +13292 -> +18148 -> +19360 -> +4924 -> s0.x30`) -/

theorem ct1Ack_done_1856_split {A : RustAlloc} {F : ShaCompress} (fsp : BitVec 64)
    (outSt : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    ct1AcknowledgedRecvEkChunkResAt A (F := F) (fsp + 1856#64) (.ok (.done outSt)) ⊢
      ∃∗ w : Words57, ∃∗ d58 : BitVec 64, ∃∗ d59 : BitVec 64, ∃∗ dq60 : BitVec 128,
      ∃∗ dw62 : BitVec 64, ∃∗ dq63 : BitVec 128, ∃∗ dw65 : BitVec 64,
        ((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
        ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
        ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
        ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗
        relocatedHeap (fun dst => chunkedCt2SampledAt A dst outSt) (wordsBytes (words57List w)) := by
  dsimp only [ct1AcknowledgedRecvEkChunkResAt]
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h2320 : (fsp + 1856#64) + 464#64 = fsp + 2320#64 := by bv_omega
  rw [h1864, h2320,
      ProofLib.memRegion_split' (b := fsp + 2320#64) (n := 8) (k := 56) (b' := fsp + 2328#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2328#64) (n := 8) (k := 48) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 16) (k := 32) (b' := fsp + 2352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 8) (k := 24) (b' := fsp + 2360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2360#64) (n := 16) (k := 8) (b' := fsp + 2376#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (fsp + 2320#64), ProofLib.memRegion_eight (fsp + 2328#64),
      ProofLib.memRegion_eight (fsp + 2352#64), ProofLib.memRegion_eight (fsp + 2376#64)]
  refine Entails.trans (sepConj_mono_right (sepConj_mono (chunkedCt2SampledAt_extract57 A (fsp + 1864#64) outSt)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (memRegion_16_entails_128_recv (fsp + 2336#64))
      (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 2360#64))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply Entails.sepExists_elim; intro dw65; apply Entails.sepExists_elim; intro dq63
  apply Entails.sepExists_elim; intro dw62; apply Entails.sepExists_elim; intro dq60
  apply Entails.sepExists_elim; intro d59; apply Entails.sepExists_elim; intro d58
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w (Entails.sepExists_right d58 (Entails.sepExists_right d59
    (Entails.sepExists_right dq60 (Entails.sepExists_right dw62 (Entails.sepExists_right dq63
      (Entails.sepExists_right dw65 (Entails.of_eq (by ac_rfl))))))))

theorem ct1Ack_done_1856_rejoin_880 (fsp d58 d59 dw62 dw65 : BitVec 64) (dq60 dq63 : BitVec 128) (w : Words57) :
    ((fsp + 1856#64) ↦₆₄ noneCap) ∗ words57At (fsp + 1864#64) w ∗
      ((fsp + 2320#64) ↦₆₄ d58) ∗ ((fsp + 2328#64) ↦₆₄ d59) ∗
      ((fsp + 2336#64) ↦₁₂₈ dq60) ∗ ((fsp + 2352#64) ↦₆₄ dw62) ∗
      ((fsp + 2360#64) ↦₁₂₈ dq63) ∗ ((fsp + 2376#64) ↦₆₄ dw65) ∗ memRegion (fsp + 2384#64) 352 ⊢
      memRegion (fsp + 1856#64) 880 := by
  rw [ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 8) (k := 872) (b' := fsp + 1864#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1864#64) (n := 456) (k := 416) (b' := fsp + 2320#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2320#64) (n := 8) (k := 408) (b' := fsp + 2328#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2328#64) (n := 8) (k := 400) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2336#64) (n := 16) (k := 384) (b' := fsp + 2352#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2352#64) (n := 8) (k := 376) (b' := fsp + 2360#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2360#64) (n := 16) (k := 360) (b' := fsp + 2376#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 2376#64) (n := 8) (k := 352) (b' := fsp + 2384#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 1856#64) noneCap)
    (sepConj_mono (words57At_entails_memRegion (fsp + 1864#64) w)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 2320#64) d58)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 2328#64) d59)
          (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 2336#64) dq60)
            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 2352#64) dw62)
              (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 2360#64) dq63)
                (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 2376#64) dw65))))))))

@[expose] def ct1AckSpillsDone4924 (sp : SendEkSpills) (w : Words57) (d58 d59 dw62 : BitVec 64) : SendEkSpills :=
  { sp with
    b0 := { sp.b0 with w0 := w.w52, w1 := w.b3.w5, w2 := w.b3.w1, w3 := w.b2.w9, w4 := w.b3.w2, w5 := w.b4.w1, w6 := w.b4.w0, w7 := w.b3.w8, w8 := w.b3.w4, w9 := w.b3.w3 }
    b1 := { sp.b1 with w0 := w.w56, w1 := w.w55, w2 := w.b3.w9, w3 := w.b3.w6, w4 := w.w53, w5 := w.b3.w7, w6 := w.b0.w0, w7 := d59, w8 := w.b1.w5, w9 := w.b1.w5 }
    b2 := { sp.b2 with w0 := w.b4.w7, w1 := w.w51, w2 := w.b4.w9, w3 := w.b4.w3, w4 := w.b4.w5, w5 := w.b0.w1, w6 := w.b4.w8, w7 := 12#64, w8 := w.b1.w9, w9 := w.b4.w2 }
    b3 := { sp.b3 with w0 := d58, w1 := dw62, w2 := w.b1.w8, w3 := w.b2.w1, w4 := w.b2.w7, w5 := w.b0.w7, w6 := w.b1.w3, w7 := w.b2.w5, w8 := w.b3.w0, w9 := w.b2.w8 }
    b4 := { sp.b4 with w0 := w.b2.w6, w1 := w.b1.w2, w2 := w.b1.w8, w3 := w.b1.w0, w4 := w.b2.w2, w5 := w.b0.w5, w6 := w.b0.w4, w7 := w.b1.w1, w8 := w.b2.w0, w9 := w.b2.w3 }
    b5 := { sp.b5 with w0 := w.b0.w9, w1 := w.b4.w4, w2 := w.b1.w4, w3 := w.b0.w8, w4 := w.b1.w7, w5 := w.w50, w6 := w.b0.w3, w7 := w.b2.w4, w8 := w.b4.w6, w9 := w.w54 }
    w60 := w.w56, w61 := w.b0.w2, w62 := w.b0.w6 }

theorem writebackWords63_ct1Ack_done (s2 s3 : State) (sp : SendEkSpills) (w : Words57) (d58 d59 dw62 : BitVec 64)
    (h2_x0 : s2.readReg64 .x0 = w.w55) (h2_x1 : s2.readReg64 .x1 = w.b0.w0) (h2_x2 : s2.readReg64 .x2 = w.b1.w2)
    (h2_x3 : s2.readReg64 .x3 = w.b2.w9) (h2_x4 : s2.readReg64 .x4 = w.b4.w9) (h2_x5 : s2.readReg64 .x5 = w.b4.w8)
    (h2_x6 : s2.readReg64 .x6 = w.w50) (h2_x7 : s2.readReg64 .x7 = w.b1.w9) (h2_x10 : s2.readReg64 .x10 = w.b1.w6)
    (h2_x11 : s2.readReg64 .x11 = w.w54) (h2_x12 : s2.readReg64 .x12 = w.b4.w0) (h2_x13 : s2.readReg64 .x13 = w.w51)
    (h2_x15 : s2.readReg64 .x15 = w.b2.w7) (h2_x16 : s2.readReg64 .x16 = w.b4.w7) (h2_x17 : s2.readReg64 .x17 = w.b4.w5)
    (h2_x18 : s2.readReg64 .x18 = w.w53) (h2_x22 : s2.readReg64 .x22 = w.w52) (h2_x24 : s2.readReg64 .x24 = w.b3.w1)
    (h2_x25 : s2.readReg64 .x25 = w.b3.w9) (h2_x26 : s2.readReg64 .x26 = w.b0.w5) (h2_x30 : s2.readReg64 .x30 = w.b3.w8)
    (h3_x0 : s3.readReg64 .x0 = s2.readReg64 .x25) (h3_x1 : s3.readReg64 .x1 = s2.readReg64 .x1)
    (h3_x2 : s3.readReg64 .x2 = s2.readReg64 .x2) (h3_x3 : s3.readReg64 .x3 = s2.readReg64 .x3)
    (h3_x4 : s3.readReg64 .x4 = s2.readReg64 .x4) (h3_x5 : s3.readReg64 .x5 = s2.readReg64 .x5)
    (h3_x6 : s3.readReg64 .x6 = s2.readReg64 .x12) (h3_x7 : s3.readReg64 .x7 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w7)
    (h3_x8 : s3.readReg64 .x8 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b2.w5) (h3_x9 : s3.readReg64 .x9 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b2.w3)
    (h3_x10 : s3.readReg64 .x10 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w1) (h3_x11 : s3.readReg64 .x11 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w8)
    (h3_x12 : s3.readReg64 .x12 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w9) (h3_x13 : s3.readReg64 .x13 = s2.readReg64 .x22)
    (h3_x14 : s3.readReg64 .x14 = s2.readReg64 .x18) (h3_x15 : s3.readReg64 .x15 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b1.w3)
    (h3_x16 : s3.readReg64 .x16 = s2.readReg64 .x0) (h3_x17 : s3.readReg64 .x17 = s2.readReg64 .x17)
    (h3_x20 : s3.readReg64 .x20 = s2.readReg64 .x30) (h3_x21 : s3.readReg64 .x21 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b2.w9)
    (h3_x22 : s3.readReg64 .x22 = s2.readReg64 .x13) (h3_x23 : s3.readReg64 .x23 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b1.w8)
    (h3_x24 : s3.readReg64 .x24 = s2.readReg64 .x24) (h3_x25 : s3.readReg64 .x25 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w4)
    (h3_x26 : s3.readReg64 .x26 = s2.readReg64 .x16) (h3_x27 : s3.readReg64 .x27 = s2.readReg64 .x10)
    (h3_x28 : s3.readReg64 .x28 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b1.w5) (h3_x30 : s3.readReg64 .x30 = (ct1AckSpillsDone4924 sp w d58 d59 dw62).b0.w5) :
    writebackWords63 s3 (ct1AckSpills4924 s2 (ct1AckSpillsDone4924 sp w d58 d59 dw62)) =
      { b0 := w.b0, b1 := w.b1, b2 := w.b2, b3 := w.b3, b4 := w.b4,
        b5 := ⟨w.w50, w.w51, w.w52, w.w53, w.w54, w.w55, w.w56, w.b1.w2, d58, w.b3.w8⟩,
        q60 := sp.q3c0, w62 := dw62 } := by
  dsimp only [writebackWords63, ct1AckSpills4924, ct1AckSpillsDone4924]
  simp only [h3_x0, h3_x1, h3_x2, h3_x3, h3_x4, h3_x5, h3_x6, h3_x7, h3_x8, h3_x9,
    h3_x10, h3_x11, h3_x12, h3_x13, h3_x14, h3_x15, h3_x16, h3_x17, h3_x20,
    h3_x21, h3_x22, h3_x23, h3_x24, h3_x25, h3_x26, h3_x27, h3_x28, h3_x30, ct1AckSpillsDone4924,
    h2_x0, h2_x1, h2_x2, h2_x3, h2_x4, h2_x5, h2_x6, h2_x7, h2_x10, h2_x11,
    h2_x12, h2_x13, h2_x15, h2_x16, h2_x17, h2_x18, h2_x22, h2_x24, h2_x25, h2_x26, h2_x30]

theorem selfA_11_528_392_entails_memRegion (selfA : BitVec 64) :
    (selfA ↦₆₄ 11#64) ∗ memRegion (selfA + 8#64) 528 ∗ memRegion (selfA + 536#64) 392 ⊢
      memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split' (b := selfA) (n := 8) (k := 920) (b' := selfA + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 528) (k := 392) (b' := selfA + 536#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 11#64)

theorem sendEkFrame_entails_976_2288 (fsp : BitVec 64) (sp : SendEkSpills) :
    sendEkSpillsAt fsp sp ∗
    memRegion (fsp + 576#64) 376 ∗
    memRegion (fsp + 1856#64) 880 ∗
    sendEkUnusedAt fsp ⊢
      memRegion fsp 976 ∗ memRegion (fsp + 1856#64) 2288 := by
  have h := sendEkFrame_entails_memRegion_4144 fsp sp
  unfold sendEkSpillsAt sendEkUnusedAt
  rw [ProofLib.memRegion_split' (b := fsp) (n := 8) (k := 968) (b' := fsp + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := fsp + 8#64) (n := 80) (k := 888) (b' := fsp + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 88#64) (n := 80) (k := 808) (b' := fsp + 168#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 168#64) (n := 80) (k := 728) (b' := fsp + 248#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 248#64) (n := 80) (k := 648) (b' := fsp + 328#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 328#64) (n := 80) (k := 568) (b' := fsp + 408#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 408#64) (n := 80) (k := 488) (b' := fsp + 488#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 488#64) (n := 8) (k := 480) (b' := fsp + 496#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 496#64) (n := 8) (k := 472) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 464) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 448) (b' := fsp + 528#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 432) (b' := fsp + 544#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 416) (b' := fsp + 560#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 560#64) (n := 8) (k := 408) (b' := fsp + 568#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 400) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 24) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 16) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 880) (k := 1408) (b' := fsp + 2736#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion fsp 8 ∗
     words10At (fsp + 8#64) sp.b0 ∗ words10At (fsp + 88#64) sp.b1 ∗
     words10At (fsp + 168#64) sp.b2 ∗ words10At (fsp + 248#64) sp.b3 ∗
     words10At (fsp + 328#64) sp.b4 ∗ words10At (fsp + 408#64) sp.b5 ∗
     ((fsp + 488#64) ↦₆₄ sp.w60) ∗ ((fsp + 496#64) ↦₆₄ sp.w61) ∗ ((fsp + 504#64) ↦₆₄ sp.w62) ∗
     ((fsp + 512#64) ↦₁₂₈ sp.q200) ∗ ((fsp + 528#64) ↦₁₂₈ sp.q210) ∗ ((fsp + 544#64) ↦₁₂₈ sp.q220) ∗
     ((fsp + 560#64) ↦₆₄ sp.w230) ∗
     memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 952#64) 8 ∗
     ((fsp + 960#64) ↦₁₂₈ sp.q3c0)) ∗
    (memRegion (fsp + 1856#64) 880 ∗ memRegion (fsp + 2736#64) 1408) by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono_right
    (sepConj_mono (words10At_entails_memRegion_80 (fsp + 8#64) sp.b0)
      (sepConj_mono (words10At_entails_memRegion_80 (fsp + 88#64) sp.b1)
        (sepConj_mono (words10At_entails_memRegion_80 (fsp + 168#64) sp.b2)
          (sepConj_mono (words10At_entails_memRegion_80 (fsp + 248#64) sp.b3)
            (sepConj_mono (words10At_entails_memRegion_80 (fsp + 328#64) sp.b4)
              (sepConj_mono (words10At_entails_memRegion_80 (fsp + 408#64) sp.b5)
                (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 488#64) sp.w60)
                  (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 496#64) sp.w61)
                    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 504#64) sp.w62)
                      (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 512#64) sp.q200)
                        (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 528#64) sp.q210)
                          (sepConj_mono (pointsTo128_entails_memRegion_16 (fsp + 544#64) sp.q220)
                            (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 560#64) sp.w230)
                              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                                (pointsTo128_entails_memRegion_16 (fsp + 960#64) sp.q3c0))))))))))))))))))

@[expose] def ct1AckRecvChunkToStatesResult {F : ShaCompress}
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F))) :
    StatesResult (V1Recv spqrPolyApi (spqrAuthApi F)) :=
  match res with
  | .error e => .error (.err e)
  | .ok (.stillReceiving s') => .ok { key := none, state := .ct1Acknowledged s' }
  | .ok (.done s') => .ok { key := none, state := .ct2Sampled s' }

theorem states_recv_ct1Acknowledged_eq_ek_res (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (heq : msg.epoch = s.uc.epoch) (hpay : msg.payload = .ek chunk)
    (hrecv : s.recv_ek_chunk K s.uc.epoch chunk = StatesResult.ofError res) :
    States.recv K (.ct1Acknowledged s) msg = ct1AckRecvChunkToStatesResult res := by
  rw [states_recv_ct1Acknowledged_eq_ek K s msg chunk heq hpay, hrecv]
  cases res with
  | error e => rfl
  | ok r => cases r <;> rfl

theorem states_recv_ct1Acknowledged_eq_ekCt1Ack_res (K : MlKem) {F : ShaCompress}
    (s : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) (chunk : Chunk)
    (res : Except Error (Chunked.SendCt.Ct1AcknowledgedRecvChunk spqrPolyApi (spqrAuthApi F)))
    (heq : msg.epoch = s.uc.epoch) (hpay : msg.payload = .ekCt1Ack chunk)
    (hrecv : s.recv_ek_chunk K s.uc.epoch chunk = StatesResult.ofError res) :
    States.recv K (.ct1Acknowledged s) msg = ct1AckRecvChunkToStatesResult res := by
  rw [states_recv_ct1Acknowledged_eq_ekCt1Ack K s msg chunk heq hpay, hrecv]
  cases res with
  | error e => rfl
  | ok r => cases r <;> rfl

theorem polyDecoderAt_entails_pts_length_16 (A : RustAlloc) (a : BitVec 64) (dec : PolyDecoder) :
    polyDecoderAt A a dec ⊢ ⌜dec.pts.length = 16⌝ ∗ polyDecoderAt A a dec := by
  unfold polyDecoderAt
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
    (sortedSetPtListOf A a dec.pts ∗
     ((a + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
     ((a + polyDecoderIsCompleteOff) ↦₈ boolByte dec.isComplete) ∗
     memRegion (a + polyDecoderPadOff) polyDecoderPadSize) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlen, hneed⟩
  refine Entails.pure_right hlen ?_
  refine Entails.trans ?_ (Entails.of_eq (show
    ⌜dec.pts.length = NUM_POLYS ∧ dec.ptsNeeded < 2 ^ 64⌝ ∗
    (sortedSetPtListOf A a dec.pts ∗
     ((a + polyDecoderPtsNeededOff) ↦₆₄ BitVec.ofNat 64 dec.ptsNeeded) ∗
     ((a + polyDecoderIsCompleteOff) ↦₈ boolByte dec.isComplete) ∗
     memRegion (a + polyDecoderPadOff) polyDecoderPadSize) = _ by ac_rfl))
  exact Entails.pure_right ⟨hlen, hneed⟩ (Entails.refl _)

theorem chunkedCt1AcknowledgedAt_entails_pts_length_16 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    chunkedCt1AcknowledgedAt A a st ⊢
      ⌜st.receiving_ek.pts.length = 16⌝ ∗ chunkedCt1AcknowledgedAt A a st := by
  unfold chunkedCt1AcknowledgedAt
  refine Entails.trans (sepConj_mono_right (polyDecoderAt_entails_pts_length_16 A (a + 128#64) st.receiving_ek)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem ct1Ack_sepWPp_intro_ex {prog : Program} {target_pc : BitVec 64} {s : State}
    {α : Type} {P : α → SepProp} {Q Q_panic : State → SepProp → Prop}
    (hrun : s.status = .Running)
    (h : ∀ x : α, SepWPp prog target_pc s (P x) Q Q_panic) :
    SepWPp prog target_pc s (∃∗ x : α, P x) Q Q_panic :=
  SepWPp.of_sepWP (ProofLib.SepWP.exists_left fun x => SepWP.done rfl hrun (h x))

end CryptoVerification.SpqrV1.States.Recv
