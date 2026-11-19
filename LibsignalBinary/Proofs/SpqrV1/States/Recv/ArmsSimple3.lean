/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvNextEpoch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `Ct2Sampled` Arm

**Checked by Lean.** Verification of the `States.ct2Sampled` arm (`tag = 12#64`, `0x55db0`, `+2396`),
covering `msg.epoch == ep + 1` (`<Ct2Sampled>::recv_next_epoch`), `msg.epoch > ep + 1`, and `msg.epoch ≤ ep`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.InImageLift
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.Top CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem selfA_ct2Sampled_entails_memRegion_928 (selfA : BitVec 64) :
    (selfA ↦₆₄ 12#64) ∗ memRegion (selfA + 8#64) 456 ∗ memRegion (selfA + 464#64) 464 ⊢ memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 456) (k := 464) (b' := selfA + 464#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 12#64)

theorem ct2Sampled_recv_le {F : ShaCompress} {K : MlKem}
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi) (hle : ¬ (msg.epoch > st.uc.epoch)) :
    (States.ct2Sampled st).recv K msg = .ok ⟨none, .ct2Sampled st⟩ := by
  simp only [States.recv, Chunked.SendCt.Ct2Sampled.epoch, Unchunked.SendCt.Ct2Sent.epoch, hle, ↓reduceIte]

theorem ct2Sampled_recv_gt_ne {F : ShaCompress} {K : MlKem}
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (hne : (msg.epoch == st.uc.epoch + 1#64) = false) :
    (States.ct2Sampled st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
  simp only [States.recv, Chunked.SendCt.Ct2Sampled.epoch, Unchunked.SendCt.Ct2Sent.epoch, hgt, hne, Bool.false_eq_true, ↓reduceIte]

theorem epoch_ne_allOnes_of_lt {ep1 ep2 : BitVec 64} (hgt : ep1 > ep2) :
    (ep2 == 0xffffffffffffffff#64) = false := by
  apply Bool.eq_false_iff.mpr; intro h
  have heq : ep2 = 0xffffffffffffffff#64 := beq_iff_eq.mp h; subst heq
  have h1 : ep1.toNat > (0xffffffffffffffff#64 : BitVec 64).toNat := BitVec.lt_def.mp hgt
  have h2 : ep1.toNat < 2 ^ 64 := ep1.isLt
  have h3 : (0xffffffffffffffff#64 : BitVec 64).toNat = 2 ^ 64 - 1 := rfl
  omega

theorem ct2Sampled_recv_gt_eq {F : ShaCompress} {K : MlKem}
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hgt : msg.epoch > st.uc.epoch) (heq : (msg.epoch == st.uc.epoch + 1#64) = true) :
    st.recv_next_epoch msg.epoch = .ok { uc := { epoch := msg.epoch, auth := st.uc.auth } } ∧
    (States.ct2Sampled st).recv K msg =
      .ok ⟨none, .keysUnsampled { uc := { epoch := msg.epoch, auth := st.uc.auth } }⟩ := by
  have hall : (st.uc.epoch == BitVec.allOnes 64) = false := epoch_ne_allOnes_of_lt hgt
  have h_eq : msg.epoch = st.uc.epoch + 1#64 := beq_iff_eq.mp heq
  have hne : (st.uc.epoch + 1#64 != msg.epoch) = false := by rw [h_eq]; simp
  have hnext : st.recv_next_epoch msg.epoch = .ok { uc := { epoch := msg.epoch, auth := st.uc.auth } } := by
    unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch Unchunked.SendCt.Ct2Sent.recv_next_epoch
    dsimp only [Bind.bind, Except.bind]; rw [hall, hne]; simp [← h_eq]
  refine ⟨hnext, ?_⟩
  simp only [States.recv, Chunked.SendCt.Ct2Sampled.epoch, Unchunked.SendCt.Ct2Sent.epoch,
    hgt, heq, ↓reduceIte, hnext, StatesResult.ofPanic, Bind.bind, Except.bind]

@[expose] def ct2SampledWords (a : BitVec 64) (off : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 st_epoch : BitVec 64) : SepProp :=
  wordsAtOff a (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
    w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
    w40 w41 w42 w43 w44 w45 w46 w47 w48 w49) off ∗
  wordsAtOff a [w50, w51, w52, w53, w54, w55, st_epoch] (off + 400)

theorem ct2SampledWords_entails_memRegion_456 (a : BitVec 64) (off : Nat)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 st_epoch : BitVec 64) :
    ct2SampledWords a off w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 st_epoch ⊢
      memRegion (a + BitVec.ofNat 64 off) 456 := by
  rw [ProofLib.memRegion_split' (b := a + BitVec.ofNat 64 off) (n := 400) (k := 56)
    (b' := a + BitVec.ofNat 64 (off + 400)) rfl (by rw [BitVec.add_assoc, ← BitVec.ofNat_add]) (by decide)]
  exact sepConj_mono (wordsAtOff_entails_memRegion a _ off 400 rfl)
    (wordsAtOff_entails_memRegion a _ (off + 400) 56 rfl)

theorem chunkedCt2SampledAt_extract_self (A : RustAlloc) {F : ShaCompress}
    (selfA : BitVec 64) (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedCt2SampledAt A (selfA + 8#64) st ⊢
      existsWordsWithBytesAtOff selfA (relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2)) 50 8 ∗
      (∃∗ g : AuthWords, wordsAtOff selfA (ct2SentWordsList g st.uc.epoch) 408 ∗
        relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch))) := by
  unfold chunkedCt2SampledAt
  have h408 : (selfA + 8#64) + 400#64 = selfA + BitVec.ofNat 64 408 := by bv_omega
  rw [h408]
  have henc_rel : Relocatable (8 * 50) (fun dst => polyEncoderAt A dst st.sending_ct2) :=
    Relocatable.of_polyEncoderAt A st.sending_ct2
  refine sepConj_mono (Relocatable.entails_existsWordsWithBytesAtOff henc_rel selfA 8) ?_
  refine Entails.trans (unchunkedCt2SentAt_extract A (selfA + BitVec.ofNat 64 408) st.uc) ?_
  apply Entails.sepExists_elim; intro g; refine Entails.sepExists_right g ?_
  rw [← wordsAtOff_eq_wordsAt selfA (ct2SentWordsList g st.uc.epoch) 408]
  exact Entails.refl _

theorem ct2SampledWords_recompose (A : RustAlloc) {F : ShaCompress} (a : BitVec 64) (off : Nat)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (g : AuthWords)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64) :
    ct2SampledWords a off w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
      g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
    relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
    relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ⊢
    chunkedCt2SampledAt A (a + BitVec.ofNat 64 off) st := by
  unfold chunkedCt2SampledAt
  have hoff400 : (a + BitVec.ofNat 64 off) + 400#64 = a + BitVec.ofNat 64 (off + 400) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [hoff400]
  have henc := wordsAtOff_recompose_relocatedHeap a off (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)
    (G := fun dst => polyEncoderAt A dst st.sending_ct2)
  have huc := wordsAtOff_recompose_relocatedHeap a (off + 400) (ct2SentWordsList g st.uc.epoch)
    (G := fun dst => unchunkedCt2SentAt A dst st.uc)
  refine Entails.trans (Entails.of_eq (show _ =
    (wordsAtOff a (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49) off ∗
     relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49))) ∗
    (wordsAtOff a (ct2SentWordsList g st.uc.epoch) (off + 400) ∗
     relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch))) by
    dsimp only [ct2SampledWords, ct2SentWordsList, authWordsList]; ac_rfl)) (sepConj_mono henc huc)

@[expose] def ct2SampledScratchLo (fsp : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64) : SepProp :=
  ((fsp + 8#64) ↦₆₄ u8) ∗ ((fsp + 16#64) ↦₆₄ u16) ∗
  ((fsp + 40#64) ↦₆₄ u40) ∗ ((fsp + 48#64) ↦₆₄ u48) ∗ ((fsp + 56#64) ↦₆₄ u56) ∗ ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
  ((fsp + 104#64) ↦₆₄ u104) ∗ ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗ ((fsp + 128#64) ↦₆₄ u128) ∗
  ((fsp + 160#64) ↦₆₄ u160) ∗ ((fsp + 168#64) ↦₆₄ u168) ∗ ((fsp + 176#64) ↦₆₄ u176) ∗ ((fsp + 184#64) ↦₆₄ u184) ∗
  ((fsp + 192#64) ↦₆₄ u192) ∗ ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗ ((fsp + 216#64) ↦₆₄ u216)

@[expose] def ct2SampledUntouchedLo (fsp : BitVec 64)
    (u0 u24 u32 u80 u88 u96 u136 u144 u152 : BitVec 64) : SepProp :=
  (fsp ↦₆₄ u0) ∗ ((fsp + 24#64) ↦₆₄ u24) ∗ ((fsp + 32#64) ↦₆₄ u32) ∗
  ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 88#64) ↦₆₄ u88) ∗ ((fsp + 96#64) ↦₆₄ u96) ∗
  ((fsp + 136#64) ↦₆₄ u136) ∗ ((fsp + 144#64) ↦₆₄ u144) ∗ ((fsp + 152#64) ↦₆₄ u152)

theorem ct2SampledLo_entails_memRegion_224 (fsp : BitVec 64)
    (u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 : BitVec 64)
    (u0 u24 u32 u80 u88 u96 u136 u144 u152 : BitVec 64) :
    ct2SampledScratchLo fsp u8 u16 u40 u48 u56 u64 u72 u104 u112 u120 u128 u160 u168 u176 u184 u192 u200 u208 u216 ∗
    ct2SampledUntouchedLo fsp u0 u24 u32 u80 u88 u96 u136 u144 u152 ⊢ memRegion fsp 224 := by
  have h := wordsAtOff_entails_memRegion fsp
    [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112, u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216]
    0 224 rfl
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h
  refine Entails.trans (Entails.of_eq ?_) h
  dsimp only [ct2SampledScratchLo, ct2SampledUntouchedLo, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  rw [BitVec.add_zero]; ac_rfl

@[expose] def ct2SampledScratchHi (fsp : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64) : SepProp :=
  ((fsp + 240#64) ↦₆₄ u240) ∗ ((fsp + 288#64) ↦₆₄ u288) ∗ ((fsp + 304#64) ↦₆₄ u304) ∗ ((fsp + 336#64) ↦₆₄ u336) ∗
  ((fsp + 376#64) ↦₆₄ u376) ∗ ((fsp + 384#64) ↦₆₄ u384) ∗ ((fsp + 392#64) ↦₆₄ u392) ∗ ((fsp + 400#64) ↦₆₄ u400) ∗
  ((fsp + 408#64) ↦₆₄ u408) ∗ ((fsp + 416#64) ↦₆₄ u416) ∗ ((fsp + 424#64) ↦₆₄ u424) ∗ ((fsp + 432#64) ↦₆₄ u432) ∗
  ((fsp + 448#64) ↦₆₄ u448) ∗ ((fsp + 456#64) ↦₆₄ u456) ∗ ((fsp + 464#64) ↦₆₄ u464) ∗ ((fsp + 480#64) ↦₆₄ u480) ∗
  ((fsp + 488#64) ↦₆₄ u488) ∗ ((fsp + 496#64) ↦₆₄ u496) ∗ ((fsp + 504#64) ↦₆₄ u504)

@[expose] def ct2SampledUntouchedHi (fsp : BitVec 64)
    (u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 : BitVec 64) : SepProp :=
  ((fsp + 224#64) ↦₆₄ u224) ∗ ((fsp + 232#64) ↦₆₄ u232) ∗ ((fsp + 248#64) ↦₆₄ u248) ∗ ((fsp + 256#64) ↦₆₄ u256) ∗
  ((fsp + 264#64) ↦₆₄ u264) ∗ ((fsp + 272#64) ↦₆₄ u272) ∗ ((fsp + 280#64) ↦₆₄ u280) ∗ ((fsp + 296#64) ↦₆₄ u296) ∗
  ((fsp + 312#64) ↦₆₄ u312) ∗ ((fsp + 320#64) ↦₆₄ u320) ∗ ((fsp + 328#64) ↦₆₄ u328) ∗ ((fsp + 344#64) ↦₆₄ u344) ∗
  ((fsp + 352#64) ↦₆₄ u352) ∗ ((fsp + 360#64) ↦₆₄ u360) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗ ((fsp + 440#64) ↦₆₄ u440) ∗
  ((fsp + 472#64) ↦₆₄ u472)

theorem ct2SampledHi_entails_memRegion_288 (fsp : BitVec 64)
    (u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 : BitVec 64)
    (u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 : BitVec 64) :
    ct2SampledScratchHi fsp u240 u288 u304 u336 u376 u384 u392 u400 u408 u416 u424 u432 u448 u456 u464 u480 u488 u496 u504 ∗
    ct2SampledUntouchedHi fsp u224 u232 u248 u256 u264 u272 u280 u296 u312 u320 u328 u344 u352 u360 u368 u440 u472 ⊢
    memRegion (fsp + 224#64) 288 := by
  have h := wordsAtOff_entails_memRegion fsp
    [u224, u232, u240, u248, u256, u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352, u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480, u488, u496, u504]
    224 288 rfl
  refine Entails.trans (Entails.of_eq ?_) h
  dsimp only [ct2SampledScratchHi, ct2SampledUntouchedHi, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem ct2Sampled_out_recompose (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) (g : AuthWords)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 v464 v472 v480 : BitVec 64) :
    epilogueRecvOutPartA out 12#64 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13
      w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 g.v1.w2 g.v2.w0 ∗
    epilogueRecvOutPartB488 out w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
      w44 w45 w46 w47 g.v1.w0 g.v1.w1 g.v2.w1 g.v2.w2 st.uc.epoch v464 v472 v480 ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
    relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch)) ⊢
    resultV1RecvAt A (F := F) out (.ok ⟨none, .ct2Sampled st⟩) := by
  rw [resultV1RecvAt_ok, chunkedStatesAt_ct2Sampled_unfold,
      ProofLib.memRegion_split' (b := out + 464#64) (n := 24) (k := 440) (b' := out + 488#64) rfl (by bv_omega) (by decide)]
  have h24 : ((out + 464#64) ↦₆₄ v464) ∗ ((out + 472#64) ↦₆₄ v472) ∗ ((out + 480#64) ↦₆₄ v480) ⊢
      memRegion (out + 464#64) 24 := by
    have h := wordsAtOff_entails_memRegion out [v464, v472, v480] 464 24 rfl
    simpa only [wordsAtOff, sepConj_emp, ← sepConj_assoc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have hrec := ct2SampledWords_recompose A out 8 st g w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
  refine Entails.trans (Entails.of_eq (show _ =
    (out ↦₆₄ 12#64) ∗
    (ct2SampledWords out 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch ∗
     relocatedHeap (fun dst => polyEncoderAt A dst st.sending_ct2) (wordsBytes (words50List w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49)) ∗
     relocatedHeap (fun dst => unchunkedCt2SentAt A dst st.uc) (wordsBytes (ct2SentWordsList g st.uc.epoch))) ∗
    (((out + 464#64) ↦₆₄ v464) ∗ ((out + 472#64) ↦₆₄ v472) ∗ ((out + 480#64) ↦₆₄ v480)) ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none by
    dsimp only [ct2SampledWords, words50List, wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    ac_rfl))
    (Entails.trans (sepConj_mono_right (sepConj_mono hrec (sepConj_mono_left h24))) (Entails.of_eq (by ac_rfl)))

theorem stackAt_statesRecvCallee_eq_ct2SampledRecvNextEpoch (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15392 ∗ stackAt fsp (dropGluePoly16Stack + 32) :=
  stackAt_split_bottom fsp (dropGluePoly16Stack + 32) 15392 (by decide)

theorem chunkedKeysUnsampledAt_976_extract (A : RustAlloc) {F : ShaCompress}
    (fsp : BitVec 64) (s' : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedKeysUnsampledAt A (fsp + 976#64) s' ⊢
      ∃∗ g' : AuthWords,
        (((fsp + 976#64) ↦₆₄ g'.v1.w0) ∗ ((fsp + 984#64) ↦₆₄ g'.v1.w1) ∗ ((fsp + 992#64) ↦₆₄ g'.v1.w2) ∗
         ((fsp + 1000#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 1008#64) ↦₆₄ g'.v2.w1) ∗ ((fsp + 1016#64) ↦₆₄ g'.v2.w2) ∗
         ((fsp + 1024#64) ↦₆₄ s'.uc.epoch)) ∗
        relocatedHeap (fun dst => authenticatorAt A dst s'.uc.auth) (wordsBytes (authWordsList g')) := by
  unfold chunkedKeysUnsampledAt unchunkedKeysUnsampledAt
  have h1024 : (fsp + 976#64) + 48#64 = fsp + 1024#64 := by bv_omega
  rw [h1024]
  refine Entails.trans (sepConj_mono_left (authenticatorAt_extract A (fsp + 976#64) s'.uc.auth)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g'; refine Entails.sepExists_right g' ?_
  rw [← wordsAtOff_eq_wordsAt fsp (authWordsList g') 976]
  dsimp only [authWordsList, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl)

theorem memRegion_4144_split_512 (fsp : BitVec 64) :
    memRegion fsp 4144 = existsWordsAtOff fsp 64 0 ∗ memRegion (fsp + 512#64) 3632 := by
  have h512 : memRegion fsp 512 = existsWordsAtOff fsp 64 0 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul] using
      memRegion_off_eq_existsWordsAtOff fsp 64 0 (by decide)
  rw [ProofLib.memRegion_split fsp 512 3632 (by decide), h512]

theorem memRegion_3632_split_976_1856 (fsp : BitVec 64) :
    memRegion (fsp + 512#64) 3632 =
      existsWordsAtOff fsp 57 1856 ∗
      memRegion (fsp + 976#64) 56 ∗
      memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 := by
  have h1856 : memRegion (fsp + 1856#64) 456 = existsWordsAtOff fsp 57 1856 := by
    simpa only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] using memRegion_off_eq_existsWordsAtOff fsp 57 1856 (by decide)
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 464) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 976#64) (n := 56) (k := 3112) (b' := fsp + 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1032#64) (n := 824) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 456) (k := 1832) (b' := fsp + 2312#64) rfl (by bv_omega) (by decide),
      h1856]
  ac_rfl

theorem ct2Sampled_recombine_3632 (fsp : BitVec 64) (g' : AuthWords) (ep : BitVec 64) :
    (((fsp + 976#64) ↦₆₄ g'.v1.w0) ∗ ((fsp + 984#64) ↦₆₄ g'.v1.w1) ∗ ((fsp + 992#64) ↦₆₄ g'.v1.w2) ∗
     ((fsp + 1000#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 1008#64) ↦₆₄ g'.v2.w1) ∗ ((fsp + 1016#64) ↦₆₄ g'.v2.w2) ∗
     ((fsp + 1024#64) ↦₆₄ ep)) ∗
    memRegion (fsp + 1856#64) 456 ∗
    memRegion (fsp + 512#64) 464 ∗ memRegion (fsp + 1032#64) 824 ∗ memRegion (fsp + 2312#64) 1832 ⊢
    memRegion (fsp + 512#64) 3632 := by
  have h56 : (((fsp + 976#64) ↦₆₄ g'.v1.w0) ∗ ((fsp + 984#64) ↦₆₄ g'.v1.w1) ∗ ((fsp + 992#64) ↦₆₄ g'.v1.w2) ∗
     ((fsp + 1000#64) ↦₆₄ g'.v2.w0) ∗ ((fsp + 1008#64) ↦₆₄ g'.v2.w1) ∗ ((fsp + 1016#64) ↦₆₄ g'.v2.w2) ∗
     ((fsp + 1024#64) ↦₆₄ ep)) ⊢ memRegion (fsp + 976#64) 56 := by
    have h := wordsAtOff_entails_memRegion fsp [g'.v1.w0, g'.v1.w1, g'.v1.w2, g'.v2.w0, g'.v2.w1, g'.v2.w2, ep] 976 56 rfl
    simpa only [wordsAtOff, sepConj_emp, ← sepConj_assoc, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 464) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 976#64) (n := 56) (k := 3112) (b' := fsp + 1032#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1032#64) (n := 824) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 456) (k := 1832) (b' := fsp + 2312#64) rfl (by bv_omega) (by decide)]
  exact Entails.trans (sepConj_mono_left h56) (Entails.of_eq (by ac_rfl))

theorem selfA_ct2SampledWords_entails_memRegion_928 (selfA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64)
    (w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 : BitVec 64)
    (w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 st_epoch : BitVec 64) :
    (selfA ↦₆₄ 12#64) ∗
    ct2SampledWords selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
      w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
      w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 st_epoch ∗
    memRegion (selfA + 464#64) 464 ⊢ memRegion selfA chunkedStatesSize :=
  Entails.trans (sepConj_mono_right (sepConj_mono_left
    (ct2SampledWords_entails_memRegion_456 selfA 8 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 st_epoch)))
    (selfA_ct2Sampled_entails_memRegion_928 selfA)

end CryptoVerification.SpqrV1.States.Recv
