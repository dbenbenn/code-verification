/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Common.InImageLift -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `HeaderReceived` Arm & `OptCallInv` Epilogue

**Checked by Lean.** Word-grid relocation combinators, `OptCallInv`-generalized `+18996` epilogue,
and the `States.headerReceived` arm (`0x55d30`, `+2268`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr CryptoVerification.InImageLift
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.LibsignalSpqrV1.PolyDecoder CryptoVerification.SpqrV1.Auth
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

@[local wp_norm] private theorem simple2_exists_two_pow_zero : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem simple2_exists_two_pow_one : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

theorem stackAt_statesRecvCallee_eq_extHook_sr (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX = memRegion (fsp - 19552#64) 3168 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 3168 (by decide)

theorem Relocatable.of_unchunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) :
    Relocatable 80 (fun a => unchunkedHeaderReceivedAt A a st) := by
  simp only [unchunkedHeaderReceivedAt_eq_ekSentAt]
  exact Relocatable.of_unchunkedEkSentAt A { epoch := st.epoch, auth := st.auth, dk := st.hdr }

theorem Relocatable.of_chunkedHeaderReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 480 (fun a => chunkedHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedHeaderReceivedAt A st.uc) (Relocatable.of_polyDecoderAt A st.receiving_ek)

theorem chunkedStatesAt_headerReceived_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.headerReceived st) =
      ((a ↦₆₄ 8#64) ∗ chunkedHeaderReceivedAt A (a + 8#64) st ∗ memRegion (a + 488#64) 440) := rfl

theorem chunkedStatesAt_ct2Sampled_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.ct2Sampled st) =
      ((a ↦₆₄ 12#64) ∗ chunkedCt2SampledAt A (a + 8#64) st ∗ memRegion (a + 464#64) 464) := rfl

/-! ## Word-Grid Relocation Combinators (`existsWordsWithBytesAtOff`) -/

@[expose] def existsWordsWithBytesAtOff (a : BitVec 64) (F : List (BitVec 8) → SepProp) : Nat → Nat → SepProp
  | 0, _ => F []
  | n + 1, off =>
      ∃∗ w : BitVec 64, ((a + BitVec.ofNat 64 off) ↦₆₄ w) ∗
        existsWordsWithBytesAtOff a (fun bs => F (unpack64 w ++ bs)) n (off + 8)

theorem pointsToBytes_entails_existsWordsWithBytesAtOff (a : BitVec 64) :
    ∀ (n off : Nat) (F : List (BitVec 8) → SepProp) (bs : List (BitVec 8)), bs.length = 8 * n →
      ((a + BitVec.ofNat 64 off) ↦ₛ bs) ∗ F bs ⊢ existsWordsWithBytesAtOff a F n off := by
  intro n; induction n with
  | zero =>
    intro off F bs hlen; have hbs := List.eq_nil_of_length_eq_zero hlen; subst hbs
    simp only [existsWordsWithBytesAtOff, pointsToBytes_nil, emp_sepConj]; exact Entails.refl _
  | succ n ih =>
    intro off F bs hlen
    have htake : (bs.take 8).length = 8 := by simp; omega
    have hdrop : (bs.drop 8).length = 8 * n := by simp; omega
    obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 htake
    have hbs : bs = unpack64 w ++ bs.drop 8 := by rw [← hw, List.take_append_drop 8 bs]
    rw [hbs, pointsToBytes_append (a + BitVec.ofNat 64 off) (unpack64 w) (bs.drop 8),
        unpack64_length, ← pointsTo64_eq_pointsToBytes, BitVec.add_assoc, ← BitVec.ofNat_add]
    dsimp only [existsWordsWithBytesAtOff]; refine Entails.sepExists_right w ?_; rw [sepConj_assoc]
    exact sepConj_mono_right (ih (off + 8) (fun bs' => F (unpack64 w ++ bs')) (bs.drop 8) hdrop)

theorem Relocatable.entails_existsWordsWithBytesAtOff {n : Nat} {G : BitVec 64 → SepProp}
    (hrel : Relocatable (8 * n) G) (a : BitVec 64) (off : Nat) :
    G (a + BitVec.ofNat 64 off) ⊢ existsWordsWithBytesAtOff a (relocatedHeap G) n off := by
  refine Entails.trans (hrel (a + BitVec.ofNat 64 off)) ?_
  apply Entails.sepExists_elim; intro bs; apply Entails.pure_left; intro hlen
  exact pointsToBytes_entails_existsWordsWithBytesAtOff a n off (relocatedHeap G) bs hlen

theorem wordsAtOff_recompose_relocatedHeap {G : BitVec 64 → SepProp}
    (a : BitVec 64) (off : Nat) (ws : List (BitVec 64)) :
    wordsAtOff a ws off ∗ relocatedHeap G (wordsBytes ws) ⊢ G (a + BitVec.ofNat 64 off) := by
  rw [wordsAtOff_eq_wordsAt a ws off]; exact relocatedHeap_recompose_words G ws (a + BitVec.ofNat 64 off)

/-! ## `States.headerReceived` (`tag = 8#64`, `+2268` / `0x55d30`) -/

theorem memRegion_4144_split_1856_480 (fsp : BitVec 64) :
    memRegion fsp 4144 = memRegion fsp 1856 ∗ memRegion (fsp + 1856#64) 480 ∗ memRegion (fsp + 2336#64) 1808 := by
  rw [ProofLib.memRegion_split fsp 1856 2288 (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 1808) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]

theorem selfA_headerReceived_entails_memRegion_928 (selfA : BitVec 64) :
    (selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 8#64) 480 ∗ memRegion (selfA + 488#64) 440 ⊢ memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize
  rw [ProofLib.memRegion_split selfA 8 920 (by decide),
      ProofLib.memRegion_split' (b := selfA + 8#64) (n := 480) (k := 440) (b' := selfA + 488#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion selfA 8#64)

theorem sepWP_intro_ex_nest {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {P Q : α → SepProp}
    (h : ∀ v : α, SepWP prog target_pc s ((Q v ∗ rest) ∗ (P v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, P v ∗ Q v) ∗ rest) ∗ R) post := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply ProofLib.SepWP.exists_left; intro v
  rw [sepConj_assoc (P v), sepConj_assoc, sepConj_left_comm (P v)]; exact h v

@[expose] def words50List
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) : List (BitVec 64) :=
  w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: w22 :: w23 :: w24 :: w25 :: w26 :: w27 :: w28 :: w29 :: w30 :: w31 :: w32 :: w33 :: w34 :: w35 :: w36 :: w37 :: w38 :: w39 :: w40 :: w41 :: w42 :: w43 :: w44 :: w45 :: w46 :: w47 :: w48 :: w49 :: w50 :: w51 :: w52 :: w53 :: w54 :: w55 :: w56 :: w57 :: w58 :: w59 :: []

@[expose] def headerReceivedStackWords (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) : SepProp :=
  wordsAtOff fsp (w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: st_epoch :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: w16 :: w17 :: w18 :: w19 :: w20 :: w21 :: w22 :: w23 :: w24 :: w25 :: w26 :: w27 :: w28 :: w29 :: w30 :: w31 :: w32 :: w33 :: w34 :: w35 :: w36 :: w37 :: w38 :: w39 :: w40 :: w41 :: w42 :: w43 :: w44 :: w45 :: w46 :: w47 :: w48 :: w49 :: w50 :: w51 :: w52 :: w53 :: w54 :: w55 :: w56 :: w57 :: w58 :: w59 :: []) 1856

theorem headerReceivedStackWords_entails_memRegion (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ⊢ memRegion (fsp + 1856#64) 480 :=
  wordsAtOff_entails_memRegion fsp _ 1856 480 rfl

theorem memRegion_1856_split_224_288 (fsp : BitVec 64) :
    memRegion fsp 1856 = memRegion fsp 224 ∗ existsWordsAtOff fsp 36 224 ∗ memRegion (fsp + 512#64) 1344 := by
  rw [ProofLib.memRegion_split fsp 224 1632 (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 288) (k := 1344) (b' := fsp + 512#64) rfl (by bv_omega) (by decide),
      memRegion_off_eq_existsWordsAtOff fsp 36 224 (by decide)]

theorem headerReceived_stack_entails_3632 (fsp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    memRegion (fsp + 512#64) 1344 ∗
    headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
    memRegion (fsp + 2336#64) 1808 ⊢ memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 1344) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 480) (k := 1808) (b' := fsp + 2336#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono_left (headerReceivedStackWords_entails_memRegion fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))

theorem chunkedHeaderReceivedAt_extract_1856 (A : RustAlloc) {F : ShaCompress}
    (fsp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A (fsp + 1856#64) st ⊢
      (∃∗ g : ThreeVecWords, wordsAtOff fsp (ekSentWordsList g st.uc.epoch) 1856 ∗
        relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
      existsWordsWithBytesAtOff fsp (relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek)) 50 1936 := by
  unfold chunkedHeaderReceivedAt
  have h1936 : (fsp + 1856#64) + 80#64 = fsp + BitVec.ofNat 64 1936 := by bv_omega
  rw [h1936]
  have hdec_rel : Relocatable (8 * 50) (fun dst => polyDecoderAt A dst st.receiving_ek) :=
    Relocatable.of_polyDecoderAt A st.receiving_ek
  refine sepConj_mono ?_ (Relocatable.entails_existsWordsWithBytesAtOff hdec_rel fsp 1936)
  rw [unchunkedHeaderReceivedAt_eq_ekSentAt]
  refine Entails.trans (unchunkedEkSentAt_extract A (fsp + 1856#64) { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr }) ?_
  apply Entails.sepExists_elim; intro g; refine Entails.sepExists_right g ?_
  rw [← wordsAtOff_eq_wordsAt fsp (ekSentWordsList g st.uc.epoch) 1856]
  exact sepConj_mono_right (relocatedHeap_congr fun dst => (unchunkedHeaderReceivedAt_eq_ekSentAt A dst st.uc).symm)

theorem headerReceived_out_recompose (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (g : ThreeVecWords)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64) :
    epilogueRecvOutPartA out 8#64 g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0
      g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13
      w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 w52 w53 ∗
    epilogueRecvOutPartB488 out w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
      w44 w45 w46 w47 w50 w51 w54 w55 w56 w57 w58 w59 ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
    relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ⊢
    resultV1RecvAt A (F := F) out (.ok ⟨none, .headerReceived st⟩) := by
  rw [resultV1RecvAt_ok, chunkedStatesAt_headerReceived_unfold]; unfold chunkedHeaderReceivedAt
  have h88 : (out + 8#64) + 80#64 = out + BitVec.ofNat 64 88 := by bv_omega
  rw [h88]
  have huc := wordsAtOff_recompose_relocatedHeap out 8 (ekSentWordsList g st.uc.epoch) (G := fun dst => unchunkedHeaderReceivedAt A dst st.uc)
  have hdec := wordsAtOff_recompose_relocatedHeap out 88 (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59) (G := fun dst => polyDecoderAt A dst st.receiving_ek)
  refine Entails.trans (Entails.of_eq (show _ = (out ↦₆₄ 8#64) ∗
    (wordsAtOff out (ekSentWordsList g st.uc.epoch) 8 ∗
     relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
    (wordsAtOff out (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59) 88 ∗
     relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))) ∗
    (memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none) by
    dsimp only [ekSentWordsList, vecWordsList, ct2SentWordsList, authWordsList, words50List,
      HAppend.hAppend, Append.append, List.append, wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488,
      Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl))
    (Entails.trans (sepConj_mono_right (sepConj_mono huc (sepConj_mono_left hdec))) (Entails.of_eq (by ac_rfl)))

theorem stackAt_statesRecvCallee_eq_dropGluePoly16 (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackX =
      memRegion (fsp - 19552#64) 15424 ∗ stackAt fsp dropGluePoly16Stack :=
  stackAt_split_bottom fsp dropGluePoly16Stack 15424 (by decide)

private theorem toNat_ne_zero_of_beq_false_s2 {c : BitVec 64} (hc : ¬ ((c == 0#64) = true)) :
    c.toNat ≠ 0 := by
  intro h; apply hc
  have h0 : c = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
  subst h0; rfl

private theorem layoutOk_one_of_ne_zero_s2 {n : Nat} (hne : n ≠ 0) (hlt : n < 2 ^ 63) :
    LayoutOk n 1 := ⟨by omega, ⟨0, rfl⟩, by omega⟩

private theorem protoAuthenticatorAt_entails_dealloc_lt_s2 (A : RustAlloc) (a : BitVec 64)
    (auth : ProtoAuthenticator) :
    protoAuthenticatorAt A a auth ⊢
      ∃∗ g : TwoVecGhost, ⌜g.v1.cap.toNat < 2 ^ 63 ∧ g.v2.cap.toNat < 2 ^ 63⌝ ∗
        twoVecHeadersAt a g ∗ vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  unfold protoAuthenticatorAt vecU8
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro c1
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro c2
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p2
  refine Entails.sepExists_right ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_bound A a c1 p1 auth.rootKey
  have h2 := vecU8At_entails_capPtr_dealloc_bound A (a + 24#64) c2 p2 auth.macKey
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  refine Entails.trans (sepConj_mono h1 h2) ?_
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜c1.toNat < 2 ^ 63⌝ ∗ (⌜c2.toNat < 2 ^ 63⌝ ∗
      (twoVecHeadersAt a ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ∗ vecCapPtrDealloc A c1 p1 ∗ vecCapPtrDealloc A c2 p2)) by
    unfold twoVecHeadersAt; dsimp only; ac_rfl)) ?_
  apply Entails.pure_left; intro hlt1; apply Entails.pure_left; intro hlt2
  exact Entails.pure_right ⟨hlt1, hlt2⟩ (Entails.refl _)

theorem chunkedHeaderReceivedAt_1856_entails_err (A : RustAlloc) {F : ShaCompress}
    (fsp : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A (fsp + 1856#64) st ⊢
      ∃∗ g12 : TwoVecGhost, ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64, ∃∗ vecs : List (List Pt),
        ⌜vecs.length = NUM_POLYS ∧ g12.v1.cap.toNat < 2 ^ 63 ∧ g12.v2.cap.toNat < 2 ^ 63 ∧ c3.toNat < 2 ^ 63⌝ ∗
        (((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
         ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8 ∗
         ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
         ((fsp + 1928#64) ↦₆₄ st.uc.epoch)) ∗
        vecCapPtrDealloc A g12.v1.cap g12.v1.ptr ∗ vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗
        vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 := by
  unfold chunkedHeaderReceivedAt; rw [unchunkedHeaderReceivedAt_eq_ekSentAt]; unfold unchunkedEkSentAt
  have hauth : authenticatorAt A (fsp + 1856#64) st.uc.auth =
      protoAuthenticatorAt A (fsp + 1856#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩ := rfl
  have h1904 : (fsp + 1856#64) + 48#64 = fsp + 1904#64 := by bv_omega
  have h1928 : (fsp + 1856#64) + 72#64 = fsp + 1928#64 := by bv_omega
  have h1936 : (fsp + 1856#64) + 80#64 = fsp + 1936#64 := by bv_omega
  rw [hauth, h1904, h1928, h1936]
  have hv3 : vecU8 A (fsp + 1904#64) st.uc.hdr ⊢ ∃∗ c3 : BitVec 64, ∃∗ p3 : BitVec 64,
      ⌜c3.toNat < 2 ^ 63⌝ ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ vecCapPtrDealloc A c3 p3 := by
    unfold vecU8; apply Entails.sepExists_elim; intro c3; apply Entails.sepExists_elim; intro p3
    refine Entails.sepExists_right c3 (Entails.sepExists_right p3 ?_)
    have h := vecU8At_entails_capPtr_dealloc_bound A (fsp + 1904#64) c3 p3 st.uc.hdr
    have h1912 : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
    have h1920 : (fsp + 1904#64) + 16#64 = fsp + 1920#64 := by bv_omega
    rw [h1912, h1920] at h; exact h
  have hdec : polyDecoderAt A (fsp + 1936#64) st.receiving_ek ⊢ ∃∗ vecs : List (List Pt),
      ⌜vecs.length = NUM_POLYS⌝ ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 := by
    refine Entails.trans (polyDecoderAt_entails_vecs_tail A (fsp + 1936#64) st.receiving_ek) ?_
    apply Entails.sepExists_elim; intro vecs; refine Entails.sepExists_right vecs ?_
    have h2320 : (fsp + 1936#64) + 384#64 = fsp + 2320#64 := by bv_omega
    rw [h2320]; exact Entails.refl _
  refine Entails.trans (sepConj_mono
    (sepConj_mono (protoAuthenticatorAt_entails_dealloc_lt_s2 A (fsp + 1856#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩)
      (sepConj_mono_left hv3)) hdec) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro vecs
  rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g12
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro c3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p3
  refine Entails.trans (Entails.of_eq (show _ =
    ⌜g12.v1.cap.toNat < 2 ^ 63 ∧ g12.v2.cap.toNat < 2 ^ 63⌝ ∗
    (⌜c3.toNat < 2 ^ 63⌝ ∗ (⌜vecs.length = NUM_POLYS⌝ ∗
      ((twoVecHeadersAt (fsp + 1856#64) g12 ∗
        ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch)) ∗
       vecCapPtrDealloc A g12.v1.cap g12.v1.ptr ∗ vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗
       vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16))) by ac_rfl)) ?_
  apply Entails.pure_left; rintro ⟨hlt1, hlt2⟩; apply Entails.pure_left; intro hlt3; apply Entails.pure_left; intro hlen
  refine Entails.sepExists_right g12 (Entails.sepExists_right c3 (Entails.sepExists_right p3 (Entails.sepExists_right vecs ?_)))
  refine Entails.pure_right ⟨hlen, hlt1, hlt2, hlt3⟩ ?_; unfold twoVecHeadersAt
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1872 : (fsp + 1856#64) + 16#64 = fsp + 1872#64 := by bv_omega
  have h1880 : (fsp + 1856#64) + 24#64 = fsp + 1880#64 := by bv_omega
  have h1888 : (fsp + 1856#64) + 32#64 = fsp + 1888#64 := by bv_omega
  have h1896 : (fsp + 1856#64) + 40#64 = fsp + 1896#64 := by bv_omega
  rw [h1864, h1872, h1880, h1888, h1896]; exact Entails.of_eq (by ac_rfl)

theorem headerReceived_err_stack_combine (fsp : BitVec 64) (g12 : TwoVecGhost) (c3 p3 ep : BitVec 64) :
    memRegion fsp 1856 ∗
    (((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8 ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗ ((fsp + 1928#64) ↦₆₄ ep)) ∗
    memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ⊢
    memRegion fsp 4144 := by
  have h48 := twoVecHeadersAt_entails_memRegion_48 (fsp + 1856#64) g12; unfold twoVecHeadersAt at h48
  have h1864 : (fsp + 1856#64) + 8#64 = fsp + 1864#64 := by bv_omega
  have h1872 : (fsp + 1856#64) + 16#64 = fsp + 1872#64 := by bv_omega
  have h1880 : (fsp + 1856#64) + 24#64 = fsp + 1880#64 := by bv_omega
  have h1888 : (fsp + 1856#64) + 32#64 = fsp + 1888#64 := by bv_omega
  have h1896 : (fsp + 1856#64) + 40#64 = fsp + 1896#64 := by bv_omega
  rw [h1864, h1872, h1880, h1888, h1896] at h48
  have h24 := Drop.header_cells_entails_memRegion_24 (fsp + 1904#64) c3 p3
  have h1912 : (fsp + 1904#64) + 8#64 = fsp + 1912#64 := by bv_omega
  have h1920 : (fsp + 1904#64) + 16#64 = fsp + 1920#64 := by bv_omega
  rw [h1912, h1920] at h24
  have h8 := ProofLib.pointsTo64_entails_memRegion (fsp + 1928#64) ep
  have h400 : memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16 ⊢ memRegion (fsp + 1936#64) 400 := by
    have h2320 : fsp + 2320#64 = (fsp + 1936#64) + 384#64 := by bv_omega
    rw [h2320]; exact polyDecoder_post_join (fsp + 1936#64)
  rw [memRegion_4144_split_1856_480 fsp,
      ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 48) (k := 432) (b' := fsp + 1904#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1904#64) (n := 24) (k := 408) (b' := fsp + 1928#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 1928#64) (n := 8) (k := 400) (b' := fsp + 1936#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans (Entails.of_eq (show _ = memRegion fsp 1856 ∗
    ((((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ memRegion (fsp + 1872#64) 8 ∗
      ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗ memRegion (fsp + 1896#64) 8) ∗
     (((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8) ∗
     ((fsp + 1928#64) ↦₆₄ ep) ∗ (memRegion (fsp + 1936#64) polyArrayBytes ∗ memRegion (fsp + 2320#64) 16)) ∗
    memRegion (fsp + 2336#64) 1808 by ac_rfl))
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono h48 (sepConj_mono h24 (sepConj_mono h8 h400)))))

end CryptoVerification.SpqrV1.States.Recv
