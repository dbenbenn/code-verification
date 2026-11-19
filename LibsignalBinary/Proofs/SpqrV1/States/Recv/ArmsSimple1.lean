/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `KeysUnsampled` Arm & Shared `Ok(V1Recv)` Epilogue

**Checked by Lean.** Offset-normalized word-grid combinators, the shared `+18996` `Ok(V1Recv)`
exit when `key = none` (`488`-byte variants), and the `States.keysUnsampled` arm (`0x554b4`, `+96`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592 Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `States.keysUnsampled` (`tag = 2#64`, `+96` / `0x554b4`) -/

theorem chunkedStatesAt_keysUnsampled_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) =
      (a ↦₆₄ 2#64) ∗ authenticatorAt A (a + 8#64) st.uc.auth ∗ ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 := by
  simp only [chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt,
    BitVec.add_assoc, show (8#64 + 48#64 : BitVec 64) = 56#64 from rfl]; ac_rfl

theorem chunkedStatesAt_keysUnsampled_entails_dealloc (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) ⊢
      ∃∗ g : TwoVecGhost,
        (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ g.v1.cap) ∗ ((a + 16#64) ↦₆₄ g.v1.ptr) ∗ memRegion (a + 24#64) 8 ∗
        ((a + 32#64) ↦₆₄ g.v2.cap) ∗ ((a + 40#64) ↦₆₄ g.v2.ptr) ∗ memRegion (a + 48#64) 8 ∗
        ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 ∗
        vecCapPtrDealloc A g.v1.cap g.v1.ptr ∗ vecCapPtrDealloc A g.v2.cap g.v2.ptr := by
  have hauth : authenticatorAt A (a + 8#64) st.uc.auth =
      protoAuthenticatorAt A (a + 8#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩ := rfl
  rw [chunkedStatesAt_keysUnsampled_unfold, hauth]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left
    (protoAuthenticatorAt_entails_dealloc A (a + 8#64) ⟨st.uc.auth.rootKey, st.uc.auth.macKey⟩))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro g
  rw [sepConj_assoc (⌜g.v1.cap.toNat < 2 ^ 63⌝), sepConj_left_comm (a ↦₆₄ 2#64)]
  apply Entails.pure_left; intro _; refine Entails.sepExists_right g ?_
  simp only [twoVecHeadersAt, BitVec.add_assoc,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (8#64 + 16#64 : BitVec 64) = 24#64 from rfl,
    show (8#64 + 24#64 : BitVec 64) = 32#64 from rfl, show (8#64 + 32#64 : BitVec 64) = 40#64 from rfl,
    show (8#64 + 40#64 : BitVec 64) = 48#64 from rfl]; exact Entails.of_eq (by ac_rfl)

theorem keysUnsampled_selfA_err_combine (a c1 p1 c2 p2 ep : BitVec 64) :
    (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ p1) ∗ memRegion (a + 24#64) 8 ∗
    ((a + 32#64) ↦₆₄ c2) ∗ ((a + 40#64) ↦₆₄ p2) ∗ memRegion (a + 48#64) 8 ∗
    ((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864 ⊢ memRegion a chunkedStatesSize := by
  have h56 : ((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864 ⊢ memRegion (a + 56#64) 872 := by
    rw [ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 864) (b' := a + 64#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (a + 56#64) ep)
  have hhdr : twoVecHeadersAt (a + 8#64) ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩ ⊢ memRegion (a + 8#64) 48 :=
    twoVecHeadersAt_entails_memRegion_48 (a + 8#64) ⟨⟨c1, p1⟩, ⟨c2, p2⟩⟩
  simp only [twoVecHeadersAt, BitVec.add_assoc,
    show (8#64 + 8#64 : BitVec 64) = 16#64 from rfl, show (8#64 + 16#64 : BitVec 64) = 24#64 from rfl,
    show (8#64 + 24#64 : BitVec 64) = 32#64 from rfl, show (8#64 + 32#64 : BitVec 64) = 40#64 from rfl,
    show (8#64 + 40#64 : BitVec 64) = 48#64 from rfl] at hhdr
  have h8 : memRegion (a + 8#64) 48 ∗ memRegion (a + 56#64) 872 ⊢ memRegion (a + 8#64) 920 := by
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 48) (k := 872) (b' := a + 56#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
  unfold chunkedStatesSize; rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 920) (b' := a + 8#64) rfl rfl (by decide)]
  refine Entails.trans (Entails.of_eq (show _ = (a ↦₆₄ 2#64) ∗
    ((((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ p1) ∗ memRegion (a + 24#64) 8 ∗
      ((a + 32#64) ↦₆₄ c2) ∗ ((a + 40#64) ↦₆₄ p2) ∗ memRegion (a + 48#64) 8) ∗
     (((a + 56#64) ↦₆₄ ep) ∗ memRegion (a + 64#64) 864)) by ac_rfl)) ?_
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a 2#64) (Entails.trans (sepConj_mono hhdr h56) h8)

theorem memRegion_4088_split_456_504 (fsp : BitVec 64) :
    memRegion (fsp + 56#64) 4088 =
      memRegion (fsp + 56#64) 400 ∗ (∃∗ v456 : BitVec 64, ((fsp + 456#64) ↦₆₄ v456)) ∗
      memRegion (fsp + 464#64) 40 ∗ (∃∗ v504 : BitVec 64, ((fsp + 504#64) ↦₆₄ v504)) ∗ memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 56#64) (n := 400) (k := 3688) (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 8) (k := 3680) (b' := fsp + 464#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 456#64),
      ProofLib.memRegion_split' (b := fsp + 464#64) (n := 40) (k := 3640) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 504#64)]

theorem cells_456_504_entails_memRegion_4088 (fsp v456 v504 : BitVec 64) :
    memRegion (fsp + 56#64) 400 ∗ ((fsp + 456#64) ↦₆₄ v456) ∗
      memRegion (fsp + 464#64) 40 ∗ ((fsp + 504#64) ↦₆₄ v504) ∗ memRegion (fsp + 512#64) 3632 ⊢ memRegion (fsp + 56#64) 4088 := by
  rw [ProofLib.memRegion_split' (b := fsp + 56#64) (n := 400) (k := 3688) (b' := fsp + 456#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 456#64) (n := 8) (k := 3680) (b' := fsp + 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 464#64) (n := 40) (k := 3640) (b' := fsp + 504#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 504#64) (n := 8) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion (fsp + 456#64) v456)
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion (fsp + 504#64) v504))))

theorem ule_false_of_gt {a b : BitVec 64} (h : a > b) : BitVec.ule a b = false := by have hlt : b < a := h; bv_kernel
theorem ule_true_of_not_gt {a b : BitVec 64} (h : ¬ (a > b)) : BitVec.ule a b = true := by
  have hle : a ≤ b := by change ¬ (b < a) at h; bv_omega
  bv_kernel
theorem ne_zero_of_beq_false {c : BitVec 64} (h : (c == 0#64) = false) : c.toNat ≠ 0 := by
  intro h0; have hc : c = 0#64 := BitVec.eq_of_toNat_eq h0; subst hc; contradiction

/-- `n` existentially quantified 64-bit word cells at `(base + (k + 8 * i)#64)`. -/
@[expose] def existsWordsAtOff (base : BitVec 64) : Nat → Nat → SepProp
  | 0, _ => emp
  | n + 1, k => (∃∗ w : BitVec 64, (base + BitVec.ofNat 64 k) ↦₆₄ w) ∗ existsWordsAtOff base n (k + 8)

theorem memRegion_off_eq_existsWordsAtOff (base : BitVec 64) :
    ∀ (n k : Nat), 8 * n ≤ 2 ^ 64 → memRegion (base + BitVec.ofNat 64 k) (8 * n) = existsWordsAtOff base n k
  | 0, k, _ => by simp [existsWordsAtOff, ProofLib.memRegion_zero]
  | n + 1, k, hn => by
    have hsplit : memRegion (base + BitVec.ofNat 64 k) (8 * (n + 1)) =
        memRegion (base + BitVec.ofNat 64 k) 8 ∗ memRegion (base + BitVec.ofNat 64 (k + 8)) (8 * n) := by
      refine ProofLib.memRegion_split' (b := base + BitVec.ofNat 64 k) (n := 8) (k := 8 * n)
        (b' := base + BitVec.ofNat 64 (k + 8)) (by omega) ?_ (by omega)
      rw [BitVec.ofNat_add]; bv_omega
    rw [hsplit, ProofLib.memRegion_eight (base + BitVec.ofNat 64 k),
        memRegion_off_eq_existsWordsAtOff base n (k + 8) (by omega), existsWordsAtOff]

/-- Contiguous 64-bit word cells at `(base + (k + 8 * i)#64)`. -/
@[expose] def wordsAtOff (base : BitVec 64) : List (BitVec 64) → Nat → SepProp
  | [], _ => emp
  | w :: ws, k => ((base + BitVec.ofNat 64 k) ↦₆₄ w) ∗ wordsAtOff base ws (k + 8)

theorem wordsAtOff_eq_wordsAt (base : BitVec 64) :
    ∀ (ws : List (BitVec 64)) (k : Nat), wordsAtOff base ws k = wordsAt (base + BitVec.ofNat 64 k) ws
  | [], k => rfl
  | w :: ws, k => by
    simp only [wordsAtOff, wordsAt]
    have haddr : base + BitVec.ofNat 64 (k + 8) = (base + BitVec.ofNat 64 k) + 8#64 := by rw [BitVec.ofNat_add]; bv_omega
    rw [wordsAtOff_eq_wordsAt base ws (k + 8), haddr]

theorem wordsAtOff_entails_memRegion (base : BitVec 64) (ws : List (BitVec 64)) (k n : Nat)
    (hn : 8 * ws.length = n) : wordsAtOff base ws k ⊢ memRegion (base + BitVec.ofNat 64 k) n := by
  rw [wordsAtOff_eq_wordsAt]; exact wordsAt_entails_memRegion ws (base + BitVec.ofNat 64 k) n hn

theorem wordsAtOff_entails_memRegion_zero (base : BitVec 64) (ws : List (BitVec 64)) (n : Nat)
    (hn : 8 * ws.length = n) : wordsAtOff base ws 0 ⊢ memRegion base n := by
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using wordsAtOff_entails_memRegion base ws 0 n hn

/-- Stack cells in `fsp + 224..504` read by Step A (`+18996 -> +19128`), excluding `q960`. -/
@[expose] def epilogueRecvStackPartA488 (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64) : SepProp :=
  ((fsp + 224#64) ↦₆₄ w224) ∗ ((fsp + 288#64) ↦₆₄ w288) ∗ ((fsp + 296#64) ↦₆₄ w296) ∗
  ((fsp + 336#64) ↦₆₄ w336) ∗ ((fsp + 352#64) ↦₆₄ w352) ∗ ((fsp + 368#64) ↦₆₄ w368) ∗
  ((fsp + 376#64) ↦₆₄ w376) ∗ ((fsp + 384#64) ↦₆₄ w384) ∗ ((fsp + 408#64) ↦₆₄ w408) ∗
  ((fsp + 432#64) ↦₆₄ w432) ∗ ((fsp + 456#64) ↦₆₄ w456) ∗ ((fsp + 496#64) ↦₆₄ w496) ∗ ((fsp + 504#64) ↦₆₄ w504)

theorem epilogueRecvStackPartA_eq_488 (fsp : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64) (q960 : BitVec 128) :
    epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 =
      epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗ ((fsp + 960#64) ↦₁₂₈ q960) := by
  simp only [epilogueRecvStackPartA, epilogueRecvStackPartA488, sepConj_assoc]

/-- First 30 words (`out + 120..480`) written in Step B (`+19128 -> +19280`). -/
@[expose] def epilogueRecvOutPartB488 (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) : SepProp :=
  ((out + 120#64) ↦₆₄ w120) ∗ ((out + 128#64) ↦₆₄ w128) ∗ ((out + 136#64) ↦₆₄ w136) ∗ ((out + 144#64) ↦₆₄ w144) ∗
  ((out + 152#64) ↦₆₄ w152) ∗ ((out + 160#64) ↦₆₄ w160) ∗ ((out + 168#64) ↦₆₄ w168) ∗ ((out + 176#64) ↦₆₄ w176) ∗
  ((out + 184#64) ↦₆₄ w184) ∗ ((out + 192#64) ↦₆₄ w192) ∗ ((out + 200#64) ↦₆₄ w200) ∗ ((out + 208#64) ↦₆₄ w208) ∗
  ((out + 216#64) ↦₆₄ w216) ∗ ((out + 224#64) ↦₆₄ w224) ∗ ((out + 232#64) ↦₆₄ w232) ∗ ((out + 240#64) ↦₆₄ w240) ∗
  ((out + 248#64) ↦₆₄ w248) ∗ ((out + 256#64) ↦₆₄ w256) ∗ ((out + 360#64) ↦₆₄ w360) ∗ ((out + 368#64) ↦₆₄ w368) ∗
  ((out + 376#64) ↦₆₄ w376) ∗ ((out + 384#64) ↦₆₄ w384) ∗ ((out + 408#64) ↦₆₄ w408) ∗ ((out + 416#64) ↦₆₄ w416) ∗
  ((out + 440#64) ↦₆₄ w440) ∗ ((out + 448#64) ↦₆₄ w448) ∗ ((out + 456#64) ↦₆₄ w456) ∗ ((out + 464#64) ↦₆₄ w464) ∗
  ((out + 472#64) ↦₆₄ w472) ∗ ((out + 480#64) ↦₆₄ w480)

theorem epilogueRecvOutPartB_eq_488 (out : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) (q488 : BitVec 128) (w504 : BitVec 64) :
    epilogueRecvOutPartB out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 q488 w504 =
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ∗
      ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w504) := by
  simp only [epilogueRecvOutPartB, epilogueRecvOutPartB488, sepConj_assoc]

theorem epilogueStack_224_512_entails_memRegion (fsp : BitVec 64)
    (w224 w232 w240 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64) :
    epilogueRecvStackPartA488 fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗ ((fsp + 240#64) ↦₆₄ w240) ∗
      epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ⊢
    memRegion (fsp + 224#64) 288 := by
  refine Entails.trans (Entails.of_eq ?_)
    (wordsAtOff_entails_memRegion fsp
      [w224, w232, w240, w248, w256, w264, w272, w280, w288, w296, w304, w312,
       w320, w328, w336, w344, w352, w360, w368, w376, w384, w392, w400, w408,
       w416, w424, w432, w440, w448, w456, w464, w472, w480, w488, w496, w504] 224 288 rfl)
  dsimp only [wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem epilogueOut_64_488_entails_words_and_memRegion (out : BitVec 64)
    (w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) :
    epilogueRecvOutPartA out w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112
      w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ⊢
    (out ↦₆₄ w0) ∗ wordsAt (out + 8#64) [w8, w16, w24, w32, w40, w48] ∗ ((out + 56#64) ↦₆₄ w56) ∗ memRegion (out + 64#64) 424 := by
  have h53 : wordsAtOff out
      [w64, w72, w80, w88, w96, w104, w112,
       w120, w128, w136, w144, w152, w160, w168, w176, w184, w192, w200, w208, w216, w224, w232, w240, w248, w256,
       w264, w272, w280, w288, w296, w304, w312, w320, w328, w336, w344, w352,
       w360, w368, w376, w384, w392, w400, w408, w416, w424, w432, w440, w448, w456, w464, w472, w480]
      64 ⊢ memRegion (out + 64#64) 424 := wordsAtOff_entails_memRegion out _ 64 424 rfl
  rw [(wordsAtOff_eq_wordsAt out [w8, w16, w24, w32, w40, w48] 8).symm]
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right h53)))
  dsimp only [wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl

theorem memRegion_entails_exists_pointsToBytes :
    ∀ (n : Nat) (a : BitVec 64), n ≤ 2 ^ 64 → (memRegion a n ⊢ ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (a ↦ₛ bs))
  | 0, a, _ => by
    rw [ProofLib.memRegion_zero]; refine Entails.sepExists_right [] ?_
    rw [pointsToBytes_nil]; exact Entails.pure_right rfl (Entails.refl _)
  | n + 1, a, hn => by
    rw [show n + 1 = 1 + n by omega, ProofLib.memRegion_split a 1 n (by omega), ProofLib.memRegion_one a]
    refine Entails.trans (sepConj_mono_right (memRegion_entails_exists_pointsToBytes n (a + 1#64) (by omega))) ?_
    rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro b0
    rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro bs
    rw [← sepConj_assoc, sepConj_comm (a ↦₈ b0), sepConj_assoc]; apply Entails.pure_left; intro hbs
    refine Entails.sepExists_right (b0 :: bs) (Entails.pure_right (by simp [hbs]; omega) ?_)
    rw [pointsToBytes_cons]; exact Entails.refl _

theorem pointsToBytes_entails_memRegion' :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64), bs.length ≤ 2 ^ 64 → ((a ↦ₛ bs) ⊢ memRegion a bs.length)
  | [], a, _ => by rw [pointsToBytes_nil, List.length_nil, ProofLib.memRegion_zero]; exact Entails.refl _
  | b0 :: bs, a, hbs => by
    simp only [List.length_cons] at hbs ⊢
    rw [show bs.length + 1 = 1 + bs.length by omega, ProofLib.memRegion_split a 1 bs.length (by omega), pointsToBytes_cons]
    exact sepConj_mono (ProofLib.pointsTo8_entails_memRegion a b0) (pointsToBytes_entails_memRegion' bs (a + 1#64) (by omega))

theorem pointsToBytes_entails_memRegion_len (a : BitVec 64) (bs : List (BitVec 8))
    (n : Nat) (hn : bs.length = n) (hbound : n ≤ 2 ^ 64) : (a ↦ₛ bs) ⊢ memRegion a n := by
  subst hn; exact pointsToBytes_entails_memRegion' bs a hbound

theorem memRegion_3632_entails_epilogue (fsp : BitVec 64) :
    memRegion (fsp + 512#64) 3632 ⊢
      ((∃∗ q512 : BitVec 128, (fsp + 512#64) ↦₁₂₈ q512) ∗ (∃∗ q528 : BitVec 128, (fsp + 528#64) ↦₁₂₈ q528) ∗
       (∃∗ q544 : BitVec 128, (fsp + 544#64) ↦₁₂₈ q544) ∗ (∃∗ w560 : BitVec 64, (fsp + 560#64) ↦₆₄ w560) ∗
       (∃∗ bs576 : List (BitVec 8), ⌜bs576.length = 376⌝ ∗ ((fsp + 576#64) ↦ₛ bs576)) ∗
       (∃∗ q960 : BitVec 128, (fsp + 960#64) ↦₁₂₈ q960)) ∗
      (memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 512#64),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 3600) (b' := fsp + 544#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 528#64),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 3584) (b' := fsp + 560#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 544#64),
      ProofLib.memRegion_split' (b := fsp + 560#64) (n := 8) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 560#64),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 960#64)]
  exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_entails_exists_pointsToBytes 376 (fsp + 576#64) (by decide))))))))
    (Entails.of_eq (by ac_rfl))

theorem epilogue_entails_memRegion_3632 (fsp : BitVec 64)
    (q512 q528 q544 q960 : BitVec 128) (w560 : BitVec 64) (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376) :
    ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗ ((fsp + 544#64) ↦₁₂₈ q544) ∗
      ((fsp + 560#64) ↦₆₄ w560) ∗ memRegion (fsp + 568#64) 8 ∗ ((fsp + 576#64) ↦ₛ bs576) ∗
      memRegion (fsp + 952#64) 8 ∗ ((fsp + 960#64) ↦₁₂₈ q960) ∗ memRegion (fsp + 976#64) 3168 ⊢
    memRegion (fsp + 512#64) 3632 := by
  rw [ProofLib.memRegion_split' (b := fsp + 512#64) (n := 16) (k := 3616) (b' := fsp + 528#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 512#64),
      ProofLib.memRegion_split' (b := fsp + 528#64) (n := 16) (k := 3600) (b' := fsp + 544#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 528#64),
      ProofLib.memRegion_split' (b := fsp + 544#64) (n := 16) (k := 3584) (b' := fsp + 560#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 544#64),
      ProofLib.memRegion_split' (b := fsp + 560#64) (n := 8) (k := 3576) (b' := fsp + 568#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (fsp + 560#64),
      ProofLib.memRegion_split' (b := fsp + 568#64) (n := 8) (k := 3568) (b' := fsp + 576#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 576#64) (n := 376) (k := 3192) (b' := fsp + 952#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 952#64) (n := 8) (k := 3184) (b' := fsp + 960#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := fsp + 960#64) (n := 16) (k := 3168) (b' := fsp + 976#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (fsp + 960#64)]
  exact sepConj_mono (Entails.sepExists_right q512 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right q528 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right q544 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w560 (Entails.refl _))
          (sepConj_mono_right (sepConj_mono
            (pointsToBytes_entails_memRegion_len (fsp + 576#64) bs576 376 hbs576 (by decide))
            (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_right q960 (Entails.refl _)))))))))

theorem memRegion_472_entails_epilogue (out : BitVec 64) :
    memRegion (out + 488#64) 472 ⊢
      ((∃∗ uq488 : BitVec 128, (out + 488#64) ↦₁₂₈ uq488) ∗ (∃∗ u504 : BitVec 64, (out + 504#64) ↦₆₄ u504) ∗
       (∃∗ uq888 : BitVec 128, (out + 888#64) ↦₁₂₈ uq888) ∗ (∃∗ uq904 : BitVec 128, (out + 904#64) ↦₁₂₈ uq904) ∗
       (∃∗ u920 : BitVec 64, (out + 920#64) ↦₆₄ u920) ∗ (∃∗ u928 : BitVec 64, (out + 928#64) ↦₆₄ u928) ∗
       (∃∗ u936 : BitVec 64, (out + 936#64) ↦₆₄ u936) ∗ (∃∗ uq944 : BitVec 128, (out + 944#64) ↦₁₂₈ uq944)) ∗
      memRegion (out + 512#64) 376 := by
  rw [ProofLib.memRegion_split' (b := out + 488#64) (n := 16) (k := 456) (b' := out + 504#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 488#64),
      ProofLib.memRegion_split' (b := out + 504#64) (n := 8) (k := 448) (b' := out + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 504#64),
      ProofLib.memRegion_split' (b := out + 512#64) (n := 376) (k := 72) (b' := out + 888#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 888#64) (n := 16) (k := 56) (b' := out + 904#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 888#64),
      ProofLib.memRegion_split' (b := out + 904#64) (n := 16) (k := 40) (b' := out + 920#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 904#64),
      ProofLib.memRegion_split' (b := out + 920#64) (n := 8) (k := 32) (b' := out + 928#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 920#64),
      ProofLib.memRegion_split' (b := out + 928#64) (n := 8) (k := 24) (b' := out + 936#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 928#64),
      ProofLib.memRegion_split' (b := out + 936#64) (n := 8) (k := 16) (b' := out + 944#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 936#64), ProofLib.memRegion_sixteen (out + 944#64)]
  exact Entails.of_eq (by ac_rfl)

theorem epilogue_out_488_960_entails_memRegion_and_optNone (A : RustAlloc) (out : BitVec 64)
    (q488 q528 q544 q512 : BitVec 128) (w256 w560 w936 : BitVec 64) (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376) :
    ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
      ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ∗
      ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512) ⊢
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none := by
  have h440 : ((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
      ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560) ⊢ memRegion (out + 488#64) 440 := by
    rw [ProofLib.memRegion_split' (b := out + 488#64) (n := 16) (k := 424) (b' := out + 504#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 488#64),
        ProofLib.memRegion_split' (b := out + 504#64) (n := 8) (k := 416) (b' := out + 512#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_eight (out + 504#64),
        ProofLib.memRegion_split' (b := out + 512#64) (n := 376) (k := 40) (b' := out + 888#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := out + 888#64) (n := 16) (k := 24) (b' := out + 904#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_sixteen (out + 888#64),
        ProofLib.memRegion_split' (b := out + 904#64) (n := 16) (k := 8) (b' := out + 920#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_sixteen (out + 904#64), ProofLib.memRegion_eight (out + 920#64)]
    exact sepConj_mono (Entails.sepExists_right q488 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w256 (Entails.refl _))
        (sepConj_mono (pointsToBytes_entails_memRegion_len (out + 512#64) bs576 376 hbs576 (by decide))
          (sepConj_mono (Entails.sepExists_right q528 (Entails.refl _))
            (sepConj_mono (Entails.sepExists_right q544 (Entails.refl _)) (Entails.sepExists_right w560 (Entails.refl _))))))
  have h24 : ((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512) ⊢ optEpochSecretAt A (out + 928#64) none := by
    rw [optEpochSecretAt_none, BitVec.add_assoc, show (928#64 + 8#64 : BitVec 64) = 936#64 from rfl,
        ProofLib.memRegion_split' (b := out + 936#64) (n := 8) (k := 16) (b' := out + 944#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (out + 936#64), ProofLib.memRegion_sixteen (out + 944#64)]
    exact sepConj_mono_right (sepConj_mono (Entails.sepExists_right w936 (Entails.refl _)) (Entails.sepExists_right q512 (Entails.refl _)))
  exact Entails.trans (Entails.of_eq (show _ =
    (((out + 488#64) ↦₁₂₈ q488) ∗ ((out + 504#64) ↦₆₄ w256) ∗ ((out + 512#64) ↦ₛ bs576) ∗
     ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗ ((out + 920#64) ↦₆₄ w560)) ∗
    (((out + 928#64) ↦₆₄ noneCap) ∗ ((out + 936#64) ↦₆₄ w936) ∗ ((out + 944#64) ↦₁₂₈ q512)) by ac_rfl))
    (sepConj_mono h440 h24)

theorem wordsAtOff_out_488_eq_epilogueOut (out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : BitVec 64)
    (u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 : BitVec 64)
    (u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 : BitVec 64)
    (u360 u368 u376 u384 u392 u400 u408 u416 u424 u432 u440 u448 u456 u464 u472 u480 : BitVec 64) :
    wordsAtOff out
      [u0, u8, u16, u24, u32, u40, u48, u56, u64, u72, u80, u88, u96, u104, u112,
       u120, u128, u136, u144, u152, u160, u168, u176, u184, u192, u200, u208, u216, u224, u232, u240, u248, u256,
       u264, u272, u280, u288, u296, u304, u312, u320, u328, u336, u344, u352,
       u360, u368, u376, u384, u392, u400, u408, u416, u424, u432, u440, u448, u456, u464, u472, u480] 0 =
    epilogueRecvOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
      u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 ∗
    epilogueRecvOutPartB488 out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
      u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 := by
  dsimp only [wordsAtOff, epilogueRecvOutPartA, epilogueRecvOutPartB488, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  rw [BitVec.add_zero]; ac_rfl

theorem stack_recombine_4144 (fsp : BitVec 64) :
    memRegion fsp 224 ∗ memRegion (fsp + 224#64) 288 ∗ memRegion (fsp + 512#64) 3632 = memRegion fsp 4144 := by
  rw [ProofLib.memRegion_split fsp 224 3920 (by decide),
      ProofLib.memRegion_split' (b := fsp + 224#64) (n := 288) (k := 3632) (b' := fsp + 512#64) rfl (by bv_omega) (by decide)]

theorem memRegion_out_960_split_488_472 (out : BitVec 64) :
    memRegion out v1RecvSize = memRegion out 488 ∗ memRegion (out + 488#64) 472 := by
  unfold v1RecvSize; exact ProofLib.memRegion_split out 488 472 (by decide)

theorem sepWP_pure_left {prog : Program} {target_pc : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {post : State → SepProp → Prop}
    (h : φ → SepWP prog target_pc s P post) : SepWP prog target_pc s (⌜φ⌝ ∗ P) post :=
  SepWP.pure_elim h

theorem sepWP_intro_ex {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {Q : α → SepProp}
    (h : ∀ v : α, SepWP prog target_pc s (rest ∗ (Q v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, Q v) ∗ rest) ∗ R) post := by
  rw [sepExists_sepConj_left, sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro v; rw [sepConj_assoc, sepConj_left_comm (Q v)]; exact h v

theorem sepWP_intro_ex_pure {α : Type} {prog : Program} {target_pc : BitVec 64} {s : State}
    {post : State → SepProp → Prop} {rest R : SepProp} {φ : α → Prop} {Q : α → SepProp}
    (h : ∀ v : α, φ v → SepWP prog target_pc s (rest ∗ (Q v ∗ R)) post) :
    SepWP prog target_pc s (((∃∗ v : α, ⌜φ v⌝ ∗ Q v) ∗ rest) ∗ R) post := by
  apply sepWP_intro_ex; intro v
  rw [sepConj_assoc (⌜φ v⌝), sepConj_left_comm rest (⌜φ v⌝)]; exact sepWP_pure_left (h v)

theorem relocatedHeap_recompose_words (F : BitVec 64 → SepProp) (ws : List (BitVec 64)) (dst : BitVec 64) :
    wordsAt dst ws ∗ relocatedHeap F (wordsBytes ws) ⊢ F dst := by
  rw [wordsAt_eq_pointsToBytes ws dst]; exact relocatedHeap_recompose F (wordsBytes ws) dst

theorem selfA_8words_entails_memRegion_928 (selfA w0 w8 w16 w24 w32 w40 w48 w56 : BitVec 64) :
    (selfA ↦₆₄ w0) ∗ ((selfA + 8#64) ↦₆₄ w8) ∗ ((selfA + 16#64) ↦₆₄ w16) ∗ ((selfA + 24#64) ↦₆₄ w24) ∗
    ((selfA + 32#64) ↦₆₄ w32) ∗ ((selfA + 40#64) ↦₆₄ w40) ∗ ((selfA + 48#64) ↦₆₄ w48) ∗
    ((selfA + 56#64) ↦₆₄ w56) ∗ memRegion (selfA + 64#64) 864 ⊢ memRegion selfA chunkedStatesSize := by
  unfold chunkedStatesSize; rw [ProofLib.memRegion_split selfA 64 864 (by decide)]
  refine Entails.trans (Entails.of_eq ?_)
    (sepConj_mono_left (wordsAtOff_entails_memRegion_zero selfA [w0, w8, w16, w24, w32, w40, w48, w56] 64 rfl))
  dsimp only [wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; rw [BitVec.add_zero]; ac_rfl

theorem resultV1RecvAt_ok (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (v : V1Recv spqrPolyApi (spqrAuthApi F)) :
    resultV1RecvAt A (F := F) out (.ok v) =
      chunkedStatesAt A out v.state ∗ optEpochSecretAt A (out + 928#64) v.key := rfl

theorem chunkedStatesAt_keysUnsampled_extract (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) ⊢
      ∃∗ g : AuthWords,
        (a ↦₆₄ 2#64) ∗ ((a + 8#64) ↦₆₄ g.v1.w0) ∗ ((a + 16#64) ↦₆₄ g.v1.w1) ∗ ((a + 24#64) ↦₆₄ g.v1.w2) ∗
        ((a + 32#64) ↦₆₄ g.v2.w0) ∗ ((a + 40#64) ↦₆₄ g.v2.w1) ∗ ((a + 48#64) ↦₆₄ g.v2.w2) ∗
        ((a + 56#64) ↦₆₄ st.uc.epoch) ∗ memRegion (a + 64#64) 864 ∗
        relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) := by
  rw [chunkedStatesAt_keysUnsampled_unfold]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (authenticatorAt_extract A (a + 8#64) st.uc.auth))) ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro g; refine Entails.sepExists_right g ?_
  rw [← wordsAtOff_eq_wordsAt a (authWordsList g) 8]
  dsimp only [authWordsList, wordsAtOff, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; exact Entails.of_eq (by ac_rfl)

theorem keysUnsampled_out_recompose (A : RustAlloc) {F : ShaCompress} (out : BitVec 64)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) (g : AuthWords)
    (w64 w72 w80 w88 w96 w104 w112 : BitVec 64)
    (w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 : BitVec 64)
    (w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256 : BitVec 64)
    (w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 : BitVec 64) :
    epilogueRecvOutPartA out 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
      w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
    epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
      w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480 ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) ⊢
    resultV1RecvAt A (F := F) out (.ok ⟨none, .keysUnsampled st⟩) := by
  rw [resultV1RecvAt_ok, chunkedStatesAt_keysUnsampled_unfold,
      ProofLib.memRegion_split' (b := out + 64#64) (n := 424) (k := 440) (b' := out + 488#64) rfl (by bv_omega) (by decide)]
  have hout := epilogueOut_64_488_entails_words_and_memRegion out
    2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
    w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432
    w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
    w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480
  have hrec := relocatedHeap_recompose_words (fun dst => authenticatorAt A dst st.uc.auth) (authWordsList g) (out + 8#64)
  dsimp only [authWordsList] at hrec
  refine Entails.trans (Entails.of_eq (show _ =
    (epilogueRecvOutPartA out 2#64 g.v1.w0 g.v1.w1 g.v1.w2 g.v2.w0 g.v2.w1 g.v2.w2 st.uc.epoch
       w64 w72 w80 w88 w96 w104 w112 w264 w272 w280 w288 w296 w304 w312 w320 w328 w336 w344 w352 w392 w400 w424 w432 ∗
     epilogueRecvOutPartB488 out w120 w128 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 w216 w224 w232 w240 w248 w256
       w360 w368 w376 w384 w408 w416 w440 w448 w456 w464 w472 w480) ∗
    memRegion (out + 488#64) 440 ∗ optEpochSecretAt A (out + 928#64) none ∗
    relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g)) by ac_rfl))
    (Entails.trans (sepConj_mono_left hout) (Entails.trans (Entails.of_eq (show _ =
      (out ↦₆₄ 2#64) ∗ (wordsAt (out + 8#64) [g.v1.w0, g.v1.w1, g.v1.w2, g.v2.w0, g.v2.w1, g.v2.w2] ∗
       relocatedHeap (fun dst => authenticatorAt A dst st.uc.auth) (wordsBytes (authWordsList g))) ∗
      ((out + 56#64) ↦₆₄ st.uc.epoch) ∗ (memRegion (out + 64#64) 424 ∗ memRegion (out + 488#64) 440) ∗
      optEpochSecretAt A (out + 928#64) none by ac_rfl))
      (Entails.trans (sepConj_mono_right (sepConj_mono_left hrec)) (Entails.of_eq (by ac_rfl)))))

end CryptoVerification.SpqrV1.States.Recv
