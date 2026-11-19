/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Sampled` Arm, Part 5 (`outMsg = some decoded`)

**Checked by Lean.** Verifies the `<Unchunked.SendCt.Ct1Sent>::recv_ek` call (`+11508 -> +11528`),
Path 5a (`recv_ek = .error`), `.ok uc_ek` staging (`+11528 -> +11620`), and Path 5b
(`recv_ek = .ok uc_ek, ack = false` → `States.ekReceivedCt1Sampled`).
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
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272

theorem unchunkedCt1SentRecvEkResAt_error_entails (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (err : Error) :
    unchunkedCt1SentRecvEkResAt A (F := F) a (.error err) ⊢
      ∃∗ w8 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ bs7 : List (BitVec 8),
        ⌜bs7.length = 7 ∧ unpack64 w8 = 12#8 :: bs7⌝ ∗
        (a ↦₆₄ noneCap) ∗
        ((a + 8#64) ↦₆₄ w8) ∗
        ((a + 16#64) ↦₆₄ w16) ∗
        ((a + 24#64) ↦₆₄ w24) ∗
        memRegion (a + 32#64) 96 := by
  dsimp only [unchunkedCt1SentRecvEkResAt]
  rw [ProofLib.memRegion_split' (b := a + 9#64) (n := 7) (k := 112)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 104)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 96)
        (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (a + 16#64),
      ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eq_exists_bytes (a + 9#64) 7 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w24
  apply Entails.sepExists_elim; intro w16
  apply Entails.sepExists_elim; intro bs7
  rw [sepConj_assoc, sepConj_left_comm ((a + 8#64) ↦₈ 12#8), sepConj_left_comm (a ↦₆₄ noneCap)]
  apply Entails.pure_left; intro hlen7
  have hlen8 : (12#8 :: bs7).length = 8 := by simp [hlen7]
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 hlen8
  refine Entails.sepExists_right w8 (Entails.sepExists_right w16
    (Entails.sepExists_right w24 (Entails.sepExists_right bs7 ?_)))
  refine Entails.pure_right ⟨hlen7, hw8.symm⟩ ?_
  have h8 : ((a + 8#64) ↦₈ 12#8) ∗ ((a + 9#64) ↦ₛ bs7) = ((a + 8#64) ↦₆₄ w8) := by
    rw [pointsTo64_eq_pointsToBytes (a + 8#64) w8, ← hw8,
        pointsToBytes_cons (a + 8#64) 12#8 bs7]
    have h9 : a + 8#64 + 1#64 = a + 9#64 := by bv_omega
    rw [h9]
  rw [← sepConj_assoc ((a + 8#64) ↦₈ 12#8), h8]
  exact Entails.of_eq (by ac_rfl)

theorem err_words_entails_resultV1RecvAt_erroneous (A : RustAlloc) {F : ShaCompress}
    (outA w8 w16 w24 : BitVec 64) {bs7 : List (BitVec 8)}
    (hlen7 : bs7.length = 7) (hw8 : unpack64 w8 = 12#8 :: bs7) :
    (outA ↦₆₄ noneCap) ∗
      ((outA + 8#64) ↦₆₄ w8) ∗
      ((outA + 16#64) ↦₆₄ w16) ∗
      ((outA + 24#64) ↦₆₄ w24) ∗
      memRegion (outA + 32#64) 928 ⊢
    resultV1RecvAt A (F := F) outA (.error (.err .erroneousDataReceived)) := by
  dsimp only [resultV1RecvAt, spqrErrorByte]
  have h8 : ((outA + 8#64) ↦₆₄ w8) ⊢ ((outA + 8#64) ↦₈ 12#8) ∗ memRegion (outA + 9#64) 7 := by
    rw [pointsTo64_eq_pointsToBytes (outA + 8#64) w8, hw8,
        pointsToBytes_cons (outA + 8#64) 12#8 bs7]
    have h9 : outA + 8#64 + 1#64 = outA + 9#64 := by bv_omega
    rw [h9, ← hlen7]
    exact sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion (outA + 9#64) bs7)
  have h16 : ((outA + 16#64) ↦₆₄ w16) ∗ ((outA + 24#64) ↦₆₄ w24) ∗ memRegion (outA + 32#64) 928 ⊢
      memRegion (outA + 16#64) 944 := by
    rw [ProofLib.memRegion_split' (b := outA + 16#64) (n := 8) (k := 936)
          (b' := outA + 24#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := outA + 24#64) (n := 8) (k := 928)
          (b' := outA + 32#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  have h9 : memRegion (outA + 9#64) 7 ∗ memRegion (outA + 16#64) 944 = memRegion (outA + 9#64) 951 :=
    (ProofLib.memRegion_split' (b := outA + 9#64) (n := 7) (k := 944)
      (b' := outA + 16#64) rfl (by bv_omega) (by decide)).symm
  rw [← h9, ← sepConj_assoc ((outA + 8#64) ↦₈ 12#8)]
  exact sepConj_mono_right (sepConj_mono h8 h16)

theorem vecU8_extract_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ _)]
  apply Entails.pure_left; intro ⟨hle, hlt, hptr⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hlt ?_)
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
  exact Entails.pure_right ⟨hle, hlt, hptr⟩ (Entails.refl _)

@[expose] def fiveVecToWords16 (g : FiveVecWords) (ep : BitVec 64) : Words16 :=
  ⟨g.v1.w0, g.v1.w1, g.v1.w2,
   g.rest.v1.w0, g.rest.v1.w1, g.rest.v1.w2,
   g.rest.rest.v1.w0, g.rest.rest.v1.w1, g.rest.rest.v1.w2,
   g.rest.rest.auth.v1.w0, g.rest.rest.auth.v1.w1, g.rest.rest.auth.v1.w2,
   g.rest.rest.auth.v2.w0, g.rest.rest.auth.v2.w1, g.rest.rest.auth.v2.w2,
   ep⟩

@[simp]
theorem fiveVecToWords16_toList (g : FiveVecWords) (ep : BitVec 64) :
    (fiveVecToWords16 g ep).toList = fiveVecWordsList g ep := rfl

theorem unchunkedCt1SentEkReceivedAt_extract_words16 (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)) :
    unchunkedCt1SentEkReceivedAt A a st ⊢
      ∃∗ c : Words16,
        ⌜c.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a c.toList ∗
        relocatedHeap (fun dst => unchunkedCt1SentEkReceivedAt A dst st) (wordsBytes c.toList) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st4 : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.es⟩, st.ek, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentCt1ReceivedAt A (dst + 24#64) st4 =
        unchunkedCt1SentEkReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.es) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ek ∗ vecU8 A ((dst + 24#64) + 72#64) st.ct1 ∗
        (((dst + 24#64) + 96#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.es ∗
        vecU8 A (dst + 72#64) st.ek ∗ vecU8 A (dst + 96#64) st.ct1 ∗
        ((dst + 120#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64, BitVec.add_assoc dst 24#64 96#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_lt A a r0)
    (unchunkedEkSentCt1ReceivedAt_extract A (a + 24#64) st4)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  rw [sepConj_assoc]
  apply Entails.pure_left; intro hlt
  refine Entails.sepExists_right (fiveVecToWords16 ⟨v1, rest⟩ st.epoch) ?_
  refine Entails.pure_right hlt ?_
  rw [fiveVecToWords16_toList]
  exact wordsExtract_sepConj rfl heq

@[expose] def mkSplit928EkReceivedCt1Sampled (c_enc : Words50) (c_ek : Words16)
    (bs352 : List (BitVec 8)) (tail5 : Words5) : Split928 where
  c0 := {
    w0 := 10#64
    w1 := c_enc.c0.w0
    w2 := c_enc.c0.w1
    w3 := c_enc.c0.w2
    w4 := c_enc.c0.w3
    w5 := c_enc.c0.w4
    w6 := c_enc.c0.w5
    w7 := c_enc.c0.w6
    w8 := c_enc.c0.w7
    w9 := c_enc.c0.w8
    w10 := c_enc.c0.w9
    w11 := c_enc.c0.w10
    w12 := c_enc.c0.w11
    w13 := c_enc.c0.w12
    w14 := c_enc.c0.w13
    w15 := c_enc.c0.w14
  }
  c1 := {
    w0 := c_enc.c0.w15
    w1 := c_enc.c1.w0
    w2 := c_enc.c1.w1
    w3 := c_enc.c1.w2
    w4 := c_enc.c1.w3
    w5 := c_enc.c1.w4
    w6 := c_enc.c1.w5
    w7 := c_enc.c1.w6
    w8 := c_enc.c1.w7
    w9 := c_enc.c1.w8
    w10 := c_enc.c1.w9
    w11 := c_enc.c1.w10
    w12 := c_enc.c1.w11
    w13 := c_enc.c1.w12
    w14 := c_enc.c1.w13
    w15 := c_enc.c1.w14
  }
  c2 := {
    w0 := c_enc.c1.w15
    w1 := c_enc.c2.w0
    w2 := c_enc.c2.w1
    w3 := c_enc.c2.w2
    w4 := c_enc.c2.w3
    w5 := c_enc.c2.w4
    w6 := c_enc.c2.w5
    w7 := c_enc.c2.w6
    w8 := c_enc.c2.w7
    w9 := c_enc.c2.w8
    w10 := c_enc.c2.w9
    w11 := c_enc.c2.w10
    w12 := c_enc.c2.w11
    w13 := c_enc.c2.w12
    w14 := c_enc.c2.w13
    w15 := c_enc.c2.w14
  }
  c3 := {
    w0 := c_enc.c2.w15
    w1 := c_enc.w48
    w2 := c_enc.w49
    w3 := c_ek.w0
    w4 := c_ek.w1
    w5 := c_ek.w2
    w6 := c_ek.w3
    w7 := c_ek.w4
    w8 := c_ek.w5
    w9 := c_ek.w6
    w10 := c_ek.w7
    w11 := c_ek.w8
    w12 := c_ek.w9
    w13 := c_ek.w10
    w14 := c_ek.w11
    w15 := c_ek.w12
  }
  mid := mid376Bytes c_ek.w13 c_ek.w14 c_ek.w15 bs352
  tail := tail5

theorem mkSplit928EkReceivedCt1Sampled_mid_length (c_enc : Words50) (c_ek : Words16)
    {bs352 : List (BitVec 8)} (tail5 : Words5) (h : bs352.length = 352) :
    (mkSplit928EkReceivedCt1Sampled c_enc c_ek bs352 tail5).mid.length = 376 :=
  mid376Bytes_length c_ek.w13 c_ek.w14 c_ek.w15 h

end CryptoVerification.SpqrV1.States.Recv
