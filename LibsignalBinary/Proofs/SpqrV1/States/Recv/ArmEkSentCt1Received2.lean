/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmEkSentCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ekSentCt1Received` Arm, Part 2

Verifies the `msg.epoch = st.uc.epoch ∧ msg.payload = .ct2 chunk` branch (`<EkSentCt1Received>::
recv_ct2_chunk` at `0x5ec2c` with `.error`, `.stillReceiving`, and `.done` continuations) and
assembles `states_recv_arm_ekSentCt1Received` (`+228 -> s0.x30`).
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

theorem ekSentCt1ReceivedAt_eq_chunked (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    ekSentCt1ReceivedAt A a st = chunkedEkSentCt1ReceivedAt A a st := rfl

@[local arm64_norm, local wp_norm]
theorem none2Cap_add_two_beq_zero :
    (18446744073709551614#64 + 2#64 == 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem none2Cap_add_two_bne_zero :
    (18446744073709551614#64 + 2#64 != 0#64) = false := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_two_beq_zero :
    (18446744073709551615#64 + 2#64 == 0#64) = false := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_two_bne_zero :
    (18446744073709551615#64 + 2#64 != 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_one_beq_zero :
    (18446744073709551615#64 + 1#64 == 0#64) = true := rfl

@[local arm64_norm, local wp_norm]
theorem noneCap_add_one_bne_zero :
    (18446744073709551615#64 + 1#64 != 0#64) = false := rfl

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  rw [bne_iff_ne]
  bv_omega

theorem cap_add_one_beq_zero_false_recv {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem cap_add_one_bne_zero_true_recv {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  rw [bne_iff_ne]
  bv_omega

/-! ## 1. Post-Call `.error (.err e)` Path (`0x56574..0x565a4 -> 0x59fd0..0x59ff0`) -/

/-- The only non-panic error returned by `EkSentCt1Received.recv_ct2_chunk` is `.macVerifyFailed`. -/
theorem recv_ct2_chunk_err_eq_macVerifyFailed {K : MlKem} {F : ShaCompress}
    (self : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (epoch : Epoch) (chunk : Chunk) (e : Error)
    (herr : self.recv_ct2_chunk K epoch chunk = .error (.err e)) :
    e = .macVerifyFailed := by
  rw [recv_ct2_chunk_eq_do] at herr
  by_cases h0 : (epoch != self.uc.epoch) = true
  · simp only [h0, ↓reduceIte] at herr; cases herr
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at herr
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure, StatesResult.ofPanic,
      Except.mapError] at herr
    cases h1 : PolyDecoder.addChunk self.receiving_ct2 chunk with
    | error p => rw [h1] at herr; cases herr
    | ok recCt2 =>
      rw [h1] at herr
      dsimp only at herr
      cases h2 : recCt2.decodedMessage with
      | error p => rw [h2] at herr; cases herr
      | ok decOpt =>
        rw [h2] at herr
        dsimp only at herr
        cases decOpt with
        | none => cases herr
        | some ct2Full =>
          dsimp only at herr
          by_cases h3 : ct2Full.length < 128
          · simp only [h3, ↓reduceIte] at herr; cases herr
          · simp only [h3, ↓reduceIte] at herr
            cases h4 : decaps K self.uc.dk self.uc.ct1 (ct2Full.take 128) with
            | error p => rw [h4] at herr; cases herr
            | ok ssRaw =>
              rw [h4] at herr
              dsimp only at herr
              cases h5 : Authenticator.verifyCtError F
                (Authenticator.update F self.uc.auth self.uc.epoch
                  (spqrHkdfWith F (List.replicate 32 0#8) ssRaw
                    (sckaKeyInfoPrefix ++ CryptoGames.HMAC.toBEBytes 8 self.uc.epoch) 32))
                self.uc.epoch (self.uc.ct1 ++ ct2Full.take 128) (ct2Full.drop 128) with
              | error p => rw [h5] at herr; cases herr
              | ok vRes =>
                rw [h5] at herr
                dsimp only at herr
                cases vRes with
                | error _ => cases herr; rfl
                | ok u =>
                  cases u
                  dsimp only at herr
                  by_cases h6 : (self.uc.epoch == BitVec.allOnes 64) = true
                  · simp only [h6, ↓reduceIte] at herr; cases herr
                  · simp only [h6, Bool.false_eq_true, ↓reduceIte] at herr; cases herr

/-! ## 2. Post-Call `.ok (.stillReceiving outSt)` Path (`0x56574..0x5658c -> 0x58598..0x5883c -> 0x59e88..0x59ff0`) -/

theorem vecU8_extract_with_cap_lt (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ v : VecWords,
        ⌜v.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (vecWordsList v) ∗
        relocatedHeap (fun dst => vecU8 A dst bs) (wordsBytes (vecWordsList v)) := by
  unfold vecU8 vecU8At vecHeader
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  rw [sepConj_left_comm ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length))]
  apply Entails.pure_left; rintro ⟨hle, hcap_lt, hptr_ne⟩
  let v : VecWords := ⟨cap, ptr, BitVec.ofNat 64 bs.length⟩
  refine Entails.sepExists_right v (Entails.pure_right hcap_lt ?_)
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
  refine sepConj_mono_right (Entails.pure_right ⟨hle, hcap_lt, hptr_ne⟩ (Entails.refl _))

theorem unchunkedEkSentCt1ReceivedAt_extract_cap (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)) :
    unchunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ g : FourVecWords,
        ⌜g.v1.w0.toNat < 2 ^ 63⌝ ∗
        wordsAt a (ekSentCt1ReceivedWordsList g st.epoch) ∗
        relocatedHeap (fun dst => unchunkedEkSentCt1ReceivedAt A dst st)
          (wordsBytes (ekSentCt1ReceivedWordsList g st.epoch)) := by
  let r0 := st.auth.rootKey
  let m0 := st.auth.macKey
  let st3 : Unchunked.SendEk.EkSent (spqrAuthApi F) := ⟨st.epoch, ⟨m0, st.dk⟩, st.ct1⟩
  have heq : ∀ dst : BitVec 64,
      vecU8 A dst r0 ∗ unchunkedEkSentAt A (dst + 24#64) st3 =
        unchunkedEkSentCt1ReceivedAt A dst st := by
    intro dst
    change vecU8 A dst r0 ∗ ((vecU8 A (dst + 24#64) m0 ∗ vecU8 A ((dst + 24#64) + 24#64) st.dk) ∗
        vecU8 A ((dst + 24#64) + 48#64) st.ct1 ∗ (((dst + 24#64) + 72#64) ↦₆₄ st.epoch)) =
      (vecU8 A dst r0 ∗ vecU8 A (dst + 24#64) m0) ∗ vecU8 A (dst + 48#64) st.dk ∗
        vecU8 A (dst + 72#64) st.ct1 ∗ ((dst + 96#64) ↦₆₄ st.epoch)
    rw [BitVec.add_assoc dst 24#64 24#64, BitVec.add_assoc dst 24#64 48#64,
        BitVec.add_assoc dst 24#64 72#64]
    ac_rfl
  rw [← heq a]
  refine Entails.trans (sepConj_mono (vecU8_extract_with_cap_lt A a r0)
    (unchunkedEkSentAt_extract A (a + 24#64) st3)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro v1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro rest
  rw [sepConj_assoc (⌜v1.w0.toNat < 2 ^ 63⌝)]
  apply Entails.pure_left; intro hcap
  refine Entails.sepExists_right ⟨v1, rest⟩ (Entails.pure_right hcap ?_)
  exact wordsExtract_sepConj rfl heq

theorem chunkedEkSentCt1ReceivedAt_extract63_cap (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    chunkedEkSentCt1ReceivedAt A a st ⊢
      ∃∗ w : Words63,
        ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w2 = st.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst st) (wordsBytes (words63List w)) := by
  unfold chunkedEkSentCt1ReceivedAt
  refine Entails.trans (sepConj_mono
    (unchunkedEkSentCt1ReceivedAt_extract_cap A a st.uc)
    (relocatable_400_extract_words5x10 (Relocatable.of_polyDecoderAt A st.receiving_ct2) (a + 104#64))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro g
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro p
  rw [sepConj_assoc (⌜g.v1.w0.toNat < 2 ^ 63⌝)]
  apply Entails.pure_left; intro hcap
  let w := mkWords63_13_50 g st.uc.epoch p
  refine Entails.sepExists_right w (Entails.pure_right ⟨hcap, rfl⟩ ?_)
  rw [words63At_eq_wordsAt, ← words63List_mkWords63_13_50]
  exact wordsExtract_sepConj rfl (fun _ => rfl)

theorem stillReceiving_result_976_extract (A : RustAlloc) {F : ShaCompress} (a : BitVec 64)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    ekSentCt1ReceivedRecvChunkResultAt A (F := F) a (.ok (.stillReceiving outSt)) ⊢
      ∃∗ w : Words63,
        ⌜w.b0.w0.toNat < 2 ^ 63 ∧ w.b1.w2 = outSt.uc.epoch⌝ ∗
        words63At a w ∗
        relocatedHeap (fun dst => chunkedEkSentCt1ReceivedAt A dst outSt) (wordsBytes (words63List w)) := by
  dsimp only [ekSentCt1ReceivedRecvChunkResultAt, ekSentCt1ReceivedRecvChunkAt, ekSentCt1ReceivedAt_eq_chunked]
  apply Entails.pure_left; intro _
  exact chunkedEkSentCt1ReceivedAt_extract63_cap A a outSt

theorem sendEkUnusedAt_split_ab0_ac0 (fsp : BitVec 64) :
    sendEkUnusedAt fsp ⊢
      ∃∗ qab0 : BitVec 128, ∃∗ qac0 : BitVec 128,
        ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
        ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
        memRegion fsp 8 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 2768#64) 1376 := by
  refine Entails.trans (sendEkUnusedAt_split_ac0 fsp) ?_
  apply Entails.sepExists_elim; intro qac0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (memRegion_16_entails_128_recv (fsp + 2736#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, ← sepConj_assoc]
  apply Entails.sepExists_elim; intro qab0
  refine Entails.sepExists_right qab0 (Entails.sepExists_right qac0 ?_)
  exact Entails.of_eq (by ac_rfl)

theorem sendEkUnusedAt_rejoin_ab0_ac0 (fsp : BitVec 64) (qab0 qac0 : BitVec 128) :
    ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
    ((fsp + 2752#64) ↦₁₂₈ qac0) ∗
    memRegion fsp 8 ∗
    memRegion (fsp + 568#64) 8 ∗
    memRegion (fsp + 952#64) 8 ∗
    memRegion (fsp + 2768#64) 1376 ⊢
      sendEkUnusedAt fsp := by
  refine Entails.trans ?_ (sendEkUnusedAt_rejoin_ac0 fsp qac0)
  refine Entails.trans (Entails.of_eq (show _ =
    ((fsp + 2736#64) ↦₁₂₈ qab0) ∗
    (((fsp + 2752#64) ↦₁₂₈ qac0) ∗ memRegion fsp 8 ∗ memRegion (fsp + 568#64) 8 ∗
      memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 2768#64) 1376) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (pointsTo128_entails_memRegion_16 (fsp + 2736#64) qab0)) ?_
  exact Entails.of_eq (by ac_rfl)

theorem Relocatable.of_chunkedEkSentCt1ReceivedAt (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedEkSentCt1ReceivedAt A a st) := by
  intro a
  refine Entails.trans (chunkedEkSentCt1ReceivedAt_extract63 A a st) ?_
  apply Entails.sepExists_elim; intro w
  apply Entails.pure_left; intro _
  rw [words63At_eq_wordsAt, wordsAt_eq_pointsToBytes]
  refine Entails.sepExists_right (wordsBytes (words63List w)) ?_
  exact Entails.pure_right (by rw [length_wordsBytes, length_words63List]) (Entails.refl _)

/-- Stack-parameterized framed call rule for `recvCt2ChunkSpecWithStack stk K F A b` (`0x5ec2c`). -/
theorem call_ekSentCt1ReceivedRecvCt2Chunk_stk {stk : Nat} {A : RustAlloc} {F : ShaCompress}
    {K : MlKem} {b : BitVec 64} {prog : Program} {entry ret_pc : BitVec 64} {P_inv : State → Prop}
    (hb : b &&& 0xfff#64 = 0#64) (hcall : subroutine_ok prog entry
      { recvCt2ChunkSpecWithStack stk K F A b with
        pre := fun x s => ⌜P_inv s⌝ ∗ (recvCt2ChunkSpecWithStack stk K F A b).pre x s })
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) (chunk : Chunk)
    (hsort : PolyDecoderStrictSorted st.receiving_ct2) (hroot : st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp} {post Q_panic : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0) (hx0 : s.readReg64 Reg.x0 = outA) (hx1 : s.readReg64 Reg.x1 = stA)
    (hx2 : s.readReg64 Reg.x2 = st.uc.epoch) (hx3 : s.readReg64 Reg.x3 = chunkA)
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗ ekSentCt1ReceivedAt A stA st ∗
      chunkAt chunkA chunk ∗ tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame)
    (hpanic : ∀ sf P_f, ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (⌜((st.recv_ct2_chunk K st.uc.epoch chunk).isPanic = true ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) → Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 → SepWP prog (s0.readReg64 Reg.lr) sf
        ((ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
          memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame) post) :
    SepWP prog entry s P (fun sm Pm => P_inv sm → SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun; intro hinv_s
  refine SepWPp.call hcall (x := ⟨outA, stA, st, st.uc.epoch, chunkA, chunk⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_ (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_) (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm; rw [hsplit] at hm; dsimp only [recvCt2ChunkSpecWithStack]; rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢; exact ⟨hinv_s, ⟨hb, hx0, hx1, hx2, hx3, hsort, hroot⟩, hm⟩
  · dsimp only [recvCt2ChunkSpecWithStack] at hmem; refine allowPanic_frame (fun ⟨hdisj, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at hdisj ⊢; rw [htrace.1] at hdisj htr_sub; exact ⟨hdisj, htr_sub⟩
  · dsimp only [recvCt2ChunkSpecWithStack]; rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => SepWPp.of_sepWP_ret ?_
    have hassoc : (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
        memRegion stA chunkedEkSentCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
        tokenInitAt b ∗ reduceTableAt b ∗ A.pool ∗ stackAt sp_call stk) ∗ Frame =
      (ekSentCt1ReceivedRecvChunkResultAt A (F := F) outA (st.recv_ct2_chunk K st.uc.epoch chunk) ∗
        (memRegion stA chunkedEkSentCt1ReceivedSize ∗ (chunkAt chunkA chunk ∗
          (tokenInitAt b ∗ (reduceTableAt b ∗ (A.pool ∗ stackAt sp_call stk)))))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

theorem subroutine_ok_pure_true {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry { spec with pre := fun x s => ⌜True⌝ ∗ spec.pre x s } := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp fun _ hout => hout

end CryptoVerification.SpqrV1.States.Recv
