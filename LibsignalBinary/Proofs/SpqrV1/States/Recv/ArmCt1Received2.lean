/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchExt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonExt
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.ct1Received` Arm, Part 2

**Checked by Lean.** Verifies `ct1Received_arm_eq_other`, `ct1Received_arm_eq_ct2`, and the
complete `.ct1Received` arm (`states_recv_arm_ct1Received`, `0x55908`, `+1204`).
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

/-- Discriminant byte at `msgA + 8#64` of `MessagePayload spqrPolyApi`. -/
@[expose] def messagePayloadTag (p : MessagePayload spqrPolyApi) : BitVec 8 :=
  match p with
  | .none => 0#8
  | .hdr _ => 1#8
  | .ek _ => 2#8
  | .ekCt1Ack _ => 3#8
  | .ct1Ack _ => 4#8
  | .ct1 _ => 5#8
  | .ct2 _ => 6#8

/-- Tail (`39` bytes at `msgA + 9#64`) of `messagePayloadAt spqrPolyApi msgA p`. -/
@[expose] def messagePayloadTailAt (a : BitVec 64) (p : MessagePayload spqrPolyApi) : SepProp :=
  match p with
  | .none => memRegion (a + 0x09#64) 39
  | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c =>
      memRegion (a + 0x09#64) 1 ∗ chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4
  | .ct1Ack b =>
      ((a + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗ memRegion (a + 0x0a#64) 38

theorem messagePayloadAt_eq_tag_tail (a : BitVec 64) (p : MessagePayload spqrPolyApi) :
    messagePayloadAt spqrPolyApi a p =
      ((a + 8#64) ↦₈ messagePayloadTag p) ∗ messagePayloadTailAt a p := by
  cases p <;> rfl

theorem messagePayloadTag_eq_6_of_not_ct2 {p : MessagePayload spqrPolyApi} (h : ∀ c, p ≠ .ct2 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) == 6#32) = false := by
  cases p with
  | ct2 c => exact absurd rfl (h c)
  | _ => rfl

theorem messagePayloadTag_bne_6_of_not_ct2 {p : MessagePayload spqrPolyApi} (h : ∀ c, p ≠ .ct2 c) :
    (BitVec.zeroExtend 32 (messagePayloadTag p) != 6#32) = true := by
  cases p with
  | ct2 c => exact absurd rfl (h c)
  | _ => rfl

theorem memRegion_880_entails_words63_376 (a a504 : BitVec 64) (ha : a + 504#64 = a504) :
    memRegion a 880 ⊢ ∃∗ w : Words63, words63At a w ∗ memRegion a504 376 := by
  rw [memRegion_880_split_504_376 a a504 ha]
  refine Entails.trans (sepConj_mono_left (memRegion_504_entails_words63At a)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro w
  exact Entails.sepExists_right w (Entails.refl _)

theorem messagePayloadAt_ct2 (a : BitVec 64) (c : Chunk) :
    messagePayloadAt spqrPolyApi a (.ct2 c) =
      ((a + 8#64) ↦₈ 6#8) ∗ memRegion (a + 9#64) 1 ∗
        chunkAt (a + 10#64) c ∗ memRegion (a + 44#64) 4 := rfl

/-- Framed call rule for `ct1ReceivedRecvCt2ChunkSpec A F` (`0x5e2f4`), bridging from `SepWP`
    before the call to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to `SepWP` after the call. -/
theorem call_ct1ReceivedRecvCt2Chunk {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (ct1ReceivedRecvCt2ChunkSpec A F))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (hrecv : st.recv_ct2_chunk st.uc.epoch chunk = .ok outSt)
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
    (hsplit : P = (memRegion outA chunkedEkSentCt1ReceivedSize ∗
      chunkedCt1ReceivedAt A stA st ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkedEkSentCt1ReceivedAt A outA outSt ∗
          memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame) post) :
    SepWP prog entry s P
      (fun sm Pm =>
        SepWPp prog (s0.readReg64 Reg.lr) sm Pm post Q_panic) := by
  apply SepWP.done hpc hrun
  refine SepWPp.call hcall (x := ⟨outA, stA, chunkA, st, chunk, outSt⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ _ h => allowPanic_not_exited h)
    (fun sf _ => hpanic sf _ fun hmem => ?_)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R' hm
    rw [hsplit] at hm
    dsimp only [ct1ReceivedRecvCt2ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [ct1ReceivedRecvCt2ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [ct1ReceivedRecvCt2ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (chunkedEkSentCt1ReceivedAt A outA outSt ∗
          memRegion stA chunkedCt1ReceivedSize ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack) ∗ Frame =
        (chunkedEkSentCt1ReceivedAt A outA outSt ∗
          (memRegion stA chunkedCt1ReceivedSize ∗
            (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call ct1ReceivedRecvCt2ChunkStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

end CryptoVerification.SpqrV1.States.Recv
