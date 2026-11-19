/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Common
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1Received1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmHeaderSent1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmKeysSampled1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSendEk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` — `.keysSampled` Arm, Part 2

**Checked by Lean.** Verifies `keysSampled_arm_eq_other`, `keysSampled_arm_eq_ct1`,
`states_recv_arm_keysSampled`, and `states_recv_keysSampled_ok_ext` for `.keysSampled`
(`0x55b58`, `+1796`).
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
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
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
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  sp_sub_4240_add_4144_hs bv376_toNat_hs

/-! ## 1. `.keysSampled` (`0x55b58`, `+1796`): `msg.epoch = st.uc.epoch` and `∀ c, msg.payload ≠ .ct1 c` -/

/-- Framed call rule for `keysSampledRecvCt1ChunkSpec A F` (`0x61768`), bridging from `SepWP`
    before the call to `SepWPp` (propagating `allocFailedIn s0 sf`) and back to `SepWP` after the call. -/
theorem call_keysSampledRecvCt1Chunk {A : RustAlloc} {F : ShaCompress}
    {prog : Program} {entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (keysSampledRecvCt1ChunkSpec A F))
    (outA stA chunkA : BitVec 64)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (chunk : Chunk)
    (outSt : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApi F))
    (hrecv : st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt)
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
    (hsplit : P = (memRegion outA chunkedHeaderSentSize ∗
      chunkedKeysSampledAt A stA st ∗ chunkAt chunkA chunk ∗
      A.pool ∗ stackAt sp_call keysSampledRecvCt1ChunkStack) ∗ Frame)
    (hpanic : ∀ sf P_f,
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) →
      Q_panic sf P_f)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog (s0.readReg64 Reg.lr) sf
        ((chunkedHeaderSentAt A outA outSt ∗
          memRegion stA 504 ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call keysSampledRecvCt1ChunkStack) ∗ Frame) post) :
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
    dsimp only [keysSampledRecvCt1ChunkSpec]
    rw [hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2, hx3, hrecv⟩, hm⟩
  · dsimp only [keysSampledRecvCt1ChunkSpec] at hmem
    refine allowPanic_frame (fun ⟨haf, htr_sub⟩ => ?_) hmem
    unfold allocFailedIn at haf ⊢
    rw [htrace.1] at haf htr_sub
    exact ⟨haf, htr_sub⟩
  · dsimp only [keysSampledRecvCt1ChunkSpec]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr => ?_
    apply SepWPp.of_sepWP_ret
    have hassoc :
        (chunkedHeaderSentAt A outA outSt ∗
          memRegion stA 504 ∗ chunkAt chunkA chunk ∗
          A.pool ∗ stackAt sp_call keysSampledRecvCt1ChunkStack) ∗ Frame =
        (chunkedHeaderSentAt A outA outSt ∗
          (memRegion stA 504 ∗
            (chunkAt chunkA chunk ∗ (A.pool ∗ stackAt sp_call keysSampledRecvCt1ChunkStack)))) ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

theorem keysSampled_recv_ct1_ok_of_no_panic {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi)
    (hno_panic : (States.recv K (.keysSampled st) msg).isPanic = false) :
    ∀ chunk, msg.epoch = st.uc.epoch → msg.payload = .ct1 chunk →
      ∃ outSt, st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt := by
  intro chunk heq hpay
  cases h : st.recv_ct1_chunk st.uc.epoch chunk with
  | ok outSt => exact ⟨outSt, rfl⟩
  | error p =>
    have hpan := states_recv_keysSampled_eq_ct1_panic K st msg chunk p heq hpay h
    rw [hno_panic] at hpan
    contradiction

theorem keysSampled_recv_ct1_ok_of_preInv {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F))
    (hinv : statesRecvPreInv (.keysSampled st))
    (chunk : spqrPolyApi.Chunk) :
    ∃ outSt, st.recv_ct1_chunk st.uc.epoch chunk = .ok outSt := by
  have hek : st.uc.ek.length = 1152 := hinv
  let pts := Poly.EncodeBytes.distributeMsgChunksTotal 0 st.uc.ek
    (List.replicate NUM_POLYS { value := [] })
  let enc : PolyEncoder := { idx := 0#32, s := .points pts }
  refine ⟨{ uc := { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.dk },
            sending_ek := enc,
            receiving_ct1 := Poly.AddChunk.addChunkTotal (emptyPolyDecoder 480) chunk }, ?_⟩
  unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk CIPHERTEXT1_SIZE Unchunked.SendEk.HeaderSent.send_ek
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [expectDecoderNew_960]
  have henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:92" st.uc.ek = .ok enc := by
    unfold expectEncodeBytes spqrPolyApi
    dsimp only [Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
    rw [Poly.EncodeBytes.encodeBytes_eq_ok]
    unfold Poly.EncodeBytes.encodeBytesResult
    have h1 : (st.uc.ek.length % 2 != 0) = false := by rw [hek]; decide
    have h2 : (st.uc.ek.length > (1 <<< 16) * NUM_POLYS) = false := by
      rw [hek]; decide
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [henc]
  dsimp only [Bind.bind, Except.bind, spqrPolyApi, liftM, monadLift, MonadLift.monadLift,
    liftSpqrPanic]
  rw [Poly.AddChunk.addChunk_eq_ok (emptyPolyDecoder 480) chunk rfl]
  rfl

end CryptoVerification.SpqrV1.States.Recv
