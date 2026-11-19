/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet First-Half Composition (`+1532..+1856`)

Composes `<Message>::deserialize` (`+1532..+1636`), `<States>::from_pb` (`+1636..+1736`), and
`<States>::recv` (`+1736..+1856`) in `SepWPpI` for `spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem traceVRegs_trans {s0 s1 s2 : State}
    (h1 : TraceVRegs s2 s1) (h0 : TraceVRegs s1 s0) : TraceVRegs s2 s0 :=
  ⟨h1.1.trans h0.1, h1.2.trans h0.2⟩

/-! ## 1. `<Message>::deserialize` Call, Error Path (`+2060`), and Relocation (`+1568..+1636`) -/

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

@[local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
theorem hsp_add_544_eq (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
theorem hsp_add_560_eq (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

theorem memRegion_928_split_header32_body896 (a : BitVec 64) :
    memRegion a 928 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        (a ↦₆₄ d0) ∗ ((a + 8#64) ↦₆₄ d1) ∗ ((a + 16#64) ↦₆₄ d2) ∗ ((a + 24#64) ↦₆₄ d3) ∗
        memRegion (a + 32#64) 896 := by
  rw [show (928 : Nat) = 32 + 896 by decide,
      memRegion_split a 32 896 (by decide),
      memRegion_32_words4 a]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun d3 => Entails.sepExists_elim fun d2 =>
    Entails.sepExists_elim fun d1 => Entails.sepExists_elim fun d0 => ?_
  refine Entails.sepExists_right d0 (Entails.sepExists_right d1
    (Entails.sepExists_right d2 (Entails.sepExists_right d3 ?_)))
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_4064_join_1968_928 (sp0 : BitVec 64) :
    memRegion (sp0 - 4064#64) 1968 ∗ memRegion (sp0 - 2096#64) 928 ⊢
      memRegion (sp0 - 4064#64) 2896 := by
  rw [show (2896 : Nat) = 1968 + 928 by decide,
      memRegion_split (sp0 - 4064#64) 1968 928 (by decide),
      show (sp0 - 4064#64) + 1968#64 = sp0 - 2096#64 by bv_omega]
  exact Entails.refl _

def IsFromPbRes {α : Type} : StatesResult α → Prop
  | .ok _ | .error (.err .stateDecode) | .error (.err .msgDecode) => True
  | _ => False

theorem isFromPbRes_bind {α β : Type} {r : StatesResult α} {f : α → StatesResult β}
    (hr : IsFromPbRes r) (hf : ∀ x, IsFromPbRes (f x)) : IsFromPbRes (r >>= f) := by
  cases r with | ok x => exact hf x | error e => rcases e with e | p <;> [cases e <;> exact hr; exact hr]

theorem isFromPbRes_map {α β : Type} (g : α → β) {r : StatesResult α} (hr : IsFromPbRes r) :
    IsFromPbRes (g <$> r) := by
  cases r with | ok _ => trivial | error e => rcases e with e | p <;> [cases e <;> exact hr; exact hr]

theorem isFromPbRes_enc (pb? : Option PolynomialEncoder) :
    IsFromPbRes (encoderFromPbStateDecode spqrPolyApi pb?) := by
  cases pb? <;> simp only [States.FromPb.encoderFromPbStateDecode_none, States.FromPb.encoderFromPbStateDecode_some] <;> repeat (first | split | trivial)

theorem isFromPbRes_dec (pb? : Option PolynomialDecoder) :
    IsFromPbRes (decoderFromPbStateDecode spqrPolyApi pb?) := by
  cases pb? <;> simp only [States.FromPb.decoderFromPbStateDecode_none, States.FromPb.decoderFromPbStateDecode_some] <;> repeat (first | split | trivial)

theorem spqrErrorByte_eq_zero_iff {Au : AuthApi} {pb : V1State} {err : Error}
    (hst0 : States.from_pb spqrPolyApi Au pb = .error (.err err)) :
    States.FromPb.spqrErrorByte err = 0#8 ↔ (err == .stateDecode) = true := by
  have hr : IsFromPbRes (States.from_pb spqrPolyApi Au pb) := by
    rcases h : pb.innerState with _ | s
    · simp [States.from_pb, h, IsFromPbRes]
    · cases s <;>
        simp only [States.from_pb, h, Chunked.SendEk.KeysUnsampled.from_pb,
          Chunked.SendEk.KeysSampled.from_pb, Chunked.SendEk.HeaderSent.from_pb,
          Chunked.SendEk.Ct1Received.from_pb, Chunked.SendEk.EkSentCt1Received.from_pb,
          Chunked.SendCt.NoHeaderReceived.from_pb, Chunked.SendCt.HeaderReceived.from_pb,
          Chunked.SendCt.Ct1Sampled.from_pb, Chunked.SendCt.EkReceivedCt1Sampled.from_pb,
          Chunked.SendCt.Ct1Acknowledged.from_pb, Chunked.SendCt.Ct2Sampled.from_pb,
          Unchunked.SendEk.KeysUnsampled.from_pb, Unchunked.SendEk.HeaderSent.from_pb,
          Unchunked.SendEk.EkSent.from_pb, Unchunked.SendEk.EkSentCt1Received.from_pb,
          Unchunked.SendCt.NoHeaderReceived.from_pb, Unchunked.SendCt.HeaderReceived.from_pb,
          Unchunked.SendCt.Ct1Sent.from_pb, Unchunked.SendCt.Ct1SentEkReceived.from_pb,
          Unchunked.SendCt.Ct2Sent.from_pb] <;>
        repeat (first | apply isFromPbRes_map | apply isFromPbRes_bind | intro _ | exact isFromPbRes_enc _ | exact isFromPbRes_dec _ | split | trivial)
  rw [hst0] at hr
  cases err <;> first | decide | exact False.elim hr

theorem resultChunkedStatesAt_panic_false (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (p : StatesPanic) :
    resultChunkedStatesAt A (F := F) a (.error (.panic p)) = ⌜False⌝ := rfl

theorem msgPreamble_epoch_beq_zero_false {msg : Bytes} {pre : MsgPreamble}
    (hpre : msgPreamble msg = .ok pre) (hmv : pre.version = 1#8) :
    (pre.epoch == 0#64) = false := by
  unfold msgPreamble msg_preamble at hpre
  cases msg with
  | nil =>
    have hinj := Except.ok.inj hpre
    subst hinj
    contradiction
  | cons v rest =>
    dsimp only [Bind.bind, Except.bind] at hpre
    rcases hd1 : decode_varint rest with _ | ⟨ep, r1⟩ <;> rw [hd1] at hpre
    · contradiction
    · dsimp only at hpre
      split at hpre
      · contradiction
      · rename_i hep_ne
        rcases hd2 : decode_varint r1 with _ | ⟨idx, r2⟩ <;> rw [hd2] at hpre
        · contradiction
        · dsimp only at hpre
          split at hpre
          · have hinj := Except.ok.inj hpre
            subst hinj
            exact beq_false_of_ne hep_ne
          · contradiction

theorem recvCt2_spqrErrorByte_eq_zero_iff (err : Error) :
    States.RecvCt2Chunk.spqrErrorByte err = 0#8 ↔ (err == .stateDecode) = true := by
  cases err <;> simp [States.RecvCt2Chunk.spqrErrorByte, BEq.beq]

theorem resultV1RecvAt_panic_false (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (p : StatesPanic) :
    resultV1RecvAt A (F := F) a (.error (.panic p)) = ⌜False⌝ := rfl

theorem onPanic_of_statesRecv {F : ShaCompress} {K : MlKem}
    {st msg : VecArg} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)}
    {outA selfA msgA : BitVec 64} {sc sf : State}
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬(1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0) :
    statesRecvOnPanic K ⟨outA, selfA, msgA, st0, sckaMsg⟩ sc sf ⊢
      ⌜(allocFailedIn sc sf ∨ (spqrV1Recv F K).recvPanics st.bytes msg.bytes) ∧ sc.trace <+: sf.trace⌝ ∗ anyHeap := by
  unfold statesRecvOnPanic
  apply Entails.pure_left
  rintro ⟨hp | halloc, hpref⟩
  · refine Entails.pure_right ⟨Or.inr ?_, hpref⟩ (Entails.refl _)
    cases hr : st0.recv K sckaMsg with
    | ok _ => rw [hr] at hp; contradiction
    | error se =>
      cases se with
      | err _ => rw [hr] at hp; contradiction
      | panic p =>
        exact spqrV1Recv_v1_statesRecv_panic F K hpre hdec hinner hmv hmin hmsg hfrom hr
  · exact Entails.pure_right ⟨Or.inl halloc, hpref⟩ (Entails.refl _)

end CryptoVerification.SpqrV1.Top.Recv
