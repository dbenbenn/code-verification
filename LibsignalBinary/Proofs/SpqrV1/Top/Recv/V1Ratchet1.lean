/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet Error Tail & `<Message>::deserialize` Continuation

**Checked by Lean.** Shared error-cleanup tail (`+2500..+2536 -> +1040`) and post-`<Message>::deserialize`
error (`+2060..+2104`) and relocation (`+1568..+1636`) steps on the V1 ratchet path of
`spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Stack Frame Splits and Shared Error Tail (`+2500 .. +2536 -> +1040`, `w26 = 0`) -/

theorem vnHeader_sub4640_entails_memRegion_48 (sp0 w0 w1 : BitVec 64) :
    ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗ memRegion (sp0 - 4624#64) 32 ⊢
      memRegion (sp0 - 4640#64) 48 := by
  have h8 : (sp0 - 4640#64) + 8#64 = sp0 - 4632#64 := bv_sub_add_lit sp0 4640 8
  have h16 : (sp0 - 4640#64) + 16#64 = sp0 - 4624#64 := bv_sub_add_lit sp0 4640 16
  rw [← h8, ← h16]
  exact vnHeader_entails_memRegion_48 (sp0 - 4640#64) w0 w1

theorem ownFrame_join_err_2524 (sp0 : BitVec 64) :
    memRegion (sp0 - 4992#64) 352 ∗
      memRegion (sp0 - 4640#64) 48 ∗
      memRegion (sp0 - 4592#64) 80 ∗
      memRegion (sp0 - 4512#64) 4416 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  rw [← ProofLib.memRegion_split' (b := sp0 - 4592#64) (n := 80) (k := 4416)
        (b' := sp0 - 4512#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp0 - 4640#64) (n := 48) (k := 4496)
        (b' := sp0 - 4592#64) rfl (by bv_omega) (by decide)]
  exact ownFrame_join_352_4544 sp0

theorem memRegion_join_4512_224_4192 (sp0 : BitVec 64) :
    memRegion (sp0 - 4512#64) 224 ∗ memRegion (sp0 - 4288#64) 4192 ⊢
      memRegion (sp0 - 4512#64) 4416 := by
  rw [← ProofLib.memRegion_split' (b := sp0 - 4512#64) (n := 224) (k := 4192)
        (b' := sp0 - 4288#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

theorem memRegion_split_4288_for_1532 (sp0 : BitVec 64) :
    memRegion (sp0 - 4288#64) 4192 ⊢
      memRegion (sp0 - 4288#64) 1232 ∗
      memRegion (sp0 - 3056#64) 48 ∗
      memRegion (sp0 - 3008#64) 2912 := by
  rw [show (4192 : Nat) = 1232 + (48 + 2912) by decide,
      memRegion_split (sp0 - 4288#64) 1232 (48 + 2912) (by decide),
      show (sp0 - 4288#64) + 1232#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 48 2912 (by decide),
      show (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 by bv_omega]
  exact Entails.refl _

theorem memRegion_join_4288_for_1532 (sp0 : BitVec 64) :
    memRegion (sp0 - 4288#64) 1232 ∗
      memRegion (sp0 - 3056#64) 48 ∗
      memRegion (sp0 - 3008#64) 2912 ⊢
    memRegion (sp0 - 4288#64) 4192 := by
  rw [show (4192 : Nat) = 1232 + (48 + 2912) by decide,
      memRegion_split (sp0 - 4288#64) 1232 (48 + 2912) (by decide),
      show (sp0 - 4288#64) + 1232#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 48 2912 (by decide),
      show (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 by bv_omega]
  exact Entails.refl _

theorem vnTail_sub4640_some_entails_dealloc (A : RustAlloc) (sp0 w0 w1 : BitVec 64)
    (vn : VersionNegotiationPB) :
    ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (sp0 - 4624#64) (some vn) ⊢
    ⌜w0.toNat < 2 ^ 63⌝ ∗
      ((sp0 - 4640#64) ↦₆₄ w0) ∗ ((sp0 - 4632#64) ↦₆₄ w1) ∗ memRegion (sp0 - 4624#64) 32 ∗
      vecCapPtrDealloc A w0 w1 := by
  have h8 : (sp0 - 4640#64) + 8#64 = sp0 - 4632#64 := bv_sub_add_lit sp0 4640 8
  have h16 : (sp0 - 4640#64) + 16#64 = sp0 - 4624#64 := bv_sub_add_lit sp0 4640 16
  rw [← h8, ← h16]
  exact vnTail_some_entails_dealloc A (sp0 - 4640#64) w0 w1 vn

theorem noneCap_slt_one_true : (noneCap).slt 1#64 = true := rfl

theorem zero_slt_one_true : (0#64 : BitVec 64).slt 1#64 = true := rfl

theorem spqrV1Recv_v1_ratchet_of_err {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hbody : (do
      let sckaMsg ← (spqrDeps F K).msgDeserialize pre.epoch pre.remaining
      let st0 ← (spqrDeps F K).statesFromPb pb
      let (key, st1) ← (spqrDeps F K).statesRecv st0 sckaMsg
      if pre.epoch == 0#64 then
        .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := pre.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation)
        let chain1 ←
          match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
          | none => pure chain0
        let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
        let newStateBytes := (spqrDeps F K).encodeState {
          inner := some ((spqrDeps F K).statesIntoPb st1)
          versionNegotiation := none
          chain := some chain2.intoPb
        }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        (.ok ({ state := newStateBytes, key := outKey } : Recv) : SpqrApiResult Recv)) = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error e.isStateDecode ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_v1_ratchet_eq (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok
    (pqRatchetStateToPb_inner_some hinner) hmv hmin
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hvn : (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl
  rw [hch, hvn] at heq
  exact spqrV1Recv_recv_noPanic_of_err (heq.trans hbody)

theorem spqrV1Recv_v1_ratchet_of_panic {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {p : SpqrApiPanic}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hbody : (do
      let sckaMsg ← (spqrDeps F K).msgDeserialize pre.epoch pre.remaining
      let st0 ← (spqrDeps F K).statesFromPb pb
      let (key, st1) ← (spqrDeps F K).statesRecv st0 sckaMsg
      if pre.epoch == 0#64 then
        .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := pre.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation)
        let chain1 ←
          match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
          | none => pure chain0
        let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
        let newStateBytes := (spqrDeps F K).encodeState {
          inner := some ((spqrDeps F K).statesIntoPb st1)
          versionNegotiation := none
          chain := some chain2.intoPb
        }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        (.ok ({ state := newStateBytes, key := outKey } : Recv) : SpqrApiResult Recv)) = .error (.panic p)) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_v1_ratchet_eq (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok
    (pqRatchetStateToPb_inner_some hinner) hmv hmin
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hvn : (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl
  rw [hch, hvn] at heq
  exact spqrV1Recv_recvPanics_of_panic (heq.trans hbody)

theorem spqrDeps_msgDeserialize_of_err (F : ShaCompress) (K : MlKem) {ep : Epoch} {rem : Bytes}
    {e : Error} (h : Message.deserialize spqrPolyApi ep rem = .error e) :
    (spqrDeps F K).msgDeserialize ep rem = .error (.err e) := by dsimp [spqrDeps]; rw [h]

theorem spqrDeps_msgDeserialize_of_ok (F : ShaCompress) (K : MlKem) {ep : Epoch} {rem : Bytes}
    {m : Message spqrPolyApi} (h : Message.deserialize spqrPolyApi ep rem = .ok m) :
    (spqrDeps F K).msgDeserialize ep rem = .ok m := by dsimp [spqrDeps]; rw [h]

theorem spqrDeps_statesRecv_of_err (F : ShaCompress) (K : MlKem)
    {st0 : States spqrPolyApi (spqrAuthApi F)} {m : Message spqrPolyApi} {e : Error}
    (h : States.recv K st0 m = .error (.err e)) :
    (spqrDeps F K).statesRecv st0 m = .error (.err e) := by dsimp [spqrDeps]; rw [h]

theorem spqrDeps_statesRecv_of_panic (F : ShaCompress) (K : MlKem)
    {st0 : States spqrPolyApi (spqrAuthApi F)} {m : Message spqrPolyApi} {p : StatesPanic}
    (h : States.recv K st0 m = .error (.panic p)) :
    (spqrDeps F K).statesRecv st0 m = .error (.panic .v1) := by dsimp [spqrDeps]; rw [h]

theorem spqrDeps_statesRecv_of_ok (F : ShaCompress) (K : MlKem)
    {st0 : States spqrPolyApi (spqrAuthApi F)} {m : Message spqrPolyApi} {rOut : _}
    (h : States.recv K st0 m = .ok rOut) :
    (spqrDeps F K).statesRecv st0 m = .ok (rOut.key, rOut.state) := by dsimp [spqrDeps]; rw [h]

theorem spqrV1Recv_v1_msgDeserialize_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .error e) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have his : e.isStateDecode = (e == .stateDecode) := by cases e <;> rfl
  rw [← his]
  refine spqrV1Recv_v1_ratchet_of_err hpre hdec hinner hmv hmin ?_
  rw [spqrDeps_msgDeserialize_of_err F K hmsg]; rfl

theorem spqrV1Recv_v1_statesFromPb_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have his : e.isStateDecode = (e == .stateDecode) := by cases e <;> rfl
  rw [← his]
  refine spqrV1Recv_v1_ratchet_of_err hpre hdec hinner hmv hmin ?_
  rw [spqrDeps_msgDeserialize_of_ok F K hmsg]
  dsimp only [Bind.bind, Except.bind]
  rw [Send.spqrDeps_statesFromPb_of_err F K hst0]

theorem spqrV1Recv_v1_statesFromPb_panic (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {p : StatesPanic}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .error (.panic p)) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  refine spqrV1Recv_v1_ratchet_of_panic hpre hdec hinner hmv hmin (p := .v1) ?_
  rw [spqrDeps_msgDeserialize_of_ok F K hmsg]
  dsimp only [Bind.bind, Except.bind]
  rw [Send.spqrDeps_statesFromPb_of_panic F K hst0]

theorem spqrV1Recv_v1_statesRecv_err (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)} {e : Error}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error (e == .stateDecode) ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  have his : e.isStateDecode = (e == .stateDecode) := by cases e <;> rfl
  rw [← his]
  refine spqrV1Recv_v1_ratchet_of_err hpre hdec hinner hmv hmin ?_
  rw [spqrDeps_msgDeserialize_of_ok F K hmsg]
  dsimp only [Bind.bind, Except.bind]
  rw [Send.spqrDeps_statesFromPb_of_ok F K hst0]
  dsimp only [Bind.bind, Except.bind]
  rw [spqrDeps_statesRecv_of_err F K hrecv]

theorem spqrV1Recv_v1_statesRecv_panic (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)} {p : StatesPanic}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .error (.panic p)) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  refine spqrV1Recv_v1_ratchet_of_panic hpre hdec hinner hmv hmin (p := .v1) ?_
  rw [spqrDeps_msgDeserialize_of_ok F K hmsg]
  dsimp only [Bind.bind, Except.bind]
  rw [Send.spqrDeps_statesFromPb_of_ok F K hst0]
  dsimp only [Bind.bind, Except.bind]
  rw [spqrDeps_statesRecv_of_panic F K hrecv]

theorem spqrV1Recv_v1_epoch_zero_panic (F : ShaCompress) (K : MlKem)
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 : States spqrPolyApi (spqrAuthApi F)} {res : _}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok res)
    (hep0 : (pre.epoch == 0#64) = true) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  refine spqrV1Recv_v1_ratchet_of_panic hpre hdec hinner hmv hmin (p := .recvEpochUnderflow) ?_
  rw [spqrDeps_msgDeserialize_of_ok F K hmsg]
  dsimp only [Bind.bind, Except.bind]
  rw [Send.spqrDeps_statesFromPb_of_ok F K hst0]
  dsimp only [Bind.bind, Except.bind]
  rw [spqrDeps_statesRecv_of_ok F K hrecv]
  dsimp only [Bind.bind, Except.bind]
  rw [hep0]; rfl

/-! ## 2b. `<Message>::deserialize` (`+1532 .. +1636` & `+2060 .. +2104`) -/

theorem msg_expose_rem_bound (A : RustAlloc) (msg : VecArg) (ptr_rem : BitVec 64)
    (rem : List (BitVec 8)) (hvalid : MsgRemValid msg ptr_rem rem) :
    msg.at A ⊢ ⌜rem.length < 2 ^ 63⌝ ∗ (ptr_rem ↦ₛ rem) ∗ msgRemFrame A msg ptr_rem rem := by
  have hle : rem.length ≤ msg.bytes.length := by
    rcases hvalid with ⟨rfl, _⟩ | ⟨p, hsplit, _⟩
    · simp
    · rw [hsplit, List.length_append]; omega
  have hbound : msgRemFrame A msg ptr_rem rem ⊢
      ⌜rem.length < 2 ^ 63⌝ ∗ msgRemFrame A msg ptr_rem rem := by
    unfold msgRemFrame
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.pure_left fun hp => ?_
    refine Entails.pure_left fun hcase => ?_
    refine Entails.pure_right (by omega) ?_
    refine Entails.sepExists_right p ?_
    exact Entails.pure_right hp (Entails.pure_right hcase (Entails.refl _))
  refine Entails.trans (msg_expose_rem A msg ptr_rem rem hvalid) ?_
  refine Entails.trans (sepConj_mono_right hbound) ?_
  rw [sepConj_pure_left_comm]
  exact Entails.refl _

theorem messageErrorAt_sub3056_expose (sp0 : BitVec 64) (err : Error) :
    messageErrorAt (sp0 - 3056#64) err ⊢
      ∃∗ q0 : BitVec 128, ∃∗ w2 : BitVec 64,
        ⌜BitVec.truncate 8 q0 = spqrErrorTag err⌝ ∗
        memRegion (sp0 - 3056#64) 8 ∗
        ((sp0 - 3048#64) ↦₈ 0xff#8) ∗
        memRegion (sp0 - 3047#64) 7 ∗
        ((sp0 - 3040#64) ↦₁₂₈ q0) ∗
        ((sp0 - 3024#64) ↦₆₄ w2) ∗
        memRegion (sp0 - 3016#64) 8 := by
  unfold messageErrorAt
  have h8 : (sp0 - 3056#64) + 0x08#64 = sp0 - 3048#64 := by bv_omega
  have h9 : (sp0 - 3056#64) + 0x09#64 = sp0 - 3047#64 := by bv_omega
  have h10 : (sp0 - 3056#64) + 0x10#64 = sp0 - 3040#64 := by bv_omega
  have h20 : (sp0 - 3056#64) + 0x20#64 = sp0 - 3024#64 := by bv_omega
  have h28 : (sp0 - 3056#64) + 0x28#64 = sp0 - 3016#64 := by bv_omega
  rw [h8, h9, h10, h20, h28]
  exact Entails.refl _

theorem pointsTo128_entails_memRegion (a : BitVec 64) (v : BitVec 128) :
    (a ↦₁₂₈ v) ⊢ memRegion a 16 := by
  rw [ProofLib.memRegion_sixteen]; exact Entails.sepExists_intro v

theorem messageErrorAt_sub3056_to_memRegion_48 (sp0 : BitVec 64) (q0 : BitVec 128) (w2 : BitVec 64) :
    memRegion (sp0 - 3056#64) 8 ∗
      ((sp0 - 3048#64) ↦₈ 0xff#8) ∗
      memRegion (sp0 - 3047#64) 7 ∗
      ((sp0 - 3040#64) ↦₁₂₈ q0) ∗
      ((sp0 - 3024#64) ↦₆₄ w2) ∗
      memRegion (sp0 - 3016#64) 8 ⊢
    memRegion (sp0 - 3056#64) 48 := by
  rw [show (48 : Nat) = 8 + (1 + (7 + (16 + (8 + 8)))) by decide,
      memRegion_split (sp0 - 3056#64) 8 40 (by decide),
      show (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 by bv_omega,
      memRegion_split (sp0 - 3048#64) 1 39 (by decide),
      show (sp0 - 3048#64) + 1#64 = sp0 - 3047#64 by bv_omega,
      memRegion_split (sp0 - 3047#64) 7 32 (by decide),
      show (sp0 - 3047#64) + 7#64 = sp0 - 3040#64 by bv_omega,
      memRegion_split (sp0 - 3040#64) 16 16 (by decide),
      show (sp0 - 3040#64) + 16#64 = sp0 - 3024#64 by bv_omega,
      memRegion_split (sp0 - 3024#64) 8 8 (by decide),
      show (sp0 - 3024#64) + 8#64 = sp0 - 3016#64 by bv_omega]
  exact sepConj_mono_right (sepConj_mono (pointsTo8_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo128_entails_memRegion _ _)
      (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))))

theorem memRegion_1232_split_err_2060 (sp0 : BitVec 64) :
    memRegion (sp0 - 4288#64) 1232 ⊢
      ∃∗ s0_128 : BitVec 128, ∃∗ s1_64 : BitVec 64,
        memRegion (sp0 - 4288#64) 231 ∗
        ((sp0 - 4057#64) ↦₁₂₈ s0_128) ∗
        ((sp0 - 4041#64) ↦₆₄ s1_64) ∗
        memRegion (sp0 - 4033#64) 977 := by
  rw [show (1232 : Nat) = 231 + (16 + (8 + 977)) by decide,
      memRegion_split (sp0 - 4288#64) 231 (16 + (8 + 977)) (by decide),
      show (sp0 - 4288#64) + 231#64 = sp0 - 4057#64 by bv_omega,
      memRegion_split (sp0 - 4057#64) 16 (8 + 977) (by decide),
      show (sp0 - 4057#64) + 16#64 = sp0 - 4041#64 by bv_omega,
      memRegion_split (sp0 - 4041#64) 8 977 (by decide),
      show (sp0 - 4041#64) + 8#64 = sp0 - 4033#64 by bv_omega,
      ProofLib.memRegion_sixteen (sp0 - 4057#64),
      ProofLib.memRegion_eight (sp0 - 4041#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s1 => Entails.sepExists_elim fun s0 => ?_
  exact Entails.sepExists_right s0 (Entails.sepExists_right s1 (Entails.refl _))

theorem memRegion_1232_join_err_2060 (sp0 : BitVec 64) (s0_128 : BitVec 128) (s1_64 : BitVec 64) :
    memRegion (sp0 - 4288#64) 231 ∗
      ((sp0 - 4057#64) ↦₁₂₈ s0_128) ∗
      ((sp0 - 4041#64) ↦₆₄ s1_64) ∗
      memRegion (sp0 - 4033#64) 977 ⊢
    memRegion (sp0 - 4288#64) 1232 := by
  rw [show (1232 : Nat) = 231 + (16 + (8 + 977)) by decide,
      memRegion_split (sp0 - 4288#64) 231 (16 + (8 + 977)) (by decide),
      show (sp0 - 4288#64) + 231#64 = sp0 - 4057#64 by bv_omega,
      memRegion_split (sp0 - 4057#64) 16 (8 + 977) (by decide),
      show (sp0 - 4057#64) + 16#64 = sp0 - 4041#64 by bv_omega,
      memRegion_split (sp0 - 4041#64) 8 977 (by decide),
      show (sp0 - 4041#64) + 8#64 = sp0 - 4033#64 by bv_omega]
  exact sepConj_mono_right (sepConj_mono (pointsTo128_entails_memRegion _ _)
    (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)))

theorem memRegion_16_eq_exists_bytes (a : BitVec 64) :
    (∃∗ v : BitVec 128, a ↦₁₂₈ v) =
      (∃∗ bs : List (BitVec 8), ⌜bs.length = 16⌝ ∗ (a ↦ₛ bs)) := by
  rw [← ProofLib.memRegion_sixteen a, ProofLib.memRegion_eq_exists_bytes a 16 (by decide)]

theorem exists_pointsTo64_of_length_8 {bs : List (BitVec 8)} (h : bs.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₆₄ w) := by
  obtain ⟨w, hw⟩ := exists_unpack64_of_length_8 h
  exact ⟨w, fun a => by rw [hw, ← pointsTo64_eq_pointsToBytes]⟩

theorem exists_pointsTo128_of_length_16 {bs : List (BitVec 8)} (h : bs.length = 16) :
    ∃ q : BitVec 128, ∀ a : BitVec 64, (a ↦ₛ bs) = (a ↦₁₂₈ q) := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have ht : (bs.take 8).length = 8 := by simp [h]
  have hd : (bs.drop 8).length = 8 := by simp [h]
  obtain ⟨w0, hw0⟩ := exists_pointsTo64_of_length_8 ht
  obtain ⟨w1, hw1⟩ := exists_pointsTo64_of_length_8 hd
  have hlo : (w1 ++ w0).extractLsb' 0 64 = w0 := by revert w0 w1; bv_kernel
  have hhi : (w1 ++ w0).extractLsb' 64 64 = w1 := by revert w0 w1; bv_kernel
  refine ⟨w1 ++ w0, fun a => ?_⟩
  rw [hsplit, pointsToBytes_append, ht, hw0 a, hw1 (a + 8#64)]
  unfold pointsTo128
  rw [hlo, hhi]

theorem chunkPayload_expose_bytes39 (a : BitVec 64) (c : Chunk) :
    memRegion (a + 0x09#64) 1 ∗ chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4 ⊢
      ∃∗ bs39 : List (BitVec 8),
        ⌜bs39.length = 39 ∧
          ∀ a' : BitVec 64, ((a' + 0x09#64) ↦ₛ bs39) ⊢
            memRegion (a' + 0x09#64) 1 ∗ chunkAt (a' + 0x0a#64) c ∗ memRegion (a' + 0x2c#64) 4⌝ ∗
        ((a + 0x09#64) ↦ₛ bs39) := by
  unfold chunkAt chunkIndexOff
  rw [ProofLib.memRegion_eq_exists_bytes (a + 0x09#64) 1 (by decide),
      ProofLib.memRegion_eq_exists_bytes (a + 0x2c#64) 4 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs4 => ?_
  refine Entails.sepExists_elim fun bs1 => ?_
  rw [sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hbs1 => ?_
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine Entails.pure_left fun hbs4 => ?_
  have hcd : c.data.toList.length = 32 := c.data.2
  have h16 : ∀ b : BitVec 64,
      ((b + 0x09#64) ↦ₛ (bs1 ++ (c.data.toList ++ (unpack16 c.index ++ bs4)))) =
      ((b + 0x09#64) ↦ₛ bs1) ∗
        (((b + 0x0a#64) ↦ₛ c.data.toList) ∗ (((b + 0x0a#64) + 32#64) ↦₁₆ c.index)) ∗
        ((b + 0x2c#64) ↦ₛ bs4) := by
    intro b
    have ha1 : (b + 0x09#64) + 1#64 = b + 0x0a#64 := by bv_omega
    have ha2 : ((b + 0x0a#64) + 32#64) + 2#64 = b + 0x2c#64 := by bv_omega
    rw [pointsToBytes_append, hbs1, ha1,
        pointsToBytes_append, hcd,
        pointsToBytes_append, unpack16_length, ha2,
        ← pointsTo16_eq_pointsToBytes]
    ac_rfl
  refine Entails.sepExists_right (bs1 ++ (c.data.toList ++ (unpack16 c.index ++ bs4))) ?_
  refine Entails.pure_right ⟨by simp [hbs1, hcd, hbs4], fun a' => ?_⟩ ?_
  · rw [h16 a']
    have hm1 : ((a' + 0x09#64) ↦ₛ bs1) ⊢ memRegion (a' + 0x09#64) 1 := by
      have h := pointsToBytes_entails_memRegion (a' + 0x09#64) bs1
      rwa [hbs1] at h
    have hm4 : ((a' + 0x2c#64) ↦ₛ bs4) ⊢ memRegion (a' + 0x2c#64) 4 := by
      have h := pointsToBytes_entails_memRegion (a' + 0x2c#64) bs4
      rwa [hbs4] at h
    exact sepConj_mono hm1 (sepConj_mono_right hm4)
  · rw [h16 a]; exact Entails.of_eq (by ac_rfl)

theorem chunkVariant_expose_bytes39 (P : PolyApi) (a ep : BitVec 64) (tag : BitVec 8)
    (htag : tag ≠ 0xff#8) (c : P.Chunk)
    (Q : BitVec 64 → SepProp)
    (hQ : ∀ a', Q a' = (a' ↦₆₄ ep) ∗ ((a' + 0x08#64) ↦₈ tag) ∗ memRegion (a' + 0x09#64) 1 ∗
      chunkAt (a' + 0x0a#64) { index := P.chunkIndex c, data := P.chunkData c } ∗
      memRegion (a' + 0x2c#64) 4) :
    Q a ⊢
      ∃∗ t : BitVec 8, ∃∗ bs39 : List (BitVec 8),
        ⌜t ≠ 0xff#8 ∧ bs39.length = 39 ∧
          ∀ a' : BitVec 64, (a' ↦₆₄ ep) ∗ ((a' + 0x08#64) ↦₈ t) ∗ ((a' + 0x09#64) ↦ₛ bs39) ⊢ Q a'⌝ ∗
        (a ↦₆₄ ep) ∗ ((a + 0x08#64) ↦₈ t) ∗ ((a + 0x09#64) ↦ₛ bs39) := by
  rw [hQ a]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right
    (chunkPayload_expose_bytes39 a { index := P.chunkIndex c, data := P.chunkData c }))) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs39 => ?_
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
  refine Entails.pure_left fun ⟨hbs39, hfold⟩ => ?_
  refine Entails.sepExists_right tag (Entails.sepExists_right bs39 ?_)
  refine Entails.pure_right ⟨htag, hbs39, fun a' => ?_⟩ (Entails.refl _)
  rw [hQ a']
  exact sepConj_mono_right (sepConj_mono_right (hfold a'))

theorem messageAt_expose_bytes39 (P : PolyApi) (a : BitVec 64) (m : Message P) :
    messageAt P a m ⊢
      ∃∗ tag : BitVec 8, ∃∗ bs39 : List (BitVec 8),
        ⌜tag ≠ 0xff#8 ∧ bs39.length = 39 ∧
          ∀ a' : BitVec 64,
            (a' ↦₆₄ m.epoch) ∗ ((a' + 0x08#64) ↦₈ tag) ∗ ((a' + 0x09#64) ↦ₛ bs39) ⊢
              messageAt P a' m⌝ ∗
        (a ↦₆₄ m.epoch) ∗ ((a + 0x08#64) ↦₈ tag) ∗ ((a + 0x09#64) ↦ₛ bs39) := by
  cases hp : m.payload with
  | none =>
    unfold messageAt messagePayloadAt; rw [hp]; dsimp only []
    rw [ProofLib.memRegion_eq_exists_bytes (a + 0x09#64) 39 (by decide)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs39 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine Entails.pure_left fun hbs39 => ?_
    refine Entails.sepExists_right 0#8 (Entails.sepExists_right bs39 ?_)
    refine Entails.pure_right ⟨by decide, hbs39, fun a' => ?_⟩ (Entails.refl _)
    refine sepConj_mono_right (sepConj_mono_right ?_)
    have hm := pointsToBytes_entails_memRegion (a' + 0x09#64) bs39
    rwa [hbs39] at hm
  | ct1Ack b =>
    unfold messageAt messagePayloadAt; rw [hp]; dsimp only []
    rw [ProofLib.memRegion_eq_exists_bytes (a + 0x0a#64) 38 (by decide)]
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs38 => ?_
    rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
    refine Entails.pure_left fun hbs38 => ?_
    have hcons : ∀ base : BitVec 64,
        ((base + 0x09#64) ↦ₛ ((if b then 1#8 else 0#8) :: bs38)) =
        ((base + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗ ((base + 0x0a#64) ↦ₛ bs38) := by
      intro base
      have ha : (base + 0x09#64) + 1#64 = base + 0x0a#64 := by bv_omega
      rw [pointsToBytes_cons, ha]
    refine Entails.sepExists_right 4#8
      (Entails.sepExists_right ((if b then 1#8 else 0#8) :: bs38) ?_)
    refine Entails.pure_right ⟨by decide, by simp [hbs38], fun a' => ?_⟩ ?_
    · rw [hcons a', ← sepConj_assoc, sepConj_assoc (a' ↦₆₄ m.epoch)]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      have hm := pointsToBytes_entails_memRegion (a' + 0x0a#64) bs38
      rwa [hbs38] at hm
    · rw [hcons a]; exact Entails.refl _
  | hdr c =>
    exact chunkVariant_expose_bytes39 P a m.epoch 1#8 (by decide) c (fun a' => messageAt P a' m)
      (fun a' => by unfold messageAt messagePayloadAt; rw [hp])
  | ek c =>
    exact chunkVariant_expose_bytes39 P a m.epoch 2#8 (by decide) c (fun a' => messageAt P a' m)
      (fun a' => by unfold messageAt messagePayloadAt; rw [hp])
  | ekCt1Ack c =>
    exact chunkVariant_expose_bytes39 P a m.epoch 3#8 (by decide) c (fun a' => messageAt P a' m)
      (fun a' => by unfold messageAt messagePayloadAt; rw [hp])
  | ct1 c =>
    exact chunkVariant_expose_bytes39 P a m.epoch 5#8 (by decide) c (fun a' => messageAt P a' m)
      (fun a' => by unfold messageAt messagePayloadAt; rw [hp])
  | ct2 c =>
    exact chunkVariant_expose_bytes39 P a m.epoch 6#8 (by decide) c (fun a' => messageAt P a' m)
      (fun a' => by unfold messageAt messagePayloadAt; rw [hp])

theorem bytes39_expose_copy_atoms {bs39 : List (BitVec 8)} (h : bs39.length = 39) :
    ∃ (bs15 b24 bs15' : List (BitVec 8)) (q1 q0 : BitVec 128) (w40 : BitVec 64),
      bs15.length = 15 ∧ b24.length = 1 ∧ bs15'.length = 15 ∧
      (∀ base : BitVec 64,
        ((base + 0x09#64) ↦ₛ bs39) =
          ((base + 0x09#64) ↦ₛ bs15) ∗ ((base + 24#64) ↦ₛ b24) ∗
          ((base + 25#64) ↦ₛ bs15') ∗ ((base + 40#64) ↦₆₄ w40)) ∧
      (∀ base : BitVec 64,
        ((base) ↦ₛ bs15) ∗ ((base + 15#64) ↦ₛ b24) = (base ↦₁₂₈ q1)) ∧
      (∀ base : BitVec 64,
        ((base) ↦ₛ b24) ∗ ((base + 1#64) ↦ₛ bs15') = (base ↦₁₂₈ q0)) := by
  let bs15 := bs39.take 15
  let r24 := bs39.drop 15
  let b24 := r24.take 1
  let r23 := r24.drop 1
  let bs15' := r23.take 15
  let bs8 := r23.drop 15
  have hbs15 : bs15.length = 15 := by simp [bs15, h]
  have hb24 : b24.length = 1 := by simp [b24, r24, h]
  have hbs15' : bs15'.length = 15 := by simp [bs15', r23, r24, h]
  have hbs8 : bs8.length = 8 := by simp [bs8, r23, r24, h]
  have hcat : bs39 = bs15 ++ (b24 ++ (bs15' ++ bs8)) := by
    simp only [bs15, b24, bs15', bs8, r23, r24, List.take_append_drop]
  obtain ⟨w40, hw40⟩ := exists_pointsTo64_of_length_8 hbs8
  obtain ⟨q1, hq1⟩ := exists_pointsTo128_of_length_16 (bs := bs15 ++ b24) (by simp [hbs15, hb24])
  obtain ⟨q0, hq0⟩ := exists_pointsTo128_of_length_16 (bs := b24 ++ bs15') (by simp [hb24, hbs15'])
  refine ⟨bs15, b24, bs15', q1, q0, w40, hbs15, hb24, hbs15', ?_, ?_, ?_⟩
  · intro base
    have ha1 : (base + 0x09#64) + 15#64 = base + 24#64 := by bv_omega
    have ha2 : (base + 24#64) + 1#64 = base + 25#64 := by bv_omega
    have ha3 : (base + 25#64) + 15#64 = base + 40#64 := by bv_omega
    conv_lhs => rw [hcat]
    rw [pointsToBytes_append, hbs15, ha1,
        pointsToBytes_append, hb24, ha2,
        pointsToBytes_append, hbs15', ha3,
        hw40 (base + 40#64)]
  · intro base
    have h := hq1 base
    rw [pointsToBytes_append, hbs15] at h
    exact h
  · intro base
    have h := hq0 base
    rw [pointsToBytes_append, hb24] at h
    exact h

theorem memRegion_15_and_byte1_to_pointsTo128 (a : BitVec 64) {b1 : List (BitVec 8)}
    (hb1 : b1.length = 1) :
    memRegion a 15 ∗ ((a + 15#64) ↦ₛ b1) ⊢ ∃∗ q : BitVec 128, a ↦₁₂₈ q := by
  rw [ProofLib.memRegion_eq_exists_bytes a 15 (by decide), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun bs15 => ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hbs15 => ?_
  obtain ⟨q, hq⟩ := exists_pointsTo128_of_length_16 (bs := bs15 ++ b1) (by simp [hbs15, hb1])
  have h := hq a
  rw [pointsToBytes_append, hbs15] at h
  rw [h]
  exact Entails.sepExists_right q (Entails.refl _)

theorem byte1_and_memRegion_15_to_pointsTo128 (a : BitVec 64) {b1 : List (BitVec 8)}
    (hb1 : b1.length = 1) :
    (a ↦ₛ b1) ∗ memRegion (a + 1#64) 15 ⊢ ∃∗ q : BitVec 128, a ↦₁₂₈ q := by
  rw [ProofLib.memRegion_eq_exists_bytes (a + 1#64) 15 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs15 => ?_
  rw [sepConj_pure_left_comm]
  refine Entails.pure_left fun hbs15 => ?_
  obtain ⟨q, hq⟩ := exists_pointsTo128_of_length_16 (bs := b1 ++ bs15) (by simp [hb1, hbs15])
  have h := hq a
  rw [pointsToBytes_append, hb1] at h
  rw [h]
  exact Entails.sepExists_right q (Entails.refl _)

theorem memRegion_1232_split_ok_1568 (sp0 : BitVec 64) :
    memRegion (sp0 - 4288#64) 1232 ⊢
      ∃∗ d0 : BitVec 64, ∃∗ d8 : BitVec 8, ∃∗ d9 : BitVec 128, ∃∗ d40 : BitVec 64, ∃∗ s_q0 : BitVec 128,
        memRegion (sp0 - 4288#64) 176 ∗
        ((sp0 - 4112#64) ↦₆₄ d0) ∗
        ((sp0 - 4104#64) ↦₈ d8) ∗
        ((sp0 - 4103#64) ↦₁₂₈ d9) ∗
        memRegion (sp0 - 4087#64) 15 ∗
        ((sp0 - 4072#64) ↦₆₄ d40) ∗
        memRegion (sp0 - 4064#64) 15 ∗
        ((sp0 - 4049#64) ↦₁₂₈ s_q0) ∗
        memRegion (sp0 - 4033#64) 977 := by
  rw [show (1232 : Nat) = 176 + (8 + (1 + (16 + (15 + (8 + (15 + (16 + 977))))))) by decide,
      memRegion_split (sp0 - 4288#64) 176 1056 (by decide),
      show (sp0 - 4288#64) + 176#64 = sp0 - 4112#64 by bv_omega,
      memRegion_split (sp0 - 4112#64) 8 1048 (by decide),
      show (sp0 - 4112#64) + 8#64 = sp0 - 4104#64 by bv_omega,
      memRegion_split (sp0 - 4104#64) 1 1047 (by decide),
      show (sp0 - 4104#64) + 1#64 = sp0 - 4103#64 by bv_omega,
      memRegion_split (sp0 - 4103#64) 16 1031 (by decide),
      show (sp0 - 4103#64) + 16#64 = sp0 - 4087#64 by bv_omega,
      memRegion_split (sp0 - 4087#64) 15 1016 (by decide),
      show (sp0 - 4087#64) + 15#64 = sp0 - 4072#64 by bv_omega,
      memRegion_split (sp0 - 4072#64) 8 1008 (by decide),
      show (sp0 - 4072#64) + 8#64 = sp0 - 4064#64 by bv_omega,
      memRegion_split (sp0 - 4064#64) 15 993 (by decide),
      show (sp0 - 4064#64) + 15#64 = sp0 - 4049#64 by bv_omega,
      memRegion_split (sp0 - 4049#64) 16 977 (by decide),
      show (sp0 - 4049#64) + 16#64 = sp0 - 4033#64 by bv_omega,
      ProofLib.memRegion_eight (sp0 - 4112#64),
      ProofLib.memRegion_one (sp0 - 4104#64),
      ProofLib.memRegion_sixteen (sp0 - 4103#64),
      ProofLib.memRegion_eight (sp0 - 4072#64),
      ProofLib.memRegion_sixteen (sp0 - 4049#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s_q0 => Entails.sepExists_elim fun d40 =>
    Entails.sepExists_elim fun d9 => Entails.sepExists_elim fun d8 =>
    Entails.sepExists_elim fun d0 => ?_
  exact Entails.sepExists_right d0 (Entails.sepExists_right d8
    (Entails.sepExists_right d9 (Entails.sepExists_right d40
      (Entails.sepExists_right s_q0 (Entails.refl _)))))

theorem src_3056_and_scratch_to_memRegion_3968 (sp0 : BitVec 64)
    {bs15 bs15' : List (BitVec 8)} (hbs15 : bs15.length = 15) (hbs15' : bs15'.length = 15)
    (ep w40 : BitVec 64) (tag : BitVec 8) (q1 q0 : BitVec 128) :
    ((sp0 - 4064#64) ↦ₛ bs15) ∗
      ((sp0 - 4049#64) ↦₁₂₈ q0) ∗
      memRegion (sp0 - 4033#64) 977 ∗
      ((sp0 - 3056#64) ↦₆₄ ep) ∗
      ((sp0 - 3048#64) ↦₈ tag) ∗
      ((sp0 - 3047#64) ↦₁₂₈ q1) ∗
      ((sp0 - 3031#64) ↦ₛ bs15') ∗
      ((sp0 - 3016#64) ↦₆₄ w40) ∗
      memRegion (sp0 - 3008#64) 2912 ⊢
    memRegion (sp0 - 4064#64) 3968 := by
  have hm15a : ((sp0 - 4064#64) ↦ₛ bs15) ⊢ memRegion (sp0 - 4064#64) 15 := by
    have h := pointsToBytes_entails_memRegion (sp0 - 4064#64) bs15
    rwa [hbs15] at h
  have hm15b : ((sp0 - 3031#64) ↦ₛ bs15') ⊢ memRegion (sp0 - 3031#64) 15 := by
    have h := pointsToBytes_entails_memRegion (sp0 - 3031#64) bs15'
    rwa [hbs15'] at h
  rw [show (3968 : Nat) = 15 + (16 + (977 + (8 + (1 + (16 + (15 + (8 + 2912))))))) by decide,
      memRegion_split (sp0 - 4064#64) 15 3953 (by decide),
      show (sp0 - 4064#64) + 15#64 = sp0 - 4049#64 by bv_omega,
      memRegion_split (sp0 - 4049#64) 16 3937 (by decide),
      show (sp0 - 4049#64) + 16#64 = sp0 - 4033#64 by bv_omega,
      memRegion_split (sp0 - 4033#64) 977 2960 (by decide),
      show (sp0 - 4033#64) + 977#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 8 2952 (by decide),
      show (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 by bv_omega,
      memRegion_split (sp0 - 3048#64) 1 2951 (by decide),
      show (sp0 - 3048#64) + 1#64 = sp0 - 3047#64 by bv_omega,
      memRegion_split (sp0 - 3047#64) 16 2935 (by decide),
      show (sp0 - 3047#64) + 16#64 = sp0 - 3031#64 by bv_omega,
      memRegion_split (sp0 - 3031#64) 15 2920 (by decide),
      show (sp0 - 3031#64) + 15#64 = sp0 - 3016#64 by bv_omega,
      memRegion_split (sp0 - 3016#64) 8 2912 (by decide),
      show (sp0 - 3016#64) + 8#64 = sp0 - 3008#64 by bv_omega]
  exact sepConj_mono hm15a (sepConj_mono (pointsTo128_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _)
        (sepConj_mono (pointsTo128_entails_memRegion _ _)
          (sepConj_mono hm15b (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))))))))

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

theorem pointsTo128_sub_eq (sp0 : BitVec 64) (k k8 : Nat) (q : BitVec 128) (hk : k - 8 = k8)
    (h : 8 < k := by decide) (ha : k < 2 ^ 64 := by decide) :
    ((sp0 - BitVec.ofNat 64 k) ↦₁₂₈ q) =
      ((sp0 - BitVec.ofNat 64 k) ↦₆₄ q.extractLsb' 0 64) ∗
      ((sp0 - BitVec.ofNat 64 k8) ↦₆₄ q.extractLsb' 64 64) := by
  unfold pointsTo128
  rw [bv_sub_add_lit sp0 k 8 h ha, hk]

end CryptoVerification.SpqrV1.Top.Recv
