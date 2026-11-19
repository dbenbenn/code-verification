/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part4
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: V1 Ratchet `Ok` Tail (`+2664..+2916 -> +876 -> +1040`)

**Checked by Lean.** Symbolic execution of `<States>::into_pb`, `<Chain>::into_pb`,
`PqRatchetState::encode_to_vec`, result writing, and `PqRatchetState` / `versionNegotiation` drop
cleanup on the V1 ratchet `Ok` tail of `spqr::recv` (`0x5462c`).
-/

public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

/-! ## 1. Pure Model & Encoded State Length Lemmas for V1 Ratchet `Ok` -/

theorem spqrDeps_statesIntoPb_eq (F : ShaCompress) (K : MlKem)
    (st1 : States spqrPolyApi (spqrAuthApi F)) :
    (spqrDeps F K).statesIntoPb st1 = st1.into_pb := rfl

theorem spqrV1Recv_v1_ratchet_of_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {chain2 : Chain} {rawKey : Bytes}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hbody : (do
      let sckaMsg ← (spqrDeps F K).msgDeserialize pre.epoch pre.remaining
      let st0 ← (spqrDeps F K).statesFromPb pb
      let (key, st1') ← (spqrDeps F K).statesRecv st0 sckaMsg
      if pre.epoch == 0#64 then .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := pre.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation)
        let chain1 ← match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
          | none => pure chain0
        let (chain2', msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey (spqrHkdfWith F) msgKeyEpoch pre.index)
        let newStateBytes := (spqrDeps F K).encodeState {
          inner := some ((spqrDeps F K).statesIntoPb st1'), versionNegotiation := none, chain := some chain2'.intoPb }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        (.ok ({ state := newStateBytes, key := outKey } : Recv) : SpqrApiResult Recv)) =
      .ok {
        state := PqRatchetState.encodeRaw {
          versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
        key := if rawKey.isEmpty then none else some rawKey }) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      .ok (PqRatchetState.encodeRaw {
        versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb)
      }, if rawKey.isEmpty then none else some rawKey) := by
  have hd_ok := decodeState_spqrDeps_of_spqrDecodeState_ok F K hdec
  have heq := recv_v1_ratchet_eq (spqrDeps F K) (spqrHkdfWith F) hpre hd_ok
    (pqRatchetStateToPb_inner_some hinner) hmv hmin
  have hch : (pqRatchetStateToPb pre_pb).chain = pre_pb.chain := rfl
  have hvn : (pqRatchetStateToPb pre_pb).versionNegotiation = pre_pb.versionNegotiation := rfl
  rw [hch, hvn] at heq
  exact spqrV1Recv_recv_of_ok (heq.trans hbody)

theorem spqrV1Recv_v1_ratchet_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {pre : MsgPreamble} {pre_pb : PqRatchetState} {pb : V1State}
    {sckaMsg : Message spqrPolyApi} {st0 st1 : States spqrPolyApi (spqrAuthApi F)}
    {key : Option EpochSecret} {chain0 chain1 chain2 : Chain} {rawKey : Bytes}
    (hpre : msgPreamble msgBytes = .ok pre)
    (hdec : Proto.spqrDecodeState stateBytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey)) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      .ok (PqRatchetState.encodeRaw {
        versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb)
      }, if rawKey.isEmpty then none else some rawKey) := by
  refine spqrV1Recv_v1_ratchet_of_ok hpre hdec hinner hmv hmin ?_
  dsimp only [spqrDeps]
  rw [hmsg]; dsimp only [Bind.bind, Except.bind]
  rw [hst0]; dsimp only [liftStatesResult, Bind.bind, Except.bind]
  rw [hrecv]; dsimp only [Bind.bind, Except.bind]
  rw [hep_ne, hcf]
  cases key with
  | none =>
    cases hadd
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
      Proto.encodeState, pbToPqRatchetState, ↓reduceIte, hrk]; rfl
  | some es =>
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
      SpqrApiResult.ofError, SpqrApiResult.ofChainResult,
      Proto.encodeState, pbToPqRatchetState, ↓reduceIte] at hadd ⊢
    rw [hadd]; simp only [hrk]; rfl

theorem encodeRaw_len_lt_of_recv_ok {F : ShaCompress} {K : MlKem}
    {stateBytes msgBytes stBytes : Bytes} {outKey : Option Bytes}
    (hst_len : stateBytes.length < 2 ^ 32)
    (hok : (spqrV1Recv F K).recv stateBytes msgBytes = .ok (stBytes, outKey)) :
    stBytes.length < 2 ^ 63 :=
  (encodeState_len_lt_spqrV1Recv F K stateBytes msgBytes stBytes outKey hst_len hok).2.2.1

/-! ## 2. 224-Byte `Option<Inner>` Relocation (`s0.sp - 2096#64 -> s0.sp - 2928#64`) -/

private theorem exists_words27_of_length_216_v1 (bs : List (BitVec 8)) (h : bs.length = 216) :
    ∃ d : Words27, ∀ out : BitVec 64, (out ↦ₛ bs) = words27At out d := by
  have hsplit (k : Nat) (l : List (BitVec 8)) : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 24).take 8) (by simp [h])
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 32).take 8) (by simp [h])
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 40).take 8) (by simp [h])
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 48).take 8) (by simp [h])
  obtain ⟨w7, hw7⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 56).take 8) (by simp [h])
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 64).take 8) (by simp [h])
  obtain ⟨w9, hw9⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 72).take 8) (by simp [h])
  obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 80).take 8) (by simp [h])
  obtain ⟨w11, hw11⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 88).take 8) (by simp [h])
  obtain ⟨w12, hw12⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 96).take 8) (by simp [h])
  obtain ⟨w13, hw13⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 104).take 8) (by simp [h])
  obtain ⟨w14, hw14⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 112).take 8) (by simp [h])
  obtain ⟨w15, hw15⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 120).take 8) (by simp [h])
  obtain ⟨w16, hw16⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 128).take 8) (by simp [h])
  obtain ⟨w17, hw17⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 136).take 8) (by simp [h])
  obtain ⟨w18, hw18⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 144).take 8) (by simp [h])
  obtain ⟨w19, hw19⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 152).take 8) (by simp [h])
  obtain ⟨w20, hw20⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 160).take 8) (by simp [h])
  obtain ⟨w21, hw21⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 168).take 8) (by simp [h])
  obtain ⟨w22, hw22⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 176).take 8) (by simp [h])
  obtain ⟨w23, hw23⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 184).take 8) (by simp [h])
  obtain ⟨w24, hw24⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 192).take 8) (by simp [h])
  obtain ⟨w25, hw25⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 200).take 8) (by simp [h])
  obtain ⟨w26, hw26⟩ := exists_unpack64_of_length_8 (bs := bs.drop 208) (by simp [h])
  refine ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
           w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩, fun out => ?_⟩
  have hbs : bs =
      unpack64 w0 ++ (unpack64 w1 ++ (unpack64 w2 ++ (unpack64 w3 ++
      (unpack64 w4 ++ (unpack64 w5 ++ (unpack64 w6 ++ (unpack64 w7 ++
      (unpack64 w8 ++ (unpack64 w9 ++ (unpack64 w10 ++ (unpack64 w11 ++
      (unpack64 w12 ++ (unpack64 w13 ++ (unpack64 w14 ++ (unpack64 w15 ++
      (unpack64 w16 ++ (unpack64 w17 ++ (unpack64 w18 ++ (unpack64 w19 ++
      (unpack64 w20 ++ (unpack64 w21 ++ (unpack64 w22 ++ (unpack64 w23 ++
      (unpack64 w24 ++ (unpack64 w25 ++ unpack64 w26))))))))))))))))))))))))) := by
    rw [← hw0, ← hw1, ← hw2, ← hw3, ← hw4, ← hw5, ← hw6, ← hw7, ← hw8,
        ← hw9, ← hw10, ← hw11, ← hw12, ← hw13, ← hw14, ← hw15, ← hw16, ← hw17,
        ← hw18, ← hw19, ← hw20, ← hw21, ← hw22, ← hw23, ← hw24, ← hw25, ← hw26]
    conv_lhs =>
      rw [hsplit 8 bs]
      rw [hsplit 8 (bs.drop 8)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 16)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 24)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 32)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 40)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 48)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 56)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 64)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 72)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 80)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 88)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 96)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 104)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 112)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 120)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 128)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 136)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 144)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 152)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 160)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 168)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 176)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 184)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 192)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 200)]; simp only [List.drop_drop, Nat.reduceAdd]
  conv_lhs => rw [hbs]
  dsimp only [words27At]
  simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]

private theorem bytes224_expose_words28_move_2096_to_2928 (sp0 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 224) :
    ((sp0 - 2096#64) ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ⊢ ((sp0 - 2928#64) ↦ₛ bs)⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have htake : (bs.take 8).length = 8 := by simp [hlen]
  have hdrop : (bs.drop 8).length = 216 := by simp [hlen]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 htake
  obtain ⟨d, hd⟩ := exists_words27_of_length_216_v1 (bs.drop 8) hdrop
  have h_at (m : Nat) (h0 : m < 2 ^ 64) (h216 : 216 < m) :
      ((sp0 - BitVec.ofNat 64 m) ↦ₛ bs) = ((sp0 - BitVec.ofNat 64 m) ↦₆₄ w0) ∗ words27SubAt sp0 m d := by
    conv_lhs => rw [hsplit]
    rw [pointsToBytes_append, htake, hw0, ← pointsTo64_eq_pointsToBytes,
        hd ((sp0 - BitVec.ofNat 64 m) + 8#64), words27At_sub_eq sp0 m d h0 h216]
  rw [h_at 2096 (by decide) (by decide)]
  refine Entails.sepExists_right w0 (Entails.sepExists_right d ?_)
  refine Entails.pure_right ?_ (Entails.refl _)
  rw [h_at 2928 (by decide) (by decide)]; exact Entails.refl _

private theorem optProtoInnerStateAt_expose_224 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (sp0 : BitVec 64) (opt : Option V1State.InnerState) :
    Drop.optProtoInnerStateAt A (sp0 - 2096#64) opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27, ∃∗ P_heap : SepProp,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ P_heap ⊢
          Drop.optProtoInnerStateAt A (sp0 - 2928#64) opt⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d ∗ P_heap := by
  have hto := (relocOptProtoInnerStateAt H_inner A opt).2.to_bytes (sp0 - 2096#64)
  rw [h_inner_eq] at hto
  refine Entails.trans hto ?_
  apply sepExists_left_entails; intro bs
  refine Entails.pure_left fun hbs => ?_
  refine Entails.trans (sepConj_mono_left (bytes224_expose_words28_move_2096_to_2928 sp0 bs hbs)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepExists_left_entails; intro w0; apply sepExists_left_entails; intro d
  refine Entails.pure_left fun hmove => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right d
    (Entails.sepExists_right ((relocOptProtoInnerStateAt H_inner A opt).1 bs) ?_))
  refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
  have hof := (relocOptProtoInnerStateAt H_inner A opt).2.of_bytes (sp0 - 2928#64) bs hbs
  rw [h_inner_eq] at hof
  refine Entails.trans ?_ hof
  refine Entails.trans (Entails.of_eq (show
    ((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs =
    (((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d) ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs by ac_rfl)) ?_
  exact sepConj_mono_left hmove

/-! ## 3. Result Writing & `PqRatchetState` Drop Helpers (`+2820 .. +2916`) -/

private theorem vecU8_sub_entails_header_payload_v1 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (bs : List (BitVec 8)) (h0 : m < 2 ^ 64 := by decide) (h16 : 16 < m := by decide) :
    vecU8 A (sp0 - BitVec.ofNat 64 m) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ cap) ∗
        ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ ptr) ∗
        ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        RustHeap.vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply sepExists_left_entails; intro cap
  apply sepExists_left_entails; intro ptr
  rw [RustHeap.vecU8At_eq_header_sep_buf A (sp0 - BitVec.ofNat 64 m) cap ptr bs]
  dsimp only [RustHeap.vecHeader]
  have h8 : (sp0 - BitVec.ofNat 64 m) + 8#64 = sp0 - BitVec.ofNat 64 (m - 8) :=
    bv_sub_add_lit sp0 m 8 (by omega) h0
  have h16_eq : (sp0 - BitVec.ofNat 64 m) + 16#64 = sp0 - BitVec.ofNat 64 (m - 16) :=
    bv_sub_add_lit sp0 m 16 (by omega) h0
  rw [h8, h16_eq]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

private theorem vecU8_of_header_buf_v1 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      RustHeap.vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [RustHeap.vecU8At_eq_header_sep_buf A a cap ptr bs]
  dsimp only [RustHeap.vecHeader]
  exact Entails.of_eq (by ac_rfl)

private theorem ret_48_split_6_v1 (ret : BitVec 64) :
    memRegion ret 48 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64,
        (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) := by
  rw [ret_48_split ret,
      ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
        (b' := ret + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (ret + 32#64),
      ProofLib.memRegion_eight (ret + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro r5
  apply sepExists_left_entails; intro r4
  apply sepExists_left_entails; intro r3
  apply sepExists_left_entails; intro r2
  apply sepExists_left_entails; intro r1
  apply sepExists_left_entails; intro r0
  refine Entails.sepExists_right r0 (Entails.sepExists_right r1 (Entails.sepExists_right r2
    (Entails.sepExists_right r3 (Entails.sepExists_right r4 (Entails.sepExists_right r5 ?_)))))
  exact Entails.refl _

private theorem recv_ok_some_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st cap_rk ptr_rk : BitVec 64) (stBytes rawKey : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
      ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, some rawKey)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have hrk := vecU8_of_header_buf_v1 A (ret + 24#64) cap_rk ptr_rk rawKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        RustHeap.vecU8Buf A cap_rk ptr_rk rawKey) by ac_rfl)) ?_
  exact sepConj_mono hst hrk

private theorem recv_ok_none_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st r4 r5 : BitVec 64) (stBytes : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
      RustHeap.vecU8Buf A cap_st ptr_st stBytes ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, none)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt, noneCap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have h16 : ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ⊢ memRegion (ret + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
          (b' := ret + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (ret + 32#64),
        ProofLib.memRegion_eight (ret + 40#64)]
    exact sepConj_mono (Entails.sepExists_right r4 (Entails.refl _))
      (Entails.sepExists_right r5 (Entails.refl _))
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        RustHeap.vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        (((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5))) by ac_rfl)) ?_
  exact sepConj_mono hst (sepConj_mono_right h16)

private theorem protoPqRatchetState_entails_drop_v1 (A : RustAlloc) (sp0 : BitVec 64)
    (chPb : ChainPB) (pb1 : V1State) :
    ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      ProtoRepr.chainPBAt A (sp0 - 3008#64) chPb ∗
      Drop.optProtoInnerStateAt A (sp0 - 2928#64) pb1.innerState ⊢
    Drop.protoPqRatchetStateAt A (sp0 - 3056#64)
      { versionNegotiation := none, chain := some chPb, inner := some (.v1 pb1) } := by
  dsimp only [Drop.protoPqRatchetStateAt, optVersionNegotiationPBAt, ProtoRepr.optChainPBAt, Drop.optProtoPqRatchetInnerAt]
  have h8 : (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 := bv_sub_add_lit sp0 3056 8
  have h48 : (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 := bv_sub_add_lit sp0 3056 48
  have h128 : (sp0 - 3056#64) + 128#64 = sp0 - 2928#64 := bv_sub_add_lit sp0 3056 128
  rw [h8, h48, h128]
  exact Entails.of_eq (by ac_rfl)

/-! ## 4. Stack Frame Splits and Reassembly for `+2664 .. +2916` -/

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_sub_96_sub_32 (sp0 : BitVec 64) :
    (sp0 - 96#64) + 18446744073709551584#64 = sp0 - 128#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_sub_96_sub_136 (sp0 : BitVec 64) :
    (sp0 - 96#64) - 136#64 = sp0 - 232#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_544 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_560 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_456 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 456#64 = s0.sp - 232#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

private theorem memRegion_2856_split_v1_ok (sp0 : BitVec 64) :
    memRegion (sp0 - 3088#64) 2856 ⊢
      memRegion (sp0 - 3088#64) 32 ∗
      (∃∗ w790 : BitVec 64, (sp0 - 3056#64) ↦₆₄ w790) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) Drop.optProtoInnerStateSize ∗
      memRegion (sp0 - 1872#64) 1640 := by
  unfold Drop.optProtoInnerStateSize
  rw [show (2856 : Nat) = 32 + (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) by decide,
      memRegion_split (sp0 - 3088#64) 32 (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 8 (40 + (80 + (224 + (608 + (224 + 1640))))) (by decide),
      show (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 by bv_omega,
      memRegion_split (sp0 - 3048#64) 40 (80 + (224 + (608 + (224 + 1640)))) (by decide),
      show (sp0 - 3048#64) + 40#64 = sp0 - 3008#64 by bv_omega,
      memRegion_split (sp0 - 3008#64) 80 (224 + (608 + (224 + 1640))) (by decide),
      show (sp0 - 3008#64) + 80#64 = sp0 - 2928#64 by bv_omega,
      memRegion_split (sp0 - 2928#64) 224 (608 + (224 + 1640)) (by decide),
      show (sp0 - 2928#64) + 224#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (224 + 1640) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 224 1640 (by decide),
      show (sp0 - 2096#64) + 224#64 = sp0 - 1872#64 by bv_omega,
      ProofLib.memRegion_eight (sp0 - 3056#64)]
  exact Entails.refl _

private theorem memRegion_224_split_24_200_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 224 ⊢
      memRegion (sp0 - 2096#64) 24 ∗ memRegion (sp0 - 2072#64) 200 := by
  rw [show (224 : Nat) = 24 + 200 by decide,
      memRegion_split (sp0 - 2096#64) 24 200 (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega]
  exact Entails.refl _

private theorem memRegion_48_split_144_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 144#64) 48 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp0 - 144#64) ↦₆₄ w0) ∗ ((sp0 - 136#64) ↦₆₄ w1) ∗
        ((sp0 - 128#64) ↦₆₄ w2) ∗ memRegion (sp0 - 120#64) 24 := by
  rw [show (48 : Nat) = 24 + 24 by decide,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega,
      memRegion_24_words3 (sp0 - 144#64),
      show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro w2; apply sepExists_left_entails; intro w1; apply sepExists_left_entails; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

private theorem ownFrame_join_v1_ok_2892 (sp0 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64) :
    memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
      memRegion (sp0 - 4016#64) chunkedStatesSize ∗ memRegion (sp0 - 3088#64) 32 ∗
      memRegion (sp0 - 3056#64) 352 ∗ memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
      ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  unfold chunkedStatesSize
  have h24_st := words3_to_memRegion_24 (sp0 - 2096#64) w0_st w1_st w2_st
  rw [show (sp0 - 2096#64) + 8#64 = sp0 - 2088#64 by bv_omega,
      show (sp0 - 2096#64) + 16#64 = sp0 - 2080#64 by bv_omega] at h24_st
  have h24_144 := words3_to_memRegion_24 (sp0 - 144#64) w0_144 w1_144 w2_144
  rw [show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega] at h24_144
  rw [show (0x1320 : Nat) = 352 + (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) by decide,
      memRegion_split (sp0 - 4992#64) 352 (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) (by decide),
      show (sp0 - 4992#64) + 352#64 = sp0 - 4640#64 by bv_omega,
      memRegion_split (sp0 - 4640#64) 48 (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))))) (by decide),
      show (sp0 - 4640#64) + 48#64 = sp0 - 4592#64 by bv_omega,
      memRegion_split (sp0 - 4592#64) 576 (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))) (by decide),
      show (sp0 - 4592#64) + 576#64 = sp0 - 4016#64 by bv_omega,
      memRegion_split (sp0 - 4016#64) 928 (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))) (by decide),
      show (sp0 - 4016#64) + 928#64 = sp0 - 3088#64 by bv_omega,
      memRegion_split (sp0 - 3088#64) 32 (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 352 (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))) (by decide),
      show (sp0 - 3056#64) + 352#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (24 + (200 + (1640 + (88 + (24 + 24))))) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 24 (200 + (1640 + (88 + (24 + 24)))) (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega,
      memRegion_split (sp0 - 2072#64) 200 (1640 + (88 + (24 + 24))) (by decide),
      show (sp0 - 2072#64) + 200#64 = sp0 - 1872#64 by bv_omega,
      memRegion_split (sp0 - 1872#64) 1640 (88 + (24 + 24)) (by decide),
      show (sp0 - 1872#64) + 1640#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗ ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗
        ((sp0 - 2080#64) ↦₆₄ w2_st) ∗ memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗
        memRegion (sp0 - 232#64) 88 ∗ ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗
        ((sp0 - 128#64) ↦₆₄ w2_144) ∗ memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        (((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st)) ∗
        memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
        (((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono h24_st
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24_144)))))))))))

/-! ## 5. Result Epilogue & Drop Cleanup (`+2820 .. +2916 -> +876 -> +1040 -> ret`) -/

private theorem vecU8Buf_expose_len_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    RustHeap.vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ RustHeap.vecU8Buf A cap ptr bs := by
  unfold RustHeap.vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

private theorem vecU8Buf_nil_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) :
    RustHeap.vecU8Buf A cap ptr [] ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold RustHeap.vecU8Buf
  apply Entails.pure_left; rintro ⟨_, hcap, hptr⟩
  refine Entails.pure_right ⟨hcap, hptr⟩ ?_
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]; exact Entails.refl _
  · simp only [hc, ↓reduceIte, List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero,
      pointsToBytes_nil, emp_sepConj]; exact Entails.refl _

private theorem ofNat64_beq_zero_false_of_ne_nil {bs : List (BitVec 8)}
    (hne : bs.isEmpty = false) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => contradiction
    | cons _ _ => exact Nat.succ_pos _
  rw [beq_eq_false_iff_ne]; intro h0
  have h0n := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at h0n; omega

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_writeVReg128_v1 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_v1 (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

end CryptoVerification.SpqrV1.Top.Recv
