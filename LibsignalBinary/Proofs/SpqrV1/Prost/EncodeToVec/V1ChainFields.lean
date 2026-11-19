/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.VersionNegPhase
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2c (`0x6d4cc .. 0x6d6dc`): `Option<Chain>` Encoding

Proves symbolic execution of the inline `Option<Chain>` encoding phase
(`+1212 .. +1740`, `0x6d4cc .. 0x6d6dc`) in
`<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec`,
appending `Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain` to
`vecU8At A (sp - 120#64) (BitVec.ofNat 64 (pqRatchetStatePBEncodedLen st)) ptr bs` and reaching
`entry + 1740#64` (`0x6d6dc`).
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Pure Protobuf Encoding Bridge Lemmas for `ChainPB` and `ChainEpochPB` -/

theorem encodeKey_1_varint :
    Proto.encodeKey 1#32 .varint = [0x08#8] := by decide

theorem encodeKey_2_lengthDelimited :
    Proto.encodeKey 2#32 .lengthDelimited = [0x12#8] := by decide

theorem encodeKey_3_lengthDelimited :
    Proto.encodeKey 3#32 .lengthDelimited = [0x1a#8] := by decide

theorem encodeKey_4_lengthDelimited :
    Proto.encodeKey 4#32 .lengthDelimited = [0x22#8] := by decide

theorem encodeKey_5_varint :
    Proto.encodeKey 5#32 .varint = [0x28#8] := by decide

theorem encodeInt32Field_1_eq (v : BitVec 32) :
    Proto.encodeInt32Field 1#32 v =
      if v == 0#32 then []
      else [0x08#8] ++ Proto.encodeVarint (v.signExtend 64) := by
  unfold Proto.encodeInt32Field
  rw [encodeKey_1_varint]

theorem encodeUint64Field_2_eq (v : BitVec 64) :
    Proto.encodeUint64Field 2#32 v =
      if v == 0#64 then []
      else [0x10#8] ++ Proto.encodeVarint v := by
  unfold Proto.encodeUint64Field
  rw [encodeKey_2_varint]

theorem encodeUint64Field_5_eq (v : BitVec 64) :
    Proto.encodeUint64Field 5#32 v =
      if v == 0#64 then []
      else [0x28#8] ++ Proto.encodeVarint v := by
  unfold Proto.encodeUint64Field
  rw [encodeKey_5_varint]

theorem encodeBytesField_4_eq (bs : List (BitVec 8)) :
    Proto.encodeBytesField 4#32 bs =
      if bs.isEmpty then []
      else [0x22#8] ++ Proto.encodeVarint (BitVec.ofNat 64 bs.length) ++ bs := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  rw [encodeKey_4_lengthDelimited]

theorem encodeMessage_epoch_3_eq (ep : ChainEpochPB) :
    Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep =
      [0x1a#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chainEpochPBEncodedLen ep)) ++
        Proto.encodeOptMessage EpochDirectionPB.encodeRaw 1#32 ep.send ++
        Proto.encodeOptMessage EpochDirectionPB.encodeRaw 2#32 ep.recv := by
  have hlen : (ChainEpochPB.encodeRaw ep).length = chainEpochPBEncodedLen ep :=
    chainEpochPBEncodedLen_eq_proto ep
  dsimp only [Proto.encodeMessage]
  rw [encodeKey_3_lengthDelimited, hlen]
  dsimp only [ChainEpochPB.encodeRaw]
  simp only [List.append_assoc]

theorem encodeOptMessage_chain_some (ch : ChainPB) :
    Proto.encodeOptMessage ChainPB.encodeRaw 2#32 (some ch) =
      [0x12#8] ++ Proto.encodeVarint (BitVec.ofNat 64 (chainPBEncodedLen ch)) ++
        Proto.encodeInt32Field 1#32 ch.direction ++
        Proto.encodeUint64Field 2#32 ch.currentEpoch ++
        Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++
        Proto.encodeBytesField 4#32 ch.nextRoot ++
        Proto.encodeUint64Field 5#32 ch.sendEpoch ++
        Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params := by
  have hlen : (ChainPB.encodeRaw ch).length = chainPBEncodedLen ch :=
    chainPBEncodedLen_eq_proto ch
  dsimp only [Proto.encodeOptMessage, Proto.encodeMessage]
  rw [encodeKey_2_lengthDelimited, hlen]
  dsimp only [ChainPB.encodeRaw, Proto.encodeOptMessage, Proto.encodeMessage]
  simp only [List.append_assoc]

theorem optChainPB_encode_len_le (st : PqRatchetState) :
    (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 st.versionNegotiation).length +
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 st.chain).length ≤
      pqRatchetStatePBEncodedLen st := by
  rw [optVersionNegotiationPBFieldEncodedLen_eq_proto 1#32 st.versionNegotiation ⟨by decide, by decide⟩,
    optChainPBFieldEncodedLen_eq_proto 2#32 st.chain ⟨by decide, by decide⟩]
  unfold pqRatchetStatePBEncodedLen
  omega

/-- First word (`[a]`) of `optEpochDirectionPBPinnedAt A g a opt`. -/
@[expose] def optEpochDirCap (g : EpochDirectionPBGhost) : Option EpochDirectionPB → BitVec 64
  | none => noneCap
  | some _ => g.next.cap

/-- Remainder (`48` bytes at `a + 8#64`) of `optEpochDirectionPBPinnedAt A g a opt` after
splitting off `(a ↦₆₄ optEpochDirCap g opt)`. -/
@[expose] def optEpochDirRest (A : RustAlloc) (g : EpochDirectionPBGhost) (a : BitVec 64) :
    Option EpochDirectionPB → SepProp
  | none => memRegion (a + 8#64) 48
  | some d =>
    ((a + 8#64) ↦₆₄ g.next.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
      EncodedLen.vecU8Buf A g.next.cap g.next.ptr d.next ∗
      vecU8At A (a + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
      ((a + 0x30#64) ↦₃₂ d.ctr) ∗
      memRegion (a + 0x34#64) 4

theorem optEpochDirectionPBPinnedAt_eq (A : RustAlloc) (g : EpochDirectionPBGhost)
    (a : BitVec 64) (opt : Option EpochDirectionPB) :
    optEpochDirectionPBPinnedAt A g a opt =
      (a ↦₆₄ optEpochDirCap g opt) ∗ optEpochDirRest A g a opt := by
  cases opt with
  | none => rfl
  | some d =>
    dsimp only [optEpochDirectionPBPinnedAt, epochDirectionPBPinnedAt,
      optEpochDirCap, optEpochDirRest]
    rw [EncodedLen.vecU8At_eq_header_sep_buf, vecHeader]
    ac_rfl

theorem optEpochDirRest_cap_bounds {A : RustAlloc} {g : EpochDirectionPBGhost} {p : BitVec 64}
    {opt : Option EpochDirectionPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEpochDirRest A g p opt ∗ R) :
    (optEpochDirCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEpochDirCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp only [optEpochDirCap, Option.isSome_none, Bool.not_false]
    exact ⟨by decide, by decide⟩
  | some d =>
    simp only [optEpochDirRest] at hm
    have hbuf : m ⊨ EncodedLen.vecU8Buf A g.next.cap g.next.ptr d.next ∗
        (((p + 8#64) ↦₆₄ g.next.ptr) ∗
         ((p + 16#64) ↦₆₄ BitVec.ofNat 64 d.next.length) ∗
         vecU8At A (p + 0x18#64) g.prev.cap g.prev.ptr d.prev ∗
         ((p + 0x30#64) ↦₃₂ d.ctr) ∗
         memRegion (p + 0x34#64) 4 ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := EncodedLen.vecU8Buf_bounds hbuf
    dsimp only [optEpochDirCap, Option.isSome_some, Bool.not_true]
    exact ⟨EncodedLen.cap_add_one_beq_zero_false hcap, EncodedLen.cap_add_one_bne_zero_true hcap⟩

/-! ## 2. Sub-Step Lemmas for `ChainPB` Scalar & Bytes Fields -/



end CryptoVerification.SpqrV1.Prost.EncodeToVec
