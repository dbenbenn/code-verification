/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.Repr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EpochEncodedLen -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Decodes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint2Base
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateHeader
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesVnEncode
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: `Option<Inner>` Header Steps & Jump-Table Setup

Unpacked `.rodata` jump table at `b + 0x9d506#64`, `[local#1]` callee address and `s.sp = sp`
call wrappers, `Option<pq_ratchet_state::Inner>` header steps (`0x32058..0x32234`), and
`StepSendInnerStateAt6616` for `spqr::send::<HookRng>`.
-/

public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet (spqrSendName AllocContracts)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth (authEncodeLocal1Name authEncodePinnedSpecOf)
open CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.Prost.EncodeToVec

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Unpacked `.rodata` Jump Table at `b + 0x9d506#64` and `HasSendEncodeJumpTableAddr` -/

/-- Unpacked 11-entry (`22 × u8`) `.rodata` jump table at `roBase` (`b + 0x9d506#64`) as `↦₈ᵣ`
    atoms. -/
@[expose] def spqrSendEncodeJumpTableBytesAt (roBase : BitVec 64) : SepProp :=
  (roBase ↦₈ᵣ 0x00#8) ∗ ((roBase + 1#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 2#64) ↦₈ᵣ 0xef#8) ∗ ((roBase + 3#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 4#64) ↦₈ᵣ 0x56#8) ∗ ((roBase + 5#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 6#64) ↦₈ᵣ 0xb3#8) ∗ ((roBase + 7#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 8#64) ↦₈ᵣ 0x20#8) ∗ ((roBase + 9#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 10#64) ↦₈ᵣ 0x0b#8) ∗ ((roBase + 11#64) ↦₈ᵣ 0x02#8) ∗
  ((roBase + 12#64) ↦₈ᵣ 0x1b#8) ∗ ((roBase + 13#64) ↦₈ᵣ 0x02#8) ∗
  ((roBase + 14#64) ↦₈ᵣ 0xce#8) ∗ ((roBase + 15#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 16#64) ↦₈ᵣ 0x46#8) ∗ ((roBase + 17#64) ↦₈ᵣ 0x02#8) ∗
  ((roBase + 18#64) ↦₈ᵣ 0x3b#8) ∗ ((roBase + 19#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 20#64) ↦₈ᵣ 0x36#8) ∗ ((roBase + 21#64) ↦₈ᵣ 0x02#8)

theorem spqrSendEncodeJumpTableBytes_eq (roBase : BitVec 64) :
    (roBase ↦ᵣ spqrSendEncodeJumpTableBytes) = spqrSendEncodeJumpTableBytesAt roBase := by
  unfold spqrSendEncodeJumpTableBytes spqrSendEncodeJumpTableBytesAt
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  Prost.EncodeToVec.noneCap2_add_two_beq_zero Prost.EncodeToVec.noneCap2_add_two_bne_zero
  ProtoRepr.noneCap_add_two_beq_zero ProtoRepr.noneCap_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

end CryptoVerification.SpqrV1.Top.Send
