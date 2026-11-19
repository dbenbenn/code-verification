/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Phase 2d Common Infrastructure (`0x6d6dc .. 0x6e660`): `V1State` Encoding Helpers

Defines exact-capacity callee specifications (`etvPolyEncoderExactSpecOf`, `etvPolyDecoderExactSpecOf`,
`etvEkSentCt1ReceivedEncodeSpecOf`, `etvCt1SentEncodeSpecOf`), relative callee address equations,
`SepWPp.call_cs` wrappers at `s.sp = sp - 144#64`, and the unpacked 22-byte `.rodata` jump-table
representation at `b + 0xa1480#64`.
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

@[simp, arm64_norm] theorem noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := by decide

@[simp, arm64_norm] theorem noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := by decide

@[simp, arm64_norm] theorem noneCap_add_two_beq_zero :
    (0xffffffffffffffff#64 + 2#64 == 0#64) = false := by decide

@[simp, arm64_norm] theorem noneCap_add_two_bne_zero :
    (0xffffffffffffffff#64 + 2#64 != 0#64) = true := by decide

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 ule_self_64 ult_self_64

/-! ## 1. Stack Split & Symbol Name Helpers for `V1State` Callees -/

abbrev etvPolyEncoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialEncoder, alloc::vec::Vec<u8>> [local#2]"

abbrev etvPolyDecoder2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::PolynomialDecoder, alloc::vec::Vec<u8>> [local#2]"

abbrev etvEkSentCt1ReceivedEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::EkSentCt1Received, alloc::vec::Vec<u8>> [local#2]"

abbrev etvCt1SentEncode2Name : String :=
  "prost::encoding::message::encode::<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent, alloc::vec::Vec<u8>> [local#2]"

theorem stackAt_callee_eq_chunkedEncodedLen {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (128 + resStack) ∗
        stackAt sp1 chunkedEncodedLenStack := by
  have h48 : chunkedEncodedLenStack = 48 := rfl
  have h := ProofLib.stackAt_split_bottom sp1 chunkedEncodedLenStack (128 + resStack)
    (by rw [h48]; omega)
  have heq : chunkedEncodedLenStack + (128 + resStack) = encodeToVecCalleeStackOf resStack := by
    rw [h48]; dsimp [encodeToVecCalleeStackOf]; omega
  simpa only [heq] using h

/-! ## 2. Callee Address Equations for `V1State` Phase (`0x6d6dc .. 0x6e660`) -/

/-- Generic 16-byte stack `encoded_len` specification shape (`unchunkedEncodedLenStack = polyEncodedLenStack = 16`). -/
@[expose] def leafEncLen16Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s.sp unchunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s0.sp unchunkedEncodedLenStack

/-- Generic 48-byte stack `encoded_len` specification shape (`chunkedEncodedLenStack = 48`). -/
@[expose] def leafEncLen48Spec {G M : Type} (reprAt : G → BitVec 64 → M → SepProp)
    (encLen : M → Nat) : Spec (PinnedEncLenGhost G M) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a ∧ encLen x.m < 2 ^ 64⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s.sp chunkedEncodedLenStack
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (encLen x.m) ∧ sf.trace = s0.trace⌝ ∗
      reprAt x.g x.a x.m ∗ stackAt s0.sp chunkedEncodedLenStack


structure EtvPolyEncoderGhost where
  encA : BitVec 64
  g : PolynomialEncoderPBGhost
  enc : PolynomialEncoder
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity specification for `encode<PolynomialEncoder> [local#2]` (`0x526d4`). -/
@[expose] def etvPolyEncoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyEncoderGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc).length ≤ x.cap.toNat⌝ ∗
      ProtoRepr.polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ProtoRepr.polynomialEncoderPBPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage PolynomialEncoder.encodeRaw 2#32 x.enc) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

structure EtvPolyDecoderGhost where
  tag : BitVec 32
  decA : BitVec 64
  g : PolynomialDecoderPBGhost
  dec : PolynomialDecoder
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity specification for `encode<PolynomialDecoder> [local#2]` (`0x52544`). -/
@[expose] def etvPolyDecoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvPolyDecoderGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (Proto.encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      ProtoRepr.polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ProtoRepr.polynomialDecoderPBPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage PolynomialDecoder.encodeRaw x.tag x.dec) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

structure EtvUnchunkedMsgEncodeGhost (G M : Type) where
  msgA : BitVec 64
  g : G
  m : M
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

@[expose] def etvEkSentCt1ReceivedEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked4PBGhost V1State.Unchunked.EkSentCt1Received) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat ∨
       x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length + 10 < 2 ^ 62)⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length +
            (Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr'
          (x.bs ++ Proto.encodeMessage V1State.Unchunked.EkSentCt1Received.encodeRaw 1#32 x.m)) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

@[expose] def etvCt1SentEncodeSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (EtvUnchunkedMsgEncodeGhost Unchunked5PBGhost V1State.Unchunked.Ct1Sent) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = x.v ∧
      (x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat ∨
       x.bs.length +
        (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length + 10 < 2 ^ 62)⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentPBPinnedAt A x.g x.msgA x.m ∗
      (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜x.cap.toNat ≤ cap'.toNat ∧
          (x.bs.length +
            (Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m).length ≤ x.cap.toNat →
              cap' = x.cap ∧ ptr' = x.ptr)⌝ ∗
        vecU8At A x.v cap' ptr'
          (x.bs ++ Proto.encodeMessage V1State.Unchunked.Ct1Sent.encodeRaw 1#32 x.m)) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Unpacked 22-byte (`11 × u16`) `.rodata` jump table at `roBase` (`b + 0xa1480#64`) as 22 `↦₈ᵣ` atoms. -/
@[expose] def encodeToVecJumpTableBytes8At (roBase : BitVec 64) : SepProp :=
  (roBase ↦₈ᵣ 0x00#8) ∗ ((roBase + 1#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 2#64) ↦₈ᵣ 0xd5#8) ∗ ((roBase + 3#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 4#64) ↦₈ᵣ 0x46#8) ∗ ((roBase + 5#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 6#64) ↦₈ᵣ 0x9c#8) ∗ ((roBase + 7#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 8#64) ↦₈ᵣ 0x14#8) ∗ ((roBase + 9#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 10#64) ↦₈ᵣ 0xee#8) ∗ ((roBase + 11#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 12#64) ↦₈ᵣ 0xfd#8) ∗ ((roBase + 13#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 14#64) ↦₈ᵣ 0xb5#8) ∗ ((roBase + 15#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 16#64) ↦₈ᵣ 0x25#8) ∗ ((roBase + 17#64) ↦₈ᵣ 0x01#8) ∗
  ((roBase + 18#64) ↦₈ᵣ 0x2d#8) ∗ ((roBase + 19#64) ↦₈ᵣ 0x00#8) ∗
  ((roBase + 20#64) ↦₈ᵣ 0x16#8) ∗ ((roBase + 21#64) ↦₈ᵣ 0x01#8)

theorem encodeToVecJumpTableBytes_eq8 (roBase : BitVec 64) :
    (roBase ↦ᵣ encodeToVecJumpTableBytes) = encodeToVecJumpTableBytes8At roBase := by
  unfold encodeToVecJumpTableBytes encodeToVecJumpTableBytes8At
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

end CryptoVerification.SpqrV1.Prost.EncodeToVec
