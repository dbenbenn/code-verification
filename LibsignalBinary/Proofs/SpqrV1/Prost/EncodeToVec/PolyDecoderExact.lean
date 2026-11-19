/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyEncoderExact -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoderBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyDecoder -- shake: keep

/-!
# Exact-Capacity Specification and Proof for `PolynomialDecoder::encode [local#2]` (`0x52544`)

Proves `encodePolyDecoderExactSpecOf` for `PolynomialDecoder::encode [local#2]` under exact
output capacity (`x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat`),
discharging the unreachable reallocation branch without external `polys.length` bounds.
-/

public section
namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
  CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalProtoCodec
  CryptoVerification.LibsignalTripleRatchet.Prost
  CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
  CryptoVerification.CodeLayout
  CryptoVerification.LibsignalSpqrV1
  CryptoVerification.SpqrV1.Alloc
  CryptoVerification.SpqrV1.Varint
  CryptoVerification.SpqrV1.ProtoRepr
  CryptoVerification.SpqrV1.Poly
  CryptoVerification.SpqrV1.Prost.MessageEncode
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

private theorem cap_beq_len_false_of_lt {cap : BitVec 64} {len : Nat}
    (hlt : len < cap.toNat) :
    (cap == BitVec.ofNat 64 len) = false := by
  have hcap : cap.toNat < 2 ^ 64 := BitVec.isLt cap
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

/-! ## Exact-Capacity `PolynomialDecoder::encode [local#2]` (`0x52544`) -/

@[expose] def encodePolyDecoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyDecoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg64 .x1 = x.decA ∧
      s.readReg64 .x2 = x.v ∧
      x.bs.length + (encodePolyDecoderMsg x.tag x.dec).length ≤ x.cap.toNat⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialDecoderPinnedAt A x.g x.decA x.dec ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyDecoderMsg x.tag x.dec) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

end CryptoVerification.SpqrV1.Prost.EncodeToVec
