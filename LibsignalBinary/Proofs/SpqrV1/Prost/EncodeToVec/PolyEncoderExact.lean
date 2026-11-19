/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoderBase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncodedLen
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeRepeated2
import LibsignalBinary.Proofs.SpqrV1.Varint.EncodeVarint4
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.PolyEncoder -- shake: keep

/-!
# Exact-Capacity Specifications and Proofs for `PolynomialEncoder::encode` and `PolynomialDecoder::encode`

In `Poly.protoPolynomialEncoderPinnedAt` and `Poly.protoPolynomialDecoderPinnedAt`, the `Vec<Vec<u8>>`
headers carry the Rust `Vec` invariant `cap.toNat * 24 < 2 ^ 63`, which yields `pts.length * 24 < 2 ^ 63`
and `polys.length * 24 < 2 ^ 63` (hence `< 2 ^ 59`).

This module lifts `encode_repeated [local#2]` from `< 2 ^ 58` to `< 2 ^ 59` (reusing
`EncodeRepeated2.step_iter` and `EncodeRepeated2.step_latch_zero` directly) and proves exact-capacity
specifications for `PolynomialEncoder::encode [local#2]` and
`PolynomialDecoder::encode [local#2]` with no external `pts.length` / `polys.length`
preconditions.
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

/-! ## 1. `encode_repeated [local#2]` with `elems.length < 2 ^ 59` -/

theorem setup_x24_eq_59 {n : Nat} (hlt : n < 2 ^ 59) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 3 =
      BitVec.ofNat 64 (24 * n) := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2n : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h3n : (BitVec.ofNat 64 (3 * n)).toNat = 3 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h24n : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : BitVec.ofNat 64 n <<< 1 = BitVec.ofNat 64 (2 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, hn, h2n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
    omega
  have h2 : BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 (3 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, hn, h2n, h3n, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h1, h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, h3n, h24n, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

theorem latch_sub24_eq_59 (k : Nat) (hk : k + 1 < 2 ^ 59) :
    BitVec.ofNat 64 (24 * (k + 1)) - 24#64 = BitVec.ofNat 64 (24 * k) := by
  have hk_toNat : (BitVec.ofNat 64 (24 * (k + 1))).toNat = 24 * (k + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hk0_toNat : (BitVec.ofNat 64 (24 * k)).toNat = 24 * k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hle : (24#64 : BitVec 64) ≤ BitVec.ofNat 64 (24 * (k + 1)) := by
    rw [BitVec.le_def, hk_toNat]
    change 24 ≤ 24 * (k + 1)
    omega
  rw [BitVec.toNat_sub_of_le hle, hk_toNat, hk0_toNat]
  change 24 * (k + 1) - 24 = 24 * k
  omega

@[expose] def encodeRepeated59SpecOf (resStack : Nat) (A : RustAlloc) : Spec EncodeRepeatedGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = BitVec.ofNat 32 x.tag ∧
      s.readReg64 .x1 = x.base ∧
      s.readReg64 .x2 = BitVec.ofNat 64 x.elems.length ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag ∧ x.tag < 2 ^ 29 ∧
      x.elems.length < 2 ^ 59 ∧
      (x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length ≤ x.cap.toNat ∨
        x.bs.length + (encodeRepeatedBytes x.tag (x.elems.map Prod.snd)).length + 10 < 2 ^ 62)⌝ ∗
      repeatedBytesSliceAt x.base x.elems ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (encodeRepeatedStackOf resStack)
  post := (encodeRepeatedSpecOf resStack A).post
  onPanic := (encodeRepeatedSpec A).onPanic

private theorem cap_beq_len_false_of_lt {cap : BitVec 64} {len : Nat}
    (hlt : len < cap.toNat) :
    (cap == BitVec.ofNat 64 len) = false := by
  have hcap : cap.toNat < 2 ^ 64 := BitVec.isLt cap
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

/-! ## 3. Exact-Capacity `PolynomialEncoder::encode [local#2]` -/

@[expose] def encodePolyEncoderExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EncodePolyEncoderPinnedGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.encA ∧
      s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodePolyEncoderMsg x.enc).length ≤ x.cap.toNat⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp (msgEnc48RepeatedStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      Poly.protoPolynomialEncoderPinnedAt A x.g x.encA x.enc ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodePolyEncoderMsg x.enc) ∗
      A.pool ∗ stackAt s0.sp (msgEnc48RepeatedStackOf resStack)
  onPanic := fun _ s0 sf => msgEncOnPanic s0 sf

end CryptoVerification.SpqrV1.Prost.EncodeToVec
