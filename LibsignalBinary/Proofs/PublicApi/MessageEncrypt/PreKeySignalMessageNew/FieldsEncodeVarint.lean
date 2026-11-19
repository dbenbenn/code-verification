/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintBase
import ProofLib.ProgramReflection.SortedFresh
import ProofLib.SepLogic.WPp

/-!
# Multi-Byte Stages and No-Grow Contract for `encode_varint`

Continuation stages 4–9 and top-level proof `encodeVarintNoGrow_ok` for
`prost::encoding::varint::encode_varint::<Vec<u8>>` (`0x30a0`) when spare capacity suffices.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open EncodeVarintNorm

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem encodeVarint_inv_done {k : Nat} {v : BitVec 64} {curBs bs : List (BitVec 8)} {val : BitVec 64}
    (h : v.ult 128#64 = true)
    (hinv : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val) :
    curBs ++ [v.setWidth 8] = bs ++ encodeVarint val := by
  rw [← hinv, encodeVarintAux_of_ult h]

theorem encodeVarint_inv_next {k : Nat} {v : BitVec 64} {curBs bs : List (BitVec 8)} {val : BitVec 64}
    (h : v.ult 128#64 = false)
    (hinv : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val) :
    (curBs ++ [varintContByte v]) ++ encodeVarintAux k (v >>> 7) = bs ++ encodeVarint val := by
  rw [List.append_assoc, List.singleton_append, ← encodeVarintAux_of_not_ult h, hinv]

@[expose] def encodeVarintNoGrowSpec (A : RustAlloc) : Spec EncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗ stackAt s.sp encodeVarintStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ encodeVarint x.val) ∗
      A.pool ∗ stackAt s0.sp encodeVarintStack

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
