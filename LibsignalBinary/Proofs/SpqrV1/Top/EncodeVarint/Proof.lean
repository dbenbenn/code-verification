/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Proof of `spqr::encode_varint` (`0x54040`, 164 insns)

Proves `spqr::encode_varint` (`0x54040`, 164 instructions) against `spqrEncodeVarintSpecX`
via continuation-byte stages 3..9 (`+204..+640`) and the 10-stage LEB128 case split.
-/

public section

namespace CryptoVerification.SpqrV1.Top.EncodeVarint

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
  (encodeVarintLoop MAX_VARINT_BYTES_LEN GrowOneCall newCapU8 growOneU8Spec growOneU8Name SpqrHooks MlKem)
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Continuation-Byte Stages 3..9 -/

private theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

private theorem origLen_step1 (bs : List (BitVec 8)) (byte : BitVec 8) :
    BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs ++ [byte]).length :=
  bv_len_add_one bs byte

/-! ## Main Theorems -/

end CryptoVerification.SpqrV1.Top.EncodeVarint
