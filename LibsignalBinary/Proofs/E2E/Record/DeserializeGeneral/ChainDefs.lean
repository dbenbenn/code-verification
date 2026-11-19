/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Base
public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs

/-!
# Loop-Head Invariant and Step Definitions for General `message::merge<Chain>`

Defines the loop-head cut invariant `ChainLoopG` at `+0x120` and return postcondition `ChainRetG`
for `prost::encoding::message::merge::<Chain>` (`0x3974`) on an in-scope `ChainG`:
* Registers at `+0x120`: `x19 = bufRef`, `x20 = a`, `x24 = tail.length`, `w21 = 98`, `w22 = 97`,
  `x25 = sp + 8`, `w26 = 1`, `x29 = sp + 0xa0`, `sp = s0.sp - 0x100`.
-/

public section

namespace CryptoVerification.E2E.Record.DeserializeGeneral

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed

theorem chainField_tag_cases (fl : ChainField) :
    (fl.tag = 1 ∨ fl.tag = 2) ∨ fl.tag = 3 ∨ fl.tag = 4 := by
  cases fl <;> simp [ChainField.tag]

theorem len_cons_sub_one_seedChain (b0 : BitVec 8) (bs1 : List (BitVec 8)) :
    BitVec.ofNat 64 (b0 :: bs1).length - 1#64 = BitVec.ofNat 64 bs1.length := by
  simp only [List.length_cons]
  bv_omega

theorem ule_ofNat_of_gt_false_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 k) = false := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_false_iff_not]
  omega

theorem ult_ofNat_of_gt_true_seedChain {n k : Nat} (hgt : k < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 k).ult (BitVec.ofNat 64 n) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    decide_eq_true_eq]
  omega

theorem pbBytes_lt128_eq_seedChain (tag : Nat) (_htag : tag < 16)
    (b : List (BitVec 8)) (_hb : b.length < 128) :
    pbBytes tag b = BitVec.ofNat 8 (tag * 8 + 2) :: BitVec.ofNat 8 b.length :: b :=
  rfl

theorem pbBytes_pointsTo_combine_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    (ptr ↦₈ BitVec.ofNat 8 (tag * 8 + 2)) ∗ ((ptr + 1#64) ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) =
      (ptr ↦ₛ pbBytes tag b) := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb, pointsToBytes_cons]
  rfl

theorem pbBytes_ptr_advance_seedChain (tag : Nat) (htag : tag < 16)
    (ptr : BitVec 64) (b : List (BitVec 8)) (hb : b.length < 128) :
    ptr + 1#64 + BitVec.ofNat 64 (b.length + 1) =
      ptr + BitVec.ofNat 64 (pbBytes tag b).length := by
  rw [pbBytes_lt128_eq_seedChain tag htag b hb]
  simp only [List.length_cons]
  bv_omega

end CryptoVerification.E2E.Record.DeserializeGeneral
