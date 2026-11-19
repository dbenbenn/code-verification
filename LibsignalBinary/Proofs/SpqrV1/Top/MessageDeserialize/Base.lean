/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize.Defs
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp

/-!
# Base Step Lemmas for `<Message>::deserialize`

Symbolic execution of the varint loop, post-varint 32-byte chunk copy, and shared `Ok` / `Err`
epilogues for `<spqr::v1::chunked::states::Message>::deserialize` (`0x5f434..0x5f780`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.MessageDeserialize

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.ChainFromVNNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem sp_sub_144_aligned (s0 : State) (h : s0.spAligned = true) :
    ((s0.sp - 144#64) &&& 15#64 == 0#64) = true := by
  simp only [State.spAligned, beq_iff_eq] at h ⊢
  generalize s0.sp = sp at h ⊢
  revert sp h; bv_kernel

/-- High callee-saved registers `x23..x28` and `calleeSavedVRegs` untouched by
    `<Message>::deserialize`. -/
@[expose] def DeserHighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem rest2_lt32_of_ult {tag : BitVec 8} {pre₁ rest2 : List (BitVec 8)}
    (hlt : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63)
    (hult : (BitVec.ofNat 64 (tag :: (pre₁ ++ rest2)).length).ult (BitVec.ofNat 64 pre₁.length + 33#64) = true) :
    rest2.length < 32 := by
  simp [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat] at hlt hult
  omega

theorem rest2_ge32_of_not_ult {tag : BitVec 8} {pre₁ rest2 : List (BitVec 8)}
    (hlt : (tag :: (pre₁ ++ rest2)).length < 2 ^ 63)
    (hult : ¬(BitVec.ofNat 64 (tag :: (pre₁ ++ rest2)).length).ult (BitVec.ofNat 64 pre₁.length + 33#64) = true) :
    ¬ rest2.length < 32 := by
  simp [BitVec.ult, BitVec.toNat_add, BitVec.toNat_ofNat] at hlt hult
  omega

theorem index_gt65535_of_lsr16 {index : BitVec 64}
    (hne : ¬index >>> 16 = 0#64) :
    index.toNat > 65535 := by
  bv_omega

theorem index_le65535_of_lsr16 {index : BitVec 64}
    (heq : index >>> 16 = 0#64) :
    ¬(index.toNat > 65535) := by
  bv_omega

theorem decodeVarintLoop_stop (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hb : b &&& 0x80#8 = 0#8) :
    decodeVarintLoop j out (b :: rest2) =
      some (out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j)), rest2) := by
  simp [decodeVarintLoop, hb]

theorem decodeVarintLoop_cont_end (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hj : j < 10) (hb : b &&& 0x80#8 ≠ 0#8) (hend : min (j + 1 + rest2.length) 10 ≤ j + 1) :
    decodeVarintLoop j out (b :: rest2) = none := by
  unfold decodeVarintLoop
  simp only [hb, ↓reduceIte, MAX_VARINT_BYTES_LEN]
  by_cases h10 : j + 1 = 10
  · simp [h10]
  · simp only [h10, ↓reduceIte]
    cases rest2 with
    | nil => rfl
    | cons b2 tl =>
      simp only [List.length_cons] at hend
      omega

theorem decodeVarintLoop_cont_step (j : Nat) (out : BitVec 64) (b : BitVec 8) (rest2 : List (BitVec 8))
    (hj : j + 1 < 10) (hb : b &&& 0x80#8 ≠ 0#8) :
    decodeVarintLoop j out (b :: rest2) =
      decodeVarintLoop (j + 1) (out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j))) rest2 := by
  have hne : j + 1 ≠ MAX_VARINT_BYTES_LEN := by unfold MAX_VARINT_BYTES_LEN; omega
  simp [decodeVarintLoop, hb, hne]

abbrev sbfm8Val (b : BitVec 8) : BitVec 64 :=
  BitVec.zeroExtend 64
    (BitVec.truncate 32
      (BitVec.zeroExtend 64 b >>> 0 &&& 255#64 |||
        (if b.getLsbD 7 = true then 18446744073709551615#64 else 0#64) &&& 18446744073709551360#64))

theorem sbfm8_bit31_nz {b : BitVec 8}
    (h : (sbfm8Val b).getLsbD 31 = true) :
    b &&& 0x80#8 ≠ 0#8 := by
  unfold sbfm8Val at h
  bv_bits

theorem sbfm8_bit31_z {b : BitVec 8}
    (h : ¬(sbfm8Val b).getLsbD 31 = true) :
    b &&& 0x80#8 = 0#8 := by
  unfold sbfm8Val at h
  bv_bits

theorem varint_orr_lsl_eq (j : Nat) (hj : j < 10) (out : BitVec 64) (b : BitVec 8) :
    ((b.zeroExtend 64 &&& 127#64) <<< ((BitVec.ofNat 64 (7 * j)).toNat % 64)) ||| out =
      out ||| ((b &&& 0x7f#8).zeroExtend 64 <<< (7 * j)) := by
  have hmod : (BitVec.ofNat 64 (7 * j)).toNat % 64 = 7 * j := by
    rw [BitVec.toNat_ofNat]
    omega
  have hand : b.zeroExtend 64 &&& 127#64 = (b &&& 0x7f#8).zeroExtend 64 := by bv_bits
  rw [hmod, hand, BitVec.or_comm]

theorem varint_cs_true {j n : Nat} (hj : j < 10)
    (h : (BitVec.ofNat 64 (min (j + 1 + n) 10)).ule (BitVec.ofNat 64 (j + 1)) = true) :
    min (j + 1 + n) 10 ≤ j + 1 := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem varint_cs_false {j n : Nat} (hj : j < 10)
    (h : ¬(BitVec.ofNat 64 (min (j + 1 + n) 10)).ule (BitVec.ofNat 64 (j + 1)) = true) :
    j + 1 < min (j + 1 + n) 10 := by
  simp [BitVec.ule, BitVec.toNat_ofNat] at h
  omega

theorem varint_pre_eq_zero {tag : BitVec 8} {rest : List (BitVec 8)}
    (hlt : (tag :: rest).length < 2 ^ 63)
    (heq : BitVec.ofNat 64 (tag :: rest).length = 1#64) :
    rest = [] := by
  have hlen : rest.length = 0 := by
    have h1 : (BitVec.ofNat 64 (tag :: rest).length).toNat = 1 := by rw [heq]; rfl
    simp [BitVec.toNat_ofNat] at hlt h1
    omega
  exact List.eq_nil_of_length_eq_zero hlen

theorem varint_pre_ne_zero {tag : BitVec 8} {rest : List (BitVec 8)}
    (hne : ¬BitVec.ofNat 64 (tag :: rest).length = 1#64) :
    rest ≠ [] := by
  intro hnil
  subst hnil
  exact hne rfl

theorem varint_pre_csel_eq {tag : BitVec 8} {rest : List (BitVec 8)}
    (hlt : (tag :: rest).length < 2 ^ 63) :
    (if (BitVec.ofNat 64 (tag :: rest).length - 1#64).ult 10#64 = true then
      BitVec.ofNat 64 (tag :: rest).length - 1#64
    else 10#64) = BitVec.ofNat 64 (min rest.length 10) := by
  have hsub : BitVec.ofNat 64 (tag :: rest).length - 1#64 = BitVec.ofNat 64 rest.length := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat] at hlt ⊢
    omega
  rw [hsub]
  have hlt' : rest.length < 2 ^ 63 := by simp at hlt; omega
  by_cases h10 : rest.length < 10
  · have hult : (BitVec.ofNat 64 rest.length).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    simp [hult, Nat.min_eq_left (by omega : rest.length ≤ 10)]
  · have hult : ¬(BitVec.ofNat 64 rest.length).ult 10#64 = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    simp [hult, Nat.min_eq_right (by omega : 10 ≤ rest.length)]

end CryptoVerification.SpqrV1.Top.MessageDeserialize

