/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.Defs
import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import ProofLib.GenDecodes

/-!
# Verification of `uuid::parser::decode_hex32`

Verifies the 32-nibble hexadecimal decoder `uuid::parser::decode_hex32` against the pure
`decodeHex32` specification.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure nibble and hex-pair lemmas -/

@[expose] def rawNibble (c : BitVec 8) : BitVec 8 :=
  if (9#32).ult (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 c - 48#32) &&& 255#64)) = true then
    BitVec.truncate 8 (BitVec.truncate 32 (BitVec.zeroExtend 64 c ||| 137438953504#64) - 87#32)
  else BitVec.truncate 8 (BitVec.zeroExtend 32 c - 48#32)

@[expose] def rawInvalid (c : BitVec 8) : BitVec 64 :=
  if (250#32).ule (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 c ||| 137438953504#64) - 103#32) &&& 255#64)) = true then
    0#64
  else if (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 c - 48#32) &&& 255#64)).ule 9#32 = true then
    0#64
  else 1#64

@[expose] def stepAcc (acc : BitVec 64) (c : BitVec 8) : BitVec 64 :=
  BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 acc) ||| rawInvalid c))

@[expose] def isHexByte (c : BitVec 8) : Bool :=
  decide (c - 0x30#8 < 10#8) || decide ((c ||| 0x20#8) - 0x61#8 < 6#8)

theorem rawInvalid_eq (c : BitVec 8) :
    rawInvalid c = if isHexByte c then 0#64 else 1#64 := by
  revert c
  unfold rawInvalid isHexByte
  decide +kernel

theorem rawNibble_digit (c : BitVec 8) (h : c - 0x30#8 < 10#8) :
    rawNibble c = c - 0x30#8 := by
  revert c
  unfold rawNibble
  decide +kernel

theorem rawNibble_alpha (c : BitVec 8) (h1 : ¬ (c - 0x30#8 < 10#8))
    (h2 : (c ||| 0x20#8) - 0x61#8 < 6#8) :
    rawNibble c = (c ||| 0x20#8) - 0x61#8 + 10#8 := by
  revert c
  unfold rawNibble
  decide +kernel

theorem hexNibble_eq (c : BitVec 8) :
    hexNibble c = if isHexByte c then some (rawNibble c) else none := by
  unfold hexNibble isHexByte
  by_cases h1 : c - 0x30#8 < 10#8
  · simp [h1, rawNibble_digit c h1]
  · by_cases h2 : (c ||| 0x20#8) - 0x61#8 < 6#8
    · simp [h1, h2, rawNibble_alpha c h1 h2]
    · simp [h1, h2]

theorem stepAcc_one (c : BitVec 8) : stepAcc 1#64 c = 1#64 := by
  unfold stepAcc
  rw [rawInvalid_eq]
  cases isHexByte c <;> rfl

theorem stepAcc_zero (c : BitVec 8) :
    stepAcc 0#64 c = if isHexByte c then 0#64 else 1#64 := by
  unfold stepAcc
  rw [rawInvalid_eq]
  cases isHexByte c <;> rfl

theorem foldl_stepAcc_one (bs : List (BitVec 8)) :
    bs.foldl stepAcc 1#64 = 1#64 := by
  induction bs with
  | nil => rfl
  | cons c rest ih => simp only [List.foldl_cons, stepAcc_one, ih]

theorem foldl_stepAcc_zero (bs : List (BitVec 8)) :
    bs.foldl stepAcc 0#64 = if bs.all isHexByte then 0#64 else 1#64 := by
  induction bs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons, List.all_cons, stepAcc_zero]
    rcases Bool.eq_false_or_eq_true (isHexByte c) with hc | hc
    · simp only [hc, Bool.true_and, ↓reduceIte, ih]
    · simp only [hc, Bool.false_and]; exact foldl_stepAcc_one rest

@[expose] def rawCombine (hi lo : BitVec 8) : BitVec 8 :=
  (hi <<< 4) ||| lo

theorem rawCombine_step_eq (hi lo : BitVec 8) :
    BitVec.zeroExtend 8
      (BitVec.zeroExtend 64 lo ||| BitVec.zeroExtend 64 (BitVec.zeroExtend 32 hi <<< 4)) =
    rawCombine hi lo := by
  unfold rawCombine
  ext i hi8
  simp
  exact Bool.or_comm _ _

@[expose] def decodeNibbles : List (BitVec 8) → List (BitVec 8)
  | hi :: lo :: rest => rawCombine hi lo :: decodeNibbles rest
  | _ => []

theorem decodeHex_cons2 (hi lo : BitVec 8) (rest : List (BitVec 8)) :
    decodeHex (hi :: lo :: rest) =
      if isHexByte hi && isHexByte lo then
        (decodeHex rest).map (fun r => rawCombine (rawNibble hi) (rawNibble lo) :: r)
      else none := by
  conv => lhs; unfold decodeHex
  unfold rawCombine
  rw [hexNibble_eq hi, hexNibble_eq lo]
  cases isHexByte hi <;> cases isHexByte lo <;> cases decodeHex rest <;> rfl

theorem decodeHex_pair_step (hi lo : BitVec 8) (rest : List (BitVec 8))
    (ih : decodeHex rest = if rest.all isHexByte then some (decodeNibbles (rest.map rawNibble)) else none) :
    decodeHex (hi :: lo :: rest) =
      if (hi :: lo :: rest).all isHexByte then
        some (decodeNibbles ((hi :: lo :: rest).map rawNibble))
      else none := by
  rw [decodeHex_cons2, ih]
  simp only [List.all_cons, List.map_cons, decodeNibbles]
  cases isHexByte hi <;> cases isHexByte lo <;> cases rest.all isHexByte <;> rfl

theorem decodeHex_even : ∀ (k : Nat) (bs : List (BitVec 8)), bs.length = 2 * k →
    decodeHex bs =
      if bs.all isHexByte then some (decodeNibbles (bs.map rawNibble)) else none
  | 0, [], _ => rfl
  | k + 1, hi :: lo :: rest, h =>
    decodeHex_pair_step hi lo rest (decodeHex_even k rest (by simp at h; omega))

theorem length_decodeNibbles : ∀ (k : Nat) (ns : List (BitVec 8)), ns.length = 2 * k →
    (decodeNibbles ns).length = k
  | 0, [], _ => rfl
  | k + 1, _ :: _ :: rest, h => by
    simp only [decodeNibbles, List.length_cons]
    rw [length_decodeNibbles k rest (by simp at h; omega)]

theorem decodeHex32_of_length_32 {hex : List (BitVec 8)} (h : hex.length = 32) :
    decodeHex32 hex =
      if hex.all isHexByte then
        some ⟨decodeNibbles (hex.map rawNibble),
          length_decodeNibbles 16 (hex.map rawNibble) (by simp [h])⟩
      else none := by
  unfold decodeHex32
  rw [decodeHex_even 16 hex h]
  have hlen : (decodeNibbles (hex.map rawNibble)).length = 16 :=
    length_decodeNibbles 16 (hex.map rawNibble) (by simp [h])
  cases hex.all isHexByte
  · rfl
  · simp [Option.bind, hlen]

/-! ## Loop invariant and step lemmas -/

structure DecodeLoopInv (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) (i : Nat) : Prop where
  hpc : s.pc = entry + bv% (20)
  hrun : s.status = .Running
  hsp : s.sp = sp'
  hsp_align : sp' &&& 15#64 = 0#64
  hx0 : s.readReg64 (Reg.gpr 0#5) = out
  hx1 : s.readReg64 (Reg.gpr 1#5) = src
  hx8 : s.readReg64 (Reg.gpr 8#5) = acc
  hx9 : s.readReg64 (Reg.gpr 9#5) = BitVec.ofNat 64 i
  hx10 : s.readReg64 (Reg.gpr 10#5) = sp'
  hx30 : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5)
  htrace : s.trace = s0.trace
  hcs : CalleeSavedPreserved s0 s

structure DecodeLoopPost (entry : BitVec 64) (s0 s : State)
    (out src sp' acc : BitVec 64) : Prop where
  hpc : s.pc = entry + bv% (88)
  hrun : s.status = .Running
  hsp : s.sp = sp'
  hsp_align : sp' &&& 15#64 = 0#64
  hx0 : s.readReg64 (Reg.gpr 0#5) = out
  hx1 : s.readReg64 (Reg.gpr 1#5) = src
  hx8 : s.readReg64 (Reg.gpr 8#5) = acc
  hx30 : s.readReg64 (Reg.gpr 30#5) = s0.readReg64 (Reg.gpr 30#5)
  htrace : s.trace = s0.trace
  hcs : CalleeSavedPreserved s0 s

theorem bne_32_of_lt {i : Nat} (hi : i + 1 < 32) :
    (BitVec.ofNat 64 i + 1#64 != 32#64) = true := by
  rw [bne_iff_ne]
  intro h
  have hnat := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hnat
  omega

theorem list_length_8_elim {α : Type _} (xs : List α) (h : xs.length = 8) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7, xs = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩

theorem list_length_16_elim {α : Type _} (xs : List α) (h : xs.length = 16) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] := by
  have h1 : (xs.take 8).length = 8 := by simp [h]
  have h2 : (xs.drop 8).length = 8 := by simp [h]
  rcases list_length_8_elim _ h1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, e1⟩
  rcases list_length_8_elim _ h2 with ⟨x8, x9, x10, x11, x12, x13, x14, x15, e2⟩
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, ?_⟩
  rw [← List.take_append_drop 8 xs, e1, e2]; rfl

theorem list_length_32_elim {α : Type _} (xs : List α) (h : xs.length = 32) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
            x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31] := by
  have h1 : (xs.take 16).length = 16 := by simp [h]
  have h2 : (xs.drop 16).length = 16 := by simp [h]
  rcases list_length_16_elim _ h1 with ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, e1⟩
  rcases list_length_16_elim _ h2 with ⟨x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, e2⟩
  refine ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
          x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31, ?_⟩
  rw [← List.take_append_drop 16 xs, e1, e2]; rfl

theorem list_length_17_elim {α : Type _} (xs : List α) (h : xs.length = 17) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16,
      xs = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16] := by
  rcases xs with _ | ⟨x0, xs'⟩
  · simp at h
  have h1 : xs'.length = 16 := by simp at h; omega
  rcases list_length_16_elim xs' h1 with ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, e1⟩
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, congrArg (x0 :: ·) e1⟩

theorem pointsToBytes_32_expand (a : BitVec 64)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15
     n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 : BitVec 8) :
    (a ↦ₛ [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
           n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]) =
    ((a ↦₈ n0) ∗ ((a + 1#64) ↦₈ n1) ∗ ((a + 2#64) ↦₈ n2) ∗ ((a + 3#64) ↦₈ n3) ∗
     ((a + 4#64) ↦₈ n4) ∗ ((a + 5#64) ↦₈ n5) ∗ ((a + 6#64) ↦₈ n6) ∗ ((a + 7#64) ↦₈ n7) ∗
     ((a + 8#64) ↦₈ n8) ∗ ((a + 9#64) ↦₈ n9) ∗ ((a + 10#64) ↦₈ n10) ∗ ((a + 11#64) ↦₈ n11) ∗
     ((a + 12#64) ↦₈ n12) ∗ ((a + 13#64) ↦₈ n13) ∗ ((a + 14#64) ↦₈ n14) ∗ ((a + 15#64) ↦₈ n15) ∗
     ((a + 16#64) ↦₈ n16) ∗ ((a + 17#64) ↦₈ n17) ∗ ((a + 18#64) ↦₈ n18) ∗ ((a + 19#64) ↦₈ n19) ∗
     ((a + 20#64) ↦₈ n20) ∗ ((a + 21#64) ↦₈ n21) ∗ ((a + 22#64) ↦₈ n22) ∗ ((a + 23#64) ↦₈ n23) ∗
     ((a + 24#64) ↦₈ n24) ∗ ((a + 25#64) ↦₈ n25) ∗ ((a + 26#64) ↦₈ n26) ∗ ((a + 27#64) ↦₈ n27) ∗
     ((a + 28#64) ↦₈ n28) ∗ ((a + 29#64) ↦₈ n29) ∗ ((a + 30#64) ↦₈ n30) ∗ ((a + 31#64) ↦₈ n31)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_17_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : BitVec 8) :
    (a ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16]) =
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₈ b3) ∗
     ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗ ((a + 7#64) ↦₈ b7) ∗
     ((a + 8#64) ↦₈ b8) ∗ ((a + 9#64) ↦₈ b9) ∗ ((a + 10#64) ↦₈ b10) ∗ ((a + 11#64) ↦₈ b11) ∗
     ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗ ((a + 15#64) ↦₈ b15) ∗
     ((a + 16#64) ↦₈ b16)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_16_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) :
    ((a + 1#64) ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) =
    (((a + 1#64) ↦₈ b0) ∗ ((a + 2#64) ↦₈ b1) ∗ ((a + 3#64) ↦₈ b2) ∗ ((a + 4#64) ↦₈ b3) ∗
     ((a + 5#64) ↦₈ b4) ∗ ((a + 6#64) ↦₈ b5) ∗ ((a + 7#64) ↦₈ b6) ∗ ((a + 8#64) ↦₈ b7) ∗
     ((a + 9#64) ↦₈ b8) ∗ ((a + 10#64) ↦₈ b9) ∗ ((a + 11#64) ↦₈ b10) ∗ ((a + 12#64) ↦₈ b11) ∗
     ((a + 13#64) ↦₈ b12) ∗ ((a + 14#64) ↦₈ b13) ∗ ((a + 15#64) ↦₈ b14) ∗ ((a + 16#64) ↦₈ b15)) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

theorem pointsToBytes_16_tail_expand (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8)
    (Tail : SepProp) :
    ((a + 1#64) ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]) ∗ Tail =
    (((a + 1#64) ↦₈ b0) ∗ ((a + 2#64) ↦₈ b1) ∗ ((a + 3#64) ↦₈ b2) ∗ ((a + 4#64) ↦₈ b3) ∗
     ((a + 5#64) ↦₈ b4) ∗ ((a + 6#64) ↦₈ b5) ∗ ((a + 7#64) ↦₈ b6) ∗ ((a + 8#64) ↦₈ b7) ∗
     ((a + 9#64) ↦₈ b8) ∗ ((a + 10#64) ↦₈ b9) ∗ ((a + 11#64) ↦₈ b10) ∗ ((a + 12#64) ↦₈ b11) ∗
     ((a + 13#64) ↦₈ b12) ∗ ((a + 14#64) ↦₈ b13) ∗ ((a + 15#64) ↦₈ b14) ∗ ((a + 16#64) ↦₈ b15) ∗ Tail) := by
  rw [pointsToBytes_16_expand a]
  simp only [sepConj_assoc]

theorem pointsToBytes_32_sub32_expand (sp : BitVec 64)
    (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15
     n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 : BitVec 8)
    (Tail : SepProp) :
    ((sp - 32#64) ↦ₛ [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15,
                      n16, n17, n18, n19, n20, n21, n22, n23, n24, n25, n26, n27, n28, n29, n30, n31]) ∗ Tail =
    ((sp - 32#64) ↦₈ n0 ∗ (sp - 31#64) ↦₈ n1 ∗ (sp - 30#64) ↦₈ n2 ∗ (sp - 29#64) ↦₈ n3 ∗
     (sp - 28#64) ↦₈ n4 ∗ (sp - 27#64) ↦₈ n5 ∗ (sp - 26#64) ↦₈ n6 ∗ (sp - 25#64) ↦₈ n7 ∗
     (sp - 24#64) ↦₈ n8 ∗ (sp - 23#64) ↦₈ n9 ∗ (sp - 22#64) ↦₈ n10 ∗ (sp - 21#64) ↦₈ n11 ∗
     (sp - 20#64) ↦₈ n12 ∗ (sp - 19#64) ↦₈ n13 ∗ (sp - 18#64) ↦₈ n14 ∗ (sp - 17#64) ↦₈ n15 ∗
     (sp - 16#64) ↦₈ n16 ∗ (sp - 15#64) ↦₈ n17 ∗ (sp - 14#64) ↦₈ n18 ∗ (sp - 13#64) ↦₈ n19 ∗
     (sp - 12#64) ↦₈ n20 ∗ (sp - 11#64) ↦₈ n21 ∗ (sp - 10#64) ↦₈ n22 ∗ (sp - 9#64) ↦₈ n23 ∗
     (sp - 8#64) ↦₈ n24 ∗ (sp - 7#64) ↦₈ n25 ∗ (sp - 6#64) ↦₈ n26 ∗ (sp - 5#64) ↦₈ n27 ∗
     (sp - 4#64) ↦₈ n28 ∗ (sp - 3#64) ↦₈ n29 ∗ (sp - 2#64) ↦₈ n30 ∗ (sp - 1#64) ↦₈ n31 ∗ Tail) := by
  simp only [arm64_norm, sepConj_assoc]

@[expose] def decodeHex32ResultAt (out : BitVec 64) : Option (List.Vector (BitVec 8) 16) → SepProp
  | some u => (out ↦₈ 1#8) ∗ ((out + 1#64) ↦ₛ u.toList)
  | none => (out ↦₈ 0#8) ∗ memRegion (out + 1#64) 16

@[expose] def decodeHex32Spec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, src, hex) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = src ∧ hex.length = 32⌝ ∗
      (src ↦ₛ hex) ∗ memRegion out 17 ∗ stackAt s.sp 0x20
  post := fun (out, src, hex) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (src ↦ₛ hex) ∗ decodeHex32ResultAt out (decodeHex32 hex) ∗ stackAt s0.sp 0x20

theorem stack32_zero_eq_replicate (sp : BitVec 64) :
    (((sp - 32#64) ↦₆₄ 0#64) ∗ ((sp - 24#64) ↦₆₄ 0#64) ∗
     ((sp - 16#64) ↦₆₄ 0#64) ∗ ((sp - 8#64) ↦₆₄ 0#64)) =
    ((sp - 32#64) ↦ₛ List.replicate 32 0#8) := by
  have h32 : List.replicate 32 (0#8) =
      List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ (List.replicate 8 0#8 ++ List.replicate 8 0#8)) := rfl
  rw [h32, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
  simp only [List.length_replicate, pointsToBytes_replicate8_zero]
  have a1 : sp - 32#64 + BitVec.ofNat 64 8 = sp - 24#64 := by bv_arith
  have a2 : sp - 24#64 + BitVec.ofNat 64 8 = sp - 16#64 := by bv_arith
  have a3 : sp - 16#64 + BitVec.ofNat 64 8 = sp - 8#64 := by bv_arith
  rw [a1, a2, a3]

theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

theorem pointsToBytes_entails_memRegion (a : BitVec 64) (bs : List (BitVec 8)) (n : Nat)
    (h : bs.length = n) (hle : n ≤ 2 ^ 64) :
    (a ↦ₛ bs) ⊢ memRegion a n := by
  rw [memRegion_eq_exists_bytes a n hle]
  exact Entails.trans (Entails.of_eq (pure_sepConj_of_true h (a ↦ₛ bs)).symm)
    (Entails.sepExists_intro (P := fun bs => ⌜bs.length = n⌝ ∗ a ↦ₛ bs) bs)

theorem pointsToBytes_entails_stackAt_32 (sp : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 32) :
    ((sp - 32#64) ↦ₛ bs) ⊢ stackAt sp 0x20 :=
  pointsToBytes_entails_memRegion (sp - 32#64) bs 0x20 h (by decide)

theorem subroutine_ok_of_sepWP_entails {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      s0.spAligned = true →
      SepWP prog (s0.readReg64 (Reg.gpr 30#5)) s0 (spec.pre x s0 ∗ R)
        (fun sf Q =>
          sf.status = .Running ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          (Q ⊢ spec.post x s0 sf ∗ R))) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp_align
  refine ⟨spec.pre x s0 ∗ R, ⌜True⌝, by simpa [sepConj_emp] using hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hsp_align) ?_
  rintro sf Q _ _ ⟨_, hsp, hcs, hent⟩
  refine ⟨fun hmf => by simpa [sepConj_emp] using Satisfies.mono (sepConj_mono_left hent) hmf, hsp, hcs⟩

theorem stackAt_32_split (sp : BitVec 64) :
    stackAt sp 0x20 =
      (∃∗ w0 : BitVec 64, (sp - 32#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 24#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (sp - 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (sp - 8#64) ↦₆₄ w3) := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x20 = 32#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64),
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

