/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.DecodeHex32 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.Sep
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Simple and Hyphenated Branches of `uuid::parser::try_parse`

Defines the 17-byte `Result<[u8; 16], InvalidUuid>` layout `parserTryParseResultAt` and verifies
the 32-byte simple and 36-byte hyphenated branches of `uuid::parser::try_parse`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## UUID word packing and `parser::try_parse` contract -/

@[expose] def uuidWord0 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 0 0#8) (u.toList.getD 1 0#8) (u.toList.getD 2 0#8) (u.toList.getD 3 0#8)
    (u.toList.getD 4 0#8) (u.toList.getD 5 0#8) (u.toList.getD 6 0#8) (u.toList.getD 7 0#8)

@[expose] def uuidWord1 (u : List.Vector (BitVec 8) 16) : BitVec 64 :=
  pack64 (u.toList.getD 8 0#8) (u.toList.getD 9 0#8) (u.toList.getD 10 0#8) (u.toList.getD 11 0#8)
    (u.toList.getD 12 0#8) (u.toList.getD 13 0#8) (u.toList.getD 14 0#8) (u.toList.getD 15 0#8)

theorem pointsToBytes_uuid (a : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    (a ↦ₛ u.toList) = ((a ↦₆₄ uuidWord0 u) ∗ ((a + 8#64) ↦₆₄ uuidWord1 u)) := by
  have hlen : u.toList.length = 16 := u.toList_length
  have hsplit : u.toList = (u.toList.drop 0).take 8 ++ (u.toList.drop 8).take 8 := by
    have hd : (u.toList.drop 8).length ≤ 8 := by simp [hlen]
    simp only [List.drop_zero, List.take_of_length_le hd, List.take_append_drop]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append]
  have ht8 : ((u.toList.drop 0).take 8).length = 8 := by simp [hlen]
  rw [ht8, pointsToBytes_take8_eq_pointsTo64 a u.toList 0 (by omega),
    pointsToBytes_take8_eq_pointsTo64 (a + 8#64) u.toList 8 (by omega)]
  rfl

/-- The 17-byte `Result<[u8; 16], InvalidUuid>` written by `uuid::parser::try_parse` (`0x4930c`)
at `out17` (`x8`):
- `some u`: 16 UUID bytes at `out17..out17+16`, tag byte `0xff` at `out17+16`;
- `none`: 16 bytes at `out17..out17+16` (error slice/offset), tag byte `≠ 0xff` (`0` or `2`) at `out17+16`. -/
@[expose] def parserTryParseResultAt (out17 : BitVec 64) : Option (List.Vector (BitVec 8) 16) → SepProp
  | some u => (out17 ↦ₛ u.toList) ∗ ((out17 + 16#64) ↦₈ 0xff#8)
  | none =>
    (∃∗ w0 : BitVec 64, out17 ↦₆₄ w0) ∗
    (∃∗ w1 : BitVec 64, (out17 + 8#64) ↦₆₄ w1) ∗
    (∃∗ tag : BitVec 8, ⌜tag ≠ 0xff#8⌝ ∗ ((out17 + 16#64) ↦₈ tag))

@[expose] def parserTryParseSpec : Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p, bs, out17) s =>
    (⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = bs.length ∧ s.readReg64 .x8 = out17⌝ ∗
      (p ↦ₛ bs) ∗ memRegion out17 17) ∗ stackAt s.sp 0x80
  post := fun (p, bs, out17) s0 sf =>
    (⌜sf.trace = s0.trace⌝ ∗
      (p ↦ₛ bs) ∗ parserTryParseResultAt out17 (uuidTryParse bs)) ∗ stackAt s0.sp 0x80

theorem exists_word64_of_length_8 (s : List (BitVec 8)) (h : s.length = 8) :
    ∃ w : BitVec 64, ∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₆₄ w) := by
  rcases list_length_8_elim s h with ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  exact ⟨pack64 b0 b1 b2 b3 b4 b5 b6 b7,
    fun a => pointsToBytes8_eq_pointsTo64 a b0 b1 b2 b3 b4 b5 b6 b7⟩

theorem exists_word32_of_length_4 (s : List (BitVec 8)) (h : s.length = 4) :
    ∃ w : BitVec 32, ∀ a : BitVec 64, (a ↦ₛ s) = (a ↦₃₂ w) := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | _⟩⟩⟩⟩ <;> try (simp at h)
  exact ⟨b3 ++ b2 ++ b1 ++ b0, fun a => pointsToBytes4_eq_pointsTo32 a b0 b1 b2 b3⟩

theorem drop_eq_take_append_cons_drop (s : List (BitVec 8)) (i m : Nat) (h : i + m < s.length) :
    s.drop i = (s.drop i).take m ++ ([s[i + m]] ++ s.drop (i + m + 1)) := by
  conv => lhs; rw [← List.take_append_drop m (s.drop i)]
  rw [List.drop_drop, List.drop_eq_getElem_cons h]
  rfl

theorem exists_36_parts (s : List (BitVec 8)) (h : s.length = 36) :
    ∃ (hex32 : List (BitVec 8)) (b8 b13 b18 b23 : BitVec 8)
      (w0 w4 : BitVec 64) (w1 w2 w3 w5 : BitVec 32),
      hex32.length = 32 ∧
      s[8]? = some b8 ∧ s[13]? = some b13 ∧ s[18]? = some b18 ∧ s[23]? = some b23 ∧
      s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 ∧
      (∀ p : BitVec 64,
        (p ↦ₛ s) =
          (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₈ b8) ∗ ((p + 9#64) ↦₃₂ w1) ∗
          ((p + 13#64) ↦₈ b13) ∗ ((p + 14#64) ↦₃₂ w2) ∗ ((p + 18#64) ↦₈ b18) ∗
          ((p + 19#64) ↦₃₂ w3) ∗ ((p + 23#64) ↦₈ b23) ∗ ((p + 24#64) ↦₆₄ w4) ∗
          ((p + 32#64) ↦₃₂ w5)) ∧
      (∀ sp : BitVec 64,
        (((sp - 88#64) ↦₆₄ w0) ∗ ((sp - 80#64) ↦₃₂ w1) ∗ ((sp - 76#64) ↦₃₂ w2) ∗
         ((sp - 72#64) ↦₃₂ w3) ∗ ((sp - 68#64) ↦₆₄ w4) ∗ ((sp - 60#64) ↦₃₂ w5)) =
        ((sp - 88#64) ↦ₛ hex32)) := by
  let s0 := s.take 8
  let b8 := s[8]'(by omega)
  let s1 := (s.drop 9).take 4
  let b13 := s[13]'(by omega)
  let s2 := (s.drop 14).take 4
  let b18 := s[18]'(by omega)
  let s3 := (s.drop 19).take 4
  let b23 := s[23]'(by omega)
  let s4 := (s.drop 24).take 8
  let s5 := s.drop 32
  have hs0 : s0.length = 8 := by simp [s0, h]
  have hs1 : s1.length = 4 := by simp [s1, h]
  have hs2 : s2.length = 4 := by simp [s2, h]
  have hs3 : s3.length = 4 := by simp [s3, h]
  have hs4 : s4.length = 8 := by simp [s4, h]
  have hs5 : s5.length = 4 := by simp [s5, h]
  rcases exists_word64_of_length_8 s0 hs0 with ⟨w0, hw0⟩
  rcases exists_word32_of_length_4 s1 hs1 with ⟨w1, hw1⟩
  rcases exists_word32_of_length_4 s2 hs2 with ⟨w2, hw2⟩
  rcases exists_word32_of_length_4 s3 hs3 with ⟨w3, hw3⟩
  rcases exists_word64_of_length_8 s4 hs4 with ⟨w4, hw4⟩
  rcases exists_word32_of_length_4 s5 hs5 with ⟨w5, hw5⟩
  have hs24 : s.drop 24 = s4 ++ s5 := by
    dsimp only [s4, s5]
    rw [show (32 : Nat) = 24 + 8 from rfl, ← List.drop_drop, List.take_append_drop]
  let hex32 := s0 ++ (s1 ++ (s2 ++ (s3 ++ (s4 ++ s5))))
  have hhex_eq : s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32 := by
    simp only [s0, s1, s2, s3, hs24, hex32, List.append_assoc]
  have hhex_len : hex32.length = 32 := by
    simp only [hex32, List.length_append, hs0, hs1, hs2, hs3, hs4, hs5]
  have hs_decomp : s = s0 ++ ([b8] ++ (s1 ++ ([b13] ++ (s2 ++ ([b18] ++ (s3 ++ ([b23] ++ (s4 ++ s5)))))))) := by
    have e1 : s = s0 ++ ([b8] ++ s.drop 9) :=
      drop_eq_take_append_cons_drop s 0 8 (by omega)
    have e2 : s.drop 9 = s1 ++ ([b13] ++ s.drop 14) :=
      drop_eq_take_append_cons_drop s 9 4 (by omega)
    have e3 : s.drop 14 = s2 ++ ([b18] ++ s.drop 19) :=
      drop_eq_take_append_cons_drop s 14 4 (by omega)
    have e4 : s.drop 19 = s3 ++ ([b23] ++ s.drop 24) :=
      drop_eq_take_append_cons_drop s 19 4 (by omega)
    rw [e1, e2, e3, e4, hs24]
  refine ⟨hex32, b8, b13, b18, b23, w0, w4, w1, w2, w3, w5, hhex_len,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    hhex_eq, ?_, ?_⟩
  · intro p
    conv => lhs; rw [hs_decomp]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append, pointsToBytes_append]
    simp only [hs0, hs1, hs2, hs3, hs4, List.length_singleton,
      hw0, hw1, hw2, hw3, hw4, hw5, pointsToBytes_singleton,
      BitVec.add_assoc, BitVec.reduceAdd]
  · intro sp
    symm
    dsimp only [hex32]
    rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
        pointsToBytes_append, pointsToBytes_append]
    simp only [hs0, hs1, hs2, hs3, hs4, hw0, hw1, hw2, hw3, hw4, hw5, arm64_norm]

theorem parseHyphenated_of_parts (s hex32 : List (BitVec 8)) (b8 b13 b18 b23 : BitVec 8)
    (hlen : s.length = 36)
    (hb8 : s[8]? = some b8) (hb13 : s[13]? = some b13)
    (hb18 : s[18]? = some b18) (hb23 : s[23]? = some b23)
    (hhex : s.take 8 ++ (s.drop 9).take 4 ++ (s.drop 14).take 4 ++ (s.drop 19).take 4 ++ s.drop 24 = hex32) :
    parseHyphenated s =
      if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then
        decodeHex32 hex32
      else none := by
  unfold parseHyphenated hyphen
  simp only [hlen, hb8, hb13, hb18, hb23, hhex, Option.some.injEq, true_and]

theorem parseHyphenated_ne_8 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b8 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b8 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_13 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b13 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b13 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_18 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b18 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b18 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem parseHyphenated_ne_23 {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (hne : BitVec.zeroExtend 32 b23 ≠ 45#32) :
    parseHyphenated s = none := by
  have : b23 ≠ 0x2d#8 := fun h => hne (by subst h; rfl)
  simp [hp, this]

theorem byte_eq_of_zext64_eq {b : BitVec 8} {c : BitVec 8}
    (h : BitVec.zeroExtend 64 b = BitVec.zeroExtend 64 c) : b = c := by
  revert h; bv_omega

theorem parseHyphenated_all_eq {s hex32 : List (BitVec 8)} {b8 b13 b18 b23 : BitVec 8}
    (hp : parseHyphenated s = if b8 = 0x2d#8 ∧ b13 = 0x2d#8 ∧ b18 = 0x2d#8 ∧ b23 = 0x2d#8 then decodeHex32 hex32 else none)
    (h8 : BitVec.zeroExtend 64 b8 = 45#64)
    (h13 : BitVec.zeroExtend 64 b13 = 45#64)
    (h18 : BitVec.zeroExtend 64 b18 = 45#64)
    (h23 : BitVec.zeroExtend 64 b23 = 45#64) :
    parseHyphenated s = decodeHex32 hex32 := by
  have e8 : b8 = 0x2d#8 := byte_eq_of_zext64_eq h8
  have e13 : b13 = 0x2d#8 := byte_eq_of_zext64_eq h13
  have e18 : b18 = 0x2d#8 := byte_eq_of_zext64_eq h18
  have e23 : b23 = 0x2d#8 := byte_eq_of_zext64_eq h23
  simp [hp, e8, e13, e18, e23]

/-! ## Stack and buffer layout splits for `uuid::parser::try_parse` (`0x4930c`) -/

theorem memRegion_out17_split (out17 : BitVec 64) :
    memRegion out17 17 =
      (∃∗ w0 : BitVec 64, out17 ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (out17 + 8#64) ↦₆₄ w1) ∗
      (∃∗ b2 : BitVec 8, (out17 + 16#64) ↦₈ b2) := by
  sep_interval_eq

theorem parserTryParseResultAt_some_eq (out17 : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    parserTryParseResultAt out17 (some u) =
      (out17 ↦₆₄ uuidWord0 u) ∗ ((out17 + 8#64) ↦₆₄ uuidWord1 u) ∗ ((out17 + 16#64) ↦₈ 0xff#8) := by
  simp only [parserTryParseResultAt, pointsToBytes_uuid out17 u, sepConj_assoc]

theorem stackAt_parser_split (sp : BitVec 64) :
    stackAt sp 0x80 =
      stackAt (sp - 96#64) 0x20 ∗
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 32 ∗
      memRegion (sp - 56#64) 4 ∗
      memRegion (sp - 52#64) 17 ∗
      memRegion (sp - 35#64) 3 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s20 : BitVec 64, (sp - 16#64) ↦₆₄ s20) ∗
      (∃∗ s19 : BitVec 64, (sp - 8#64) ↦₆₄ s19) := by
  dsimp only [stackAt]
  sep_interval_eq

theorem memRegion_sp88_32_for_hyphen (sp : BitVec 64) :
    memRegion (sp - 88#64) 32 =
      (∃∗ t0 : BitVec 64, (sp - 88#64) ↦₆₄ t0) ∗
      (∃∗ t1 : BitVec 32, (sp - 80#64) ↦₃₂ t1) ∗
      (∃∗ t2 : BitVec 32, (sp - 76#64) ↦₃₂ t2) ∗
      (∃∗ t3 : BitVec 32, (sp - 72#64) ↦₃₂ t3) ∗
      (∃∗ t4 : BitVec 64, (sp - 68#64) ↦₆₄ t4) ∗
      (∃∗ t5 : BitVec 32, (sp - 60#64) ↦₃₂ t5) := by
  sep_interval_eq

theorem memRegion_sp88_32_for_simple (sp : BitVec 64) :
    memRegion (sp - 88#64) 32 =
      memRegion (sp - 88#64) 17 ∗ memRegion (sp - 71#64) 15 := by
  sep_interval_eq

theorem memRegion_sp52_17_none (sp : BitVec 64) :
    memRegion (sp - 52#64) 17 =
      (∃∗ b : BitVec 8, (sp - 52#64) ↦₈ b) ∗ memRegion (sp - 51#64) 16 := by
  sep_interval_eq

theorem memRegion_sp52_17_some (sp : BitVec 64) :
    memRegion (sp - 52#64) 17 =
      (∃∗ b : BitVec 8, (sp - 52#64) ↦₈ b) ∗
      (∃∗ w0 : BitVec 64, (sp - 51#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 43#64) ↦₆₄ w1) := by
  sep_interval_eq

theorem memRegion_sp88_17_none (sp : BitVec 64) :
    memRegion (sp - 88#64) 17 =
      (∃∗ b : BitVec 8, (sp - 88#64) ↦₈ b) ∗ memRegion (sp - 87#64) 16 := by
  sep_interval_eq

theorem memRegion_sp88_17_some (sp : BitVec 64) :
    memRegion (sp - 88#64) 17 =
      (∃∗ b : BitVec 8, (sp - 88#64) ↦₈ b) ∗
      (∃∗ w0 : BitVec 64, (sp - 87#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 79#64) ↦₆₄ w1) := by
  sep_interval_eq

theorem decodeHex32ResultAt_sp52_none (sp : BitVec 64) :
    decodeHex32ResultAt (sp - 52#64) none =
      ((sp - 52#64) ↦₈ 0#8) ∗ memRegion (sp - 51#64) 16 := by
  simp only [decodeHex32ResultAt]
  have h51 : sp - 52#64 + 1#64 = sp - 51#64 := by bv_arith
  rw [h51]

theorem decodeHex32ResultAt_sp52_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    decodeHex32ResultAt (sp - 52#64) (some u) =
      ((sp - 52#64) ↦₈ 1#8) ∗
      ((sp - 51#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 43#64) ↦₆₄ uuidWord1 u) := by
  simp only [decodeHex32ResultAt]
  have h51 : sp - 52#64 + 1#64 = sp - 51#64 := by bv_arith
  have h43 : sp - 51#64 + 8#64 = sp - 43#64 := by bv_arith
  rw [h51, pointsToBytes_uuid (sp - 51#64) u, h43]

theorem decodeHex32ResultAt_sp88_none (sp : BitVec 64) :
    decodeHex32ResultAt (sp - 88#64) none =
      ((sp - 88#64) ↦₈ 0#8) ∗ memRegion (sp - 87#64) 16 := by
  simp only [decodeHex32ResultAt]
  have h87 : sp - 88#64 + 1#64 = sp - 87#64 := by bv_arith
  rw [h87]

theorem decodeHex32ResultAt_sp88_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    decodeHex32ResultAt (sp - 88#64) (some u) =
      ((sp - 88#64) ↦₈ 1#8) ∗
      ((sp - 87#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 79#64) ↦₆₄ uuidWord1 u) := by
  simp only [decodeHex32ResultAt]
  have h87 : sp - 88#64 + 1#64 = sp - 87#64 := by bv_arith
  have h79 : sp - 87#64 + 8#64 = sp - 79#64 := by bv_arith
  rw [h87, pointsToBytes_uuid (sp - 87#64) u, h79]

/-! ## Execution lemmas for `uuid::parser::try_parse` (`0x4930c`) -/

abbrev parserPost (p : BitVec 64) (bs : List (BitVec 8)) (out17 : BitVec 64) (s0 : State)
    (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ parserTryParseSpec.post (p, bs, out17) s0 sf ∗ R) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf

abbrev ParserRegsPreserved (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
