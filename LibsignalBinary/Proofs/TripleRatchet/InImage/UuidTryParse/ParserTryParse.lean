/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.UuidTryParse.ParserHyphenated -- proof-setup: allow-public-import
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Verification of `uuid::parser::try_parse` and `<uuid::Uuid>::try_parse`

Verifies the 38-byte braced and 45-byte URN branches of `uuid::parser::try_parse`, assembles
`parserTryParse_ok`, and proves `uuidTryParse_ok_impl` for `<uuid::Uuid>::try_parse`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## BitVec / List length helpers for entry dispatch -/

theorem eq_ofNat_of_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem len_eq_of_reg_eq {x : BitVec 64} {n k : Nat}
    (hx : x.toNat = n) (h : x = BitVec.ofNat 64 k) (hk : k < 2 ^ 64 := by decide) :
    n = k := by
  have := congrArg BitVec.toNat h
  rw [hx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
  exact this

theorem len_ne_of_reg_ne {x : BitVec 64} {n k : Nat}
    (hx : x.toNat = n) (h : x ≠ BitVec.ofNat 64 k) :
    n ≠ k := by
  intro hn
  apply h
  rw [eq_ofNat_of_toNat_eq hx, hn]

theorem uuidTryParse_of_other_len {bs : List (BitVec 8)}
    (h32 : bs.length ≠ 32) (h36 : bs.length ≠ 36)
    (h38 : bs.length ≠ 38) (h45 : bs.length ≠ 45) :
    uuidTryParse bs = none := by
  unfold uuidTryParse
  simp [h32, h36, h38, h45]

/-! ## Pure decomposition of 38-byte braced inputs -/

theorem exists_38_parts (bs : List (BitVec 8)) (h : bs.length = 38) :
    ∃ (b0 b37 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      bs = [b0] ++ (s36 ++ [b37]) ∧
      uuidTryParse bs =
        (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ₛ bs) =
          ((p + 1#64) ↦ₛ s36) ∗ ((p ↦₈ b0) ∗ ((p + 37#64) ↦₈ b37))) := by
  let b0 := bs[0]'(by omega)
  let s36 := (bs.drop 1).take 36
  let b37 := bs[37]'(by omega)
  have hs36 : s36.length = 36 := by simp [s36, h]
  have hbs0 : bs = [b0] ++ bs.drop 1 := by
    conv => lhs; rw [← List.take_append_drop 1 bs]
    rw [List.take_one, List.head?_eq_getElem?, getElem?_pos bs 0 (by omega), Option.toList_some]
  have hbs1 : bs.drop 1 = s36 ++ [b37] := by
    have := drop_eq_take_append_cons_drop bs 1 36 (by omega)
    have h38 : bs.drop 38 = [] := List.drop_eq_nil_of_le (by omega)
    rw [h38, List.append_nil] at this
    exact this
  have hbs : bs = [b0] ++ (s36 ++ [b37]) := by rw [hbs0, hbs1]
  have hhead : bs.head? = some b0 := by simp [hbs]
  have hlast : bs.getLast? = some b37 := by
    have : bs = ([b0] ++ s36) ++ [b37] := by simp [hbs]
    rw [this, List.getLast?_concat]
  have hdrop : bs.tail.take 36 = s36 := by rw [hbs0]; rfl
  have huuid : uuidTryParse bs =
      (if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    simp [h, hhead, hlast, hdrop]
  refine ⟨b0, b37, s36, hs36, hbs, huuid, fun p => ?_⟩
  have h1 := pointsToBytes_append p [b0] (s36 ++ [b37])
  have h2 := pointsToBytes_append (p + 1#64) s36 [b37]
  have hlen36 : BitVec.ofNat 64 s36.length = 36#64 := by rw [hs36]
  have hp37 : p + 1#64 + 36#64 = p + 37#64 := by bv_arith
  rw [hbs, h1, pointsToBytes_singleton p b0]
  change (p ↦₈ b0) ∗ ((p + 1#64) ↦ₛ (s36 ++ [b37])) = _
  rw [h2, hlen36, hp37, pointsToBytes_singleton (p + 37#64) b37]
  simp only [sepConj_left_comm]

theorem braced_ne_0 {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (hne : BitVec.zeroExtend 32 b0 ≠ 123#32) :
    uuidTryParse bs = none := by
  have : b0 ≠ 0x7b#8 := fun h => hne (by subst h; rfl)
  simp [hu, this]

theorem braced_ne_37 {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (hne : BitVec.zeroExtend 32 b37 ≠ 125#32) :
    uuidTryParse bs = none := by
  have : b37 ≠ 0x7d#8 := fun h => hne (by subst h; rfl)
  simp [hu, this]

theorem braced_all_eq {bs s36 : List (BitVec 8)} {b0 b37 : BitVec 8}
    (hu : uuidTryParse bs = if b0 = 0x7b#8 ∧ b37 = 0x7d#8 then parseHyphenated s36 else none)
    (h0 : BitVec.zeroExtend 64 b0 = 123#64)
    (h37 : BitVec.zeroExtend 64 b37 = 125#64) :
    uuidTryParse bs = parseHyphenated s36 := by
  have e0 : b0 = 0x7b#8 := byte_eq_of_zext64_eq h0
  have e37 : b37 = 0x7d#8 := byte_eq_of_zext64_eq h37
  simp [hu, e0, e37]

/-! ## Pure decomposition of 45-byte URN inputs -/

theorem urnPrefix_val :
    urnPrefix = [0x75#8, 0x72#8, 0x6e#8, 0x3a#8, 0x75#8, 0x75#8, 0x69#8, 0x64#8, 0x3a#8] := by
  decide +kernel

theorem exists_word9_of_length_9 (s : List (BitVec 8)) (h : s.length = 9) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8,
      s = [b0, b1, b2, b3, b4, b5, b6, b7, b8] := by
  rcases s with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at h)
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩

theorem pointsToBytes9_eq (p : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) :
    (p ↦ₛ [b0, b1, b2, b3, b4, b5, b6, b7, b8]) =
      (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
      ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗
      ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8) := by
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem exists_45_parts (bs : List (BitVec 8)) (h : bs.length = 45) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (s36 : List (BitVec 8)),
      s36.length = 36 ∧
      uuidTryParse bs =
        (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
            0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
         then parseHyphenated s36 else none) ∧
      (∀ p : BitVec 64,
        (p ↦ₛ bs) =
          ((p + 9#64) ↦ₛ s36) ∗
          ((p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₈ b2) ∗ ((p + 3#64) ↦₈ b3) ∗
           ((p + 4#64) ↦₈ b4) ∗ ((p + 5#64) ↦₈ b5) ∗ ((p + 6#64) ↦₈ b6) ∗
           ((p + 7#64) ↦₈ b7) ∗ ((p + 8#64) ↦₈ b8))) := by
  let pfx := bs.take 9
  let s36 := bs.drop 9
  have hpfx_len : pfx.length = 9 := by simp [pfx, h]
  have hs36_len : s36.length = 36 := by simp [s36, h]
  rcases exists_word9_of_length_9 pfx hpfx_len with ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, hpfx⟩
  have hbs : bs = [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ s36 := by
    rw [← hpfx]
    exact (List.take_append_drop 9 bs).symm
  have huuid : uuidTryParse bs =
      (if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
          0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
       then parseHyphenated s36 else none) := by
    unfold uuidTryParse
    rw [urnPrefix_val]
    simp [hbs, hs36_len, List.isPrefixOf]
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, s36, hs36_len, huuid, fun p => ?_⟩
  have h1 := pointsToBytes_append p [b0, b1, b2, b3, b4, b5, b6, b7, b8] s36
  have hlen9 : BitVec.ofNat 64 [b0, b1, b2, b3, b4, b5, b6, b7, b8].length = 9#64 := rfl
  rw [hbs, h1, hlen9, pointsToBytes9_eq p b0 b1 b2 b3 b4 b5 b6 b7 b8, sepConj_comm]

theorem urn_all_eq {bs s36 : List (BitVec 8)} {b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8}
    (hu : uuidTryParse bs =
      if 0x75#8 = b0 ∧ 0x72#8 = b1 ∧ 0x6e#8 = b2 ∧ 0x3a#8 = b3 ∧
         0x75#8 = b4 ∧ 0x75#8 = b5 ∧ 0x69#8 = b6 ∧ 0x64#8 = b7 ∧ 0x3a#8 = b8
      then parseHyphenated s36 else none)
    (h0 : BitVec.zeroExtend 64 b0 = 117#64)
    (h1 : BitVec.zeroExtend 64 b1 = 114#64)
    (h2 : BitVec.zeroExtend 64 b2 = 110#64)
    (h3 : BitVec.zeroExtend 64 b3 = 58#64)
    (h4 : BitVec.zeroExtend 64 b4 = 117#64)
    (h5 : BitVec.zeroExtend 64 b5 = 117#64)
    (h6 : BitVec.zeroExtend 64 b6 = 105#64)
    (h7 : BitVec.zeroExtend 64 b7 = 100#64)
    (h8 : BitVec.zeroExtend 64 b8 = 58#64) :
    uuidTryParse bs = parseHyphenated s36 := by
  have e0 : b0 = 0x75#8 := byte_eq_of_zext64_eq h0
  have e1 : b1 = 0x72#8 := byte_eq_of_zext64_eq h1
  have e2 : b2 = 0x6e#8 := byte_eq_of_zext64_eq h2
  have e3 : b3 = 0x3a#8 := byte_eq_of_zext64_eq h3
  have e4 : b4 = 0x75#8 := byte_eq_of_zext64_eq h4
  have e5 : b5 = 0x75#8 := byte_eq_of_zext64_eq h5
  have e6 : b6 = 0x69#8 := byte_eq_of_zext64_eq h6
  have e7 : b7 = 0x64#8 := byte_eq_of_zext64_eq h7
  have e8 : b8 = 0x3a#8 := byte_eq_of_zext64_eq h8
  subst e0 e1 e2 e3 e4 e5 e6 e7 e8
  simp [hu]

/-! ## Symbolic execution of braced (`0x49490`) and URN (`0x493e0`) branches -/

theorem subroutine_ok_of_sepWP_simple {α : Type} {prog : Program} {entry_pc : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc →
      s0.status = .Running →
      s0.spAligned = true →
      SepWP prog (s0.readReg64 (Reg.gpr 30#5)) s0 (spec.pre x s0)
        (fun sf Q =>
          (sf.mem ⊨ Q ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf)) :
    subroutine_ok prog entry_pc spec := by
  apply subroutine_ok_of_sepWP
  intro x R s0 hpc hrun hpre hsp_align
  exact ⟨spec.pre x s0, R, hpre, h x R s0 hpc hrun hsp_align⟩

theorem sepWP_parser_branch {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 P3 P4 Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s ((P1 ∗ P2 ∗ P3 ∗ P4) ∗ Rest) post) :
    SepWP prog target_pc s (P1 ∗ P2 ∗ P3 ∗ P4 ∗ Rest) post := by
  simpa only [sepConj_assoc] using h

theorem sepWP_parser_hyph36 {prog : Program} {target_pc : BitVec 64} {s : State}
    {P1 P2 P3 P4 Rest : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog target_pc s (((P1 ∗ emp) ∗ P2 ∗ P3 ∗ P4) ∗ Rest) post) :
    SepWP prog target_pc s (P1 ∗ P2 ∗ P3 ∗ P4 ∗ Rest) post := by
  simpa only [sepConj_assoc, emp_sepConj] using h

theorem memRegion_out32_split (out : BitVec 64) :
    memRegion out 32 =
      (∃∗ w_tag : BitVec 32, out ↦₃₂ w_tag) ∗
      (∃∗ w_u0 : BitVec 64, (out + 4#64) ↦₆₄ w_u0) ∗
      (∃∗ w_u1 : BitVec 64, (out + 12#64) ↦₆₄ w_u1) ∗
      memRegion (out + 20#64) 12 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 4) (k := 28)
        (b' := out + 4#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := out + 4#64) (n := 8) (k := 20)
        (b' := out + 12#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 8) (k := 12)
        (b' := out + 20#64) rfl (by bv_arith) (by decide),
      memRegion_four out, memRegion_eight (out + 4#64), memRegion_eight (out + 12#64)]

theorem memRegion_out28_split (out : BitVec 64) :
    memRegion (out + 4#64) 28 =
      (∃∗ w_u0 : BitVec 64, (out + 4#64) ↦₆₄ w_u0) ∗
      (∃∗ w_u1 : BitVec 64, (out + 12#64) ↦₆₄ w_u1) ∗
      memRegion (out + 20#64) 12 := by
  rw [ProofLib.memRegion_split' (b := out + 4#64) (n := 8) (k := 20)
        (b' := out + 12#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := out + 12#64) (n := 8) (k := 12)
        (b' := out + 20#64) rfl (by bv_arith) (by decide),
      memRegion_eight (out + 4#64), memRegion_eight (out + 12#64)]

theorem stackAt_uuid_split (sp : BitVec 64) :
    stackAt sp uuidTryParseStack =
      stackAt (sp - 64#64) 0x80 ∗
      memRegion (sp - 64#64) 8 ∗
      memRegion (sp - 56#64) 17 ∗
      memRegion (sp - 39#64) 7 ∗
      (∃∗ s29 : BitVec 64, (sp - 32#64) ↦₆₄ s29) ∗
      (∃∗ s30 : BitVec 64, (sp - 24#64) ↦₆₄ s30) ∗
      (∃∗ s19 : BitVec 64, (sp - 16#64) ↦₆₄ s19) ∗
      memRegion (sp - 8#64) 8 := by
  simp only [stackAt, uuidTryParseStack]
  rw [ProofLib.memRegion_split' (b := sp - 192#64) (n := 128) (k := 64)
        (b' := sp - 64#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 56)
        (b' := sp - 56#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 17) (k := 39)
        (b' := sp - 39#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 8) (k := 24)
        (b' := sp - 24#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 24#64) (n := 8) (k := 16)
        (b' := sp - 16#64) rfl (by bv_arith) (by decide),
      ProofLib.memRegion_split' (b := sp - 16#64) (n := 8) (k := 8)
        (b' := sp - 8#64) rfl (by bv_arith) (by decide),
      memRegion_eight (sp - 32#64), memRegion_eight (sp - 24#64), memRegion_eight (sp - 16#64)]
  have h192 : sp - 64#64 - BitVec.ofNat 64 128 = sp - 192#64 := by bv_arith
  rw [h192]

theorem parserTryParseResultAt_sp56_none (sp : BitVec 64) :
    parserTryParseResultAt (sp - 56#64) none =
      (∃∗ w0 : BitVec 64, (sp - 56#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 48#64) ↦₆₄ w1) ∗
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0xff#8⌝ ∗ ((sp - 40#64) ↦₈ tag)) := by
  simp only [parserTryParseResultAt]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem parserTryParseResultAt_sp56_some (sp : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    parserTryParseResultAt (sp - 56#64) (some u) =
      ((sp - 56#64) ↦₆₄ uuidWord0 u) ∗
      ((sp - 48#64) ↦₆₄ uuidWord1 u) ∗
      ((sp - 40#64) ↦₈ 0xff#8) := by
  rw [parserTryParseResultAt_some_eq]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem memRegion_sp56_17_split (sp : BitVec 64) :
    memRegion (sp - 56#64) 17 =
      (∃∗ w0 : BitVec 64, (sp - 56#64) ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (sp - 48#64) ↦₆₄ w1) ∗
      (∃∗ tag : BitVec 8, (sp - 40#64) ↦₈ tag) := by
  rw [memRegion_out17_split (sp - 56#64)]
  have h48 : sp - 56#64 + 8#64 = sp - 48#64 := by bv_arith
  have h40 : sp - 56#64 + 16#64 = sp - 40#64 := by bv_arith
  rw [h48, h40]

theorem uuidResultAt_some_eq (out : BitVec 64) (u : List.Vector (BitVec 8) 16) :
    uuidResultAt out (some u) =
      (out ↦₃₂ 0xffffffff#32) ∗
      ((out + 4#64) ↦₆₄ uuidWord0 u) ∗
      ((out + 12#64) ↦₆₄ uuidWord1 u) ∗
      memRegion (out + 20#64) 12 := by
  simp only [uuidResultAt, uuidOkTag, pointsToBytes_uuid (out + 4#64) u]
  have h12 : out + 4#64 + 8#64 = out + 12#64 := by bv_arith
  rw [h12]
  simp only [sepConj_assoc]

end CryptoVerification.LibsignalTripleRatchet.InImage.UuidTryParse
