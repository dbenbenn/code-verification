/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.Decomp.NormAttr
public import ProofLib.Lemmas
public import ProofLib.BV.MaskLemmas
public import ProofLib.SepLogic.SymBlock.Step

/-!
# `decomp_norm`: Normal Forms for Decompiled Terms

Populates the `decomp_norm` simp set (`ProofLib.Decomp.NormAttr`), which brings a decompiled
`BitVec` / `Bool` / `Option` term and a pure Lean model into one normal form so that the remaining
equation is closed by `rfl` or by one decision procedure (`ProofLib.Decomp.NormTactic`).

| Input | Normal form |
|---|---|
| `ConditionHolds cc (AddWithCarry x (~~~y) true).2` (`SUBS` / `CMP`) | `decide (y ≤ x)`, `decide (x = y)`, `BitVec.slt`, ... |
| `(AddWithCarry x y c).2.c` (`ADDS` / `ADCS` carry) | `decide (2 ^ w ≤ x.toNat + y.toNat + (if c then 1 else 0))` |
| `(AddWithCarry x y c).1` | `x + y + (if c then 1#w else 0#w)` |
| `a == b`, `a != b`, `b₁ && b₂`, `!b`, `BitVec.ult` / `ule` | `decide (a = b)`, `decide ¬...`, `decide (p ∧ q)`, `decide (x < y)` |
| `truncate` / `zeroExtend`, nested `setWidth` | one `setWidth` |
| `x <<< k` | `x * BitVec.ofNat w (2 ^ k)` (literal `2 ^ k` folded) |
| `(x >>> k).toNat` | `x.toNat / 2 ^ k` |
| `UMULH` (`((x.zeroExtend 128 * y.zeroExtend 128) >>> 64).truncate 64`) | `BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)` |
| two-limb `ADDS` / `ADC` vs. 128-bit `+` | limbwise sums with an explicit `if 2 ^ 64 ≤ ... then 1#64 else 0#64` carry |
| `Option.bind` / `map` / `pure`, `if c then some a else some b` | inlined, `some (if c then a else b)` |
| `(x + y).toNat`, `(x - y).toNat`, `BitVec.ofNat w (a - b)` | `Nat` arithmetic, when the no-overflow side condition is in context |
| `CSET` then compare / mask / truncate with closed operands, `if p then true else false` | pushed into the literal arms and collapsed to the condition |
| `Bool` `if` with one literal arm (`CCMP` chains) | `decide p && b`, `!decide p \|\| b`, ... |
| limb of a 128-bit `+` / `-` / `-x` / `*` / `&&&` / `\|\|\|` / `^^^` / `~~~` | the `ADC` / `SBC` / `NGC` / `UMULH`+`MADD` / limbwise chain the machine computes |
| two-limb carry / borrow / equality chains | one 128-bit comparison (`y ≤ x`, `x = y`, `2 ^ 128 ≤ ...`) |
| `x.toNat ≤ y.toNat`, `x.toNat < y.toNat` | `x ≤ y`, `x < y` (`BitVec` order) |
| `x ≤ x + y` (no-wrap test), `if p then x + k else x` | `¬2 ^ w ≤ x.toNat + y.toNat`, `x + (if p then k else 0)` |
| commutative `*` / `&&&` / `\|\|\|` / `^^^` | one operand order (ordered rewriting) |

Opt-in rule families that change one of these normal forms are not in `decomp_norm`. They are
the simp sets `decomp_norm_bitfield`, `decomp_norm_or_add`, `decomp_norm_concat`, and
`decomp_norm_add_order` (members listed in `ProofLib.Decomp.NormAttr`), used as
`simp only [decomp_norm, decomp_norm_concat]`.

Every rule is a theorem (no definition is registered by name, so the set has no delta-unfold
entries), and every new rule mentions only `BitVec`, `Nat`, `Bool`, `Option`, and the pure ISA
helpers (`AddWithCarry64`, `ConditionHolds`, `shiftVal`, `extendVal`, `evalLogical`,
`evalDataProc3Val`), never `Arm64.State`.
Literal arithmetic is folded by the core simprocs registered at the top of this file, so
`simp only [decomp_norm]` needs no extra arguments.

Priorities: rules about a specific operand shape (`SUBS` operands `x (~~~y) true`, `UMULH`,
zero-extended comparisons) are pre-rules (`↓`) with priority 1500-2000, so they fire before simp
rewrites the operands (e.g. folds `~~~5#64` to a literal). Generic per-flag fallbacks for
`ConditionHolds` have priority 100 so that every specific rule wins.
-/

/-! ## Literal folding

Core simprocs that `simp only` does not run unless they are listed, registered here so that
`simp only [decomp_norm]` folds ground `Nat` / `BitVec` arithmetic and decided `if`s. -/

namespace ProofLib.Decomp

public meta section

-- `attribute_builtin_simproc` (scoped in `ProofLib`) registers compiled core simprocs, which are
-- not marked `meta`, into a custom simp set.
attribute_builtin_simproc [decomp_norm] reduceIte reduceDIte reduceCtorEq
  Nat.reduceAdd Nat.reduceMul Nat.reduceSub Nat.reduceDiv Nat.reduceMod Nat.reducePow
  Nat.reduceLT Nat.reduceGT Nat.reduceLeDiff Nat.reduceEqDiff Nat.reduceBEq Nat.reduceBNe
  Nat.reduceSubDiff
  BitVec.reduceAdd BitVec.reduceMul BitVec.reduceSub BitVec.reduceNeg BitVec.reduceNot
  BitVec.reduceAnd BitVec.reduceOr BitVec.reduceXOr BitVec.reduceToNat BitVec.reduceOfNat
  BitVec.reduceSetWidth BitVec.reduceSignExtend BitVec.reduceExtractLsb BitVec.reduceAppend
  BitVec.reduceShiftLeft BitVec.reduceUShiftRight BitVec.reduceULT BitVec.reduceULE
  BitVec.reduceSLT BitVec.reduceSLE BitVec.reduceEq BitVec.reduceNe BitVec.reduceBEq
  BitVec.reduceBNe BitVec.reduceLT BitVec.reduceLE BitVec.reduceGT BitVec.reduceGE
  BitVec.reduceGetLsb BitVec.reduceUDiv BitVec.reduceUMod

end

public section

open Arm64

/-! ## `Bool` / `decide` / `Prop` -/

/-- `a != b` is `decide ¬(a = b)` for a lawful `BEq`. -/
theorem bne_eq_decide_not {α : Type _} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) :
    (a != b) = decide (¬a = b) :=
  Bool.eq_iff_iff.mpr (by simp [bne_iff_ne])

/-- A conjunction of decided propositions is one decided conjunction. -/
theorem and_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p ∧ q) := (Bool.decide_and p q).symm

/-- A disjunction of decided propositions is one decided disjunction. -/
theorem or_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p ∨ q) := (Bool.decide_or p q).symm

/-- The negation of a decided proposition is the decided negation. -/
theorem not_decide (p : Prop) [Decidable p] : (!decide p) = decide (¬p) := decide_not.symm

/-- `x - y = 0` iff `x = y` (the `Z` flag of `SUBS` / `CMP`). -/
theorem sub_eq_zero_iff_eq {w : Nat} (x y : BitVec w) : (x - y = 0#w) = (x = y) := by
  apply propext; constructor
  · intro h; have := congrArg (· + y) h; simpa [BitVec.sub_add_cancel] using this
  · intro h; subst h; simp

attribute [decomp_norm] Bool.beq_eq_decide_eq bne_eq_decide_not and_decide or_decide not_decide
  decide_eq_true_eq decide_eq_false_iff_not decide_eq_decide decide_true decide_false
  Bool.not_not Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.or_true
  Bool.true_or Bool.or_false Bool.false_or Bool.not_true Bool.not_false Bool.false_eq_true
  Bool.true_eq_false
attribute [decomp_norm] eq_self_iff_true iff_self and_true true_and and_false false_and or_true
  true_or or_false false_or not_true_eq_false not_false_eq_true ne_eq Classical.not_not and_self
  or_self Nat.not_le Nat.not_lt BitVec.not_lt BitVec.not_le sub_eq_zero_iff_eq
attribute [decomp_norm] ite_true ite_false ite_self ite_not

/-- A conditional nested in the `then` branch of the same condition takes its `then` branch
    (repeated flag tests on one path, as when a shift by a variable amount is split twice). -/
theorem ite_then_ite_same {α : Sort _} (c : Prop) [Decidable c] (a b e : α) :
    (if c then (if c then a else b) else e) = if c then a else e := by
  by_cases h : c <;> simp [h]

/-- A conditional nested in the `else` branch of the same condition takes its `else` branch. -/
theorem ite_else_ite_same {α : Sort _} (c : Prop) [Decidable c] (t a b : α) :
    (if c then t else (if c then a else b)) = if c then t else b := by
  by_cases h : c <;> simp [h]

attribute [decomp_norm] ite_then_ite_same ite_else_ite_same
attribute [decomp_norm] BitVec.ult_eq_decide_lt BitVec.ule_eq_decide_le

/-! ## Flags as comparisons -/

/-- Carry of `AddWithCarry64`: the unsigned sum overflows 64 bits. -/
theorem addWithCarry64_c (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x y c).2.c = decide (2 ^ 64 ≤ x.toNat + y.toNat + (if c then 1 else 0)) := by
  cases c <;> (simp only [AddWithCarry64, Bool.false_eq_true, ite_false, ite_true]; bv_bits)

/-- Carry of `AddWithCarry32`: the unsigned sum overflows 32 bits. -/
theorem addWithCarry32_c (x y : BitVec 32) (c : Bool) :
    (AddWithCarry32 x y c).2.c = decide (2 ^ 32 ≤ x.toNat + y.toNat + (if c then 1 else 0)) := by
  cases c <;> (simp only [AddWithCarry32, Bool.false_eq_true, ite_false, ite_true]; bv_bits)

/-- Carry of a 64-bit subtraction (`SUBS` / `CMP`): no borrow, i.e. `y ≤ x`. -/
theorem subWithCarry64_c (x y : BitVec 64) :
    (AddWithCarry64 x (~~~y) true).2.c = decide (y ≤ x) := by
  have := conditionHolds_cs_subs64 x y
  simp only [ConditionHolds] at this
  rw [this, BitVec.ule_eq_decide_le]

/-- Carry of a 32-bit subtraction (`SUBS` / `CMP`): no borrow, i.e. `y ≤ x`. -/
theorem subWithCarry32_c (x y : BitVec 32) :
    (AddWithCarry32 x (~~~y) true).2.c = decide (y ≤ x) := by
  have := conditionHolds_cs_subs32 x y
  simp only [ConditionHolds] at this
  rw [this, BitVec.ule_eq_decide_le]

/-- Carry of a 64-bit subtract-with-carry (`SBCS`): no borrow out of `x - y - (!c)`. -/
theorem sbcWithCarry64_c (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x (~~~y) c).2.c = decide (y.toNat + (if c then 0 else 1) ≤ x.toNat) := by
  cases c <;> (simp only [AddWithCarry64, Bool.false_eq_true, ite_false, ite_true]; bv_bits)

/-- Carry of a 32-bit subtract-with-carry (`SBCS`): no borrow out of `x - y - (!c)`. -/
theorem sbcWithCarry32_c (x y : BitVec 32) (c : Bool) :
    (AddWithCarry32 x (~~~y) c).2.c = decide (y.toNat + (if c then 0 else 1) ≤ x.toNat) := by
  cases c <;> (simp only [AddWithCarry32, Bool.false_eq_true, ite_false, ite_true]; bv_bits)

/-- Negative flag of `AddWithCarry64`: the sign bit of the result. -/
theorem addWithCarry64_n (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x y c).2.n = (AddWithCarry64 x y c).1.msb := rfl

/-- Negative flag of `AddWithCarry32`: the sign bit of the result. -/
theorem addWithCarry32_n (x y : BitVec 32) (c : Bool) :
    (AddWithCarry32 x y c).2.n = (AddWithCarry32 x y c).1.msb := rfl

/-- Zero flag of `AddWithCarry64`: the result is zero. -/
theorem addWithCarry64_z (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x y c).2.z = ((AddWithCarry64 x y c).1 == 0#64) := rfl

/-- Zero flag of `AddWithCarry32`: the result is zero. -/
theorem addWithCarry32_z (x y : BitVec 32) (c : Bool) :
    (AddWithCarry32 x y c).2.z = ((AddWithCarry32 x y c).1 == 0#32) := rfl

/-- Fallback: `EQ` reads the `Z` flag. -/
theorem conditionHolds_eq_flag (ps : PState) : ConditionHolds .EQ ps = ps.z := rfl
/-- Fallback: `NE` reads the negated `Z` flag. -/
theorem conditionHolds_ne_flag (ps : PState) : ConditionHolds .NE ps = !ps.z := rfl
/-- Fallback: `CS` reads the `C` flag. -/
theorem conditionHolds_cs_flag (ps : PState) : ConditionHolds .CS ps = ps.c := rfl
/-- Fallback: `CC` reads the negated `C` flag. -/
theorem conditionHolds_cc_flag (ps : PState) : ConditionHolds .CC ps = !ps.c := rfl
/-- Fallback: `MI` reads the `N` flag. -/
theorem conditionHolds_mi_flag (ps : PState) : ConditionHolds .MI ps = ps.n := rfl
/-- Fallback: `PL` reads the negated `N` flag. -/
theorem conditionHolds_pl_flag (ps : PState) : ConditionHolds .PL ps = !ps.n := rfl
/-- Fallback: `VS` reads the `V` flag. -/
theorem conditionHolds_vs_flag (ps : PState) : ConditionHolds .VS ps = ps.v := rfl
/-- Fallback: `VC` reads the negated `V` flag. -/
theorem conditionHolds_vc_flag (ps : PState) : ConditionHolds .VC ps = !ps.v := rfl
/-- Fallback: `HI` is `C ∧ ¬Z`. -/
theorem conditionHolds_hi_flag (ps : PState) : ConditionHolds .HI ps = (ps.c && !ps.z) := rfl
/-- Fallback: `LS` is `¬(C ∧ ¬Z)`. -/
theorem conditionHolds_ls_flag (ps : PState) : ConditionHolds .LS ps = !(ps.c && !ps.z) := rfl
/-- Fallback: `GE` is `N = V`. -/
theorem conditionHolds_ge_flag (ps : PState) : ConditionHolds .GE ps = (ps.n == ps.v) := rfl
/-- Fallback: `LT` is `N ≠ V`. -/
theorem conditionHolds_lt_flag (ps : PState) : ConditionHolds .LT ps = (ps.n != ps.v) := rfl
/-- Fallback: `GT` is `¬Z ∧ N = V`. -/
theorem conditionHolds_gt_flag (ps : PState) :
    ConditionHolds .GT ps = (!ps.z && (ps.n == ps.v)) := rfl
/-- Fallback: `LE` is `¬(¬Z ∧ N = V)`. -/
theorem conditionHolds_le_flag (ps : PState) :
    ConditionHolds .LE ps = !(!ps.z && (ps.n == ps.v)) := rfl
/-- `AL` always holds. -/
theorem conditionHolds_al (ps : PState) : ConditionHolds .AL ps = true := rfl
/-- `NV` always holds (it behaves as `AL` on AArch64). -/
theorem conditionHolds_nv (ps : PState) : ConditionHolds .NV ps = true := rfl

-- Specific `SUBS` / `CMP` operand shapes first, before simp folds `~~~y`.
attribute [decomp_norm ↓ 2000] conditionHolds_eq_subs64 conditionHolds_ne_subs64
  conditionHolds_cs_subs64 conditionHolds_cc_subs64 conditionHolds_hi_subs64
  conditionHolds_ls_subs64 conditionHolds_ge_subs64 conditionHolds_lt_subs64
  conditionHolds_gt_subs64 conditionHolds_le_subs64 conditionHolds_mi_subs64
  conditionHolds_pl_subs64
attribute [decomp_norm ↓ 2000] conditionHolds_eq_subs32 conditionHolds_ne_subs32
  conditionHolds_cs_subs32 conditionHolds_cc_subs32 conditionHolds_hi_subs32
  conditionHolds_ls_subs32 conditionHolds_ge_subs32 conditionHolds_lt_subs32
  conditionHolds_gt_subs32 conditionHolds_le_subs32 conditionHolds_mi_subs32
  conditionHolds_pl_subs32
attribute [decomp_norm ↓ 2000] conditionHolds_eq_subsPState64 conditionHolds_ne_subsPState64
  conditionHolds_cs_subsPState64 conditionHolds_cc_subsPState64 conditionHolds_hi_subsPState64
  conditionHolds_ls_subsPState64 conditionHolds_ge_subsPState64 conditionHolds_lt_subsPState64
  conditionHolds_gt_subsPState64 conditionHolds_le_subsPState64 conditionHolds_mi_subsPState64
  conditionHolds_pl_subsPState64 subsPState64_c
attribute [decomp_norm ↓ 2000] conditionHolds_eq_subsPState32 conditionHolds_ne_subsPState32
  conditionHolds_cs_subsPState32 conditionHolds_cc_subsPState32 conditionHolds_hi_subsPState32
  conditionHolds_ls_subsPState32 conditionHolds_ge_subsPState32 conditionHolds_lt_subsPState32
  conditionHolds_gt_subsPState32 conditionHolds_le_subsPState32 conditionHolds_mi_subsPState32
  conditionHolds_pl_subsPState32 subsPState32_c
attribute [decomp_norm ↓ 2000] subWithCarry64_c subWithCarry32_c SymBlock.subs64_n
  SymBlock.subs32_n SymBlock.subs64_v SymBlock.subs32_v addWithCarry64_sub_fst
  addWithCarry32_sub_fst
-- `ADDS` / `CMN` and `SBCS` shapes; the `ADDS` carry goes through the generic carry rule.
attribute [decomp_norm ↓ 1500] conditionHolds_eq_adds64 conditionHolds_ne_adds64
  conditionHolds_mi_adds64 conditionHolds_pl_adds64 conditionHolds_eq_adds32
  conditionHolds_ne_adds32 conditionHolds_mi_adds32 conditionHolds_pl_adds32
  conditionHolds_eq_addsPState64 conditionHolds_ne_addsPState64 conditionHolds_mi_addsPState64
  conditionHolds_pl_addsPState64 conditionHolds_eq_addsPState32 conditionHolds_ne_addsPState32
  conditionHolds_mi_addsPState32 conditionHolds_pl_addsPState32 addsPState64_c addsPState32_c
  SymBlock.adds64_n SymBlock.adds32_n SymBlock.adds64_v SymBlock.adds32_v
  sbcWithCarry64_c sbcWithCarry32_c addWithCarry64_sbc_fst addWithCarry64_add_fst
  addWithCarry32_add_fst
attribute [decomp_norm] addWithCarry64_c addWithCarry32_c addWithCarry64_n addWithCarry32_n
  addWithCarry64_z addWithCarry32_z addWithCarry64_adc_fst
attribute [decomp_norm] evalAddSub_w64_add evalAddSub_w64_adds evalAddSub_w64_sub
  evalAddSub_w64_subs evalAddSub_w64_adc evalAddSub_w64_adcs evalAddSub_w64_sbc
  evalAddSub_w64_sbcs evalAddSub_w32_add evalAddSub_w32_sub evalAddSub_w32_subs
  evalAddSub_w32_adds
attribute [decomp_norm 100] conditionHolds_eq_flag conditionHolds_ne_flag conditionHolds_cs_flag
  conditionHolds_cc_flag conditionHolds_mi_flag conditionHolds_pl_flag conditionHolds_vs_flag
  conditionHolds_vc_flag conditionHolds_hi_flag conditionHolds_ls_flag conditionHolds_ge_flag
  conditionHolds_lt_flag conditionHolds_gt_flag conditionHolds_le_flag conditionHolds_al
  conditionHolds_nv
attribute [decomp_norm] BitVec.msb_eq_decide

/-! ## Multi-limb carry chains -/

/-- The high 64 bits of a 128-bit sum: the high limbs plus the carry out of the low limbs. -/
theorem add128_hi (a b : BitVec 128) :
    (a + b).extractLsb' 64 64 =
      a.extractLsb' 64 64 + b.extractLsb' 64 64 +
        (if 2 ^ 64 ≤ (a.setWidth 64).toNat + (b.setWidth 64).toNat then 1#64 else 0#64) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.shiftRight_eq_div_pow]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- A 128-bit sum of limb concatenations is the limbwise sum with the low-limb carry propagated
    into the high limb (an `ADDS` / `ADC` chain). -/
theorem append_add_append (aHi aLo bHi bLo : BitVec 64) :
    (aHi ++ aLo) + (bHi ++ bLo) =
      (aHi + bHi + (if 2 ^ 64 ≤ aLo.toNat + bLo.toNat then 1#64 else 0#64)) ++ (aLo + bLo) := by
  apply BitVec.eq_of_toNat_eq
  have h1 := aHi.isLt; have h2 := aLo.isLt; have h3 := bHi.isLt; have h4 := bLo.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt h2, ← Nat.shiftLeft_add_eq_or_of_lt h4,
    ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  simp only [Nat.shiftLeft_eq]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- The low `n` bits extracted at offset 0 are a truncation. -/
theorem extractLsb'_zero_eq_setWidth {w : Nat} (n : Nat) (x : BitVec w) :
    x.extractLsb' 0 n = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb']

attribute [decomp_norm] add128_hi append_add_append extractLsb'_zero_eq_setWidth
  BitVec.extractLsb'_append_eq_left BitVec.extractLsb'_append_eq_right
  BitVec.setWidth_append_eq_right BitVec.setWidth_add BitVec.setWidth_mul

/-! ## Widths -/

/-- Truncating a sign extension to at most the source width drops the extension. -/
theorem setWidth_signExtend_of_le {w v k : Nat} (x : BitVec w) (hkv : k ≤ v) (hkw : k ≤ w) :
    (x.signExtend v).setWidth k = x.setWidth k := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  have h1 : i < v := by omega
  have h2 : i < w := by omega
  simp [h1, h2]

attribute [decomp_norm] BitVec.truncate_eq_setWidth BitVec.zeroExtend_eq_setWidth
  BitVec.setWidth_eq BitVec.setWidth_setWidth_of_le BitVec.signExtend_eq_setWidth_of_le
  setWidth_signExtend_of_le
attribute [decomp_norm ↓ 1500] SymBlock.ult_zext32_eq SymBlock.ule_zext32_eq
  SymBlock.slt_sext32_eq SymBlock.sle_sext32_eq SymBlock.zext32_eq_iff

/-! ## Shifts and multiplication -/

/-- A left shift by a constant is a multiplication by a power of two. -/
theorem shiftLeft_eq_mul {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< k = x * BitVec.ofNat w (2 ^ k) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow]

/-- A logical right shift by a constant is a `Nat` division by a power of two. -/
theorem toNat_ushiftRight_eq_div {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `UMULH` (high 64 bits of the 128-bit product) as a `Nat` quotient. -/
theorem umulh_eq (x y : BitVec 64) :
    ((x.setWidth 128 * y.setWidth 128) >>> 64).setWidth 64 =
      BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt hxy]

/-- `LSL` shifted-register operand at 64 bits. -/
theorem shiftVal_w64_lsl (x : BitVec 64) (k : Nat) :
    shiftVal .W64 x .LSL k = x <<< (k % 64) := rfl
/-- `LSR` shifted-register operand at 64 bits. -/
theorem shiftVal_w64_lsr (x : BitVec 64) (k : Nat) :
    shiftVal .W64 x .LSR k = x >>> (k % 64) := rfl
/-- `ASR` shifted-register operand at 64 bits. -/
theorem shiftVal_w64_asr (x : BitVec 64) (k : Nat) :
    shiftVal .W64 x .ASR k = x.sshiftRight (k % 64) := rfl
/-- `ROR` shifted-register operand at 64 bits. -/
theorem shiftVal_w64_ror (x : BitVec 64) (k : Nat) :
    shiftVal .W64 x .ROR k = x.rotateRight (k % 64) := rfl
/-- `LSL` shifted-register operand at 32 bits, zero-extended to 64. -/
theorem shiftVal_w32_lsl (x : BitVec 64) (k : Nat) :
    shiftVal .W32 x .LSL k = (x.setWidth 32 <<< (k % 32)).setWidth 64 := rfl
/-- `LSR` shifted-register operand at 32 bits, zero-extended to 64. -/
theorem shiftVal_w32_lsr (x : BitVec 64) (k : Nat) :
    shiftVal .W32 x .LSR k = (x.setWidth 32 >>> (k % 32)).setWidth 64 := rfl
/-- `UXTB` extended-register operand at 64 bits. -/
theorem extendVal_w64_uxtb (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .UXTB k = (x.setWidth 8).setWidth 64 <<< k := rfl
/-- `UXTH` extended-register operand at 64 bits. -/
theorem extendVal_w64_uxth (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .UXTH k = (x.setWidth 16).setWidth 64 <<< k := rfl
/-- `UXTW` extended-register operand at 64 bits. -/
theorem extendVal_w64_uxtw (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .UXTW k = (x.setWidth 32).setWidth 64 <<< k := rfl
/-- `UXTX` extended-register operand at 64 bits. -/
theorem extendVal_w64_uxtx (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .UXTX k = x <<< k := rfl
/-- `SXTB` extended-register operand at 64 bits. -/
theorem extendVal_w64_sxtb (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .SXTB k = (x.setWidth 8).signExtend 64 <<< k := rfl
/-- `SXTH` extended-register operand at 64 bits. -/
theorem extendVal_w64_sxth (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .SXTH k = (x.setWidth 16).signExtend 64 <<< k := rfl
/-- `SXTW` extended-register operand at 64 bits. -/
theorem extendVal_w64_sxtw (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .SXTW k = (x.setWidth 32).signExtend 64 <<< k := rfl
/-- `SXTX` extended-register operand at 64 bits. -/
theorem extendVal_w64_sxtx (x : BitVec 64) (k : Nat) :
    extendVal .W64 x .SXTX k = x <<< k := rfl

/-- `AND` / `ANDS` result at 64 bits. -/
theorem evalLogical_w64_and_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .AND x y ps).1 = x &&& y := rfl
/-- `ANDS` / `TST` result at 64 bits. -/
theorem evalLogical_w64_ands_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .ANDS x y ps).1 = x &&& y := rfl
/-- `BIC` result at 64 bits. -/
theorem evalLogical_w64_bic_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .BIC x y ps).1 = x &&& ~~~y := rfl
/-- `ORR` result at 64 bits. -/
theorem evalLogical_w64_orr_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .ORR x y ps).1 = x ||| y := rfl
/-- `ORN` result at 64 bits. -/
theorem evalLogical_w64_orn_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .ORN x y ps).1 = x ||| ~~~y := rfl
/-- `EOR` result at 64 bits. -/
theorem evalLogical_w64_eor_fst (x y : BitVec 64) (ps : PState) :
    (evalLogical .W64 .EOR x y ps).1 = x ^^^ y := rfl
/-- `MADD` (`MUL` when `a = 0`) at 64 bits. -/
theorem evalDataProc3Val_w64_madd (n m a : BitVec 64) :
    SymBlock.evalDataProc3Val .W64 .MADD n m a = a + n * m := rfl
/-- `MSUB` (`MNEG` when `a = 0`) at 64 bits. -/
theorem evalDataProc3Val_w64_msub (n m a : BitVec 64) :
    SymBlock.evalDataProc3Val .W64 .MSUB n m a = a - n * m := rfl
/-- `UMADDL` (`UMULL` when `a = 0`): widening 32 x 32 -> 64 multiply-add. -/
theorem evalDataProc3Val_umaddl (w : Width) (n m a : BitVec 64) :
    SymBlock.evalDataProc3Val w .UMADDL n m a =
      a + (n.setWidth 32).setWidth 64 * (m.setWidth 32).setWidth 64 := rfl
/-- `UMULH`: the high 64 bits of the 128-bit unsigned product (then `umulh_eq`). -/
theorem evalDataProc3Val_umulh (w : Width) (n m a : BitVec 64) :
    SymBlock.evalDataProc3Val w .UMULH n m a =
      ((n.setWidth 128 * m.setWidth 128) >>> 64).setWidth 64 := rfl

attribute [decomp_norm ↓ 2000] umulh_eq
attribute [decomp_norm 1500] BitVec.shiftLeft_zero BitVec.ushiftRight_zero
attribute [decomp_norm] toNat_ushiftRight_eq_div shiftVal_w64_lsl
  shiftVal_w64_lsr shiftVal_w64_asr shiftVal_w64_ror shiftVal_w32_lsl shiftVal_w32_lsr
  extendVal_w64_uxtb extendVal_w64_uxth extendVal_w64_uxtw extendVal_w64_uxtx extendVal_w64_sxtb
  extendVal_w64_sxth extendVal_w64_sxtw extendVal_w64_sxtx evalLogical_w64_and_fst
  evalLogical_w64_ands_fst evalLogical_w64_bic_fst evalLogical_w64_orr_fst evalLogical_w64_orn_fst
  evalLogical_w64_eor_fst evalDataProc3Val_w64_madd evalDataProc3Val_w64_msub
  evalDataProc3Val_umaddl evalDataProc3Val_umulh

/-! ## `Option` -/

/-- `Option.bind` distributes over `if`. -/
theorem option_bind_ite {α β : Type _} (c : Prop) [Decidable c] (a b : Option α)
    (f : α → Option β) : (if c then a else b).bind f = if c then a.bind f else b.bind f := by
  split <;> rfl

/-- `Option.map` distributes over `if`. -/
theorem option_map_ite {α β : Type _} (c : Prop) [Decidable c] (a b : Option α) (f : α → β) :
    (if c then a else b).map f = if c then a.map f else b.map f := by
  split <;> rfl

/-- An `if` whose branches are both `some` is `some` of an `if`. -/
theorem ite_some_some {α : Type _} (c : Prop) [Decidable c] (a b : α) :
    (if c then some a else some b) = some (if c then a else b) := by
  split <;> rfl

attribute [decomp_norm] option_bind_ite option_map_ite ite_some_some Option.bind_some
  Option.bind_none Option.map_some Option.map_none Option.bind_eq_bind Option.pure_def
  Option.map_eq_map Option.some.injEq Prod.mk.injEq Option.getD_some Option.getD_none
  Option.ite_none_right_eq_some Option.ite_none_left_eq_some Option.isSome_some
  Option.isSome_none

/-! ## `BitVec` ↔ `Nat` range bridges -/

/-- Masking with `2 ^ 32 - 1` keeps the low 32 bits of the `Nat` value. -/
theorem toNat_and_4294967295 {w : Nat} (x : BitVec w) :
    (x &&& 4294967295#w).toNat = x.toNat % 4294967296 :=
  BitVec.toNat_and_twoPow_sub_one x 32

attribute [decomp_norm] BitVec.toNat_add_of_lt BitVec.toNat_mul_of_lt BitVec.toNat_sub_of_le
  ProofLib.BV.Arith.ofNat_sub_of_le BitVec.ofNat_add BitVec.ofNat_mul BitVec.ofNat_toNat
attribute [decomp_norm] BitVec.toNat_and_twoPow_sub_one BitVec.toNat_and_1 BitVec.toNat_and_3
  BitVec.toNat_and_7 BitVec.toNat_and_15 BitVec.toNat_and_31 BitVec.toNat_and_63
  BitVec.toNat_and_255 BitVec.toNat_and_511 BitVec.toNat_and_4095 BitVec.toNat_and_65535
  toNat_and_4294967295

/-! ## Arithmetic identities -/

attribute [decomp_norm] BitVec.add_zero BitVec.zero_add BitVec.sub_zero BitVec.sub_self
  BitVec.mul_one BitVec.one_mul BitVec.mul_zero BitVec.zero_mul BitVec.add_sub_cancel
  BitVec.sub_add_cancel Nat.add_zero Nat.zero_add Nat.mul_one Nat.one_mul Nat.sub_zero
  Nat.mul_zero Nat.zero_mul

/-! ## `if` with literal arms (`CSET` idioms)

`CSET` / `CSINC` materialise a `Bool` as `if c then 1#w else 0#w`, and later instructions compare,
mask, or truncate that value. When every other operand is a closed term, the operation is pushed
into both arms (`apply_ite`), the arms fold to literals, and a `Prop` / `Bool` `if` with constant
arms collapses to its condition. Pushing `setWidth` or `toNat` into an `if` duplicates nothing, so
it is a plain rewrite rule for arbitrary arms. -/

/-- An `if` with arms `True` / `False` is its condition. -/
theorem ite_prop_true_false (p : Prop) [Decidable p] : (if p then True else False) = p := by
  by_cases h : p <;> simp [h]

/-- An `if` with arms `False` / `True` is the negated condition. -/
theorem ite_prop_false_true (p : Prop) [Decidable p] : (if p then False else True) = ¬p := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` with arms `true` / `false` is the decided condition. -/
theorem ite_bool_true_false (p : Prop) [Decidable p] :
    (if p then true else false) = decide p := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` with arms `false` / `true` is the decided negated condition. -/
theorem ite_bool_false_true (p : Prop) [Decidable p] :
    (if p then false else true) = decide (¬p) := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` whose else arm is `false` is a conjunction (short-circuit `CCMP` chains). -/
theorem ite_bool_else_false (p : Prop) [Decidable p] (b : Bool) :
    (if p then b else false) = (decide p && b) := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` whose else arm is `true` is an implication, written as a disjunction. -/
theorem ite_bool_else_true (p : Prop) [Decidable p] (b : Bool) :
    (if p then b else true) = (!decide p || b) := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` whose then arm is `true` is a disjunction. -/
theorem ite_bool_then_true (p : Prop) [Decidable p] (b : Bool) :
    (if p then true else b) = (decide p || b) := by
  by_cases h : p <;> simp [h]

/-- A `Bool` `if` whose then arm is `false` is a conjunction with the negated condition. -/
theorem ite_bool_then_false (p : Prop) [Decidable p] (b : Bool) :
    (if p then false else b) = (!decide p && b) := by
  by_cases h : p <;> simp [h]

/-- `setWidth` distributes over `if`. -/
theorem setWidth_ite {w : Nat} (v : Nat) (p : Prop) [Decidable p] (a b : BitVec w) :
    (if p then a else b).setWidth v = if p then a.setWidth v else b.setWidth v := by
  split <;> rfl

/-- `toNat` distributes over `if`. -/
theorem toNat_ite {w : Nat} (p : Prop) [Decidable p] (a b : BitVec w) :
    (if p then a else b).toNat = if p then a.toNat else b.toNat := by
  split <;> rfl

/-- A logical right shift distributes over `if`. -/
theorem ushiftRight_ite {w : Nat} (k : Nat) (p : Prop) [Decidable p] (a b : BitVec w) :
    (if p then a else b) >>> k = if p then a >>> k else b >>> k := by
  split <;> rfl

/-- `allOnes w` as a literal (folded by the literal simprocs at a concrete width). -/
theorem allOnes_eq_ofNat (w : Nat) : BitVec.allOnes w = BitVec.ofNat w (2 ^ w - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h := Nat.two_pow_pos w
  simp only [BitVec.toNat_allOnes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

attribute [decomp_norm 1100] ite_prop_true_false ite_prop_false_true ite_bool_true_false
  ite_bool_false_true
attribute [decomp_norm] ite_bool_else_false ite_bool_else_true ite_bool_then_true
  ite_bool_then_false Bool.and_true Bool.true_and Bool.and_false Bool.false_and Bool.or_true
  Bool.true_or Bool.or_false Bool.false_or Bool.not_true Bool.not_false setWidth_ite toNat_ite
  ushiftRight_ite

/-! ## Two-limb (128-bit) normal forms

A 128-bit value in two 64-bit registers is `x.setWidth 64` (low limb) and `(x >>> 64).setWidth 64`
(high limb). Machine code computes 128-bit `+` / `-` / `-x` / comparisons as `ADDS`+`ADC`,
`SUBS`+`SBC`, `NEGS`+`NGC`, `CMP`+`SBCS` chains; the rules below rewrite the model side (a limb of a
128-bit result) into the same chain, and fold a full carry / borrow chain back into one 128-bit
`toNat` comparison. The constant `2 ^ 64` is written as the literal that `Nat.reducePow` produces. -/

theorem setWidth_sub_of_le {w : Nat} (v : Nat) (x y : BitVec w) (h : v ≤ w) :
    (x - y).setWidth v = x.setWidth v - y.setWidth v := by
  have := BitVec.setWidth_add (x - y) y h
  rw [BitVec.sub_add_cancel] at this
  rw [this, BitVec.add_sub_cancel]

theorem setWidth_neg_of_le {w : Nat} (v : Nat) (x : BitVec w) (h : v ≤ w) :
    (-x).setWidth v = -x.setWidth v := by
  rw [← BitVec.zero_sub, setWidth_sub_of_le v _ _ h, ← BitVec.zero_sub]
  simp

theorem hi128_add (x y : BitVec 128) :
    ((x + y) >>> 64).setWidth 64 =
      (x >>> 64).setWidth 64 + (y >>> 64).setWidth 64 +
        (if 18446744073709551616 ≤ (x.setWidth 64).toNat + (y.setWidth 64).toNat
         then 1#64 else 0#64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem hi128_add_carry (x y : BitVec 128) (c : Bool) :
    ((x + y + (if c = true then 1#128 else 0#128)) >>> 64).setWidth 64 =
      (x >>> 64).setWidth 64 + (y >>> 64).setWidth 64 +
        (if 18446744073709551616 ≤
            (x.setWidth 64).toNat + (y.setWidth 64).toNat + (if c = true then 1 else 0)
         then 1#64 else 0#64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  cases c <;> simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_add, Bool.false_eq_true,
    ↓reduceIte, BitVec.toNat_ofNat] <;> split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem hi128_sub (x y : BitVec 128) :
    ((x - y) >>> 64).setWidth 64 =
      (x >>> 64).setWidth 64 - (y >>> 64).setWidth 64 -
        (if y.setWidth 64 ≤ x.setWidth 64 then 0#64 else 1#64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem hi128_sub_borrow (x y : BitVec 128) (c : Bool) :
    ((x - y - (if c = true then 1#128 else 0#128)) >>> 64).setWidth 64 =
      (x >>> 64).setWidth 64 - (y >>> 64).setWidth 64 -
        (if (y.setWidth 64).toNat + (if c = true then 1 else 0) ≤ (x.setWidth 64).toNat
         then 0#64 else 1#64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  cases c <;> simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, Bool.false_eq_true,
    ↓reduceIte, BitVec.toNat_ofNat] <;> split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem hi128_neg (x : BitVec 128) :
    ((-x) >>> 64).setWidth 64 =
      -(x >>> 64).setWidth 64 - (if (x.setWidth 64).toNat = 0 then 0#64 else 1#64) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_neg]
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem carry128_add (x y : BitVec 128) :
    (18446744073709551616 ≤ ((x >>> 64).setWidth 64).toNat + ((y >>> 64).setWidth 64).toNat +
      (if 18446744073709551616 ≤ (x.setWidth 64).toNat + (y.setWidth 64).toNat then 1 else 0)) =
      (2 ^ 128 ≤ x.toNat + y.toNat) := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, eq_iff_iff]
  split <;> omega

theorem carry128_add_carry (x y : BitVec 128) (c : Bool) :
    (18446744073709551616 ≤ ((x >>> 64).setWidth 64).toNat + ((y >>> 64).setWidth 64).toNat +
      (if 18446744073709551616 ≤
          (x.setWidth 64).toNat + (y.setWidth 64).toNat + (if c = true then 1 else 0)
       then 1 else 0)) =
      (2 ^ 128 ≤ x.toNat + y.toNat + (if c = true then 1 else 0)) := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, eq_iff_iff]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> omega

theorem borrow128_sub (x y : BitVec 128) :
    (((y >>> 64).setWidth 64).toNat +
        (if y.setWidth 64 ≤ x.setWidth 64 then 0 else 1) ≤
      ((x >>> 64).setWidth 64).toNat) = (y ≤ x) := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, eq_iff_iff]
  split <;> omega

theorem borrow128_sub_borrow (x y : BitVec 128) (c : Bool) :
    (((y >>> 64).setWidth 64).toNat +
        (if (y.setWidth 64).toNat + (if c = true then 1 else 0) ≤ (x.setWidth 64).toNat
         then 0 else 1) ≤
      ((x >>> 64).setWidth 64).toNat) = (y.toNat + (if c = true then 1 else 0) ≤ x.toNat) := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, eq_iff_iff]
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> omega

theorem eq128_limbs (x y : BitVec 128) :
    (x.setWidth 64 = y.setWidth 64 ∧ (x >>> 64).setWidth 64 = (y >>> 64).setWidth 64) =
      (x = y) := by
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have e1 := congrArg BitVec.toNat h1; have e2 := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at e1 e2
    omega
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem ne128_limbs (x y : BitVec 128) :
    (¬x.setWidth 64 = y.setWidth 64 ∨ ¬(x >>> 64).setWidth 64 = (y >>> 64).setWidth 64) =
      ¬(x = y) := by
  rw [← eq128_limbs x y]
  exact propext (Classical.not_and_iff_not_or_not).symm

/-- The high limb of a complement is the complement of the high limb. -/
theorem hi128_not (x : BitVec 128) : ((~~~x) >>> 64).setWidth 64 = ~~~((x >>> 64).setWidth 64) := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not,
    BitVec.getElem_not, BitVec.getElem_setWidth]
  have : 64 + i < 128 := by omega
  simp [this]

/-- The high limb of a 128-bit product (`MUL` / `UMULH` / two `MADD`s). -/
theorem hi128_mul (x y : BitVec 128) :
    ((x * y) >>> 64).setWidth 64 =
      BitVec.ofNat 64 ((x.setWidth 64).toNat * (y.setWidth 64).toNat / 18446744073709551616) +
        x.setWidth 64 * (y >>> 64).setWidth 64 + (x >>> 64).setWidth 64 * y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *
  generalize x.toNat = X at *
  generalize y.toNat = Y at *
  obtain ⟨X1, X0, hX0, rfl⟩ : ∃ X1 X0, X0 < 18446744073709551616 ∧
      X = X0 + 18446744073709551616 * X1 :=
    ⟨X / 18446744073709551616, X % 18446744073709551616, Nat.mod_lt _ (by decide), by omega⟩
  obtain ⟨Y1, Y0, hY0, rfl⟩ : ∃ Y1 Y0, Y0 < 18446744073709551616 ∧
      Y = Y0 + 18446744073709551616 * Y1 :=
    ⟨Y / 18446744073709551616, Y % 18446744073709551616, Nat.mod_lt _ (by decide), by omega⟩
  have e1 : (X0 + 18446744073709551616 * X1) % 18446744073709551616 = X0 := by omega
  have e2 : (X0 + 18446744073709551616 * X1) / 18446744073709551616 % 18446744073709551616 = X1 := by
    omega
  have e3 : (Y0 + 18446744073709551616 * Y1) % 18446744073709551616 = Y0 := by omega
  have e4 : (Y0 + 18446744073709551616 * Y1) / 18446744073709551616 % 18446744073709551616 = Y1 := by
    omega
  have hexp : (X0 + 18446744073709551616 * X1) * (Y0 + 18446744073709551616 * Y1) =
      X0 * Y0 + 18446744073709551616 * (X0 * Y1 + X1 * Y0) +
        18446744073709551616 * (18446744073709551616 * (X1 * Y1)) := by
    grind
  rw [e1, e2, e3, e4, hexp]
  generalize X0 * Y0 = A; generalize X0 * Y1 = B; generalize X1 * Y0 = C; generalize X1 * Y1 = D
  omega

/-- The high limb of a zero-extended value is zero. -/
theorem setWidth_ushiftRight_setWidth_of_le {w : Nat} (v k u : Nat) (x : BitVec w) (h : w ≤ k) :
    ((x.setWidth v) >>> k).setWidth u = 0#u := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.zero_mod]
  have : x.toNat % 2 ^ v < 2 ^ k :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))
  rw [Nat.div_eq_of_lt this, Nat.zero_mod]

/-- `x ≤ x + y` (an unsigned add that did not wrap) is the no-carry condition. -/
theorem le_add_self_eq {w : Nat} (x y : BitVec w) :
    (x ≤ x + y) = ¬(2 ^ w ≤ x.toNat + y.toNat) := by
  have hx := x.isLt; have hy := y.isLt
  rw [BitVec.le_def, BitVec.toNat_add]
  apply propext
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The high half of a 64×64 product is at most `2 ^ 64 - 2`, so adding a carry bit to it never
    carries out (`UMULH` then `ADC`/`CINC` in a multiply-add). -/
theorem umulh_add_bit_no_carry (x y : BitVec 64) (c : Prop) [Decidable c] :
    (18446744073709551616 ≤
        (BitVec.ofNat 64 (x.toNat * y.toNat / 18446744073709551616)).toNat + (if c then 1 else 0)) =
      False := by
  have hx := x.isLt; have hy := y.isLt
  have hxy : x.toNat * y.toNat ≤ 18446744073709551615 * 18446744073709551615 :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [BitVec.toNat_ofNat, eq_iff_iff, iff_false, Nat.not_le]
  generalize x.toNat * y.toNat = P at *
  split <;> omega

/-- A conditional increment is an addition of a conditional addend. -/
theorem ite_add_left {w : Nat} (p : Prop) [Decidable p] (x k : BitVec w) :
    (if p then x + k else x) = x + (if p then k else 0#w) := by
  split <;> simp

/-- A conditional increment is an addition of a conditional addend. -/
theorem ite_add_right {w : Nat} (p : Prop) [Decidable p] (x k : BitVec w) :
    (if p then x else x + k) = x + (if p then 0#w else k) := by
  split <;> simp

theorem ite_lt_swap {α : Sort _} (a b : Nat) (t e : α) :
    (if a < b then t else e) = (if b ≤ a then e else t) := by
  by_cases h : a < b
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.not_lt.mp h]

theorem toNat_le_toNat {w : Nat} (x y : BitVec w) : (x.toNat ≤ y.toNat) = (x ≤ y) := by
  simp [BitVec.le_def]

theorem toNat_lt_toNat {w : Nat} (x y : BitVec w) : (x.toNat < y.toNat) = (x < y) := by
  simp [BitVec.lt_def]

attribute [decomp_norm] setWidth_neg_of_le hi128_add hi128_sub hi128_neg carry128_add
  borrow128_sub eq128_limbs ne128_limbs ite_lt_swap toNat_le_toNat toNat_lt_toNat ge_iff_le gt_iff_lt
attribute [decomp_norm 1100] hi128_add_carry hi128_sub_borrow carry128_add_carry
  borrow128_sub_borrow
attribute [decomp_norm] setWidth_sub_of_le
/- Bitwise limb distribution. One canonical operand order for the commutative operators
   (`&&&`, `|||`, `^^^`, `*`) comes from the `commOrder*` simprocs below, so both sides of an
   equation agree. -/
attribute [decomp_norm] BitVec.setWidth_and BitVec.setWidth_or BitVec.setWidth_xor
  BitVec.ushiftRight_and_distrib BitVec.ushiftRight_or_distrib BitVec.ushiftRight_xor_distrib
  hi128_not
attribute [decomp_norm] hi128_mul setWidth_ushiftRight_setWidth_of_le le_add_self_eq ite_add_left
  ite_add_right umulh_add_bit_no_carry
attribute [decomp_norm 900] BitVec.setWidth_not

/-! ## Variable shifts, funnel shifts, and two-limb (128-bit) shifts and rotates

`LSLV` / `LSRV` shift by the register amount modulo the width, so a shift by a register reaches
the normaliser as `x <<< (r.toNat % 64)`. A 128-bit shift or rotate shifts each limb by `s % 64`
and combines the limbs with a funnel `(y >>> 1) >>> (~~~s % 64)`, which is `y >>> (64 - s % 64)`
and `0` when `s % 64 = 0`. It then selects on bit 6 of the amount (`TST s, #64` + `CSEL`).
The normal forms:
- amounts reduce to `x.toNat % m`, through truncations and complements;
- funnels fold to one shift by `m - n % m`;
- a single-bit test `x &&& 2 ^ j = 0` becomes `x % 2 ^ (j + 1) < 2 ^ j` (simproc
  `andPow2EqZero`);
- the limbs of a 128-bit shift or rotate by `n % 128` are the limbwise forms above;
- `if` is pushed out of shifts and merged across `|||`. -/

/-- The residue of a truncated value modulo a divisor of `2 ^ v` is the residue of the value. -/
theorem toNat_setWidth_mod {w : Nat} (v m : Nat) (x : BitVec w) (h : 2 ^ v % m = 0) :
    (x.setWidth v).toNat % m = x.toNat % m := by
  rw [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero h)]

/-- The residue of `~~~x` modulo a divisor `m` of `2 ^ w` is `m - 1 - x % m`. -/
theorem toNat_not_mod {w : Nat} (m : Nat) (x : BitVec w) (h : 2 ^ w % m = 0) (hm : 0 < m) :
    (~~~x).toNat % m = m - 1 - x.toNat % m := by
  rw [BitVec.toNat_not]
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
  have hx := x.isLt
  have hdm := Nat.div_add_mod x.toNat m
  have hr := Nat.mod_lt x.toNat hm
  rw [hq] at hx ⊢
  generalize x.toNat % m = r at *
  generalize x.toNat / m = a at *
  generalize x.toNat = t at *
  subst hdm
  have haq : a < q := by
    rcases Nat.lt_or_ge a q with h' | h'
    · exact h'
    · have := Nat.mul_le_mul_left m h'
      omega
  obtain ⟨b, rfl⟩ : ∃ b, q = a + 1 + b := ⟨q - (a + 1), by omega⟩
  have e : m * (a + 1 + b) - 1 - (m * a + r) = m * b + (m - 1 - r) := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- A funnel right shift: `(x >>> 1) >>> (m - 1 - n % m)` is `x >>> (m - n % m)`. -/
theorem ushiftRight_one_ushiftRight_mod {w : Nat} (x : BitVec w) (n m k : Nat) (hk : k + 1 = m) :
    x >>> 1 >>> (k - n % m) = x >>> (m - n % m) := by
  have hn : n % m < m := Nat.mod_lt n (by omega)
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_ushiftRight]
  congr 1
  omega

/-- A funnel left shift (`x <<< 1` normalised to `2 * x`): `(2 * x) <<< (m - 1 - n % m)` is
    `x <<< (m - n % m)`. -/
theorem two_mul_shiftLeft_mod {w : Nat} (x : BitVec w) (n m k : Nat) (hk : k + 1 = m) :
    (2#w * x) <<< (k - n % m) = x <<< (m - n % m) := by
  have hn : n % m < m := Nat.mod_lt n (by omega)
  rw [(BitVec.mul_comm _ _).trans (shiftLeft_eq_mul x 1).symm, ← BitVec.shiftLeft_add]
  congr 1
  omega

/-- See `two_mul_shiftLeft_mod`. -/
theorem mul_two_shiftLeft_mod {w : Nat} (x : BitVec w) (n m k : Nat) (hk : k + 1 = m) :
    (x * 2#w) <<< (k - n % m) = x <<< (m - n % m) := by
  rw [BitVec.mul_comm]
  exact two_mul_shiftLeft_mod x n m k hk

/-- Bit `j` of `x` is clear iff `x % 2 ^ (j + 1) < 2 ^ j` (`TST x, #(2 ^ j)`). -/
theorem and_twoPow_eq_zero {w : Nat} (x : BitVec w) (j : Nat) (hj : j < w) :
    (x &&& BitVec.ofNat w (2 ^ j) = 0#w) = (x.toNat % 2 ^ (j + 1) < 2 ^ j) := by
  have hbit : (x &&& BitVec.ofNat w (2 ^ j) = 0#w) ↔ x.getLsbD j = false := by
    constructor
    · intro h0
      have h := congrArg (fun v => v.getLsbD j) h0
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_self, hj,
        decide_true, Bool.true_and, Bool.and_true, Nat.zero_testBit] at h
      exact h
    · intro hb
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
      by_cases hij : j = i
      · subst hij
        simp [hb]
      · simp [hij]
  rw [propext hbit]
  have hc : 0 < 2 ^ j := Nat.two_pow_pos j
  have hm : x.toNat % 2 ^ (j + 1) = x.toNat % 2 ^ j + 2 ^ j * (x.toNat / 2 ^ j % 2) := by
    rw [Nat.pow_succ]
    exact Nat.mod_mul
  rw [hm, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  have hr := Nat.mod_lt x.toNat hc
  have hd := Nat.mod_lt (x.toNat / 2 ^ j) (show 0 < 2 by decide)
  generalize x.toNat % 2 ^ j = r at *
  generalize x.toNat / 2 ^ j % 2 = d at *
  generalize 2 ^ j = c at *
  apply propext
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> simp <;> omega

/-- See `and_twoPow_eq_zero`. -/
theorem twoPow_and_eq_zero {w : Nat} (x : BitVec w) (j : Nat) (hj : j < w) :
    (BitVec.ofNat w (2 ^ j) &&& x = 0#w) = (x.toNat % 2 ^ (j + 1) < 2 ^ j) := by
  rw [BitVec.and_comm]
  exact and_twoPow_eq_zero x j hj

/-- A left shift distributes over `if`. -/
theorem shiftLeft_ite {w : Nat} (k : Nat) (p : Prop) [Decidable p] (a b : BitVec w) :
    (if p then a else b) <<< k = if p then a <<< k else b <<< k := by
  split <;> rfl

/-- Two `if`s on the same condition merge across `|||`. -/
theorem ite_or_ite {w : Nat} (p : Prop) [Decidable p] (a b c d : BitVec w) :
    ((if p then a else b) ||| (if p then c else d)) = if p then a ||| c else b ||| d := by
  split <;> rfl

/-- The low limb of a 128-bit left shift by `n % 128`. -/
theorem lo128_shiftLeft (x : BitVec 128) (n : Nat) :
    (x <<< (n % 128)).setWidth 64 =
      if n % 128 < 64 then x.setWidth 64 <<< (n % 64) else 0#64 := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft]
    grind
  · simp only [hr, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_zero]
    grind

/-- The high limb of a 128-bit left shift by `n % 128`. -/
theorem hi128_shiftLeft (x : BitVec 128) (n : Nat) :
    ((x <<< (n % 128)) >>> 64).setWidth 64 =
      if n % 128 < 64 then
        (x >>> 64).setWidth 64 <<< (n % 64) ||| x.setWidth 64 >>> (64 - n % 64)
      else x.setWidth 64 <<< (n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight]
    grind

/-- The low limb of a 128-bit logical right shift by `n % 128`. -/
theorem lo128_ushiftRight (x : BitVec 128) (n : Nat) :
    (x >>> (n % 128)).setWidth 64 =
      if n % 128 < 64 then
        x.setWidth 64 >>> (n % 64) ||| (x >>> 64).setWidth 64 <<< (64 - n % 64)
      else (x >>> 64).setWidth 64 >>> (n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    grind

/-- The high limb of a 128-bit logical right shift by `n % 128`. -/
theorem hi128_ushiftRight (x : BitVec 128) (n : Nat) :
    ((x >>> (n % 128)) >>> 64).setWidth 64 =
      if n % 128 < 64 then (x >>> 64).setWidth 64 >>> (n % 64) else 0#64 := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight]
    grind
  · simp only [hr, ↓reduceIte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_zero]
    grind

/-- The low limb of a 128-bit rotate left by `n % 128`. -/
theorem lo128_rotateLeft (x : BitVec 128) (n : Nat) :
    (x.rotateLeft (n % 128)).setWidth 64 =
      if n % 128 < 64 then
        x.setWidth 64 <<< (n % 64) ||| (x >>> 64).setWidth 64 >>> (64 - n % 64)
      else (x >>> 64).setWidth 64 <<< (n % 64) ||| x.setWidth 64 >>> (64 - n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind

/-- The high limb of a 128-bit rotate left by `n % 128`. -/
theorem hi128_rotateLeft (x : BitVec 128) (n : Nat) :
    ((x.rotateLeft (n % 128)) >>> 64).setWidth 64 =
      if n % 128 < 64 then
        (x >>> 64).setWidth 64 <<< (n % 64) ||| x.setWidth 64 >>> (64 - n % 64)
      else x.setWidth 64 <<< (n % 64) ||| (x >>> 64).setWidth 64 >>> (64 - n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateLeft, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind

/-- The low limb of a 128-bit rotate right by `n % 128`. -/
theorem lo128_rotateRight (x : BitVec 128) (n : Nat) :
    (x.rotateRight (n % 128)).setWidth 64 =
      if n % 128 < 64 then
        x.setWidth 64 >>> (n % 64) ||| (x >>> 64).setWidth 64 <<< (64 - n % 64)
      else (x >>> 64).setWidth 64 >>> (n % 64) ||| x.setWidth 64 <<< (64 - n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind

/-- The high limb of a 128-bit rotate right by `n % 128`. -/
theorem hi128_rotateRight (x : BitVec 128) (n : Nat) :
    ((x.rotateRight (n % 128)) >>> 64).setWidth 64 =
      if n % 128 < 64 then
        (x >>> 64).setWidth 64 >>> (n % 64) ||| x.setWidth 64 <<< (64 - n % 64)
      else x.setWidth 64 >>> (n % 64) ||| (x >>> 64).setWidth 64 <<< (64 - n % 64) := by
  have h1 : n % 128 < 128 := Nat.mod_lt n (by decide)
  rw [← Nat.mod_mod_of_dvd n (show 64 ∣ 128 by decide)]
  generalize n % 128 = r at *
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hr : r < 64
  · simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind
  · rw [show r % 64 = r - 64 by omega]
    simp only [hr, ↓reduceIte, Nat.mod_eq_of_lt h1, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_or]
    grind

/-! ### Complementary variable shifts

A funnel shift or rotate by a register amount `k` moves one limb by `k` and the other by `w - k`.
Undoing it shifts every cross-limb bit by `w` in total, so those terms vanish
(`*_sub_*_eq_zero`), and each limb is rebuilt from its two complementary masks
(`*_or_*_cancel`). None of these needs `k ≤ w`: for `k > w` the `w - k` shift is the identity
and the `k` shift clears everything. -/

/-- Shifting right by `w - k` and then by `k` shifts out every bit. -/
theorem ushiftRight_sub_ushiftRight_eq_zero {w : Nat} (x : BitVec w) (k : Nat) :
    x >>> (w - k) >>> k = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  exact BitVec.getLsbD_of_ge x _ (by omega)

/-- Shifting right by `k` and then by `w - k` shifts out every bit. -/
theorem ushiftRight_ushiftRight_sub_eq_zero {w : Nat} (x : BitVec w) (k : Nat) :
    x >>> k >>> (w - k) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
  exact BitVec.getLsbD_of_ge x _ (by omega)

/-- Shifting left by `w - k` and then by `k` shifts out every bit. -/
theorem shiftLeft_sub_shiftLeft_eq_zero {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< (w - k) <<< k = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  grind

/-- Shifting left by `k` and then by `w - k` shifts out every bit. -/
theorem shiftLeft_shiftLeft_sub_eq_zero {w : Nat} (x : BitVec w) (k : Nat) :
    x <<< k <<< (w - k) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
  grind

/-- The low `w - k` bits (`x <<< k >>> k`) and the high `k` bits (`x >>> (w - k) <<< (w - k)`)
together are `x`. -/
theorem shiftLeft_ushiftRight_or_cancel {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< k >>> k ||| x >>> (w - k) <<< (w - k)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : k + i < w
  · simp [h, hi, show i < w - k by omega]
  · simp [h, hi, show ¬i < w - k by omega, show w - k + (i - (w - k)) = i by omega]

/-- `shiftLeft_ushiftRight_or_cancel` with the operands of `|||` swapped. -/
theorem ushiftRight_shiftLeft_or_cancel {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> (w - k) <<< (w - k) ||| x <<< k >>> k) = x := by
  rw [BitVec.or_comm, shiftLeft_ushiftRight_or_cancel]

/-- The high `w - k` bits (`x >>> k <<< k`) and the low `k` bits (`x <<< (w - k) >>> (w - k)`)
together are `x`. -/
theorem ushiftRight_shiftLeft_sub_or_cancel {w : Nat} (x : BitVec w) (k : Nat) :
    (x >>> k <<< k ||| x <<< (w - k) >>> (w - k)) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : i < k
  · by_cases hk : k ≤ w
    · simp [h, hi, show w - k + i < w by omega]
    · simp [h, hi, show w - k = 0 by omega]
  · simp [h, hi, show k + (i - k) = i by omega, show ¬w - k + i < w by omega]

/-- `ushiftRight_shiftLeft_sub_or_cancel` with the operands of `|||` swapped. -/
theorem shiftLeft_sub_ushiftRight_or_cancel {w : Nat} (x : BitVec w) (k : Nat) :
    (x <<< (w - k) >>> (w - k) ||| x >>> k <<< k) = x := by
  rw [BitVec.or_comm, ushiftRight_shiftLeft_sub_or_cancel]

/- Only `|||` is distributed over `<<<`: distributing `&&&` would turn a masked field
   `(x &&& m) <<< k` into `x <<< k &&& m <<< k`, which the disjoint-field rules do not match. -/
attribute [decomp_norm] BitVec.shiftLeft_or_distrib ushiftRight_sub_ushiftRight_eq_zero
  ushiftRight_ushiftRight_sub_eq_zero shiftLeft_sub_shiftLeft_eq_zero
  shiftLeft_shiftLeft_sub_eq_zero shiftLeft_ushiftRight_or_cancel ushiftRight_shiftLeft_or_cancel
  ushiftRight_shiftLeft_sub_or_cancel shiftLeft_sub_ushiftRight_or_cancel

/-! ## Single-bit extraction

`AND x, #1` (and the `LSR` + `AND #1` bit test) becomes `if x.getLsbD 0 then 1 else 0`; the bit
index is then pushed through `if`, truncations, and right shifts, and a two-limb selection of bit
`n % m` or `m + n % m` on `m ≤ n % (2 * m)` folds back to bit `n % (2 * m)`. -/

/-- Masking with `1` keeps bit 0: `1#w &&& x` is `if x.getLsbD 0 then 1#w else 0#w`. -/
theorem one_and_eq_ite {w : Nat} (x : BitVec w) :
    (1#w &&& x) = if x.getLsbD 0 = true then 1#w else 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases i with _ | i
  · split <;> simp_all
  · split <;> simp [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_succ]

/-- See `one_and_eq_ite`. -/
theorem and_one_eq_ite {w : Nat} (x : BitVec w) :
    (x &&& 1#w) = if x.getLsbD 0 = true then 1#w else 0#w := by
  rw [BitVec.and_comm]
  exact one_and_eq_ite x

/-- `getLsbD` distributes over `if`. -/
theorem getLsbD_ite {w : Nat} (p : Prop) [Decidable p] (a b : BitVec w) (i : Nat) :
    (if p then a else b).getLsbD i = if p then a.getLsbD i else b.getLsbD i := by
  split <;> rfl

/-- Two bits of one value selected by `if` are one bit at a selected index. -/
theorem ite_getLsbD {w : Nat} (p : Prop) [Decidable p] (x : BitVec w) (i j : Nat) :
    (if p then x.getLsbD i else x.getLsbD j) = x.getLsbD (if p then i else j) := by
  split <;> rfl

/-- A residue is below its (positive) modulus. -/
theorem mod_lt_self_eq_true (n m : Nat) (h : 0 < m) : (n % m < m) = True :=
  eq_true (Nat.mod_lt n h)

/-- The two-limb index selection: bit `m + n % m` of the high half when `m ≤ n % (2 * m)`, else
    bit `n % m` of the low half, is bit `n % (2 * m)`. -/
theorem ite_le_mod_two_mul (n m k : Nat) (hk : k = 2 * m) :
    (if m ≤ n % k then m + n % m else n % m) = n % k := by
  subst hk
  rw [← Nat.mod_mod_of_dvd n (Nat.dvd_mul_left m 2)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hr : n % (2 * m) < 2 * m := Nat.mod_lt _ (by omega)
  generalize n % (2 * m) = r at *
  split
  · rw [Nat.mod_eq_sub_mod ‹m ≤ r›, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]

attribute [decomp_norm] one_and_eq_ite and_one_eq_ite getLsbD_ite ite_getLsbD mod_lt_self_eq_true
  ite_le_mod_two_mul BitVec.getLsbD_setWidth BitVec.getLsbD_ushiftRight

attribute [decomp_norm] toNat_setWidth_mod toNat_not_mod ushiftRight_one_ushiftRight_mod
  two_mul_shiftLeft_mod mul_two_shiftLeft_mod shiftLeft_ite ite_or_ite lo128_shiftLeft
  hi128_shiftLeft lo128_ushiftRight hi128_ushiftRight lo128_rotateLeft hi128_rotateLeft
  lo128_rotateRight hi128_rotateRight

/-! ## Zero-extension injectivity and 0/1-valued choices

A byte compared after zero-extension (`ldrb` + `cmp w, w`) compares the bytes. `CSET` results
`if c then 1 else 0` combined with `and` / `orr` stay `if`s of the combined condition. -/

/-- Zero-extension is injective (`=` form). -/
theorem setWidth_eq_setWidth_of_le {w v : Nat} (x y : BitVec w) (h : w ≤ v) :
    (x.setWidth v = y.setWidth v) = (x = y) := by
  refine propext ⟨fun hxy => ?_, fun hxy => hxy ▸ rfl⟩
  have := congrArg (BitVec.setWidth w) hxy
  rwa [BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_setWidth_of_le _ h,
    BitVec.setWidth_eq, BitVec.setWidth_eq] at this

/-- Zero-extension is injective (`==` form). -/
theorem setWidth_beq_setWidth_of_le {w v : Nat} (x y : BitVec w) (h : w ≤ v) :
    (x.setWidth v == y.setWidth v) = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact (setWidth_eq_setWidth_of_le x y h).to_iff

/-- The `and` of two 0/1 choices is the choice of the conjunction. -/
theorem ite_one_zero_and_ite {w : Nat} (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#w else 0#w) &&& (if q then 1#w else 0#w)) = if p ∧ q then 1#w else 0#w := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The `or` of two 0/1 choices is the choice of the disjunction. -/
theorem ite_one_zero_or_ite {w : Nat} (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1#w else 0#w) ||| (if q then 1#w else 0#w)) = if p ∨ q then 1#w else 0#w := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

attribute [decomp_norm] setWidth_beq_setWidth_of_le setWidth_eq_setWidth_of_le
  ite_one_zero_and_ite ite_one_zero_or_ite

/-! ## Leading and trailing zero counts

`CLZ` of a bit-reversed value (`RBIT` + `CLZ`) is `ctz`. A scan for the first set bit
(`List.find?` over the bit indices) is `clz` / `ctz`. A 128-bit count is a two-limb `if` on the
limb that is scanned first. -/

/-- `CLZ` after `RBIT` counts trailing zeros. -/
theorem reverse_clz_eq_ctz {w : Nat} (x : BitVec w) : x.reverse.clz = x.ctz :=
  BitVec.ctz_eq_reverse_clz.symm

private theorem find?_congr_of_mem {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = q x) → l.find? p = l.find? q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.find?_cons, h x List.mem_cons_self]
    cases q x
    · exact find?_congr_of_mem (fun y hy => h y (List.mem_cons_of_mem x hy))
    · rfl

private theorem ctz_zero_toNat' (w : Nat) : (0#w : BitVec w).ctz.toNat = w := by
  have hctz : (0#w : BitVec w).ctz = BitVec.ofNat w w := by
    rw [BitVec.ctz_eq_reverse_clz, BitVec.reverse_eq_zero_iff.mpr rfl]
    exact BitVec.clz_eq_iff_eq_zero.mpr rfl
  rw [hctz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_two_pow_self)]

/-- Scanning up from bit 0 for the first set bit finds `ctz` (`w` if none). -/
theorem find_getLsbD_getD_eq_ctz {w : Nat} (x : BitVec w) :
    ((List.range w).find? (fun i => x.getLsbD i)).getD w = x.ctz.toNat := by
  by_cases hx : x = 0#w
  · subst hx
    have hnone : (List.range w).find? (fun i => (0#w : BitVec w).getLsbD i) = none := by
      rw [List.find?_eq_none]
      intro i _; simp
    rw [hnone, Option.getD_none, ctz_zero_toNat']
  · have hlt : x.ctz < BitVec.ofNat w w := BitVec.ctz_lt_iff_ne_zero.mpr hx
    have hk : x.ctz.toNat < w := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self] at hlt
      exact hlt
    have hsome : (List.range w).find? (fun i => x.getLsbD i) = some x.ctz.toNat := by
      rw [List.find?_eq_some_iff_getElem]
      refine ⟨BitVec.getLsbD_true_ctz_of_ne_zero hx, x.ctz.toNat, ?_, ?_, ?_⟩
      · simp [hk]
      · simp
      · intro j hj
        simp only [List.getElem_range, BitVec.getLsbD_false_of_lt_ctz hj, Bool.not_false]
    rw [hsome, Option.getD_some]

/-- Scanning down from the top bit for the first set bit finds `clz` (`w` if none). -/
theorem find_getMsbD_getD_eq_clz {w : Nat} (x : BitVec w) :
    ((List.range w).find? (fun i => x.getMsbD i)).getD w = x.clz.toNat := by
  have hcongr : (List.range w).find? (fun i => x.getMsbD i) =
      (List.range w).find? (fun i => x.reverse.getLsbD i) := by
    apply find?_congr_of_mem
    intro i _
    rw [BitVec.getLsbD_reverse]
  rw [hcongr, find_getLsbD_getD_eq_ctz, ← BitVec.clz_eq_reverse_ctz]

/-- `ctz` is `k` when bit `k` is the lowest set bit. -/
private theorem ctz_toNat_eq_of_getLsbD' {w k : Nat} {x : BitVec w}
    (ht : x.getLsbD k = true) (hf : ∀ j < k, x.getLsbD j = false) : x.ctz.toNat = k := by
  have hx : x ≠ 0#w := by rintro rfl; simp at ht
  have h1 := BitVec.getLsbD_true_ctz_of_ne_zero hx
  apply Nat.le_antisymm
  · exact Nat.le_of_not_lt (fun hgt => by
      have h2 := BitVec.getLsbD_false_of_lt_ctz (x := x) hgt
      rw [ht] at h2; cases h2)
  · exact Nat.le_of_not_lt (fun hlt => by rw [hf _ hlt] at h1; cases h1)

private theorem ctz64_toNat_lt {x : BitVec 64} (hx : x ≠ 0#64) : x.ctz.toNat < 64 := by
  have hlt : x.ctz < 64#64 := BitVec.ctz_lt_iff_ne_zero.mpr hx
  simpa [BitVec.lt_def] using hlt

/-- Two-limb trailing-zero count: the low limb, or `64 +` the high limb when the low limb is 0. -/
theorem ctz128_toNat_limbs (x : BitVec 128) :
    x.ctz.toNat =
      if x.setWidth 64 = 0#64 then ((x >>> 64).setWidth 64).ctz.toNat + 64
      else (x.setWidth 64).ctz.toNat := by
  by_cases hlo : x.setWidth 64 = 0#64
  · simp only [hlo, ↓reduceIte]
    by_cases hhi : (x >>> 64).setWidth 64 = 0#64
    · have hx0 : x = 0#128 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        by_cases hi64 : i < 64
        · have := congrArg (·.getLsbD i) hlo
          simpa [BitVec.getLsbD_setWidth, hi64] using this
        · have := congrArg (·.getLsbD (i - 64)) hhi
          simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
            show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega] using this
      rw [hhi, hx0, ctz_zero_toNat', ctz_zero_toNat']
    · have hm := ctz64_toNat_lt hhi
      apply ctz_toNat_eq_of_getLsbD'
      · have ht := BitVec.getLsbD_true_ctz_of_ne_zero hhi
        rw [BitVec.getLsbD_setWidth, decide_eq_true hm, Bool.true_and,
          BitVec.getLsbD_ushiftRight] at ht
        rwa [Nat.add_comm]
      · intro j hj
        by_cases hj64 : j < 64
        · have hz := congrArg (·.getLsbD j) hlo
          simpa [BitVec.getLsbD_setWidth, hj64] using hz
        · have hf := BitVec.getLsbD_false_of_lt_ctz (x := (x >>> 64).setWidth 64)
            (i := j - 64) (by omega)
          rw [BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
            BitVec.getLsbD_ushiftRight] at hf
          simpa [show 64 + (j - 64) = j by omega] using hf
  · simp only [hlo, ↓reduceIte]
    have hm := ctz64_toNat_lt hlo
    apply ctz_toNat_eq_of_getLsbD'
    · have ht := BitVec.getLsbD_true_ctz_of_ne_zero hlo
      rwa [BitVec.getLsbD_setWidth, decide_eq_true hm, Bool.true_and] at ht
    · intro j hj
      have hf := BitVec.getLsbD_false_of_lt_ctz (x := x.setWidth 64) hj
      rwa [BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and] at hf

/-- Two-limb leading-zero count: the high limb, or `64 +` the low limb when the high limb is 0. -/
theorem clz128_toNat_limbs (x : BitVec 128) :
    x.clz.toNat =
      if (x >>> 64).setWidth 64 = 0#64 then (x.setWidth 64).clz.toNat + 64
      else ((x >>> 64).setWidth 64).clz.toNat := by
  have hlo : x.reverse.setWidth 64 = ((x >>> 64).setWidth 64).reverse := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, show i < 128 by omega, show 64 - 1 - i < 64 by omega,
      BitVec.getLsbD_ushiftRight]
    exact congrArg x.getLsbD (by omega)
  have hhi : (x.reverse >>> 64).setWidth 64 = (x.setWidth 64).reverse := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse, show 64 + i < 128 by omega,
      BitVec.getMsbD_eq_getLsbD, show 64 - 1 - i < 64 by omega]
    exact congrArg x.getLsbD (by omega)
  rw [BitVec.clz_eq_reverse_ctz, ctz128_toNat_limbs, hlo, hhi, ← BitVec.clz_eq_reverse_ctz,
    ← BitVec.clz_eq_reverse_ctz]
  simp only [BitVec.reverse_eq_zero_iff]

/-- `BitVec.ofNat` of an `if` is an `if` of `BitVec.ofNat`s. -/
theorem ofNat_ite {n : Nat} (p : Prop) [Decidable p] (a b : Nat) :
    BitVec.ofNat n (if p then a else b) = if p then BitVec.ofNat n a else BitVec.ofNat n b := by
  split <;> rfl

/-- A count plus a literal, cast to `n` bits, is the truncated count plus the literal. -/
theorem ofNat_toNat_add {w n : Nat} (x : BitVec w) (k : Nat) :
    BitVec.ofNat n (x.toNat + k) = x.setWidth n + BitVec.ofNat n k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.add_mod]

/-- A count cast to `n` bits is the truncated count. -/
theorem ofNat_toNat_eq_setWidth {w n : Nat} (x : BitVec w) :
    BitVec.ofNat n x.toNat = x.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

attribute [decomp_norm] reverseBits_eq_reverse reverse_clz_eq_ctz find_getLsbD_getD_eq_ctz
  find_getMsbD_getD_eq_clz ctz128_toNat_limbs clz128_toNat_limbs ofNat_ite ofNat_toNat_add
  ofNat_toNat_eq_setWidth

/-! ## Constant rotates

A64 has only a right rotate (`ROR`, `EXTR x, x, #k`, shifted-register `ror #k`), while
specifications are usually written with left rotates. Rotates by a literal amount are normalised to
`rotateLeft` (simproc `rotateRightLit`), and `EXTR` of a register with itself
(`setWidth w ((x ++ x) >>> k)`) is a right rotate (`setWidth_append_self_ushiftRight`). -/

/-- A right rotate by `k` is a left rotate by `(w - k % w) % w`. -/
theorem rotateRight_eq_rotateLeft {w : Nat} (x : BitVec w) (k : Nat) :
    x.rotateRight k = x.rotateLeft ((w - k % w) % w) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hw : 0 < w := by omega
  have hk : k % w < w := Nat.mod_lt _ hw
  rw [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, Nat.mod_mod]
  generalize k % w = r at hk
  by_cases h0 : r = 0
  · simp [h0, hi]
  · have he : (w - r) % w = w - r := Nat.mod_eq_of_lt (by omega)
    rw [he]
    simp [hi]
    by_cases hlt : i < w - r
    · simp [hlt]; congr 1; omega
    · simp [hlt]

/-- `EXTR x, x, #k`: the low `w` bits of `(x ++ x) >>> k` are `x.rotateRight k`, for `k ≤ w`. -/
theorem setWidth_append_self_ushiftRight {w : Nat} (x : BitVec w) (k : Nat) (hk : k ≤ w) :
    ((x ++ x) >>> k).setWidth w = x.rotateRight k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
    BitVec.getLsbD_rotateRight]
  by_cases hkw : k = w
  · rw [hkw, Nat.mod_self]
    simp [hi]
  · have hkm : k % w = k := Nat.mod_eq_of_lt (by omega)
    rw [hkm]
    by_cases hlt : i < w - k
    · have hki : k + i < w := by omega
      simp [hi, hlt, hki]
    · have hnki : ¬ (k + i < w) := by omega
      simp [hi, hlt, hnki]; congr 1; omega

/-! ## Known-zero bits: masks and disjoint fields

Byte-assembly code (LEB128 varints, little-endian merges, bit-field packing) masks values that are
already narrow (`UXTB` then `AND #0x7f0000007f`) and `ORR`s fields that occupy disjoint bit ranges.
A literal bit mask `m` with `x &&& m = x` ("`x` fits in `m`") is computed bottom-up through
literals, `&&&` / `|||` / `^^^`, `setWidth`, literal shifts, multiplication by a literal power of
two, and `if`, falling back to `2 ^ w - 1`. Simproc `andLitMask` drops `x &&& c` to `x` when `m`
fits in `c` and otherwise shrinks `c` to `m &&& c`. Simproc `orDisjointAdd` (opt-in simp set
`decomp_norm_or_add`, not in `decomp_norm`) rewrites `x ||| y` with disjoint masks to `x + y`, which moves byte assembly to
`Nat` arithmetic; `toNatAndLowOnes` rewrites `(x &&& (2 ^ k - 1)).toNat` to `x.toNat % 2 ^ k`. -/

theorem fits_of_getLsbD {w m : Nat} (x : BitVec w)
    (h : ∀ i, x.getLsbD i = true → m.testBit i = true) : x &&& BitVec.ofNat w m = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  cases hx : x.getLsbD i
  · simp
  · simp [hi, h i hx]

theorem testBit_of_fits {w m : Nat} {x : BitVec w} (h : x &&& BitVec.ofNat w m = x) (i : Nat)
    (hx : x.getLsbD i = true) : m.testBit i = true := by
  have := congrArg (fun y => y.getLsbD i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hx, Bool.true_and] at this
  exact (Bool.and_eq_true _ _ ▸ this).2

/-- Every value fits in `2 ^ w - 1`. -/
theorem fits_full {w m : Nat} (x : BitVec w) (hm : m = 2 ^ w - 1) :
    x &&& BitVec.ofNat w m = x := by
  subst hm
  apply fits_of_getLsbD
  intro i hi
  have := BitVec.lt_of_getLsbD hi
  rw [Nat.testBit_two_pow_sub_one]
  simpa using this

/-- A literal fits in its own value. -/
theorem fits_ofNat (w c : Nat) : BitVec.ofNat w c &&& BitVec.ofNat w c = BitVec.ofNat w c :=
  BitVec.and_self

theorem fits_and {w mx my : Nat} (m : Nat) {x y : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hy : y &&& BitVec.ofNat w my = y) (hm : mx &&& my = m) :
    (x &&& y) &&& BitVec.ofNat w m = x &&& y := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_and, Bool.and_eq_true] at h
  rw [Nat.testBit_and, testBit_of_fits hx i h.1, testBit_of_fits hy i h.2]; rfl

theorem fits_or {w mx my : Nat} (m : Nat) {x y : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hy : y &&& BitVec.ofNat w my = y) (hm : mx ||| my = m) :
    (x ||| y) &&& BitVec.ofNat w m = x ||| y := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_or, Bool.or_eq_true] at h
  rw [Nat.testBit_or]
  rcases h with h | h
  · rw [testBit_of_fits hx i h]; rfl
  · rw [testBit_of_fits hy i h, Bool.or_true]

theorem fits_xor {w mx my : Nat} (m : Nat) {x y : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hy : y &&& BitVec.ofNat w my = y) (hm : mx ||| my = m) :
    (x ^^^ y) &&& BitVec.ofNat w m = x ^^^ y := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_xor] at h
  rw [Nat.testBit_or]
  cases hxi : x.getLsbD i
  · rw [hxi, Bool.false_xor] at h; rw [testBit_of_fits hy i h, Bool.or_true]
  · rw [testBit_of_fits hx i hxi]; rfl

theorem fits_setWidth {w mx : Nat} (v m : Nat) {x : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hm : mx % 2 ^ v = m) : x.setWidth v &&& BitVec.ofNat v m = x.setWidth v := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_setWidth, Bool.and_eq_true] at h
  rw [Nat.testBit_mod_two_pow, testBit_of_fits hx i h.2]
  simpa using h.1

theorem fits_ushiftRight {w mx : Nat} (k m : Nat) {x : BitVec w}
    (hx : x &&& BitVec.ofNat w mx = x) (hm : mx >>> k = m) :
    (x >>> k) &&& BitVec.ofNat w m = x >>> k := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_ushiftRight] at h
  rw [Nat.testBit_shiftRight, testBit_of_fits hx _ h]

theorem fits_shiftLeft {w mx : Nat} (k m : Nat) {x : BitVec w}
    (hx : x &&& BitVec.ofNat w mx = x) (hm : (mx <<< k) % 2 ^ w = m) :
    (x <<< k) &&& BitVec.ofNat w m = x <<< k := by
  subst hm
  apply fits_of_getLsbD
  intro i h
  rw [BitVec.getLsbD_shiftLeft, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hi, hk⟩, hb⟩ := h
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, testBit_of_fits hx _ hb]
  simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hi hk
  simp [hi, hk]

theorem fits_mul_twoPow {w mx : Nat} (k m : Nat) {x : BitVec w}
    (hx : x &&& BitVec.ofNat w mx = x) (hm : (mx <<< k) % 2 ^ w = m) :
    (x * BitVec.ofNat w (2 ^ k)) &&& BitVec.ofNat w m = x * BitVec.ofNat w (2 ^ k) := by
  rw [← shiftLeft_eq_mul]; exact fits_shiftLeft k m hx hm

theorem fits_twoPow_mul {w mx : Nat} (k m : Nat) {x : BitVec w}
    (hx : x &&& BitVec.ofNat w mx = x) (hm : (mx <<< k) % 2 ^ w = m) :
    (BitVec.ofNat w (2 ^ k) * x) &&& BitVec.ofNat w m = BitVec.ofNat w (2 ^ k) * x := by
  rw [BitVec.mul_comm, ← shiftLeft_eq_mul]; exact fits_shiftLeft k m hx hm

theorem fits_ite {w mx my : Nat} (p : Prop) [Decidable p] (m : Nat) {x y : BitVec w}
    (hx : x &&& BitVec.ofNat w mx = x) (hy : y &&& BitVec.ofNat w my = y) (hm : mx ||| my = m) :
    (if p then x else y) &&& BitVec.ofNat w m = if p then x else y := by
  subst hm
  split
  · apply fits_of_getLsbD; intro i h; rw [Nat.testBit_or, testBit_of_fits hx i h]; rfl
  · apply fits_of_getLsbD; intro i h; rw [Nat.testBit_or, testBit_of_fits hy i h, Bool.or_true]

/-- `x &&& c = x` when `x` fits in `m` and `m` fits in `c`. -/
theorem and_eq_self_of_fits {w m c : Nat} {x : BitVec w} (hx : x &&& BitVec.ofNat w m = x)
    (hc : m &&& c = m) : x &&& BitVec.ofNat w c = x := by
  apply fits_of_getLsbD
  intro i h
  have := testBit_of_fits hx i h
  rw [← hc, Nat.testBit_and, Bool.and_eq_true] at this
  exact this.2

/-- `x &&& c = x &&& (m &&& c)` when `x` fits in `m`. -/
theorem and_eq_and_of_fits {w m c c' : Nat} {x : BitVec w} (hx : x &&& BitVec.ofNat w m = x)
    (hc : m &&& c = c') : x &&& BitVec.ofNat w c = x &&& BitVec.ofNat w c' := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_and]
  cases h : x.getLsbD i
  · rfl
  · simp [testBit_of_fits hx i h]

/-- `ORR` of values with disjoint masks is their sum. -/
theorem or_eq_add_of_fits {w mx my : Nat} {x y : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hy : y &&& BitVec.ofNat w my = y) (hm : mx &&& my = 0) : x ||| y = x + y := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_ofNat]
  cases h1 : x.getLsbD i
  · simp
  cases h2 : y.getLsbD i
  · simp
  have := congrArg (fun n => n.testBit i) hm
  simp only [Nat.testBit_and, testBit_of_fits hx i h1, testBit_of_fits hy i h2,
    Nat.zero_testBit] at this
  exact absurd this (by decide)

/-- A sum of values with disjoint masks fits in the union of the masks. -/
theorem fits_add {w mx my : Nat} (m : Nat) {x y : BitVec w} (hx : x &&& BitVec.ofNat w mx = x)
    (hy : y &&& BitVec.ofNat w my = y) (hd : mx &&& my = 0) (hm : mx ||| my = m) :
    (x + y) &&& BitVec.ofNat w m = x + y := by
  rw [← or_eq_add_of_fits hx hy hd]; exact fits_or m hx hy hm

/-- Masking with a literal `2 ^ k - 1` keeps the `Nat` value modulo `2 ^ k`. -/
theorem toNat_and_lowOnes {w c : Nat} (k p : Nat) (x : BitVec w) (hc : c = 2 ^ k - 1)
    (hp : 2 ^ k = p) : (x &&& BitVec.ofNat w c).toNat = x.toNat % p := by
  subst hc hp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, BitVec.testBit_toNat, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat]
  cases h : x.getLsbD i
  · simp
  · simp [BitVec.lt_of_getLsbD h]

/-- `(y ||| c₁) &&& c₂ = (y &&& c₂) ||| (c₁ &&& c₂)`, folded at literals `c₁`, `c₂`. -/
theorem and_or_lit {w c₁ c₂ c : Nat} (y : BitVec w) (hc : c₁ &&& c₂ = c) :
    (y ||| BitVec.ofNat w c₁) &&& BitVec.ofNat w c₂ =
      (y &&& BitVec.ofNat w c₂) ||| BitVec.ofNat w c := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ofNat, Nat.testBit_and, hi,
    decide_true, Bool.true_and]
  cases y.getLsbD i <;> cases c₁.testBit i <;> cases c₂.testBit i <;> rfl

/-- `(y &&& c₁) &&& c₂ = y &&& (c₁ &&& c₂)` at literals `c₁`, `c₂`. -/
theorem and_and_lit {w c₁ c₂ c : Nat} (y : BitVec w) (hc : c₁ &&& c₂ = c) :
    (y &&& BitVec.ofNat w c₁) &&& BitVec.ofNat w c₂ = y &&& BitVec.ofNat w c := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_and, hi, decide_true,
    Bool.true_and, Bool.and_assoc]

/-- `BitVec.ofNat w (x.toNat % 2 ^ k)` is `x` truncated to `k` bits, as a mask at width `w`. -/
theorem ofNat_toNat_mod {v : Nat} (w c p : Nat) (x : BitVec v) (hc : c + 1 = p)
    (hp : p = 2 ^ (p.log2)) :
    BitVec.ofNat w (x.toNat % p) = x.setWidth w &&& BitVec.ofNat w c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hp, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, BitVec.testBit_toNat]
  have : c = 2 ^ p.log2 - 1 := by omega
  rw [this, Nat.testBit_two_pow_sub_one]
  cases x.getLsbD i <;> simp [hi, Bool.and_comm]

attribute [decomp_norm] BitVec.or_zero BitVec.zero_or BitVec.and_zero BitVec.zero_and
  BitVec.xor_zero BitVec.zero_xor

/-! ### Bit-field merging

Byte assembly extracts fields `(y >>> 7 * j).setWidth 8`, masks them, scales them back by
`2 ^ (7 * j)` and `ORR`s them together. The lemmas below rewrite each field to a mask of one
common `y.setWidth w` and merge the masks, so the result meets `y.setWidth w &&& c` (or, after
`andLitMask`, `y.setWidth w`). The simprocs that apply them (`setWidthNarrowAnd`,
`setWidthLossless`, `shiftFieldMul`, `andLitOrMerge`) form the opt-in simp set
`decomp_norm_bitfield`. -/

/-- A narrowing below a mask that fits in it is redundant. -/
theorem setWidth_setWidth_and_of_lt {u : Nat} (w v c : Nat) (y : BitVec u) (hc : c < 2 ^ v) :
    (y.setWidth v).setWidth w &&& BitVec.ofNat w c = y.setWidth w &&& BitVec.ofNat w c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  by_cases h : i < v
  · simp [h]
  · have : c.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [this]

/-- A narrowing of a value that fits in it is lossless. -/
theorem setWidth_setWidth_of_fits {u : Nat} (w v m : Nat) {y : BitVec u}
    (hy : y &&& BitVec.ofNat u m = y) (hm : m < 2 ^ v) :
    (y.setWidth v).setWidth w = y.setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h : i < v
  · simp [h]
  · cases hb : y.getLsbD i
    · simp
    · have h1 := testBit_of_fits hy i hb
      have h2 : m.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))
      simp_all

/-- A masked field `(y >>> k).setWidth w &&& c` scaled back by `2 ^ k` is a mask of `y`. -/
theorem setWidth_ushiftRight_and_mul_twoPow {u : Nat} (w k c c' : Nat) (y : BitVec u)
    (hc : (c <<< k) % 2 ^ w = c') :
    ((y >>> k).setWidth w &&& BitVec.ofNat w c) * BitVec.ofNat w (2 ^ k) =
      y.setWidth w &&& BitVec.ofNat w c' := by
  subst hc
  rw [← shiftLeft_eq_mul]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft]
  by_cases hk : i < k
  · have : ¬ k ≤ i := by omega
    simp [hk, this]
  · have e : k + (i - k) = i := by omega
    have : i - k < w := by omega
    have hki : k ≤ i := by omega
    simp [hk, hi, e, this, hki]

/-- An unmasked field `(y >>> k).setWidth w` scaled back by `2 ^ k` is a mask of `y`. -/
theorem setWidth_ushiftRight_mul_twoPow {u : Nat} (w k c' : Nat) (y : BitVec u)
    (hc : ((2 ^ w - 1) <<< k) % 2 ^ w = c') :
    (y >>> k).setWidth w * BitVec.ofNat w (2 ^ k) = y.setWidth w &&& BitVec.ofNat w c' := by
  have h := setWidth_ushiftRight_and_mul_twoPow w k (2 ^ w - 1) c' y hc
  rwa [fits_full _ rfl] at h

/-- Two masks of one value merge under `|||`. -/
theorem and_lit_or_and_lit {w : Nat} (z : BitVec w) (c₁ c₂ c : Nat) (hc : c₁ ||| c₂ = c) :
    (z &&& BitVec.ofNat w c₁) ||| (z &&& BitVec.ofNat w c₂) = z &&& BitVec.ofNat w c := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_or]
  cases z.getLsbD i <;> simp [hi]

/-! ### Narrowing through shifts, absorbed masks, shift thresholds -/

/-- A narrowing below a right shift is redundant when the shifted window fits in it. -/
theorem setWidth_ushiftRight_setWidth_of_add_le {u : Nat} (v k w : Nat) (y : BitVec u)
    (h : k + w ≤ v) : ((y.setWidth v) >>> k).setWidth w = (y >>> k).setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have : k + i < v := by omega
  simp [hi, this]

/-- `(y &&& c₁) ||| c₂` drops the mask when every bit `y` may set (`y` fits in `m`) is kept by
    `c₁` or set by `c₂`. -/
theorem and_lit_or_lit_of_fits {w m : Nat} (c₁ c₂ : Nat) {y : BitVec w}
    (hy : y &&& BitVec.ofNat w m = y) (hc : m &&& (c₁ ||| c₂) = m) :
    (y &&& BitVec.ofNat w c₁) ||| BitVec.ofNat w c₂ = y ||| BitVec.ofNat w c₂ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hi, decide_true,
    Bool.true_and]
  cases hb : y.getLsbD i
  · simp
  · have h1 := testBit_of_fits hy i hb
    have h2 := congrArg (fun n => n.testBit i) hc
    simp only [Nat.testBit_and, Nat.testBit_or, h1, Bool.true_and] at h2
    cases h₁ : c₁.testBit i <;> cases h₂ : c₂.testBit i <;> simp_all

/-- `x >>> k = 0` is the threshold `x < 2 ^ k`. -/
theorem ushiftRight_eq_zero_iff_lt {w : Nat} (k c : Nat) (x : BitVec w) (hc : 2 ^ k = c)
    (hk : c < 2 ^ w) : (x >>> k = 0#w) = (x < BitVec.ofNat w c) := by
  subst hc
  apply propext
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, ← BitVec.toNat_inj,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.zero_mod]
  constructor
  · intro h
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).1 h
  · intro h
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos k)).2 h

/-- `x >>> k < c` is the threshold `x < c * 2 ^ k`. -/
theorem ushiftRight_lt_lit {w : Nat} (k c d : Nat) (x : BitVec w) (hc : c < 2 ^ w)
    (hd : c * 2 ^ k = d) (hdw : d < 2 ^ w) :
    (x >>> k < BitVec.ofNat w c) = (x < BitVec.ofNat w d) := by
  subst hd
  apply propext
  rw [BitVec.lt_def, BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hdw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)

/-- `c ≤ x >>> k` is the threshold `c * 2 ^ k ≤ x`. -/
theorem lit_le_ushiftRight {w : Nat} (k c d : Nat) (x : BitVec w) (hc : c < 2 ^ w)
    (hd : c * 2 ^ k = d) (hdw : d < 2 ^ w) :
    (BitVec.ofNat w c ≤ x >>> k) = (BitVec.ofNat w d ≤ x) := by
  subst hd
  apply propext
  rw [BitVec.le_def, BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt hdw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.le_div_iff_mul_le (Nat.two_pow_pos k)

/-- Two right shifts are one shift by the sum of the amounts. -/
theorem ushiftRight_ushiftRight_lit {w : Nat} (x : BitVec w) (a b c : Nat) (h : a + b = c) :
    x >>> a >>> b = x >>> c := by
  subst h
  rw [BitVec.shiftRight_add]

/-- The top bit of `x` is the threshold `2 ^ (w - 1) ≤ x.toNat` (the `msb_eq_decide` form). -/
theorem getLsbD_top_lit {w : Nat} (x : BitVec w) (k c : Nat) (hw : k + 1 = w) (hc : 2 ^ k = c) :
    x.getLsbD k = decide (c ≤ x.toNat) := by
  subst hw hc
  exact BitVec.getLsbD_last x

/-! ### Concatenations (opt-in `concat*` simprocs)

Lemmas behind the opt-in `concat*` simprocs, which push narrowing, widening, literal shifts, and
literal masks through `x ++ y` when every width is a literal, so that register values packed by
`orr`/`lsl`/`ubfx`/`bfi` sequences stay in the `hi ++ mid ++ lo` form of the specification. -/

/-- Narrowing `x ++ y` to at most the width of `y` keeps only `y`. -/
theorem setWidth_append_of_le_right {n m : Nat} (k : Nat) (x : BitVec n) (y : BitVec m)
    (h : k ≤ m) : (x ++ y).setWidth k = y.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [show i < m by omega, hi]

/-- Resizing `x ++ y` to `j + m` bits resizes `x` to `j` bits (`hx : x.setWidth j = x'`). -/
theorem setWidth_append_add {n m : Nat} (j : Nat) (x : BitVec n) (y : BitVec m) {x' : BitVec j}
    (hx : x.setWidth j = x') : (x ++ y).setWidth (j + m) = x' ++ y := by
  subst hx
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  by_cases him : i < m
  · simp [him, hi]
  · simp [him, show i - m < j by omega, hi]

/-- Widening `x` by `p` bits prepends `0#p`. -/
theorem setWidth_eq_zero_append {w : Nat} (p : Nat) (x : BitVec w) :
    x.setWidth (p + w) = 0#p ++ x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
  by_cases hiw : i < w
  · simp [hiw, hi]
  · simp [hiw, hi, BitVec.getLsbD_of_ge x i (by omega)]

/-- `0#p ++ x` is the widening of `x`. -/
theorem zero_append_eq_setWidth {w : Nat} (p : Nat) (x : BitVec w) :
    0#p ++ x = x.setWidth (p + w) :=
  (setWidth_eq_zero_append p x).symm

/-- `0#p` widened to `j` bits is `0#j`. -/
theorem setWidth_zero_lit (p j : Nat) : (0#p).setWidth j = 0#j := by
  simp

/-- A right shift of `x ++ y` by at least the width of `y` shifts `x` by the rest. -/
theorem append_ushiftRight_of_le {n m : Nat} (j : Nat) (x : BitVec n) (y : BitVec m)
    (h : m ≤ j) : (x ++ y) >>> j = (x >>> (j - m)).setWidth (n + m) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  simp only [show ¬(j + i < m) by omega, ite_false, hi, decide_true, Bool.true_and]
  rw [show j + i - m = j - m + i by omega]

/-- A right shift of `x ++ y` by exactly the width of `y` is `x`, widened. -/
theorem append_ushiftRight_eq {n m : Nat} (x : BitVec n) (y : BitVec m) :
    (x ++ y) >>> m = x.setWidth (n + m) := by
  rw [append_ushiftRight_of_le m x y (Nat.le_refl m)]
  simp

/-- A left shift by `j` of a `p + j`-bit value is its low `p` bits followed by `0#j`
    (`hx : x.setWidth p = x'`). -/
theorem shiftLeft_eq_append {p : Nat} (j : Nat) (x : BitVec (p + j)) {x' : BitVec p}
    (hx : x.setWidth p = x') : x <<< j = x' ++ 0#j := by
  subst hx
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_zero]
  by_cases hij : i < j
  · simp [hij]
  · simp [hij, hi, show i - j < p by omega]

/-- `x &&& c` for a literal `c = ch ++ cl` split at the boundary of `x = xh ++ xl`, given the
    two halves `hh : xh &&& ch = rh` and `hl : xl &&& cl = rl`. -/
theorem append_and_lit {n m : Nat} (c ch cl : Nat) (xh : BitVec n) (xl : BitVec m)
    {rh : BitVec n} {rl : BitVec m}
    (hh : xh &&& BitVec.ofNat n ch = rh) (hl : xl &&& BitVec.ofNat m cl = rl)
    (hc : BitVec.ofNat (n + m) c = BitVec.ofNat n ch ++ BitVec.ofNat m cl) :
    (xh ++ xl) &&& BitVec.ofNat (n + m) c = rh ++ rl := by
  rw [hc, BitVec.and_append, hh, hl]

/-- `x ||| c` for a literal `c = ch ++ cl` split at the boundary of `x = xh ++ xl`
    (see `append_and_lit`). -/
theorem append_or_lit {n m : Nat} (c ch cl : Nat) (xh : BitVec n) (xl : BitVec m)
    {rh : BitVec n} {rl : BitVec m}
    (hh : xh ||| BitVec.ofNat n ch = rh) (hl : xl ||| BitVec.ofNat m cl = rl)
    (hc : BitVec.ofNat (n + m) c = BitVec.ofNat n ch ++ BitVec.ofNat m cl) :
    (xh ++ xl) ||| BitVec.ofNat (n + m) c = rh ++ rl := by
  rw [hc, BitVec.or_append, hh, hl]

/-- `x &&& c` with the all-ones literal `c` is `x`. -/
theorem and_ones_lit {w : Nat} (c : Nat) (x : BitVec w) (hc : c = 2 ^ w - 1) :
    x &&& BitVec.ofNat w c = x := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi]

/-- `x ||| c` with the all-ones literal `c` is all ones. -/
theorem or_ones_lit {w : Nat} (c : Nat) (x : BitVec w) (hc : c = 2 ^ w - 1) :
    x ||| BitVec.ofNat w c = BitVec.ofNat w c := by
  subst hc
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi]

/-- A widened `u`-bit value is unchanged by a literal mask whose low `u` bits are all ones. -/
theorem setWidth_and_lit_low_ones {u : Nat} (w c : Nat) (y : BitVec u)
    (hc : c % 2 ^ u = 2 ^ u - 1) : y.setWidth w &&& BitVec.ofNat w c = y.setWidth w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, hi,
    decide_true, Bool.true_and]
  by_cases hiu : i < u
  · have h := congrArg (fun n => n.testBit i) hc
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, hiu, decide_true,
      Bool.true_and] at h
    simp [h]
  · simp [BitVec.getLsbD_of_ge y i (by omega)]

/-- A bit of `x ++ y` below the width of `y` is a bit of `y`. -/
theorem getLsbD_append_lt {n m : Nat} (x : BitVec n) (y : BitVec m) (i : Nat) (h : i < m) :
    (x ++ y).getLsbD i = y.getLsbD i := by
  simp [BitVec.getLsbD_append, h]

/-- A bit of `x ++ y` at or above the width of `y` is a bit of `x`. -/
theorem getLsbD_append_ge {n m : Nat} (x : BitVec n) (y : BitVec m) (i k : Nat) (h : m ≤ i)
    (hk : i - m = k) : (x ++ y).getLsbD i = x.getLsbD k := by
  subst hk
  simp [BitVec.getLsbD_append, show ¬i < m by omega]

/-- Two resizes are one when the middle width does not cut below both ends. -/
theorem setWidth_setWidth_of_ge {u : Nat} (v k : Nat) (y : BitVec u) (h : u ≤ v ∨ k ≤ v) :
    (y.setWidth v).setWidth k = y.setWidth k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hiv : i < v
  · simp [hiv]
  · simp only [hiv, decide_false, Bool.false_and]
    exact (BitVec.getLsbD_of_ge y i (by omega)).symm

end

public meta section

open Lean Meta Simp

/-- A closed term: no free variables or metavariables. -/
def isClosedTerm (e : Expr) : Bool := !e.hasFVar && !e.hasMVar

/-- Rewrite `f .. (if c then t else e) ..` to `if c then f .. t .. else f .. e ..` (`apply_ite`) when
    `t`, `e`, and every other explicit argument are closed terms, so that the arms fold to
    literals. Only the first such `if` argument is pushed; simp revisits the result. -/
def pushIteLitCore (e : Expr) : SimpM Simp.Step := do
  let e := e.consumeMData
  let args := e.getAppArgs
  let some i := args.findIdx? (fun a =>
      let a := a.consumeMData
      a.isAppOfArity ``ite 5 && isClosedTerm (a.getArg! 3) && isClosedTerm (a.getArg! 4))
    | return .continue
  for j in [0:args.size] do
    if j != i && !isClosedTerm args[j]! then return .continue
  let itE := args[i]!.consumeMData
  let α ← inferType itE
  let f ← withLocalDeclD `x α fun x => mkLambdaFVars #[x] (mkAppN e.getAppFn (args.set! i x))
  let prf ← mkAppM ``apply_ite #[f, itE.getArg! 1, itE.getArg! 3, itE.getArg! 4]
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := (← instantiateMVars rhs).headBeta, proof? := some prf }

/-- Push a comparison, mask, or truncation with closed operands into an `if` with literal arms. -/
simproc [decomp_norm] pushIteLitLE ((_ : BitVec _) ≤ (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitLT ((_ : BitVec _) < (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitEq ((_ : BitVec _) = (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitAnd ((_ : BitVec _) &&& (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitOr ((_ : BitVec _) ||| (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitXor ((_ : BitVec _) ^^^ (_ : BitVec _)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitNatLE ((_ : Nat) ≤ (_ : Nat)) := pushIteLitCore
/-- See `pushIteLitLE`. -/
simproc [decomp_norm] pushIteLitNatLT ((_ : Nat) < (_ : Nat)) := pushIteLitCore

/-- Fold `BitVec.allOnes n` at a literal width `n` to a literal. -/
simproc [decomp_norm] reduceAllOnesLit (BitVec.allOnes _) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.allOnes 1 do return .continue
  let some _ ← Nat.fromExpr? (e.getArg! 0) | return .continue
  let prf ← mkAppM ``allOnes_eq_ofNat #[e.getArg! 0]
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some prf }

/-- A left shift by a literal amount is a multiplication by a power of two (`shiftLeft_eq_mul`).
    Shifts by a variable amount stay shifts, so their limb and funnel structure is kept. -/
simproc [decomp_norm] shiftLeftLit ((_ : BitVec _) <<< (_ : Nat)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HShiftLeft.hShiftLeft 6 do return .continue
  let some _ ← Nat.fromExpr? (e.getArg! 5) | return .continue
  let prf ← mkAppM ``shiftLeft_eq_mul #[e.getArg! 4, e.getArg! 5]
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some prf }

/-- A right rotate by a literal amount at a literal width is a left rotate by the complementary
    literal (`rotateRight_eq_rotateLeft`). Variable amounts are left alone. -/
simproc [decomp_norm] rotateRightLit (BitVec.rotateRight _ _) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.rotateRight 3 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 0) | return .continue
  let some k ← Nat.fromExpr? (e.getArg! 2) | return .continue
  unless 0 < w do return .continue
  let x := e.getArg! 1
  let prf ← mkAppM ``rotateRight_eq_rotateLeft #[x, e.getArg! 2]
  let rhs ← mkAppM ``BitVec.rotateLeft #[x, mkNatLit ((w - k % w) % w)]
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `EXTR x, x, #k` at a literal width `w` and literal `k ≤ w`: `setWidth w ((x ++ x) >>> k)` is
    `x.rotateRight k` (`setWidth_append_self_ushiftRight`). A simproc rather than a lemma because
    the shifted value is typed `BitVec (2 * w)` as a literal, which does not unify with `w + w`. -/
simproc [decomp_norm] extrSelfLit (BitVec.setWidth _ ((_ : BitVec _) >>> (_ : Nat))) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 1) | return .continue
  let sh := (e.getArg! 2).consumeMData
  unless sh.isAppOfArity ``HShiftRight.hShiftRight 6 do return .continue
  let some k ← Nat.fromExpr? (sh.getArg! 5) | return .continue
  unless k ≤ w do return .continue
  let app := (sh.getArg! 4).consumeMData
  unless app.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let x := app.getArg! 4
  unless x == app.getArg! 5 do return .continue
  let xTy ← whnfR (← inferType x)
  unless xTy.isAppOfArity ``BitVec 1 do return .continue
  let some xw ← Nat.fromExpr? xTy.appArg! | return .continue
  unless xw == w do return .continue
  let hk ← mkDecideProof (← mkLe (mkNatLit k) (mkNatLit w))
  let prf ← mkAppM ``setWidth_append_self_ushiftRight #[x, sh.getArg! 5, hk]
  let rhs ← mkAppM ``BitVec.rotateRight #[x, sh.getArg! 5]
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `x &&& c = 0` for a literal power of two `c = 2 ^ j` with `j < w` (`TST x, #c`) is the bit
    test `x.toNat % 2 ^ (j + 1) < 2 ^ j` (`and_twoPow_eq_zero`, either operand order). -/
simproc [decomp_norm] andPow2EqZero ((_ : BitVec _) &&& (_ : BitVec _) = (_ : BitVec _)) :=
    fun e => do
  let e := e.consumeMData
  let some (_, lhs, rhs) := e.eq? | return .continue
  let some ⟨w, z⟩ ← getBitVecValue? rhs | return .continue
  unless z.toNat == 0 do return .continue
  let lhs := lhs.consumeMData
  unless lhs.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let mut x := lhs.getArg! 4
  let mut thm := ``and_twoPow_eq_zero
  let mut c := 0
  if let some ⟨_, v⟩ ← getBitVecValue? (lhs.getArg! 5) then
    c := v.toNat
  else if let some ⟨_, v⟩ ← getBitVecValue? (lhs.getArg! 4) then
    x := lhs.getArg! 5
    thm := ``twoPow_and_eq_zero
    c := v.toNat
  else
    return .continue
  unless c != 0 && c &&& (c - 1) == 0 do return .continue
  let j := c.log2
  unless j < w do return .continue
  let hj ← mkDecideProof (← mkLt (mkNatLit j) (mkNatLit w))
  let prf ← mkAppM thm #[x, mkNatLit j, hj]
  let some (_, _, rhs') := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs', proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs')) }

/-- The width of a `BitVec` term, when it is a literal. -/
def bvWidth? (x : Expr) : SimpM (Option Nat) := do
  let ty ← whnfR (← inferType x)
  unless ty.isAppOfArity ``BitVec 1 do return none
  Nat.fromExpr? ty.appArg!

/-- Apply `f` (a partially applied `fits_*` / `*_of_fits` lemma) to `decide` proofs of its
    remaining hypotheses (closed `Nat` equations). -/
def appDecide (f : Expr) : MetaM Expr := do
  let mut f := f
  repeat
    let ty ← whnfR (← instantiateMVars (← inferType f))
    let .forallE _ d _ _ := ty | break
    f := mkApp f (← mkDecideProof d)
  return f

/-- A literal mask `m` and a proof of `x &&& BitVec.ofNat w m = x` (see "Known-zero bits"). `fuel`
    bounds the recursion depth; below it, and for unrecognised terms, `m = 2 ^ w - 1`. -/
partial def fitsMask (x : Expr) (w : Nat) (fuel : Nat := 8) : SimpM (Nat × Expr) := do
  let full : SimpM (Nat × Expr) := do
    let m := 2 ^ w - 1
    let prf ← mkAppOptM ``fits_full #[none, mkNatLit m, x]
    return (m, ← appDecide prf)
  if fuel == 0 then return ← full
  let x' := x.consumeMData
  if let some ⟨_, v⟩ ← getBitVecValue? x' then
    let m := v.toNat
    let prf ← mkAppM ``fits_ofNat #[mkNatLit w, mkNatLit m]
    let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit m]
    let ty ← mkEq (← mkAppM ``HAnd.hAnd #[x, lit]) x
    return (m, ← mkExpectedTypeHint prf ty)
  let bin (thm : Name) (op : Nat → Nat → Nat) : SimpM (Nat × Expr) := do
    let (mx, hx) ← fitsMask (x'.getArg! 4) w (fuel - 1)
    let (my, hy) ← fitsMask (x'.getArg! 5) w (fuel - 1)
    let m := op mx my
    return (m, ← appDecide (← mkAppOptM thm #[none, none, none, mkNatLit m, none, none, hx, hy]))
  if x'.isAppOfArity ``HAnd.hAnd 6 then return ← bin ``fits_and (· &&& ·)
  if x'.isAppOfArity ``HOr.hOr 6 then return ← bin ``fits_or (· ||| ·)
  if x'.isAppOfArity ``HXor.hXor 6 then return ← bin ``fits_xor (· ||| ·)
  if x'.isAppOfArity ``HAdd.hAdd 6 then
    let (mx, hx) ← fitsMask (x'.getArg! 4) w (fuel - 1)
    let (my, hy) ← fitsMask (x'.getArg! 5) w (fuel - 1)
    unless mx &&& my == 0 do return ← full
    let m := mx ||| my
    return (m, ← appDecide
      (← mkAppOptM ``fits_add #[none, none, none, mkNatLit m, none, none, hx, hy]))
  if x'.isAppOfArity ``BitVec.setWidth 3 || x'.isAppOfArity ``BitVec.zeroExtend 3 ||
      x'.isAppOfArity ``BitVec.truncate 3 then
    let some sw ← bvWidth? (x'.getArg! 2) | return ← full
    let (mx, hx) ← fitsMask (x'.getArg! 2) sw (fuel - 1)
    let m := mx % 2 ^ w
    let prf ← appDecide
      (← mkAppOptM ``fits_setWidth #[none, none, x'.getArg! 1, mkNatLit m, none, hx])
    let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit m]
    return (m, ← mkExpectedTypeHint prf (← mkEq (← mkAppM ``HAnd.hAnd #[x, lit]) x))
  if x'.isAppOfArity ``HShiftRight.hShiftRight 6 || x'.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    let some k ← Nat.fromExpr? (x'.getArg! 5) | return ← full
    unless (← inferType (x'.getArg! 5)).isConstOf ``Nat do return ← full
    let (mx, hx) ← fitsMask (x'.getArg! 4) w (fuel - 1)
    if x'.isAppOfArity ``HShiftRight.hShiftRight 6 then
      let m := mx >>> k
      return (m, ← appDecide (← mkAppOptM ``fits_ushiftRight
        #[none, none, mkNatLit k, mkNatLit m, none, hx]))
    let m := (mx <<< k) % 2 ^ w
    return (m, ← appDecide (← mkAppOptM ``fits_shiftLeft
      #[none, none, mkNatLit k, mkNatLit m, none, hx]))
  if x'.isAppOfArity ``HMul.hMul 6 then
    let pow2 (c : Nat) : Option Nat :=
      if c != 0 && c &&& (c - 1) == 0 && c.log2 < w then some c.log2 else none
    let (thm, y, k) ← do
      if let some ⟨_, v⟩ ← getBitVecValue? (x'.getArg! 5) then
        pure (``fits_mul_twoPow, x'.getArg! 4, pow2 v.toNat)
      else if let some ⟨_, v⟩ ← getBitVecValue? (x'.getArg! 4) then
        pure (``fits_twoPow_mul, x'.getArg! 5, pow2 v.toNat)
      else pure (``fits_mul_twoPow, x, none)
    let some k := k | return ← full
    let (mx, hx) ← fitsMask y w (fuel - 1)
    let m := (mx <<< k) % 2 ^ w
    let prf ← appDecide (← mkAppOptM thm #[none, none, mkNatLit k, mkNatLit m, none, hx])
    let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit m]
    return (m, ← mkExpectedTypeHint prf (← mkEq (← mkAppM ``HAnd.hAnd #[x, lit]) x))
  if x'.isAppOfArity ``ite 5 then
    let (mx, hx) ← fitsMask (x'.getArg! 3) w (fuel - 1)
    let (my, hy) ← fitsMask (x'.getArg! 4) w (fuel - 1)
    let m := mx ||| my
    return (m, ← appDecide (← mkAppOptM ``fits_ite
      #[none, none, none, x'.getArg! 1, x'.getArg! 2, mkNatLit m, none, none, hx, hy]))
  full

/-- `x &&& c` (either operand order) for a literal `c` and a mask `m` of `x` (`fitsMask`): `x`
    when `m` fits in `c` (`and_eq_self_of_fits`), else `x &&& (m &&& c)` when that changes `c`
    (`and_eq_and_of_fits`). Drops masks that a zero extension or a narrower mask already implies. -/
simproc [decomp_norm] andLitMask ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let a := e.getArg! 4
  let b := e.getArg! 5
  let (x, c, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? b then pure (a, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? a then pure (b, v.toNat, true)
    else return .continue
  if (← getBitVecValue? x).isSome then return .continue
  let some w ← bvWidth? x | return .continue
  let c := c % 2 ^ w
  let (m, hx) ← fitsMask x w
  let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c]
  let comm (prf : Expr) : MetaM Expr := do
    if swapped then mkEqTrans (← mkAppM ``BitVec.and_comm #[lit, x]) prf else pure prf
  if m &&& c == m then
    let prf ← appDecide (← mkAppOptM ``and_eq_self_of_fits #[none, none, mkNatLit c, none, hx])
    let prf ← comm prf
    return .visit { expr := x, proof? := some (← mkExpectedTypeHint prf (← mkEq e x)) }
  let c' := m &&& c
  if c' == c then return .continue
  let prf ← appDecide (← mkAppOptM ``and_eq_and_of_fits
    #[none, none, mkNatLit c, mkNatLit c', none, hx])
  let prf ← comm prf
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `(y op c₁) &&& c₂` for `op ∈ {|||, &&&}` and literals `c₁`, `c₂` (either operand order of
    `op` and of `&&&`): the literals fold (`and_or_lit`, `and_and_lit`), so a
    continuation bit `y ||| 0x80` masked by `0x7f` is `y &&& 0x7f`. -/
simproc [decomp_norm] andLitFold ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let (innerE, n₂, outerSwapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? (e.getArg! 5) then pure (e.getArg! 4, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? (e.getArg! 4) then
      pure (e.getArg! 5, v.toNat, true)
    else return .continue
  let inner := innerE.consumeMData
  let isOr := inner.isAppOfArity ``HOr.hOr 6
  unless isOr || inner.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let (y, n₁, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? (inner.getArg! 5) then
      pure (inner.getArg! 4, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? (inner.getArg! 4) then
      pure (inner.getArg! 5, v.toNat, true)
    else return .continue
  if (← getBitVecValue? y).isSome then return .continue
  let some w ← bvWidth? y | return .continue
  let c₁ := n₁ % 2 ^ w
  let c₂ := n₂ % 2 ^ w
  let lit₁ ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c₁]
  let lit₂ ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c₂]
  let thm := if isOr then ``and_or_lit else ``and_and_lit
  let prf ← appDecide
    (← mkAppOptM thm #[none, mkNatLit c₁, mkNatLit c₂, mkNatLit (c₁ &&& c₂), y])
  let prf ← do
    if swapped then
      let comm ← mkAppM (if isOr then ``BitVec.or_comm else ``BitVec.and_comm) #[lit₁, y]
      let f ← withLocalDeclD `z (← inferType y) fun z => do
        mkLambdaFVars #[z] (← mkAppM ``HAnd.hAnd #[z, lit₂])
      mkEqTrans (← mkCongrArg f comm) prf
    else pure prf
  let prf ← do
    if outerSwapped then mkEqTrans (← mkAppM ``BitVec.and_comm #[lit₂, innerE]) prf
    else pure prf
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `BitVec.ofNat w (x.toNat % c)` for a literal power of two `c` is the mask
    `x.setWidth w &&& (c - 1)` (`ofNat_toNat_mod`), the form `andLitMask` and `toNatAndLowOnes`
    work with. -/
simproc [decomp_norm] ofNatToNatMod (BitVec.ofNat _ (BitVec.toNat _ % _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.ofNat 2 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 0) | return .continue
  let m := (e.getArg! 1).consumeMData
  unless m.isAppOfArity ``HMod.hMod 6 do return .continue
  let some p ← Nat.fromExpr? (m.getArg! 5) | return .continue
  unless p != 0 && p &&& (p - 1) == 0 do return .continue
  let t := (m.getArg! 4).consumeMData
  unless t.isAppOfArity ``BitVec.toNat 2 do return .continue
  let prf ← appDecide (← mkAppOptM ``ofNat_toNat_mod
    #[none, mkNatLit w, mkNatLit (p - 1), mkNatLit p, t.getArg! 1])
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `x ||| y` with disjoint masks (`fitsMask`) is `x + y` (`or_eq_add_of_fits`). Opt-in (simp set
    `decomp_norm_or_add`, not in `decomp_norm`): it turns bit-field packing into addition, the form `Nat`-level byte-assembly
    proofs (LEB128 groups, little-endian merges) need, but changes the normal form of `ORR`. -/
simproc [decomp_norm_or_add] orDisjointAdd ((_ : BitVec _) ||| (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HOr.hOr 6 do return .continue
  let x := e.getArg! 4
  let y := e.getArg! 5
  let some w ← bvWidth? x | return .continue
  let (mx, hx) ← fitsMask x w
  if mx == 2 ^ w - 1 then return .continue
  let (my, hy) ← fitsMask y w
  unless mx &&& my == 0 do return .continue
  let prf ← appDecide (← mkAppOptM ``or_eq_add_of_fits #[none, none, none, none, none, hx, hy])
  let rhs ← mkAppM ``HAdd.hAdd #[x, y]
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `(x &&& c).toNat` (either operand order) for a literal `c = 2 ^ k - 1` is `x.toNat % 2 ^ k`
    (`toNat_and_lowOnes`). -/
simproc [decomp_norm] toNatAndLowOnes (BitVec.toNat ((_ : BitVec _) &&& (_ : BitVec _))) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.toNat 2 do return .continue
  let a := (e.getArg! 1).consumeMData
  unless a.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let (x, c, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? (a.getArg! 5) then pure (a.getArg! 4, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? (a.getArg! 4) then pure (a.getArg! 5, v.toNat, true)
    else return .continue
  let some w ← bvWidth? x | return .continue
  let c := c % 2 ^ w
  let k := (c + 1).log2
  unless c + 1 == 2 ^ k do return .continue
  let prf ← appDecide (← mkAppOptM ``toNat_and_lowOnes
    #[none, mkNatLit c, mkNatLit k, mkNatLit (2 ^ k), x])
  let prf ← do
    if swapped then
      let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c]
      let h ← mkCongrArg (mkConst ``BitVec.toNat |>.app (mkNatLit w))
        (← mkAppM ``BitVec.and_comm #[lit, x])
      mkEqTrans h prf
    else pure prf
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- Close the remaining closed-`Nat` hypotheses of `prf : e = rhs` by `decide` and visit `rhs`. -/
def visitDecide (e prf : Expr) : SimpM Step := do
  let prf ← appDecide prf
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `t = (y >>> k).setWidth w` for a literal `k`: `(y, k)`. -/
def shiftField? (t : Expr) : SimpM (Option (Expr × Nat)) := do
  let t := t.consumeMData
  unless t.isAppOfArity ``BitVec.setWidth 3 do return none
  let s := (t.getArg! 2).consumeMData
  unless s.isAppOfArity ``HShiftRight.hShiftRight 6 do return none
  unless (← inferType (s.getArg! 5)).isConstOf ``Nat do return none
  let some k ← Nat.fromExpr? (s.getArg! 5) | return none
  return some (s.getArg! 4, k)

/-- `(y.setWidth v).setWidth w &&& c` with a literal `c < 2 ^ v` drops the inner narrowing
    (`setWidth_setWidth_and_of_lt`). Opt-in bit-field merging rule; the literal must be the
    right operand (the `decomp_norm` order). -/
simproc [decomp_norm_bitfield] setWidthNarrowAnd ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some ⟨_, cv⟩ ← getBitVecValue? (e.getArg! 5) | return .continue
  let t := (e.getArg! 4).consumeMData
  unless t.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let inner := (t.getArg! 2).consumeMData
  unless inner.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let some w ← Nat.fromExpr? (t.getArg! 1) | return .continue
  let some v ← Nat.fromExpr? (inner.getArg! 1) | return .continue
  let c := cv.toNat
  unless c < 2 ^ v do return .continue
  visitDecide e (← mkAppOptM ``setWidth_setWidth_and_of_lt
    #[none, mkNatLit w, mkNatLit v, mkNatLit c, inner.getArg! 2])

/-- `(y.setWidth v).setWidth w` drops the inner narrowing when `y` fits in `v` bits (`fitsMask`,
    `setWidth_setWidth_of_fits`). Opt-in bit-field merging rule. -/
simproc [decomp_norm_bitfield] setWidthLossless (BitVec.setWidth _ (BitVec.setWidth _ _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let inner := (e.getArg! 2).consumeMData
  unless inner.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 1) | return .continue
  let some v ← Nat.fromExpr? (inner.getArg! 1) | return .continue
  let y := inner.getArg! 2
  let some u ← bvWidth? y | return .continue
  if v ≥ u then return .continue
  let (m, hy) ← fitsMask y u
  unless m < 2 ^ v do return .continue
  visitDecide e (← mkAppOptM ``setWidth_setWidth_of_fits
    #[none, mkNatLit w, mkNatLit v, mkNatLit m, none, hy])

/-- A field `(y >>> k).setWidth w` (optionally `&&& c`) times the literal `2 ^ k` is the mask
    `y.setWidth w &&& (c <<< k)` (`setWidth_ushiftRight_and_mul_twoPow`,
    `setWidth_ushiftRight_mul_twoPow`). Opt-in bit-field merging rule. -/
simproc [decomp_norm_bitfield] shiftFieldMul ((_ : BitVec _) * (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HMul.hMul 6 do return .continue
  let some ⟨_, pv⟩ ← getBitVecValue? (e.getArg! 5) | return .continue
  let some w ← bvWidth? e | return .continue
  let p := pv.toNat
  unless p != 0 && p &&& (p - 1) == 0 && p.log2 < w do return .continue
  let k := p.log2
  let a := (e.getArg! 4).consumeMData
  if let some (y, k') ← shiftField? a then
    unless k' == k do return .continue
    return ← visitDecide e (← mkAppOptM ``setWidth_ushiftRight_mul_twoPow
      #[none, mkNatLit w, mkNatLit k, mkNatLit (((2 ^ w - 1) <<< k) % 2 ^ w), y])
  unless a.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some ⟨_, cv⟩ ← getBitVecValue? (a.getArg! 5) | return .continue
  let some (y, k') ← shiftField? (a.getArg! 4) | return .continue
  unless k' == k do return .continue
  let c := cv.toNat
  visitDecide e (← mkAppOptM ``setWidth_ushiftRight_and_mul_twoPow
    #[none, mkNatLit w, mkNatLit k, mkNatLit c, mkNatLit ((c <<< k) % 2 ^ w), y])

/-- `(z &&& c₁) ||| (z &&& c₂)` for literals is `z &&& (c₁ ||| c₂)` (`and_lit_or_and_lit`).
    Opt-in bit-field merging rule. -/
simproc [decomp_norm_bitfield] andLitOrMerge ((_ : BitVec _) ||| (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HOr.hOr 6 do return .continue
  let a := (e.getArg! 4).consumeMData
  let b := (e.getArg! 5).consumeMData
  unless a.isAppOfArity ``HAnd.hAnd 6 && b.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let some ⟨_, c₁⟩ ← getBitVecValue? (a.getArg! 5) | return .continue
  let some ⟨_, c₂⟩ ← getBitVecValue? (b.getArg! 5) | return .continue
  unless (a.getArg! 4).consumeMData == (b.getArg! 4).consumeMData do return .continue
  visitDecide e (← mkAppOptM ``and_lit_or_and_lit
    #[none, a.getArg! 4, mkNatLit c₁.toNat, mkNatLit c₂.toNat, mkNatLit (c₁.toNat ||| c₂.toNat)])

/-- `((y.setWidth v) >>> k).setWidth w` for literals with `k + w ≤ v` drops the inner narrowing
    (`setWidth_ushiftRight_setWidth_of_add_le`): the shifted window lies inside it. -/
simproc [decomp_norm] setWidthShiftNarrow (BitVec.setWidth _ ((_ : BitVec _) >>> (_ : Nat))) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 1) | return .continue
  let some (t, k) ← shiftField? e | return .continue
  let t := t.consumeMData
  unless t.isAppOfArity ``BitVec.setWidth 3 do return .continue
  let some v ← Nat.fromExpr? (t.getArg! 1) | return .continue
  unless k + w ≤ v do return .continue
  visitDecide e (← mkAppOptM ``setWidth_ushiftRight_setWidth_of_add_le
    #[none, mkNatLit v, mkNatLit k, mkNatLit w, t.getArg! 2])

/-- `(y &&& c₁) ||| c₂` for literals (either operand order of `|||` and of `&&&`) drops the mask
    when every bit `y` may set (`fitsMask`) is kept by `c₁` or set by `c₂`
    (`and_lit_or_lit_of_fits`), e.g. a 7-bit mask under an `ORR` of the bit above it. -/
simproc [decomp_norm] andLitOrAbsorb ((_ : BitVec _) ||| (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HOr.hOr 6 do return .continue
  let (innerE, n₂, outerSwapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? (e.getArg! 5) then pure (e.getArg! 4, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? (e.getArg! 4) then
      pure (e.getArg! 5, v.toNat, true)
    else return .continue
  let inner := innerE.consumeMData
  unless inner.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let (y, n₁, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? (inner.getArg! 5) then
      pure (inner.getArg! 4, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? (inner.getArg! 4) then
      pure (inner.getArg! 5, v.toNat, true)
    else return .continue
  if (← getBitVecValue? y).isSome then return .continue
  let some w ← bvWidth? y | return .continue
  let c₁ := n₁ % 2 ^ w
  let c₂ := n₂ % 2 ^ w
  let (m, hy) ← fitsMask y w
  unless m &&& (c₁ ||| c₂) == m do return .continue
  let lit₁ ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c₁]
  let lit₂ ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c₂]
  let prf ← appDecide (← mkAppOptM ``and_lit_or_lit_of_fits
    #[none, none, mkNatLit c₁, mkNatLit c₂, none, hy])
  let prf ← do
    if swapped then
      let comm ← mkAppM ``BitVec.and_comm #[lit₁, y]
      let f ← withLocalDeclD `z (← inferType y) fun z => do
        mkLambdaFVars #[z] (← mkAppM ``HOr.hOr #[z, lit₂])
      mkEqTrans (← mkCongrArg f comm) prf
    else pure prf
  let prf ← do
    if outerSwapped then mkEqTrans (← mkAppM ``BitVec.or_comm #[lit₂, innerE]) prf
    else pure prf
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint prf (← mkEq e rhs)) }

/-- `s = x >>> k` for a literal `k`: `(x, k)`. -/
def shiftRightLit? (s : Expr) : SimpM (Option (Expr × Nat)) := do
  let s := s.consumeMData
  unless s.isAppOfArity ``HShiftRight.hShiftRight 6 do return none
  unless (← inferType (s.getArg! 5)).isConstOf ``Nat do return none
  let some k ← Nat.fromExpr? (s.getArg! 5) | return none
  return some (s.getArg! 4, k)

/-- `x >>> a >>> b` for literal amounts is `x >>> (a + b)` (`ushiftRight_ushiftRight_lit`), so
    the shifts of an unrolled encoder loop meet one shift per byte. Register amounts are left to
    the funnel-shift rules. -/
simproc [decomp_norm] ushiftRightLitLit ((_ : BitVec _) >>> (_ : Nat)) := fun e => do
  let some (y, b) ← shiftRightLit? e | return .continue
  let some (x, a) ← shiftRightLit? y | return .continue
  visitDecide e (← mkAppOptM ``ushiftRight_ushiftRight_lit
    #[none, x, mkNatLit a, mkNatLit b, mkNatLit (a + b)])

/-- `x.getLsbD k` for the literal top bit `k = w - 1` is `decide (2 ^ k ≤ x.toNat)`
    (`getLsbD_top_lit`), the form `BitVec.msb_eq_decide` gives the sign bit. -/
simproc [decomp_norm] getLsbDTopLit (BitVec.getLsbD _ _) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.getLsbD 3 do return .continue
  let some w ← Nat.fromExpr? (e.getArg! 0) | return .continue
  let some k ← Nat.fromExpr? (e.getArg! 2) | return .continue
  unless k + 1 == w do return .continue
  visitDecide e (← mkAppOptM ``getLsbD_top_lit
    #[none, e.getArg! 1, mkNatLit k, mkNatLit (2 ^ k)])

/-- `x >>> k = 0` for a literal `k < w` is the threshold `x < 2 ^ k`
    (`ushiftRight_eq_zero_iff_lt`). -/
simproc [decomp_norm] ushiftRightEqZero ((_ : BitVec _) >>> (_ : Nat) = (_ : BitVec _)) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``Eq 3 do return .continue
  let some ⟨_, z⟩ ← getBitVecValue? (e.getArg! 2) | return .continue
  unless z.toNat == 0 do return .continue
  let some (x, k) ← shiftRightLit? (e.getArg! 1) | return .continue
  let some w ← bvWidth? x | return .continue
  unless k < w do return .continue
  visitDecide e (← mkAppOptM ``ushiftRight_eq_zero_iff_lt #[none, mkNatLit k, mkNatLit (2 ^ k), x])

/-- `x >>> k < c` for literals is the threshold `x < c * 2 ^ k` when `c * 2 ^ k < 2 ^ w`
    (`ushiftRight_lt_lit`). -/
simproc [decomp_norm] ushiftRightLtLit ((_ : BitVec _) >>> (_ : Nat) < (_ : BitVec _)) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``LT.lt 4 do return .continue
  let some ⟨_, cv⟩ ← getBitVecValue? (e.getArg! 3) | return .continue
  let some (x, k) ← shiftRightLit? (e.getArg! 2) | return .continue
  let some w ← bvWidth? x | return .continue
  let c := cv.toNat
  let d := c * 2 ^ k
  unless c < 2 ^ w && d < 2 ^ w do return .continue
  visitDecide e (← mkAppOptM ``ushiftRight_lt_lit #[none, mkNatLit k, mkNatLit c, mkNatLit d, x])

/-- `c ≤ x >>> k` for literals is the threshold `c * 2 ^ k ≤ x` when `c * 2 ^ k < 2 ^ w`
    (`lit_le_ushiftRight`). -/
simproc [decomp_norm] litLeUshiftRight ((_ : BitVec _) ≤ (_ : BitVec _) >>> (_ : Nat)) :=
    fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``LE.le 4 do return .continue
  let some ⟨_, cv⟩ ← getBitVecValue? (e.getArg! 2) | return .continue
  let some (x, k) ← shiftRightLit? (e.getArg! 3) | return .continue
  let some w ← bvWidth? x | return .continue
  let c := cv.toNat
  let d := c * 2 ^ k
  unless c < 2 ^ w && d < 2 ^ w do return .continue
  visitDecide e (← mkAppOptM ``lit_le_ushiftRight #[none, mkNatLit k, mkNatLit c, mkNatLit d, x])

/-- Operands of at most this `approxDepth` and at most `commOrderMaxSize` nodes (counted as a
    tree, i.e. without sharing) are ordered by `acLt` (the order `simp` uses for permutation
    lemmas such as `BitVec.and_comm`). Larger operands are ordered by `Expr.quickLt`: `acLt` is
    an LPO without memoisation, exponential in the depth of shared terms, while `quickLt` is
    cheap. Both are strict orders, and an operand pair always uses the same one (the test is
    symmetric), so the swap never loops. -/
def commOrderMaxDepth : UInt32 := 24

/-- See `commOrderMaxDepth`. -/
def commOrderMaxSize : Nat := 256

/-- `budget` minus the tree size of `e`, or `none` once the size exceeds `budget`. Binders and
    projections count as leaves; operands of arithmetic operators contain neither. -/
partial def treeSizeWithin (e : Expr) (budget : Nat) : Option Nat :=
  if budget == 0 then none else
  match e with
  | .app f a => do
    let b ← treeSizeWithin f (budget - 1)
    treeSizeWithin a b
  | .mdata _ b => treeSizeWithin b budget
  | _ => some (budget - 1)

/-- Whether `e` is small enough for `acLt` (see `commOrderMaxDepth`). -/
def commOrderSmall (e : Expr) : Bool :=
  e.approxDepth ≤ commOrderMaxDepth && (treeSizeWithin e commOrderMaxSize).isSome

/-- Whether `e` mentions a `let`-bound local: `acLt` may unfold it, so its tree size is unknown. -/
def hasLetFVar (e : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  return e.hasAnyFVar fun fv => (lctx.find? fv).any (·.isLet)

/-- Swap the operands `a`, `b` of a commutative operator `e = op a b` (`op` a heterogeneous binary
    operator such as `HOr.hOr`) when `b` comes first in the canonical order, using the
    commutativity lemma `comm : op a b = op b a`. Terms that only unfold to `op` (an `abbrev`
    matched through the discrimination tree) are left alone. -/
def commOrderCore (op comm : Name) (e : Expr) : SimpM Simp.Step := do
  let e := e.consumeMData
  unless e.isAppOfArity op 6 do return .continue
  let args := e.getAppArgs
  let a := args[4]!
  let b := args[5]!
  if a == b then return .continue
  let prf ← mkAppM comm #[a, b]
  let some (_, _, rhs) := (← inferType prf).eq? | return .continue
  let swap ←
    if commOrderSmall a && commOrderSmall b && !(← hasLetFVar a) && !(← hasLetFVar b) then
      acLt rhs e .reduceSimpleOnly
    else
      pure (Expr.quickLt b a)
  unless swap do return .continue
  return .visit { expr := rhs, proof? := some prf }

/-- Canonical operand order for `&&&` (see `commOrderCore`). -/
simproc [decomp_norm] commOrderAnd ((_ : BitVec _) &&& (_ : BitVec _)) :=
  commOrderCore ``HAnd.hAnd ``BitVec.and_comm
/-- Canonical operand order for `|||` (see `commOrderCore`). -/
simproc [decomp_norm] commOrderOr ((_ : BitVec _) ||| (_ : BitVec _)) :=
  commOrderCore ``HOr.hOr ``BitVec.or_comm
/-- Canonical operand order for `^^^` (see `commOrderCore`). -/
simproc [decomp_norm] commOrderXor ((_ : BitVec _) ^^^ (_ : BitVec _)) :=
  commOrderCore ``HXor.hXor ``BitVec.xor_comm
/-- Canonical operand order for `BitVec` `*` (see `commOrderCore`). -/
simproc [decomp_norm] commOrderMul ((_ : BitVec _) * (_ : BitVec _)) :=
  commOrderCore ``HMul.hMul ``BitVec.mul_comm
/-- Canonical operand order for `Nat` `*` (see `commOrderCore`). -/
simproc [decomp_norm] commOrderNatMul ((_ : Nat) * (_ : Nat)) :=
  commOrderCore ``HMul.hMul ``Nat.mul_comm

/-- Canonical operand order for `BitVec` `+` (see `commOrderCore`). Not part of `decomp_norm`,
    whose carry and borrow normal forms are stated for a fixed operand order; add it explicitly
    (`simp only [decomp_norm, decomp_norm_add_order]`) for add-rotate-xor code whose specification adds
    the operands in a different order than the compiler. -/
simproc [decomp_norm_add_order] commOrderAdd ((_ : BitVec _) + (_ : BitVec _)) :=
  commOrderCore ``HAdd.hAdd ``BitVec.add_comm

/-! ### Concatenations (opt-in)

`concatResize`, `concatShiftRight`, `concatShiftLeft`, `concatAndLit`, `concatOrLit`, and
`concatGetLsbD` push narrowing, widening, literal shifts, and literal masks through `x ++ y` when
every width is a literal, keeping packed register values in the left-nested `hi ++ mid ++ lo`
form. A leading `0#p ++ y` of a single atom `y` is spelled `y.zeroExtend _`. None is part of
`decomp_norm`; they form the opt-in simp set `decomp_norm_concat`
(`simp only [decomp_norm, decomp_norm_concat]`), or register them for step-time normalization
with `attribute [local arm64_norm] ProofLib.Decomp.concatResize …`. -/

/-- `x ++ y`: `(x, y)`. -/
def append? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAppend.hAppend 6 then some (e.getArg! 4, e.getArg! 5) else none

/-- The width of a `BitVec` term, evaluating closed `Nat` arithmetic (`16 + 16`). -/
def bvWidthEval? (x : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR (← inferType x)
  unless ty.isAppOfArity ``BitVec 1 do return none
  evalNat (← instantiateMVars ty.appArg!) |>.run

/-- `setWidth`, `truncate`, or `zeroExtend` applied to a width and an operand: `(width, x)`. -/
def resize? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``BitVec.setWidth 3 || e.isAppOfArity ``BitVec.truncate 3 ||
      e.isAppOfArity ``BitVec.zeroExtend 3 then
    some (e.getArg! 1, e.getArg! 2)
  else none

/-- `x` resized from `w` to `k` bits, spelled `zeroExtend` (widening) or `truncate`. -/
def mkResize (x : Expr) (w k : Nat) : MetaM Expr :=
  mkAppM (if k ≥ w then ``BitVec.zeroExtend else ``BitVec.truncate) #[mkNatLit k, x]

/-- `x.setWidth j` pushed down the left spine of a left-nested `++` chain: `(r, x.setWidth j = r)`.
    Literals fold, nested resizes and sign extensions that do not cut collapse, and a widened
    leaf `a` becomes `0#p ++ a`. -/
partial def pushSetWidth (x : Expr) (j : Nat) : MetaM (Option (Expr × Expr)) := do
  let some w ← bvWidthEval? x | return none
  let lhs ← mkAppM ``BitVec.setWidth #[mkNatLit j, x]
  let hint (prf r : Expr) : MetaM (Option (Expr × Expr)) := do
    return some (r, ← mkExpectedTypeHint prf (← mkEq lhs r))
  if j == w then
    return ← hint (← mkAppM ``BitVec.setWidth_eq #[x]) x
  if let some ⟨_, v⟩ ← getBitVecValue? x then
    let r ← mkAppM ``BitVec.ofNat #[mkNatLit j, mkNatLit (v.toNat % 2 ^ j)]
    return ← hint (← mkDecideProof (← mkEq lhs r)) r
  if let some (xh, xl) := append? x then
    let some m ← bvWidthEval? xl | return none
    if j ≤ m then
      let prf ← appDecide (← mkAppOptM ``setWidth_append_of_le_right
        #[none, none, mkNatLit j, xh, xl])
      let some (r, hr) ← pushSetWidth xl j | return none
      return ← hint (← mkEqTrans prf hr) r
    let some (xh', hh) ← pushSetWidth xh (j - m) | return none
    let prf ← mkAppOptM ``setWidth_append_add
      #[none, none, mkNatLit (j - m), xh, xl, none, hh]
    return ← hint prf (← mkAppM ``HAppend.hAppend #[xh', xl])
  if let some (_, y) := resize? x then
    let some u ← bvWidthEval? y | return none
    if u ≤ w || j ≤ w then
      let prf ← appDecide (← mkAppOptM ``setWidth_setWidth_of_ge
        #[none, mkNatLit w, mkNatLit j, y])
      let some (y', hy) ← pushSetWidth y j | return none
      return ← hint (← mkEqTrans prf hy) y'
  let xs := x.consumeMData
  if xs.isAppOfArity ``BitVec.signExtend 3 && j ≤ w then
    let y := xs.getArg! 2
    let some u ← bvWidthEval? y | return none
    if j ≤ u then
      let prf ← appDecide (← mkAppOptM ``setWidth_signExtend_of_le
        #[none, mkNatLit w, mkNatLit j, y])
      let some (y', hy) ← pushSetWidth y j | return none
      return ← hint (← mkEqTrans prf hy) y'
  if j > w then
    let p := j - w
    let r ← mkAppM ``HAppend.hAppend #[← mkAppM ``BitVec.ofNat #[mkNatLit p, mkNatLit 0], x]
    return ← hint (← mkAppM ``setWidth_eq_zero_append #[mkNatLit p, x]) r
  let r ← mkResize x w j
  hint (← mkEqRefl lhs) r

/-- A top-level `0#p ++ a` of a single atom `a` respelled `a.zeroExtend (p + w)`. -/
def tidyTop (r prf : Expr) : MetaM (Expr × Expr) := do
  let some (z, a) := append? r | return (r, prf)
  if (append? a).isSome then return (r, prf)
  let some ⟨p, zv⟩ ← getBitVecValue? z | return (r, prf)
  unless zv.toNat == 0 do return (r, prf)
  let some w ← bvWidthEval? a | return (r, prf)
  let r' ← mkResize a w (p + w)
  let prf' ← mkEqTrans prf (← mkAppM ``zero_append_eq_setWidth #[mkNatLit p, a])
  return (r', prf')

/-- Return `rhs` for `e` when it differs from `e`. -/
def concatVisit (e r prf : Expr) : MetaM Step := do
  if r == e.consumeMData then return .continue
  return .visit { expr := r, proof? := some (← mkExpectedTypeHint prf (← mkEq e r)) }

/-- `x.setWidth k` (also `truncate` / `zeroExtend`) of a `++` chain or of a nested resize, pushed
    down the chain (`pushSetWidth`). Opt-in concatenation rule. -/
def concatResizeCore (e : Expr) : SimpM Step := do
  let some (kE, x) := resize? e | return .continue
  let xs := x.consumeMData
  unless (append? xs).isSome || (resize? xs).isSome || xs.isAppOfArity ``BitVec.signExtend 3 do
    return .continue
  let some k ← (evalNat kE).run | return .continue
  let some (r, prf) ← pushSetWidth x k | return .continue
  let (r, prf) ← tidyTop r prf
  concatVisit e r prf

/-- See `concatResizeCore`. -/
simproc [decomp_norm_concat] concatResize (BitVec.setWidth _ _) := concatResizeCore
/-- See `concatResizeCore`. -/
simproc [decomp_norm_concat] concatTruncate (BitVec.truncate _ _) := concatResizeCore
/-- See `concatResizeCore`. -/
simproc [decomp_norm_concat] concatZeroExtend (BitVec.zeroExtend _ _) := concatResizeCore

/-- `(x ++ y) >>> j` for a literal `j` at least the width of `y`: `x >>> (j - m)`, widened.
    Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatShiftRight ((_ : BitVec _) >>> (_ : Nat)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HShiftRight.hShiftRight 6 do return .continue
  let some (xh, xl) := append? (e.getArg! 4) | return .continue
  let some j ← Nat.fromExpr? (e.getArg! 5) | return .continue
  let some n ← bvWidthEval? xh | return .continue
  let some m ← bvWidthEval? xl | return .continue
  unless m ≤ j do return .continue
  let (inner, prf0) ← if j == m then
      pure (xh, ← mkAppM ``append_ushiftRight_eq #[xh, xl])
    else
      let s ← mkAppM ``HShiftRight.hShiftRight #[xh, mkNatLit (j - m)]
      let prf ← appDecide (← mkAppOptM ``append_ushiftRight_of_le
        #[none, none, mkNatLit j, xh, xl])
      pure (s, ← mkExpectedTypeHint prf (← mkEq e (← mkAppM ``BitVec.setWidth
        #[mkNatLit (n + m), s])))
  let some (r, hr) ← pushSetWidth inner (n + m) | return .continue
  let (r, prf) ← tidyTop r (← mkEqTrans prf0 hr)
  concatVisit e r prf

/-- `x <<< j` for a literal `j` below the width `p + j` of `x`, when `x` is a `++` chain or a
    resize / sign extension of a term at least `p` bits wide: `x.setWidth p ++ 0#j`, with the
    narrowing pushed down (`pushSetWidth`). Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatShiftLeft ((_ : BitVec _) <<< (_ : Nat)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HShiftLeft.hShiftLeft 6 do return .continue
  let x := e.getArg! 4
  let some j ← Nat.fromExpr? (e.getArg! 5) | return .continue
  let some w ← bvWidthEval? x | return .continue
  unless 0 < j && j < w do return .continue
  let p := w - j
  let xs := x.consumeMData
  let inner? : Option Expr :=
    if let some (_, y) := resize? xs then some y
    else if xs.isAppOfArity ``BitVec.signExtend 3 then some (xs.getArg! 2) else none
  let ok ← if (append? xs).isSome then pure true else
    match inner? with
    | some y => do
      let some u ← bvWidthEval? y | pure false
      pure ((append? y).isSome || (p ≤ u && u ≤ w))
    | none => pure false
  unless ok do return .continue
  let some (x', hx) ← pushSetWidth x p | return .continue
  let prf ← mkAppOptM ``shiftLeft_eq_append #[mkNatLit p, mkNatLit j, x, none, hx]
  let r ← mkAppM ``HAppend.hAppend #[x', ← mkAppM ``BitVec.ofNat #[mkNatLit j, mkNatLit 0]]
  concatVisit e r prf

/-- `x op c` (for `op = &&&` with `and_zero` / `and_ones_lit`, or `|||` with `or_zero` /
    `or_ones_lit`) for a literal `c` of width `w`: folds `c = 0`, all-ones `c`, and literal `x`;
    else `x op c` unchanged. Returns `(r, x op c = r)`. -/
def litPiece (isAnd : Bool) (x : Expr) (w c : Nat) : MetaM (Expr × Expr) := do
  let op := if isAnd then ``HAnd.hAnd else ``HOr.hOr
  let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c]
  let lhs ← mkAppM op #[x, lit]
  let hint (prf r : Expr) : MetaM (Expr × Expr) := do
    return (r, ← mkExpectedTypeHint prf (← mkEq lhs r))
  if let some ⟨_, v⟩ ← getBitVecValue? x then
    let r ← mkAppM ``BitVec.ofNat #[mkNatLit w,
      mkNatLit (if isAnd then v.toNat &&& c else (v.toNat ||| c) % 2 ^ w)]
    return ← hint (← mkDecideProof (← mkEq lhs r)) r
  if c == 0 then
    let prf ← mkAppOptM (if isAnd then ``BitVec.and_zero else ``BitVec.or_zero) #[mkNatLit w, x]
    return ← hint prf (if isAnd then lit else x)
  if c == 2 ^ w - 1 then
    let prf ← appDecide (← mkAppOptM (if isAnd then ``and_ones_lit else ``or_ones_lit)
      #[mkNatLit w, mkNatLit c, x])
    return ← hint prf (if isAnd then x else lit)
  hint (← mkEqRefl lhs) lhs

/-- `(xh ++ xl) op c` (either operand order) for a literal `c`: the literal split at the
    boundary, each half folded (`litPiece`). -/
def concatLitCore (isAnd : Bool) (e : Expr) : SimpM Step := do
  let e := e.consumeMData
  let op := if isAnd then ``HAnd.hAnd else ``HOr.hOr
  unless e.isAppOfArity op 6 do return .continue
  let a := e.getArg! 4
  let b := e.getArg! 5
  let (x, c, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? b then pure (a, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? a then pure (b, v.toNat, true)
    else return .continue
  let some (xh, xl) := append? x | return .continue
  let some n ← bvWidthEval? xh | return .continue
  let some m ← bvWidthEval? xl | return .continue
  let c := c % 2 ^ (n + m)
  let ch := c >>> m
  let cl := c % 2 ^ m
  let (rh, hh) ← litPiece isAnd xh n ch
  let (rl, hl) ← litPiece isAnd xl m cl
  let thm := if isAnd then ``append_and_lit else ``append_or_lit
  let prf ← appDecide (← mkAppOptM thm
    #[mkNatLit n, mkNatLit m, mkNatLit c, mkNatLit ch, mkNatLit cl, xh, xl, rh, rl, hh, hl])
  let r ← mkAppM ``HAppend.hAppend #[rh, rl]
  let lit ← mkAppM ``BitVec.ofNat #[mkNatLit (n + m), mkNatLit c]
  let prf ← mkExpectedTypeHint prf (← mkEq (← mkAppM op #[x, lit]) r)
  let prf ← if swapped then
      mkEqTrans (← mkAppM (if isAnd then ``BitVec.and_comm else ``BitVec.or_comm) #[lit, x]) prf
    else pure prf
  concatVisit e r prf

/-- `(xh ++ xl) &&& c` for a literal `c` (see `concatLitCore`). Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatAndLit ((_ : BitVec _) &&& (_ : BitVec _)) := concatLitCore true
/-- `(xh ++ xl) ||| c` for a literal `c` (see `concatLitCore`). Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatOrLit ((_ : BitVec _) ||| (_ : BitVec _)) := concatLitCore false

/-- `x &&& c` (either operand order) for a literal `c` that keeps every bit `x` may set: `c` all
    ones (`and_ones_lit`), or `x` a widened `u`-bit term and the low `u` bits of `c` all ones
    (`setWidth_and_lit_low_ones`). A narrow subset of `andLitMask` that never rewrites the literal.
    Opt-in concatenation rule. -/
simproc [decomp_norm_concat] andOnesLit ((_ : BitVec _) &&& (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HAnd.hAnd 6 do return .continue
  let a := e.getArg! 4
  let b := e.getArg! 5
  let (x, c, swapped) ← do
    if let some ⟨_, v⟩ ← getBitVecValue? b then pure (a, v.toNat, false)
    else if let some ⟨_, v⟩ ← getBitVecValue? a then pure (b, v.toNat, true)
    else return .continue
  if (← getBitVecValue? x).isSome then return .continue
  let some w ← bvWidthEval? x | return .continue
  let c := c % 2 ^ w
  let lit ← mkAppM ``BitVec.ofNat #[mkNatLit w, mkNatLit c]
  let lhs ← mkAppM ``HAnd.hAnd #[x, lit]
  let prf? ← do
    if c == 2 ^ w - 1 then
      pure (some (← appDecide (← mkAppOptM ``and_ones_lit #[mkNatLit w, mkNatLit c, x])))
    else if let some (_, y) := resize? x then
      let some u ← bvWidthEval? y | pure none
      if u ≤ w && c % 2 ^ u == 2 ^ u - 1 then
        pure (some (← appDecide (← mkAppOptM ``setWidth_and_lit_low_ones
          #[none, mkNatLit w, mkNatLit c, y])))
      else pure none
    else pure none
  let some prf := prf? | return .continue
  let prf ← mkExpectedTypeHint prf (← mkEq lhs x)
  let prf ← if swapped then mkEqTrans (← mkAppM ``BitVec.and_comm #[lit, x]) prf else pure prf
  concatVisit e x prf

/-- `~~~(x ++ y)` is `~~~x ++ ~~~y` (`BitVec.not_append`, whose statement does not unify with a
    literal width). Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatNot (~~~(_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``Complement.complement 3 do return .continue
  let some (x, y) := append? (e.getArg! 2) | return .continue
  let prf ← mkAppOptM ``BitVec.not_append #[none, none, x, y]
  let r ← mkAppM ``HAppend.hAppend #[← mkAppM ``Complement.complement #[x],
    ← mkAppM ``Complement.complement #[y]]
  concatVisit e r prf

/-- `(a ++ b) op (c ++ d)` for `op ∈ {&&&, |||}` with `b`, `d` of one width: `(a op c) ++ (b op d)`
    (`BitVec.and_append`, `BitVec.or_append`). -/
def concatAppendOpCore (isAnd : Bool) (e : Expr) : SimpM Step := do
  let e := e.consumeMData
  let op := if isAnd then ``HAnd.hAnd else ``HOr.hOr
  unless e.isAppOfArity op 6 do return .continue
  let some (a, b) := append? (e.getArg! 4) | return .continue
  let some (c, d) := append? (e.getArg! 5) | return .continue
  let some wb ← bvWidthEval? b | return .continue
  let some wd ← bvWidthEval? d | return .continue
  unless wb == wd do return .continue
  let some wa ← bvWidthEval? a | return .continue
  let some wc ← bvWidthEval? c | return .continue
  unless wa == wc do return .continue
  let thm := if isAnd then ``BitVec.and_append else ``BitVec.or_append
  let prf ← mkAppOptM thm #[mkNatLit wa, mkNatLit wb, a, c, b, d]
  let r ← mkAppM ``HAppend.hAppend #[← mkAppM op #[a, c], ← mkAppM op #[b, d]]
  concatVisit e r prf

/-- `(a ++ b) &&& (c ++ d)` with matching split (see `concatAppendOpCore`). Opt-in
    concatenation rule. -/
simproc [decomp_norm_concat] concatAndAppend ((_ : BitVec _) &&& (_ : BitVec _)) :=
  concatAppendOpCore true
/-- `(a ++ b) ||| (c ++ d)` with matching split (see `concatAppendOpCore`). Opt-in
    concatenation rule. -/
simproc [decomp_norm_concat] concatOrAppend ((_ : BitVec _) ||| (_ : BitVec _)) :=
  concatAppendOpCore false

/-- `(x ++ y).getLsbD i` for a literal `i`: the bit of `y` or of `x` (`getLsbD_append_lt`,
    `getLsbD_append_ge`). Opt-in concatenation rule. -/
simproc [decomp_norm_concat] concatGetLsbD (BitVec.getLsbD _ _) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``BitVec.getLsbD 3 do return .continue
  let some (xh, xl) := append? (e.getArg! 1) | return .continue
  let some i ← Nat.fromExpr? (e.getArg! 2) | return .continue
  let some m ← bvWidthEval? xl | return .continue
  if i < m then
    visitDecide e (← mkAppOptM ``getLsbD_append_lt #[none, none, xh, xl, mkNatLit i])
  else
    visitDecide e (← mkAppOptM ``getLsbD_append_ge
      #[none, none, xh, xl, mkNatLit i, mkNatLit (i - m)])

end

end ProofLib.Decomp
