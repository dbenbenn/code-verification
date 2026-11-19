/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Decomp.NormTactic
public import ProofLib.Testing.SimpSetUnfoldLint

/-!
# Tests for `decomp_norm` and `decomp_eq`

Positive tests pin, via `trace.decomp_eq`, the rung of `decomp_eq` that closes each goal (one per
rung: `rfl`, `decomp_norm`, `bv_lin`, `grind`, `omega`, `bv_robdd`), together with the
`decomp_norm` idioms (flags as comparisons, two-limb carry chains, shifts, `UMULH`, `Option`
chains, `BitVec` ↔ `Nat` range bridges). Negative tests pin the residual-goal message of
`decomp_eq` and the error of `decomp_eq!`. The simp set itself is checked for delta-unfold entries
and `rfl`-proved `Arm64.State` lemmas, and pinned under a heartbeat budget.
-/

@[expose] public section

namespace Testing.DecompNorm

open Arm64 _root_.ProofLib _root_.ProofLib.Decomp

/-! ## Simp-set hygiene -/

#assert_simp_set_no_delta_unfold decomp_norm

/-- info: [] -/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  Lean.logInfo m!"{← findRflStateSimpLemmas `decomp_norm}"

/-! ## One example per rung -/

section Rungs

set_option trace.decomp_eq true

/-- trace: [decomp_eq] closed by rfl -/
#guard_msgs in
/-- Rung 1: syntactically equal sides. -/
theorem rung_rfl (x y : BitVec 64) : x + y = x + y := by decomp_eq

/-- trace: [decomp_eq] closed by decomp_norm -/
#guard_msgs in
/-- Rung 2: an `ADDS` / `ADC` two-limb chain is the 128-bit sum of the concatenated limbs. -/
theorem rung_norm_carry_chain (aLo aHi bLo bHi : BitVec 64) :
    (AddWithCarry64 aHi bHi (AddWithCarry64 aLo bLo false).2.c).1 ++
        (AddWithCarry64 aLo bLo false).1 = (aHi ++ aLo) + (bHi ++ bLo) := by
  decomp_eq

/-- trace: [decomp_eq] closed by decomp_norm -/
#guard_msgs in
/-- Rung 2: a constant left shift is a multiplication. -/
theorem rung_norm_shift (x : BitVec 64) : x <<< 3 = x * 8#64 := by decomp_eq

/-- trace: [decomp_eq] closed by decomp_norm -/
#guard_msgs in
/-- Rung 2: an `Option.bind` chain with a guard. -/
theorem rung_norm_option (x : BitVec 64) :
    ((some x).bind fun a => if a = 0#64 then none else some (a + 1#64)) =
      (if x = 0#64 then none else some (x + 1#64)) := by
  decomp_eq

/-- trace: [decomp_eq] closed by decomp_norm -/
#guard_msgs in
/-- Rung 2: `CMP x, y; B.HI` is the unsigned comparison `y < x`. -/
theorem rung_norm_flags (x y : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 = decide (y < x) := by
  decomp_eq

/-- trace: [decomp_eq] closed by decomp_norm -/
#guard_msgs in
/-- Rung 2: a range bridge, with the side condition `y.toNat ≤ x.toNat` discharged from `h`. -/
theorem rung_norm_range (x y : BitVec 64) (h : y ≤ x) :
    BitVec.ofNat 64 (x.toNat - y.toNat) = x - y := by
  decomp_eq

/-- trace: [decomp_eq] closed by bv_lin -/
#guard_msgs in
/-- Rung 3: a linear stack-offset identity. -/
theorem rung_bv_lin (sp : BitVec 64) : sp - 16#64 + 8#64 = sp - 8#64 := by decomp_eq

/-- trace: [decomp_eq] closed by grind -/
#guard_msgs in
/-- Rung 4: a ring identity. -/
theorem rung_grind (a b c : BitVec 64) : (a + b) * c - b * c = a * c := by decomp_eq

/- `UMULH` by a power of two and halving-add range identities: closed at rung 5 (`omega`) on
   Lean ≤ 4.34 and already at rung 4 (`grind`) on Lean ≥ 4.35. -/
#guard_msgs (drop trace) in
/-- `UMULH` by a power of two is a right shift (a `Nat` division identity). -/
theorem rung_omega_umulh (x : BitVec 64) :
    SymBlock.evalDataProc3Val .W64 .UMULH x 8#64 0#64 = x >>> 61 := by
  decomp_eq

#guard_msgs (drop trace) in
/-- A halving add without overflow, using the hypothesis. -/
theorem rung_omega_range (x y : BitVec 64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y) >>> 1 = BitVec.ofNat 64 ((x.toNat + y.toNat) / 2) := by
  decomp_eq

/-- trace: [decomp_eq] closed by bv_slice -/
#guard_msgs in
/-- Rung 6: a byte reversal is an involution. The hypothesis `_h` (outside the `bv_slice`
    grammar) does not mention the goal's variables and is cleared first. -/
theorem rung_bv_slice (x : BitVec 32) (pc : BitVec 64) (_h : pc + 4#64 ≠ 0#64) :
    (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).extractLsb' 0 8 ++
      (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).extractLsb' 8 8 ++
      (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).extractLsb' 16 8 ++
      (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8).extractLsb' 24 8 = x := by
  decomp_eq

/-- trace: [decomp_eq] closed by bv_robdd -/
#guard_msgs in
/-- Rung 7: a small-width bit trick. -/
theorem rung_bv_robdd (x y : BitVec 8) : x ^^^ y = (x ||| y) - (x &&& y) := by decomp_eq

end Rungs

/-! ## `decomp_norm` idioms -/

/-- Conjunctions are split: each component is closed by its own rung. -/
example (a b c : BitVec 64) :
    some (a + 0#64, (a + b) * c - b * c) = some (a, a * c) := by
  decomp_eq

/-- An `ADDS` carry under no-overflow hypotheses is `false`. -/
example (x y : BitVec 64) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    ConditionHolds .CS (AddWithCarry64 x y false).2 = false := by
  decomp_eq

/-- `UMULH` as a `Nat` quotient. -/
example (x y : BitVec 64) :
    SymBlock.evalDataProc3Val .W64 .UMULH x y 0#64 = BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) := by
  decomp_eq

/-- Masking keeps the low bits of the `Nat` value. -/
example (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by decomp_eq

/-- Nested width changes collapse. -/
example (x : BitVec 64) : ((x.truncate 32).zeroExtend 64).truncate 32 = x.truncate 32 := by
  decomp_eq

/-- `(x + y).toNat` under a no-overflow hypothesis. -/
example (x y : BitVec 64) (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := by
  decomp_eq

/-- `(x * y).toNat` under a no-overflow hypothesis. -/
example (x y : BitVec 64) (h : x.toNat * y.toNat < 2 ^ 64) :
    (x * y).toNat = x.toNat * y.toNat := by
  decomp_eq

/-- Extra simp lemmas (e.g. a model definition) are passed to rung 2. -/
def model (a b : BitVec 64) : BitVec 64 := a * 4#64 + b

example (a b : BitVec 64) : a <<< 2 + b = model a b := by decomp_eq [model]

/-- `(budget := k)` raises the per-rung heartbeat budget. -/
example (a b : BitVec 64) : (a + b) * (a + b) = a * a + 2#64 * a * b + b * b := by
  decomp_eq (budget := 2000)

/-! ## Literal-arm `if`s and two-limb normal forms -/

/-- `CSET` then compare: the comparison is pushed into the literal arms and collapses. -/
example (c : Bool) :
    (if 1#32 ≤ (if c = true then 1#32 else 0#32) then 1#64 else 0#64) =
      (if c = true then 1#64 else 0#64) := by
  decomp_eq

/-- A `CCMP` chain over two limbs is 128-bit equality. -/
example (x y : BitVec 128) :
    (if (if x.setWidth 64 = y.setWidth 64 then
          decide ¬(x >>> 64).setWidth 64 = (y >>> 64).setWidth 64 else true) = true
      then 0#32 else 1#32) = (if x = y then 1#32 else 0#32) := by
  decomp_eq

/-- The high limb of a 128-bit sum is an `ADC` of the high limbs with the low carry. -/
example (x y : BitVec 128) :
    (AddWithCarry64 ((x >>> 64).setWidth 64) ((y >>> 64).setWidth 64)
        (AddWithCarry64 (x.setWidth 64) (y.setWidth 64) false).2.c).1 =
      ((x + y) >>> 64).setWidth 64 := by
  decomp_eq

/-- A `SUBS` / `SBCS` borrow chain is one 128-bit unsigned comparison. -/
example (x y : BitVec 128) :
    (((y >>> 64).setWidth 64).toNat +
        (if (y.setWidth 64).toNat ≤ (x.setWidth 64).toNat then 0 else 1) ≤
      ((x >>> 64).setWidth 64).toNat) = (y ≤ x) := by
  decomp_eq

/-- The high limb of a 128-bit product (`UMULH` + two `MADD`s), operands in either order. -/
example (x y : BitVec 128) :
    BitVec.ofNat 64 ((y.setWidth 64).toNat * (x.setWidth 64).toNat / 2 ^ 64) +
        y.setWidth 64 * (x >>> 64).setWidth 64 + (y >>> 64).setWidth 64 * x.setWidth 64 =
      ((x * y) >>> 64).setWidth 64 := by
  decomp_eq

/-- Bitwise operators distribute over limbs, in canonical operand order. -/
example (x y : BitVec 128) :
    (y >>> 64).setWidth 64 &&& ~~~(x >>> 64).setWidth 64 = ((~~~x &&& y) >>> 64).setWidth 64 := by
  decomp_eq

/-- A conditional increment (`CINC`) is an addition of a conditional addend. -/
example (p : Prop) [Decidable p] (x : BitVec 64) :
    (if p then x + 1#64 else x) = x + (if p then 1#64 else 0#64) := by
  decomp_eq

/-- The literal-arm push needs every other operand closed: an open operand blocks it. -/
example (c : Bool) (y : BitVec 64) (h : (if c = true then 1#64 else 0#64) ≤ y) :
    (if c = true then 1#64 else 0#64) ≤ y := by
  fail_if_success simp only [pushIteLitLE]
  exact h

/-- The literal-arm push needs literal arms: an open arm blocks it. -/
example (c : Bool) (x : BitVec 64) (h : (if c = true then x else 0#64) ≤ 5#64) :
    (if c = true then x else 0#64) ≤ 5#64 := by
  fail_if_success simp only [pushIteLitLE]
  exact h

/-! ## Variable shifts, two-limb shifts and rotates, single-bit tests -/

/-- A funnel `(y >>> 1) >>> (~~~s % 64)` is one shift by `64 - s % 64`, through the truncation. -/
example (y : BitVec 64) (s : BitVec 32) :
    y >>> 1 >>> (((~~~s).setWidth 64).toNat % 64) = y >>> (64 - s.toNat % 64) := by
  decomp_eq

/-- `TST s, #64` is a test of bit 6. -/
example (s : BitVec 32) : (s &&& 64#32 = 0#32) = (s.toNat % 128 < 64) := by
  simp only [decomp_norm]

/-- The high limb of a 128-bit left shift (`LSL` / `LSR` funnel / `TST` / `CSEL`). -/
example (x : BitVec 128) (s : BitVec 32) :
    (if s &&& 64#32 = 0#32 then
        x.setWidth 64 >>> 1 >>> (((~~~s).setWidth 64).toNat % 64) |||
          (x >>> 64).setWidth 64 <<< (s.toNat % 64)
      else x.setWidth 64 <<< (s.toNat % 64)) =
      ((x <<< (s.toNat % 128)) >>> 64).setWidth 64 := by
  decomp_eq

/-- The low limb of a 128-bit rotate left, with the `TST` mask on the 64-bit register (normalising
    it takes more than the default per-rung budget). -/
example (x : BitVec 128) (r : BitVec 64) :
    ((if 64#64 &&& r = 0#64 then (x >>> 64).setWidth 64 >>> 1 >>>
          (((~~~r.setWidth 32).setWidth 64).toNat % 64)
        else x.setWidth 64 >>> 1 >>> (((~~~r.setWidth 32).setWidth 64).toNat % 64)) |||
      (if 64#64 &&& r = 0#64 then x.setWidth 64 else (x >>> 64).setWidth 64) <<< (r.toNat % 64)) =
      (x.rotateLeft ((r.setWidth 32).toNat % 128)).setWidth 64 := by
  decomp_eq (budget := 4000)

/-- A single-bit test of a two-limb value (`LSR` + `AND #1`) is the bit at `n % 128`. -/
example (x : BitVec 128) (n : Nat) :
    (1#64 &&& if 64 ≤ n % 128 then (x >>> 64).setWidth 64 >>> (n % 64)
      else x.setWidth 64 >>> (n % 64)).setWidth 32 =
      if x.getLsbD (n % 128) = true then 1#32 else 0#32 := by
  decomp_eq

/-- A shift by a variable amount stays a shift (only literal amounts become multiplications). -/
example (x : BitVec 64) (n : Nat) (h : x <<< n = 0#64) : x <<< n = 0#64 := by
  fail_if_success simp only [shiftLeftLit]
  exact h

/-- Undoing a two-limb funnel shift by a register amount `k` rebuilds the limb: the cross-limb
    terms shift by `64` in total and vanish, and the two complementary masks give back `lo`. -/
example (lo hi : BitVec 64) (k : Nat) :
    (lo <<< k >>> k ||| hi >>> (64 - k) >>> k ||| (lo >>> (64 - k) ||| hi <<< k) <<< (64 - k)) =
      lo := by
  simp only [decomp_norm]

/-- The mirror image: the low `k` bits come back through `<<< (64 - k) >>> (64 - k)`. -/
example (lo hi : BitVec 64) (k : Nat) :
    (lo >>> k <<< k ||| hi <<< (64 - k) <<< k ||| (lo <<< (64 - k) ||| hi >>> k) >>> (64 - k)) =
      lo := by
  simp only [decomp_norm]

/-- Complementary-shift cancellation needs `w - k` and `k`: unrelated amounts do not vanish. -/
example (x : BitVec 64) (j k : Nat) (h : x >>> (64 - j) >>> k = 0#64) :
    x >>> (64 - j) >>> k = 0#64 := by
  fail_if_success (simp only [decomp_norm]; done)
  exact h

/-- Masks by unrelated amounts do not rebuild the value. -/
example (x : BitVec 64) (j k : Nat) (h : (x <<< k >>> k ||| x >>> (64 - j) <<< (64 - j)) = x) :
    (x <<< k >>> k ||| x >>> (64 - j) <<< (64 - j)) = x := by
  fail_if_success (simp only [decomp_norm]; done)
  exact h

/-! ## Commutative operand order, zero-extension injectivity, 0/1 choices -/

/-- Both sides reach one operand order. -/
example (x y z : BitVec 64) : (x &&& y) ||| z = z ||| (y &&& x) := by
  simp only [decomp_norm]

/-- Operands deeper than the `acLt` depth cap are still put in one order. -/
example (x y : BitVec 64) :
    x * (y * (x * (y * (x * (y * (x * y)))))) ^^^ y = y ^^^ (y * x * y * x * y * x * y * x) := by
  simp only [decomp_norm]

/-- An operand pair already in canonical order is left alone (the order is strict). -/
example (x y : BitVec 64) (h : x &&& y = 0#64) : x &&& y = 0#64 := by
  fail_if_success simp only [commOrderAnd] at h
  exact h

/-- Bytes compared after zero-extension compare the bytes. -/
example (a b : BitVec 8) : (a.setWidth 32 == b.setWidth 32) = (a == b) := by
  simp only [decomp_norm]

/-- The `CSET` form of a byte comparison is a 0/1 choice on the bytes. -/
example (a b : BitVec 8) :
    (if ¬(BitVec.setWidth 32 a == BitVec.setWidth 32 b) = true then (0#64 : BitVec 64) else 1#64) =
      if (a == b) = true then 1#64 else 0#64 := by
  simp only [decomp_norm]

/-- A 0/1 accumulator built with `and`, through zero-extension and truncation. -/
example (a b c d : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64
      ((if (a.setWidth 32 == b.setWidth 32) = true then 1#32 else 0#32) &&&
        (if (c.setWidth 32 == d.setWidth 32) = true then 1#32 else 0#32))) =
      if (a == b) = true ∧ (c == d) = true then 1#32 else 0#32 := by
  simp only [decomp_norm]

/-- Truncation is not injective: the rule needs `w ≤ v`. -/
example (a b : BitVec 32) (h : a.setWidth 8 = b.setWidth 8) : a.setWidth 8 = b.setWidth 8 := by
  fail_if_success simp only [setWidth_eq_setWidth_of_le, Nat.reduceLeDiff] at h
  exact h

/-! ## Leading and trailing zero counts -/

/-- A scan for the highest set bit is `clz`. -/
example (x : BitVec 32) :
    ((List.range 32).find? (fun i => x.getMsbD i)).getD 32 = x.clz.toNat := by
  simp only [decomp_norm]

/-- `RBIT` + `CLZ` is `ctz`. -/
example (x : BitVec 64) : (Arm64.reverseBits x).clz = x.ctz := by
  simp only [decomp_norm]

/-- A two-limb `CLZ` sequence (`CMP hi, #0`, `CLZ`, `ADD #64`, `CSEL`) computes the 128-bit count. -/
example (x : BitVec 128) :
    (if (x >>> 64).setWidth 64 = 0#64 then (x.setWidth 64).clz.setWidth 32 + 64#32
     else ((x >>> 64).setWidth 64).clz.setWidth 32) =
      BitVec.ofNat 32 ((List.range 128).find? (fun i => x.getMsbD i) |>.getD 128) := by
  simp only [decomp_norm]

/-- The limb rules are 128-bit only. -/
example (x : BitVec 64) (h : x.clz.toNat = 3) : x.clz.toNat = 3 := by
  fail_if_success simp only [clz128_toNat_limbs, ctz128_toNat_limbs] at h
  exact h

/-! ## Constant rotates, opt-in `+` order, large shared operands -/

/-- `ROR #51`, shifted-register `ror #48`, and `EXTR x, x, #32` reach left rotates. -/
example (x y : BitVec 64) :
    (y ^^^ shiftVal .W64 x .ROR 51) + ((x ++ x) >>> 32).setWidth 64 +
        (x ^^^ y).rotateRight 48 =
      (x.rotateLeft 13 ^^^ y) + x.rotateLeft 32 + (y ^^^ x).rotateLeft 16 := by
  simp only [decomp_norm]

/-- `+` is reordered only on request. -/
example (x y z : BitVec 64) : (x + y) ^^^ z = z ^^^ (y + x) := by
  simp only [decomp_norm, commOrderAdd]

/-- Operands with a small depth but a large unshared tree are ordered without `acLt`. -/
example (a b : BitVec 64) :
    let t1 := a + b; let t2 := t1 + t1; let t3 := t2 + t2; let t4 := t3 + t3
    let t5 := t4 + t4; let t6 := t5 + t5; let t7 := t6 + t6; let t8 := t7 + t7
    let t9 := t8 + t8; let t10 := t9 + t9
    t10 ^^^ (t10 * t9) = (t9 * t10) ^^^ t10 := by
  intros
  simp only [decomp_norm]

/-- Rotates by a variable amount stay right rotates. -/
example (x : BitVec 64) (n : Nat) (h : x.rotateRight n = 0#64) : x.rotateRight n = 0#64 := by
  fail_if_success simp only [rotateRightLit] at h
  exact h

/-- `EXTR` of two different registers is not a rotate. -/
example (x y : BitVec 64) (h : ((x ++ y) >>> 32).setWidth 64 = 0#64) :
    ((x ++ y) >>> 32).setWidth 64 = 0#64 := by
  fail_if_success simp only [extrSelfLit] at h
  exact h

/-- `decomp_norm` alone does not reorder `+`. -/
example (x y : BitVec 64) (h : x + y = 0#64) : x + y = 0#64 := by
  fail_if_success simp only [commOrderAdd] at h
  exact h

/-! ## Known-zero bits: masks and disjoint fields -/

/-- Masks implied by a zero extension or by a narrower shifted value are dropped. -/
example (x : BitVec 16) :
    (x.setWidth 64 &&& 0xffff0000ffff#64) ^^^ (x.setWidth 64 >>> 7 &&& 511#64) =
      x.setWidth 64 ^^^ x.setWidth 64 >>> 7 := by
  simp only [decomp_norm]

/-- A mask is shrunk to the bits its operand can have (`UXTB`, then `AND #0x7f0000007f`). -/
example (b : BitVec 8) : b.setWidth 64 &&& 0x7f0000007f#64 = b.setWidth 64 &&& 0x7f#64 := by
  simp only [decomp_norm]

/-- A low-ones mask is a `Nat` remainder at any width and in either operand order. -/
example (x : BitVec 32) (y : BitVec 64) :
    (x &&& 0x7f#32).toNat + (0x3fff#64 &&& y).toNat = x.toNat % 128 + y.toNat % 16384 := by
  simp only [decomp_norm]

/-- LEB128 groups: `ORR` of disjoint 7-bit fields is their sum (opt-in `orDisjointAdd`). -/
example (b0 b1 b2 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 |||
        (b2.setWidth 32 &&& 0x7f#32) <<< 14 =
      (b0.setWidth 32 &&& 0x7f#32) + (b1.setWidth 32 &&& 0x7f#32) * 128#32 +
        (b2.setWidth 32 &&& 0x7f#32) * 16384#32 := by
  simp only [decomp_norm, orDisjointAdd]

/-- An unrolled LEB128 decoder stage (`AND` of two lanes with `0x7f`, `ORR` of the next byte
    shifted by 7) is the `Nat` sum of the 7-bit groups. -/
example (b8 b9 : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 b8 &&& 545460846719#64 |||
      BitVec.setWidth 64 (BitVec.setWidth 32 b9 * 128#32)) =
      BitVec.ofNat 32 (b8.toNat % 128 + b9.toNat * 128) := by
  simp only [decomp_norm, orDisjointAdd]

/-- A continuation bit masked off by `0x7f` folds away; `ORR` with `0` is dropped. -/
example (x : BitVec 8) :
    0#32 ||| 127#32 &&& (x.setWidth 32 ||| 128#32) = x.setWidth 32 &&& 127#32 := by
  simp only [decomp_norm]

/-- A mask that the operand may exceed is kept. -/
example (x : BitVec 64) (h : x &&& 0x7f#64 = 0#64) : x &&& 0x7f#64 = 0#64 := by
  fail_if_success simp only [andLitMask] at h
  exact h

/-- Overlapping fields are not added. -/
example (b : BitVec 8) (h : b.setWidth 32 ||| b.setWidth 32 <<< 4 = 0#32) :
    b.setWidth 32 ||| b.setWidth 32 <<< 4 = 0#32 := by
  fail_if_success simp only [orDisjointAdd] at h
  exact h

/-- A mask that is not `2 ^ k - 1` is not a remainder. -/
example (x : BitVec 32) (h : (x &&& 0x7e#32).toNat = 0) : (x &&& 0x7e#32).toNat = 0 := by
  fail_if_success simp only [toNatAndLowOnes] at h
  exact h

/-! ## Bit-field merging (opt-in) -/

/-- A byte view of a halfword, masked to 7 bits, is a mask of the halfword. -/
example (x : BitVec 16) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (x.extractLsb' 0 8) &&& 545460846719#64 ||| 0#64) =
      BitVec.zeroExtend 32 (x &&& 0x007f#16) := by
  simp only [decomp_norm, setWidthNarrowAnd]

/-- Two LEB128 groups re-assemble the low 14 bits. -/
example (x : BitVec 16) :
    (BitVec.truncate 32
        (BitVec.zeroExtend 64 ((x >>> 7).extractLsb' 0 8) &&& 545460846719#64) <<< 7 |||
      BitVec.truncate 32
        (BitVec.zeroExtend 64 (x.extractLsb' 0 8 ||| 128#8) &&& 545460846719#64 ||| 0#64)) =
      BitVec.zeroExtend 32 (x &&& 0x3fff#16) := by
  simp only [decomp_norm, setWidthNarrowAnd, shiftFieldMul, andLitOrMerge]

/-- Three LEB128 groups (continuation bits set) re-assemble a halfword. -/
example (x : BitVec 16) :
    (BitVec.truncate 32
        (BitVec.zeroExtend 64 ((x >>> 14).extractLsb' 0 8) &&& 545460846719#64) <<< 14 |||
      (BitVec.truncate 32
          (BitVec.zeroExtend 64 ((x >>> 7).extractLsb' 0 8 ||| 128#8) &&& 545460846719#64) <<< 7 |||
        BitVec.truncate 32
          (BitVec.zeroExtend 64 (x.extractLsb' 0 8 ||| 128#8) &&& 545460846719#64 ||| 0#64))) =
      BitVec.zeroExtend 32 x := by
  simp only [decomp_norm, setWidthNarrowAnd, setWidthLossless, shiftFieldMul, andLitOrMerge]

/-- A lossy narrowing is kept. -/
example (x : BitVec 16) (h : (x.setWidth 8).setWidth 32 = 0#32) :
    (x.setWidth 8).setWidth 32 = 0#32 := by
  fail_if_success simp only [setWidthLossless] at h
  exact h

/-- A mask wider than the inner narrowing keeps it. -/
example (x : BitVec 16) (h : (x.setWidth 8).setWidth 32 &&& 0x1ff#32 = 0#32) :
    (x.setWidth 8).setWidth 32 &&& 0x1ff#32 = 0#32 := by
  fail_if_success simp only [setWidthNarrowAnd] at h
  exact h

/-- A field scaled by a different power of two is not merged. -/
example (x : BitVec 16) (h : (x >>> 7).setWidth 32 * 256#32 = 0#32) :
    (x >>> 7).setWidth 32 * 256#32 = 0#32 := by
  fail_if_success simp only [shiftFieldMul] at h
  exact h

/-- Masks of different values are not merged. -/
example (x y : BitVec 32) (h : x &&& 0x7f#32 ||| y &&& 0x3f80#32 = 0#32) :
    x &&& 0x7f#32 ||| y &&& 0x3f80#32 = 0#32 := by
  fail_if_success simp only [andLitOrMerge] at h
  exact h

/-! ## Concatenations (opt-in) -/

/-- The `concat*` rules plus the core literal folds they leave behind. -/
macro "concat_norm" : tactic => `(tactic| simp only [concatResize, concatTruncate,
  concatZeroExtend, concatShiftRight, concatShiftLeft, concatAndLit, concatOrLit, concatGetLsbD,
  concatNot, concatAndAppend, concatOrAppend, andOnesLit, andLitOrMerge, BitVec.reduceAppend,
  BitVec.reduceGetLsb, BitVec.reduceBEq, BitVec.reduceZeroExtend, BitVec.reduceSetWidth,
  BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceNot])

/-- `orr` of a tag bit with a shifted halfword packs `0 ++ alpha ++ tag`. -/
example (alpha : BitVec 16) :
    (1#64 ||| BitVec.zeroExtend 64 (BitVec.zeroExtend 32 alpha <<< 16)) =
      0#32 ++ alpha ++ 1#16 := by concat_norm

/-- A sign extension whose extension bits are shifted out packs the same way. -/
example (alpha : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (1#64 ||| BitVec.zeroExtend 64 (BitVec.signExtend 32 alpha <<< 16))) =
      0#32 ++ alpha ++ 1#16 := by concat_norm

/-- Narrowing and re-widening a packed value whose top half is zero is the identity. -/
example (alpha beta : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (0#32 ++ alpha ++ beta)) = 0#32 ++ alpha ++ beta := by
  concat_norm

/-- A literal mask is split at the field boundary and folds per field. -/
example (alpha : BitVec 16) : (0#32 ++ alpha ++ 1#16) &&& 281470681808895#64 = 1#64 := by
  concat_norm

/-- A single-bit test of a packed value reads the field. -/
example (alpha : BitVec 16) :
    (BitVec.setWidth 32 ((0#32 ++ alpha ++ 1#16) &&& 4294967297#64) == 0#32) = false := by
  concat_norm

/-- `lsr` by a field width drops the low field; a lone remaining field is a zero extension. -/
example (alpha : BitVec 16) : (0#32 ++ alpha ++ 0#16) >>> 16 = BitVec.zeroExtend 64 alpha := by
  concat_norm

/-- `ubfx` of a middle field. -/
example (alpha beta : BitVec 16) (gamma : BitVec 8) :
    ((0#16 ++ alpha ++ beta ++ gamma ++ 0#8) >>> 32) &&& 65535#64 = BitVec.zeroExtend 64 alpha := by
  concat_norm

/-- `lsl` of a packed value narrows it and appends zeros. -/
example (alpha beta : BitVec 16) :
    BitVec.truncate 32 (0#32 ++ alpha ++ beta) <<< 16 = beta ++ 0#16 := by concat_norm

/-- `bic` against a packed value with a zero low field. -/
example (alpha beta : BitVec 16) :
    (1#32 &&& ~~~BitVec.truncate 32 (0#16 ++ alpha ++ beta ++ 0#16)) = 1#32 := by concat_norm

/-- Two byte masks of one halfword, packed with the same split, re-join. -/
example (alpha : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (0#32 ++ (alpha &&& 65280#16) ++ 0#16)) |||
      BitVec.zeroExtend 64 (BitVec.truncate 32 (0#32 ++ (alpha &&& 255#16) ++ 0#16)) =
      0#32 ++ alpha ++ 0#16 := by concat_norm

/-- A mask that clears bits of a widened value is kept. -/
example (alpha : BitVec 16) (h : BitVec.zeroExtend 64 alpha &&& 255#64 = 0#64) :
    BitVec.zeroExtend 64 alpha &&& 255#64 = 0#64 := by
  fail_if_success simp only [andOnesLit] at h
  exact h

/-- A left shift that does not move whole lanes of a narrower source is kept. -/
example (alpha : BitVec 16) (h : BitVec.zeroExtend 64 alpha <<< 16 = 0#64) :
    BitVec.zeroExtend 64 alpha <<< 16 = 0#64 := by
  fail_if_success simp only [concatShiftLeft] at h
  exact h

/-- A right shift by less than the low field is kept. -/
example (alpha beta : BitVec 16) (h : (alpha ++ beta) >>> 8 = 0#32) :
    (alpha ++ beta) >>> 8 = 0#32 := by
  fail_if_success simp only [concatShiftRight] at h
  exact h

/-- A bit test at a variable index is kept. -/
example (alpha beta : BitVec 16) (i : Nat) (h : (alpha ++ beta).getLsbD i = true) :
    (alpha ++ beta).getLsbD i = true := by
  fail_if_success simp only [concatGetLsbD] at h
  exact h

/-- Narrowing an atom (no concatenation, no nested resize) is kept. -/
example (alpha : BitVec 64) (h : BitVec.truncate 32 alpha = 0#32) :
    BitVec.truncate 32 alpha = 0#32 := by
  fail_if_success simp only [concatTruncate] at h
  exact h

/-! ## Narrowing through shifts, absorbed masks, shift thresholds -/

/-- A byte of a shifted 32-bit view (`LSR w, #7` then `STRB`) is a byte of the shifted value, also
    through a re-widening to 64 bits and under an `ORR` of the continuation bit. -/
example (v : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 32 v >>> 7) = BitVec.setWidth 8 (v >>> 7) ∧
      BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v) >>> 21) =
        BitVec.setWidth 8 (v >>> 21) ∧
      BitVec.setWidth 8 ((BitVec.setWidth 32 v >>> 14) ||| 0xffffff80#32) =
        BitVec.setWidth 8 (v >>> 14) ||| 0x80#8 := by
  simp only [decomp_norm, and_self]

/-- A 7-bit mask under an `ORR` of bit 7 is dropped, in either operand order. -/
example (w : BitVec 64) :
    (BitVec.setWidth 8 w &&& 127#8 ||| 128#8) = (BitVec.setWidth 8 w ||| 128#8) ∧
      (128#8 ||| 127#8 &&& BitVec.setWidth 8 w) = (BitVec.setWidth 8 w ||| 128#8) := by
  simp only [decomp_norm, and_self]

/-- A zero high part and its complement are thresholds, so one bound implies the others. -/
example (v : BitVec 64) (h₁ : v >>> 28 = 0#64) (h₂ : ¬v < 0x4000#64) :
    v >>> 21 < 0x80#64 ∧ ¬v >>> 7 < 0x80#64 ∧ v >>> 7 ≠ 0#64 := by
  simp only [decomp_norm] at h₁ h₂ ⊢
  bv_omega

/-- Literal right shifts compose (an unrolled `LSR #7` chain). -/
example (x : BitVec 64) : x >>> 7 >>> 7 >>> 7 = x >>> 21 := by
  simp only [decomp_norm]

/-- A byte with its continuation bit, behind an `abbrev` that unfolds to `|||`. -/
abbrev orTag (v : BitVec 64) (sh : Nat) : BitVec 8 := BitVec.setWidth 8 (v >>> sh) ||| 0x80#8

/-- Operand-order rules leave a term that only unfolds to `|||` alone: its last two arguments are
    not the operands. -/
example (v : BitVec 64) (sh : Nat) : orTag v sh ||| 0#8 = orTag v sh := by
  simp only [decomp_norm]

/-- The literal top bit is the sign threshold (as `msb`); a lower bit is not. -/
example (x : BitVec 64) (h : x.getLsbD 63 = false) : x < 0x8000000000000000#64 := by
  simp only [decomp_norm] at h
  bv_omega

example (x : BitVec 64) (h : x.getLsbD 62 = false) : x.getLsbD 62 = false := by
  fail_if_success simp only [getLsbDTopLit] at h
  exact h

/-- A shift by a register amount does not compose. -/
example (x : BitVec 64) (n : Nat) (h : x >>> 7 >>> n = 0#64) : x >>> 7 >>> n = 0#64 := by
  fail_if_success simp only [ushiftRightLitLit] at h
  exact h

/-- A narrowing below the shifted window is kept. -/
example (v : BitVec 64) (h : BitVec.setWidth 8 (BitVec.setWidth 32 v >>> 28) = 0#8) :
    BitVec.setWidth 8 (BitVec.setWidth 32 v >>> 28) = 0#8 := by
  fail_if_success simp only [setWidthShiftNarrow] at h
  exact h

/-- A mask that the `ORR` does not cover is kept. -/
example (w : BitVec 64) (h : BitVec.setWidth 8 w &&& 63#8 ||| 128#8 = 0#8) :
    BitVec.setWidth 8 w &&& 63#8 ||| 128#8 = 0#8 := by
  fail_if_success simp only [andLitOrAbsorb] at h
  exact h

/-- A shift by the full width, or a threshold that overflows, is not rewritten. -/
example (v : BitVec 64) (h : v >>> 64 = 0#64 ∧ v >>> 60 < 0x80#64) :
    v >>> 64 = 0#64 ∧ v >>> 60 < 0x80#64 := by
  fail_if_success simp only [ushiftRightEqZero, ushiftRightLtLit] at h
  exact h

/-- Repeated tests of one condition on a path collapse (`ite_then_ite_same`,
    `ite_else_ite_same`). -/
example (n : Nat) (x y z w : BitVec 64) :
    (if 64 ≤ n then (if 64 ≤ n then x else y) else (if 64 ≤ n then z else w)) =
      if 64 ≤ n then x else w := by
  simp only [decomp_norm]

/-! ## Negative tests -/

-- A false equation: the note shows the original equation and the `decomp_norm`-normalized
-- residual goal (`x <<< 1 + 0#64` became `x * 2#64`), which stays open.
/--
info: decomp_eq: could not close `x <<< 1 + 0#64 = 1#64`;
tried rfl, decomp_norm, bv_lin, grind, omega, bv_slice, bv_robdd; residual goal left open
x : BitVec 64
⊢ x * 2#64 = 1#64
---
error: unsolved goals
x : BitVec 64
⊢ x * 2#64 = 1#64
-/
#guard_msgs in
example (x : BitVec 64) : x <<< 1 + 0#64 = 1#64 := by
  decomp_eq

-- A false lane shuffle (the halves are swapped): `bv_slice` runs and fails, the goal stays open.
/--
info: decomp_eq: could not close `BitVec.extractLsb' 0 16 x ++ BitVec.extractLsb' 16 16 x = x`;
tried rfl, decomp_norm, bv_lin, grind, omega, bv_slice, bv_robdd; residual goal left open
x : BitVec 32
⊢ BitVec.setWidth 16 x ++ BitVec.extractLsb' 16 16 x = x
---
error: unsolved goals
x : BitVec 32
⊢ BitVec.setWidth 16 x ++ BitVec.extractLsb' 16 16 x = x
-/
#guard_msgs in
example (x : BitVec 32) : x.extractLsb' 0 16 ++ x.extractLsb' 16 16 = x := by
  decomp_eq

/--
error: decomp_eq!: could not close `x + y = x - y`;
tried rfl, decomp_norm, bv_lin, grind, omega, bv_slice, bv_robdd; residual goal:
x y : BitVec 64
⊢ x + y = x - y
-/
#guard_msgs in
example (x y : BitVec 64) : x + y = x - y := by
  decomp_eq!

/-! ## Heartbeat pin for the simp set -/

set_option maxHeartbeats 500 in
/-- `simp only [decomp_norm]` on a flag-heavy term stays within a fixed heartbeat budget. -/
theorem norm_budget (x y z : BitVec 64) :
    (ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 &&
        ConditionHolds .GE (AddWithCarry64 y (~~~z) true).2 &&
        ConditionHolds .NE (AddWithCarry64 x (~~~z) true).2 &&
        ConditionHolds .CS (AddWithCarry64 (x <<< 3) z false).2) =
      (decide (y < x) && z.sle y && decide (¬x = z) &&
        decide (2 ^ 64 ≤ (x * 8#64).toNat + z.toNat)) := by
  simp only [decomp_norm]

/-! ## Axioms -/

/-- info: 'Testing.DecompNorm.rung_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_grind

#guard_msgs in
#eval show Lean.CoreM Unit from do
  let axs ← Lean.collectAxioms ``rung_omega_umulh
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected axioms: {axs.toList}"

/-- info: 'Testing.DecompNorm.rung_bv_robdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_bv_robdd

/-- info: 'Testing.DecompNorm.rung_norm_carry_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rung_norm_carry_chain

/-- info: 'Testing.DecompNorm.norm_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms norm_budget

end Testing.DecompNorm
