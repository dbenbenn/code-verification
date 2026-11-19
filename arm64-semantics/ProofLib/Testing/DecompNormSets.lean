/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Decomp.Norm

/-!
# Opt-in `decomp_norm` Simp Sets Outside `ProofLib.Decomp`

The opt-in rule families of `ProofLib.Decomp.Norm` (`decomp_norm_bitfield`, `decomp_norm_or_add`,
`decomp_norm_concat`, `decomp_norm_add_order`) are global simp set names. This file opens no
namespace, as in a case study, and checks that every set resolves and fires. It also checks that
`decomp_norm` alone does not do their work, and that a bare rule name such as `orDisjointAdd` is
an error here (the reason the sets exist).
-/

@[expose] public section

/-! ## `decomp_norm_or_add` -/

/-- LEB128 groups: `ORR` of disjoint 7-bit fields is their sum. -/
example (b0 b1 b2 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 |||
        (b2.setWidth 32 &&& 0x7f#32) <<< 14 =
      (b0.setWidth 32 &&& 0x7f#32) + (b1.setWidth 32 &&& 0x7f#32) * 128#32 +
        (b2.setWidth 32 &&& 0x7f#32) * 16384#32 := by
  simp only [decomp_norm, decomp_norm_or_add]

/-- `decomp_norm` alone keeps `ORR` as `|||`. -/
example (b0 b1 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 =
      (b0.setWidth 32 &&& 0x7f#32) + (b1.setWidth 32 &&& 0x7f#32) * 128#32 := by
  fail_if_success (simp only [decomp_norm]; done)
  simp only [decomp_norm, decomp_norm_or_add]

/-- The qualified rule name works too. -/
example (b0 b1 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 =
      (b0.setWidth 32 &&& 0x7f#32) + (b1.setWidth 32 &&& 0x7f#32) * 128#32 := by
  simp only [decomp_norm, ProofLib.Decomp.orDisjointAdd]

-- The bare rule name does not resolve outside `ProofLib.Decomp`: `simp` logs the error and
-- carries on without the rule.
/-- error: Unknown identifier `orDisjointAdd` -/
#guard_msgs in
example (b0 b1 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 =
      (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 := by
  simp only [decomp_norm, orDisjointAdd]

-- Under `try`, the same error is swallowed silently and the rule never runs.
#guard_msgs in
example (b0 b1 : BitVec 8) :
    (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 =
      (b0.setWidth 32 &&& 0x7f#32) ||| (b1.setWidth 32 &&& 0x7f#32) <<< 7 := by
  try simp only [orDisjointAdd]
  rfl

/-! ## `decomp_norm_bitfield` -/

/-- A field narrowed to a byte, masked to 7 bits, and widened again is a mask of the wide
    value. -/
example (y : BitVec 64) :
    (y.setWidth 8).setWidth 32 &&& 0x7f#32 = y.setWidth 32 &&& 0x7f#32 := by
  simp only [decomp_norm, decomp_norm_bitfield]

/-- `decomp_norm` alone keeps the inner narrowing. -/
example (y : BitVec 64) :
    (y.setWidth 8).setWidth 32 &&& 0x7f#32 = y.setWidth 32 &&& 0x7f#32 := by
  fail_if_success (simp only [decomp_norm]; done)
  simp only [decomp_norm, decomp_norm_bitfield]

/-! ## `decomp_norm_concat` -/

/-- A literal right shift by a limb width drops the low limb. -/
example (a b : BitVec 32) : (a ++ b) >>> 32 = a.zeroExtend 64 := by
  simp only [decomp_norm, decomp_norm_concat]

/-- `decomp_norm` alone does not see through `++`. -/
example (a b : BitVec 32) : (a ++ b) >>> 32 = a.zeroExtend 64 := by
  fail_if_success (simp only [decomp_norm]; done)
  simp only [decomp_norm, decomp_norm_concat]

/-! ## `decomp_norm_add_order` -/

/-- Sums in different operand orders meet. -/
example (x y : BitVec 64) : x + y = y + x := by
  simp only [decomp_norm, decomp_norm_add_order]

/-- `decomp_norm` alone keeps the operand order of `+`. -/
example (x y : BitVec 64) : x + y = y + x := by
  fail_if_success (simp only [decomp_norm]; done)
  simp only [decomp_norm, decomp_norm_add_order]

end
