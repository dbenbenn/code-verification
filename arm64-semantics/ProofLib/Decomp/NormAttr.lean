/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean

/-!
# Simp Set for Decompiled-Term Normalization

Registers the `decomp_norm` simp attribute. `ProofLib.Decomp.Norm` populates it with generic
rewrite rules that bring a decompiled `BitVec` / `Bool` / `Option` term and a pure Lean model into
a common normal form (flags as comparisons, carries as `toNat` bounds, canonical widths, shifts as
multiplications, `Option` combinators inlined). `decomp_eq` (`ProofLib.Decomp.NormTactic`) runs
`simp only [decomp_norm]` as its second rung.

It also registers the opt-in rule families, which change a normal form that `decomp_norm`
fixes and therefore are not part of it. Add them by name, e.g.
`simp only [decomp_norm, decomp_norm_concat]`. Simp set names are global, so this works without
opening `ProofLib.Decomp`, while the bare rule names (`orDisjointAdd`) do not. For step-time
normalization, register the members with `attribute [local arm64_norm] ProofLib.Decomp.<rule>`.

| Set | Members (`ProofLib.Decomp.*`) | Use |
|---|---|---|
| `decomp_norm_bitfield` | `setWidthNarrowAnd`, `setWidthLossless`, `shiftFieldMul`, `andLitOrMerge` | merge masked, shifted byte fields into one masked field (byte assembly) |
| `decomp_norm_or_add` | `orDisjointAdd` | `x \|\|\| y` with disjoint bits is `x + y` (`Nat`-level byte assembly) |
| `decomp_norm_concat` | `concatResize`, `concatTruncate`, `concatZeroExtend`, `concatShiftRight`, `concatShiftLeft`, `concatAndLit`, `concatOrLit`, `concatGetLsbD`, `concatNot`, `concatAndAppend`, `concatOrAppend`, `andOnesLit` | push resizes, literal shifts, and masks through `hi ++ lo` (packed registers) |
| `decomp_norm_add_order` | `commOrderAdd` | one operand order for `BitVec` `+` (add-rotate-xor code) |
-/

public section

/-- Normalization rules for decompiled `BitVec` / `Bool` / `Option` terms; see
    `ProofLib.Decomp.Norm`. -/
register_simp_attr decomp_norm

/-- Opt-in bit-field merging rules (byte assembly); use with `decomp_norm`. -/
register_simp_attr decomp_norm_bitfield

/-- Opt-in rule rewriting `|||` of disjoint bit fields to `+`; use with `decomp_norm`. -/
register_simp_attr decomp_norm_or_add

/-- Opt-in concatenation rules (`hi ++ lo` packed registers); use with `decomp_norm`. -/
register_simp_attr decomp_norm_concat

/-- Opt-in canonical operand order for `BitVec` `+`; use with `decomp_norm`. -/
register_simp_attr decomp_norm_add_order

end
