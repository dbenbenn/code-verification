# `ProofLib/Decomp/`: Decompiled-Term Normalization

Value reasoning for proofs that machine code computes a pure Lean function. After symbolic
execution, a goal typically says that a register or flag expression built from ISA helpers
(`AddWithCarry`, `ConditionHolds`, `setWidth`, shifts, masks, two-limb arithmetic) equals a model
expression. This directory brings both sides into one normal form (`decomp_norm`) and closes the
remaining equation with a fixed, deterministic ladder of decision procedures (`decomp_eq`).

Everything here is untrusted: `decomp_norm` contains only proved rewrite theorems, and `decomp_eq`
only chains existing tactics, so every proof is checked by the Lean kernel. Neither uses
`native_decide`, `bv_decide` or `debug.skipKernelTC`. Both are engine-independent: they act on
pure `BitVec` / `Nat` / `Bool` / `Option` terms and never mention `Arm64.State`.

## Which file for X

| I want to... | File |
|---|---|
| See what `decomp_norm` rewrites into what (flags as comparisons, carries as `toNat` bounds, canonical widths, shifts as multiplications, `Option` combinators inlined, two-limb arithmetic) | [`Norm.lean`](Norm.lean) (table in the module header) |
| Find the simp attribute declarations and the members of the named opt-in sets | [`NormAttr.lean`](NormAttr.lean) |
| Close a pure equation `machineExpr = modelExpr` with the `decomp_eq` ladder | [`NormTactic.lean`](NormTactic.lean) |
| See worked examples (each rung, residual-goal messages, opt-in sets) | [`Testing/DecompNorm.lean`](../Testing/DecompNorm.lean), [`Testing/DecompNormSets.lean`](../Testing/DecompNormSets.lean) |

Import `ProofLib.Decomp` (or `ProofLib.Decomp.NormTactic` for `decomp_eq`, `ProofLib.Decomp.Norm`
for the simp sets only). Neither is part of the `ProofLib` umbrella.

## `decomp_norm`

`simp only [decomp_norm]` normalizes a decompiled term and a model term to one form, so that
equal values usually become syntactically equal. Typical rewrites:

| Input | Normal form |
|---|---|
| `ConditionHolds cc (AddWithCarry x (~~~y) true).2` (`SUBS` / `CMP`) | `decide (y ≤ x)`, `decide (x = y)`, `BitVec.slt`, ... |
| `(AddWithCarry x y c).2.c` (carry) | `decide (2 ^ w ≤ x.toNat + y.toNat + (if c then 1 else 0))` |
| `truncate` / `zeroExtend`, nested `setWidth` | one `setWidth` |
| `x <<< k` | `x * BitVec.ofNat w (2 ^ k)` |
| `Option.bind` / `map` / `pure`, `if c then some a else some b` | inlined, `some (if c then a else b)` |
| `(x + y).toNat`, `(x - y).toNat` | `Nat` arithmetic, when the no-overflow side condition is in context |
| limbs of a 128-bit `+` / `-` / `*` / bitwise operator | the two-limb chain the machine computes |

The full table is in the header of [`Norm.lean`](Norm.lean). Every rule is a theorem (no
definition is registered by name), and literal arithmetic is folded by core simprocs registered
into the set, so `simp only [decomp_norm]` needs no extra arguments. Model definitions and other
simp sets are passed the same way: `simp only [decomp_norm, myModel, bv_arith_norm]`.

## Named opt-in sets

Some rule families change a normal form that `decomp_norm` fixes, so they are not part of it.
Add them by name next to `decomp_norm`:

```lean
simp only [decomp_norm, decomp_norm_concat]
```

| Set | Use |
|---|---|
| `decomp_norm_bitfield` | merge masked, shifted byte fields into one masked field (byte assembly) |
| `decomp_norm_or_add` | `x \|\|\| y` with disjoint bits is `x + y` (`Nat`-level byte assembly) |
| `decomp_norm_concat` | push resizes, literal shifts, and masks through `hi ++ lo` (packed registers) |
| `decomp_norm_add_order` | one operand order for `BitVec` `+` (add-rotate-xor code) |

Simp set names are global, so these work without opening `ProofLib.Decomp`. Listing a set that
does not exist is an error, so a proof that depends on a set fails loudly if the set is renamed.
To use the members during symbolic execution instead, register them locally with
`attribute [local arm64_norm] ProofLib.Decomp.<rule>` (member names are listed in
[`NormAttr.lean`](NormAttr.lean)).

## The `decomp_eq` ladder

`decomp_eq [extra, …]` proves a pure equation `lhs = rhs` over `BitVec` / `Nat` / `Bool`, and
`Option`s and tuples of those, by running a fixed ladder. Each rung sees only what the previous
rungs left open:

| Rung | Tactic | Closes |
|---|---|---|
| 1 | `with_reducible rfl` | syntactically equal sides |
| 2 | `simp only [decomp_norm, extra*]`, then `rfl` | equal after normalization |
| 3 | `bv_lin` | linear `BitVec` identities |
| 4 | `grind` | ring identities, congruence |
| 5 | `bv_omega`, then `(repeat' split) <;> bv_omega` | `toNat` range facts, carries, hypotheses in context |
| 6 | `bv_slice` with the context cleared to what the goal mentions | byte/lane shuffles (`++`, `extractLsb'`), only when the goal contains them |
| 7 | `bv_robdd` | bit tricks, only when every `BitVec` width is a literal `≤ decompEq.robddMaxWidth` (default 16) |

Rung 2 splits a normalized conjunction (`some (a, b) = some (c, d)` becomes `a = c ∧ b = d`) and
runs rungs 3–7 on each conjunct; its simp discharger (`assumption`, `omega`, `bv_omega`) lets
conditional range rules fire when the side condition follows from the context.

Every rung is speculative: it runs on the isolated goal with error recovery off and a heartbeat
budget of `decompEq.budget` (default 1000, in `maxHeartbeats` units; `decomp_eq (budget := k)`
overrides it, never above the enclosing `maxHeartbeats`). A rung that throws, logs an error, or
leaves a `sorry` is rolled back. On failure `decomp_eq` leaves the normalized residual goal open
with a message naming the rungs it tried; `decomp_eq!` fails instead.
`set_option trace.decomp_eq true` reports which rung closed each goal.
