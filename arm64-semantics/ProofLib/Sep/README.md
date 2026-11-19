# `ProofLib/Sep/`: Unified Separation-Logic Automation

High-throughput, kernel-checked separation-logic tactics and combinators for byte-interval carving and coalescing, deterministic key-indexed bi-abduction, first-order composite lenses, reflected footprint disjointness, and diamond branch-join reconciliation.

Everything in this directory is untrusted (`Role::Proof`): every tactic constructs explicit Lean 4 kernel proof terms against the sealed `Arm64` separation-logic vocabulary without `native_decide`, `bv_decide`, `allowUnsafeReducibility`, or `debug.skipKernelTC`.

Import `ProofLib.Sep` (or individual sub-modules `ProofLib.Sep.{Interval,BiAbd,Lens,Consolidate}`). All tactic, command, and attribute names are global, so they work without `open ProofLib.Sep`.

## Which file and tactic for `X`

| Goal shape / proof task | Tactic / API | File |
|---|---|---|
| Carve, split, coalesce, or permute byte regions (`memRegion`, `stackAt`, `cells`, `↦₈`..`↦₁₂₈`, `↦ₛ`) across positive/negative signed offsets, `let`-bound bases, or `.rodata` (`↦ᵣ`, `pointsToBytesRO`) subslices (`P ⊢ Q` or `m ⊨ Q`) | `sep_interval` | [`Interval.lean`](Interval.lean) |
| Prove `SepProp` equality `LHS = RHS` across byte-interval splits/merges and spatial permutations | `sep_interval_eq` | [`Interval.lean`](Interval.lean) |
| Entailment `P ⊢ Q` or frame inference `P ⊢ Goal ∗ ?Frame` with `∃∗` skolemization/witnesses, dynamic `ByteSlice` splits/writes, symbolic-offset deferral, and user composite rules | `bi_entail`, `bi_frame`, `@[sep_key]`, `@[biabd_rule]` | [`BiAbd.lean`](BiAbd.lean) |
| Declare a C/Rust struct's byte layout once over a pure Lean snapshot (with automatic `memRegion` padding and 1-step stack reclaim `struct_to_memRegion`) | `StructField`, `StructLayout`, `SepLens`, `LawfulSepLens` | [`Lens.lean`](Lens.lean) |
| Step loads/stores directly into structs, symbolic-offset arrays (`pointsToArray`), downward slot tables (`slotsDownFrom`), byte slices (`↦ₛ`), or `OwnByteMap` byte maps without manual open/re-pack lemmas | `wp_lens_auto`, `wp_lens_step`, `lens_open`, `lens_switch`, `lens_close`, `@[sep_lens]` | [`Lens.lean`](Lens.lean) |
| Extract pointer non-aliasing (`p ≠ q`), list/set freshness (`hd ∉ cs`), RW-vs-RO disjointness, or total address-space bounds (`∑ lenᵢ ≤ 2 ^ 64`) from `h : m ⊨ P` or a live `SepWP` goal | `sep_disjoint`, `wp_disjoint`, `HasFootprint`, `@[sep_footprint]` | [`Consolidate.lean`](Consolidate.lean) |
| Name spatial conjuncts in the InfoView, preserve persistent `⌜φ⌝` facts across framing, or discover symbolic loop-invariant frames | `sintro`, `sname`, `sframe`, `sep_accu` | [`Consolidate.lean`](Consolidate.lean) |
| Reconcile diamond `if`/`else` branch spatial states (differing cell values → `∃∗ v`, split-vs-whole `memRegion` → coalesced region, null-vs-pointer → custom `SepJoinLub`) | `wp_if_join_auto`, `wp_join_auto`, `sep_join_lub`, `SepJoinLub` | [`Consolidate.lean`](Consolidate.lean) |
| Shared 64-bit linear address canonicalizer (`LinAddr64`, `canonAddr64`, `peelAddrRoot`) and `@[expose]` spatial bundle unfolder | `ProofLib.Sep` (`MetaM` helpers) | [`Addr.lean`](Addr.lean) |
| Worked positive, negative (`#guard_msgs`), and `#print axioms` regression suites | — | [`../Testing/SepInterval.lean`](../Testing/SepInterval.lean), [`../Testing/SepBiAbd.lean`](../Testing/SepBiAbd.lean), [`../Testing/SepLens.lean`](../Testing/SepLens.lean), [`../Testing/SepConsolidate.lean`](../Testing/SepConsolidate.lean) |

## Module Overview

### 1. Byte-Interval & `.ro` Sweep (`ProofLib.Sep.Interval`)

`sep_interval` canonicalizes every 64-bit address expression into `(root, signedByteOff)` (unfolding non-recursive local `let` bindings, substituting acyclic local pointer equalities such as `h_sp : s.sp = sp - 64#64`, and normalizing `BitVec.ofNat 64 u.toNat` to `u.zeroExtend 64`), buckets spatial atoms syntactically by `root`, runs an $O(K \log K)$ interval sweep per base pointer to carve/coalesce `memRegion`, `stackAt`, `cells`, `pointsToBytes`, and typed `↦₈`..`↦₁₂₈` (including 128-bit SIMD endian splits and `.rodata` subslice absorption), and emits a single `SepTree` permutation pass. `sep_interval_eq` proves symmetric `LHS = RHS` equalities when both sides cover identical RW/RO intervals.

### 2. Deterministic Key-First Bi-Abduction (`ProofLib.Sep.BiAbd`)

`bi_entail` and `bi_frame` run a deterministic 5-step pipeline without AC-permuting `SepProp` proof terms at intermediate steps:
1. Single-pass zipper skolemization of hypothesis `∃∗` binders and pure `⌜φ⌝` facts.
2. Exact `(Head, Key)` hash-join before payload unification (defaulting to syntactic root/offset keys so unequal symbolic offsets never trigger expensive `isDefEq` reductions).
3. Deferral of unresolved metavariable keys (`?addr`) until surrounding spatial atoms instantiate them.
4. Contiguous `ByteSlice` / `memRegion` carving and coalescing plus registered `@[biabd_rule]` hint theorems.
5. One terminal `SepTree` spine alignment followed by scheduled pure side-condition discharge.

Register custom spatial predicates and rules with `@[sep_key 0]` (or `register_sep_key MyPred [0]`) and `@[biabd_rule]` (or `register_biabd_rule my_pack_thm`).

### 3. First-Order Lenses, `StructLayout`, & `WordCodec` (`ProofLib.Sep.Lens`)

`SepLens Whole Focus Hole get put` and `LawfulSepLens` represent composite spatial access as first-order `(Focus, Hole)` pairs rather than higher-order magic-wand closures:
- **`StructLayout`**: Declare field offsets and scalar types (`u8`, `u16`, `u32`, `u64`, `u128`) over a pure snapshot struct once; padding holes become `memRegion` slices automatically, small flat scalar structs (`≤ 6` fields) take a low-overhead fast path, and `StructLayout.to_memRegion` reclaims the entire struct and its padding back into `memRegion base size` in one step.
- **Symbolic-offset arrays & byte maps**: Built-in `@[sep_lens]` rules cover `pointsToArray`, downward `slotsDownFrom` tables, `↦ₛ` byte slices, and `OwnByteMap` (`ownCells`) across `u8`..`u128` via `WordCodec`.
- **Demand-driven stepping**: `wp_lens_step` steps a single load/store instruction by inspecting its effective address, opening/switching the owning composite predicate on demand; `wp_lens_auto` drives a straight-line sequence of loads/stores and closes open lenses afterward.

### 4. Lazy Footprint Disjointness, Named Context, & Diamond Joins (`ProofLib.Sep.Consolidate`)

- **Reflected `FpTree` disjointness (`sep_disjoint`, `wp_disjoint`)**: Reifies spatial hypotheses with `HasFootprint` instances (extensible via `@[sep_footprint]` for parameterized container membership rules) into a balanced binary `FpTree` and extracts `p ≠ q`, container non-membership `hd ∉ cs`, RW-vs-RO disjointness, or total 64-bit address-space capacity bounds (`∑ lenᵢ ≤ 2 ^ 64`) in $O(\log N)$ LCA steps.
- **Named spatial context (`sintro`, `sname`, `sframe`, `sep_accu`)**: Attaches lightweight `sepHyp` labels rendered in the InfoView without `Qq` reification overhead, duplicates `SepDup` persistent facts across framing, and synthesizes symbolic loop-invariant frames (`sep_accu`).
- **Automatic diamond branch joins (`wp_if_join_auto`, `wp_join_auto`, `sep_join_lub`)**: Computes the spatial least upper bound across `then`/`else` branches—existentially quantifying differing cell values, coalescing asymmetric `memRegion` splits, and folding user `SepJoinLub` predicates—before continuing symbolic execution from the join PC.
