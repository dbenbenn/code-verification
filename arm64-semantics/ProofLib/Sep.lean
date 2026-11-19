/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Addr
public import ProofLib.Sep.Interval
public import ProofLib.Sep.BiAbd
public import ProofLib.Sep.Lens
public import ProofLib.Sep.Consolidate

/-!
# Separation-Logic Automation Suite (`ProofLib.Sep`)

Umbrella module for `ProofLib/Sep/`:
- `ProofLib.Sep.Addr`: shared 64-bit linear address canonicalization (`LinAddr64`, `canonAddr64`,
  `peelAddrRoot`) and `@[expose]` spatial bundle unfolding.
- `ProofLib.Sep.Interval`: root-bucketed $O(K \log K)$ byte-interval and `.ro` subslice sweep
  (`sep_interval`, `sep_interval_eq`).
- `ProofLib.Sep.BiAbd`: deterministic key-before-payload `DiscrTree` bi-abduction engine
  (`bi_entail`, `bi_frame`, `@[sep_key]`, `@[biabd_rule]`).
- `ProofLib.Sep.Lens`: first-order algebraic `SepLens` / `LawfulSepLens`, declarative
  `StructLayout`, width-polymorphic `WordCodec` / `OwnByteMap`, and demand-driven stepping
  (`lens_open`, `lens_switch`, `lens_close`, `wp_lens_step`, `wp_lens_auto`, `@[sep_lens]`).
- `ProofLib.Sep.Consolidate`: reflected `FpTree` RW/RO disjointness and $2^{64}$ capacity bounds
  (`HasFootprint`, `@[sep_footprint]`, `sep_disjoint`, `wp_disjoint`), named spatial context tags
  (`sintro`, `sname`, `sframe`, `sep_accu`), and automatic `SepWP` diamond branch-join spatial LUB
  reconciliation (`SepJoinLub`, `sep_join_lub`, `wp_if_join_auto`, `wp_join_auto`).

See `ProofLib/Sep/README.md` for usage and goal-shape dispatch.
-/
