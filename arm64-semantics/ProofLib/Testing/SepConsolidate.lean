/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Consolidate
meta import Lean

/-!
# Regression Suite for `ProofLib.Sep.Consolidate`

Exercises:
1. Global (non-`scoped`) resolution of `@[sep_footprint]`, `register_sep_footprint`, `sep_disjoint`,
   `wp_disjoint`, `□ "..." : P`, `∗ "..." : P`, `sintro`, `sname`, `sframe`, `sep_accu`,
   `sep_join_lub`, `wp_if_join_auto`, and `wp_join_auto` **without** `open ProofLib.Sep`.
2. Parameterized container-membership non-aliasing (`hd ∉ cs`, `¬ PtrTree.Mem hd t`, `p ≠ q`,
   non-null, `OutsideRegion`, `DisjointRegions`) on 20+ conjunct spines via `sep_disjoint` and
   mid-`SepWP` `wp_disjoint`.
3. Total 64-bit address-space pigeonhole bounds (`a + b + c ≤ 2 ^ 64`) and mixed RW-vs-RO
   disjointness (`pointsTo*` vs `pointsTo*RO` / `pointsToBytesRO` / `pointsToWords64RO`).
4. IPM named dual context (`Γ_□`, `Σ_∗`), InfoView delaboration, semireducibility preservation
   under `simp`, persistent `Γ_□` duplication across `sframe`, and `sep_accu` loop-invariant frame
   discovery.
5. 25-atom `wp_if_join_auto` and `wp_join_auto` diamond branch joins combining value LUB (`∃∗ v`),
   asymmetric `memRegion` split-vs-whole coalescing, and custom `SepJoinLub` (`OptCString`)
   null-vs-string re-folding.
6. Negative `#guard_msgs` / `fail_if_success` soundness gates (rejecting RO-vs-RO aliasing claims,
   unrelated pointers, unbounded single-anchor sums, and incompatible `sep_join_lub` footprints)
   plus `#print axioms` checks.
-/

@[expose] public section

/-! ## 1. Global Resolution Without `open ProofLib.Sep` -/

namespace SepConsolidateNoOpenTests

open Arm64 ProofLib

/-- Generic singly-linked free-list chunk invariant fixture (16 bytes per chunk). -/
def FreeListInv : List (BitVec 64) → SepProp
  | [] => emp
  | c :: cs => memRegion c 16 ∗ FreeListInv cs

@[sep_footprint]
theorem freeListInv_footprint {cs : List (BitVec 64)} {c : BitVec 64} (hc : c ∈ cs) :
    ProofLib.Sep.HasFootprint (FreeListInv cs) true c 16 := by
  induction cs with
  | nil => cases hc
  | cons hd tl ih =>
    rcases List.mem_cons.mp hc with rfl | hmem
    · refine ⟨fun x hx => ?_⟩
      simpa [FreeListInv] using ownsRW_sepConj_left (ownsRW_memRegion c 16 x hx)
    · refine ⟨fun x hx => ?_⟩
      have hsub := (ih hmem).ownsRW hx
      simpa [FreeListInv] using ownsRW_sepConj_right hsub

/-- Generic binary tree of active pointer nodes (32 bytes per node). -/
inductive PtrTree where
  | leaf
  | node (ptr : BitVec 64) (l r : PtrTree)

/-- Membership predicate over `PtrTree`. -/
def PtrTree.Mem (q : BitVec 64) : PtrTree → Prop
  | .leaf => False
  | .node p l r => q = p ∨ PtrTree.Mem q l ∨ PtrTree.Mem q r

/-- Spatial pool owning 32 bytes read-write for every node in `PtrTree`. -/
def TreeNodePool : PtrTree → SepProp
  | .leaf => emp
  | .node p l r => memRegion p 32 ∗ TreeNodePool l ∗ TreeNodePool r

theorem treeNodePool_footprint {t : PtrTree} {s : BitVec 64} (hs : PtrTree.Mem s t) :
    ProofLib.Sep.HasFootprint (TreeNodePool t) true s 32 := by
  induction t with
  | leaf => cases hs
  | node p l r ihl ihr =>
    rcases hs with rfl | hl | hr
    · refine ⟨fun x hx => ?_⟩
      simpa [TreeNodePool] using ownsRW_sepConj_left (ownsRW_memRegion s 32 x hx)
    · refine ⟨fun x hx => ?_⟩
      simpa [TreeNodePool] using ownsRW_sepConj_right (ownsRW_sepConj_left ((ihl hl).ownsRW hx))
    · refine ⟨fun x hx => ?_⟩
      simpa [TreeNodePool] using ownsRW_sepConj_right (ownsRW_sepConj_right ((ihr hr).ownsRW hx))

register_sep_footprint treeNodePool_footprint

theorem noOpen_sep_disjoint_mem (m : Arm64.Memory) (hd : BitVec 64) (v : BitVec 64)
    (cs : List (BitVec 64))
    (hm : m ⊨ (hd ↦₆₄ v) ∗ FreeListInv cs) :
    hd ∉ cs := by
  sep_disjoint

theorem noOpen_sep_disjoint_entails (hd : BitVec 64) (v : BitVec 64) (cs : List (BitVec 64)) :
    (hd ↦₆₄ v) ∗ FreeListInv cs ⊢ ⌜hd ∉ cs⌝ ∗ ((hd ↦₆₄ v) ∗ FreeListInv cs) := by
  sep_disjoint

theorem noOpen_wp_disjoint (prog : Program) (target_pc : BitVec 64) (s : Arm64.State)
    (hd : BitVec 64) (v : BitVec 64) (cs : List (BitVec 64))
    (post : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp)
    (hnext : hd ∉ cs → SepWP prog target_pc s ((hd ↦₆₄ v) ∗ FreeListInv cs) post oom) :
    SepWP prog target_pc s ((hd ↦₆₄ v) ∗ FreeListInv cs) post oom := by
  wp_disjoint hnot : hd ∉ cs
  exact hnext hnot

theorem noOpen_named_context_and_accu (hdr pa pb : BitVec 64) (magic va vb : BitVec 64) :
    ∃ R : SepProp,
      ((□ "hdr" : (hdr ↦₆₄ᵣ magic)) ∗ (∗ "slot_a" : (pa ↦₆₄ va)) ∗ (pb ↦₆₄ vb)) ⊢
        ((hdr ↦₆₄ᵣ magic) ∗ (pa ↦₆₄ va)) ∗ R := by
  apply Exists.intro
  sname "slot_b" : (pb ↦₆₄ vb)
  sintro
  sep_accu

theorem noOpen_sframe (hdr pa : BitVec 64) (magic va : BitVec 64) :
    ((hdr ↦₆₄ᵣ magic) ∗ (pa ↦₆₄ va)) ⊢ (pa ↦₆₄ va) ∗ (hdr ↦₆₄ᵣ magic) := by
  sintro "hdr" "slot_a"
  sframe

theorem noOpen_if_join_and_join_auto (prog : Program) (pc1 pc2 pc_join target_pc : BitVec 64)
    (s : Arm64.State) (cond : Bool) (p fptr : BitVec 64) (v0 fval : BitVec 64)
    (post : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp)
    (hpc : s.pc = if cond then pc1 else pc2)
    (hthen : cond = true →
      SepWP prog pc_join (s.setPC pc1) ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval))
        (sepPost (fun _ => True) ((p ↦₆₄ 1#64) ∗ (fptr ↦₆₄ fval))) oom)
    (helse : cond = false →
      SepWP prog pc_join (s.setPC pc2) ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval))
        (sepPost (fun _ => True) ((p ↦₆₄ 0#64) ∗ (fptr ↦₆₄ fval))) oom)
    (hcont : ∀ sj, sj.pc = pc_join → sj.status = .Running → True →
      SepWP prog target_pc sj ((∃∗ v : BitVec 64, p ↦₆₄ v) ∗ (fptr ↦₆₄ fval)) post oom) :
    SepWP prog target_pc s ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval)) post oom := by
  wp_if_join_auto (fun _ => True), hpc then
    intro hc; exact hthen hc
  else
    intro hc; exact helse hc
  exact hcont

theorem noOpen_wp_join_auto_term (prog : Program) (pc1 pc2 pc_join target_pc : BitVec 64)
    (s : Arm64.State) (cond : Bool) (p fptr : BitVec 64) (v0 fval : BitVec 64)
    (post : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp)
    (hpc : s.pc = if cond then pc1 else pc2)
    (hthen : cond = true →
      SepWP prog pc_join (s.setPC pc1) ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval))
        (sepPost (fun _ => True) ((p ↦₆₄ 1#64) ∗ (fptr ↦₆₄ fval))) oom)
    (helse : cond = false →
      SepWP prog pc_join (s.setPC pc2) ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval))
        (sepPost (fun _ => True) ((p ↦₆₄ 0#64) ∗ (fptr ↦₆₄ fval))) oom)
    (hcont : ∀ sj, sj.pc = pc_join → sj.status = .Running → True →
      SepWP prog target_pc sj ((∃∗ v : BitVec 64, p ↦₆₄ v) ∗ (fptr ↦₆₄ fval)) post oom) :
    SepWP prog target_pc s ((p ↦₆₄ v0) ∗ (fptr ↦₆₄ fval)) post oom := by
  wp_join_auto (fun _ => True), hpc, hthen, helse
  exact hcont

end SepConsolidateNoOpenTests

/-! ## 2. 20+ Conjunct `FpTree` Disjointness, RW-vs-RO, and $2^{64}$ Pigeonhole Tests -/

namespace SepConsolidateTests

open Arm64 ProofLib ProofLib.Sep
open SepConsolidateNoOpenTests (FreeListInv PtrTree TreeNodePool)

/-- Opaque spatial invariant with no `HasFootprint` instance (mapped to `FpTree.opaqueAtom`). -/
def OpaqueWidgetState (tag : Nat) : SepProp := ⌜tag = tag⌝

/-- 24-conjunct mixed spatial spine exercising RW cells, RO tables, stack frames, slices,
    `FreeListInv`, `TreeNodePool`, null guard, and opaque invariants. -/
abbrev Spine24
    (hd sp poolBase roTbl : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64)
    (v64 : BitVec 64) (v32 : BitVec 32) (v16 : BitVec 16) (v8 : BitVec 8) (v128 : BitVec 128)
    (bs : List (BitVec 8)) (ws : List (BitVec 64)) : SepProp :=
  (0#64 ↦₈ᵣ v8) ∗
  (p1 ↦₆₄ v64) ∗
  (p2 ↦₃₂ v32) ∗
  (p3 ↦₁₆ v16) ∗
  (p4 ↦₈ v8) ∗
  (p5 ↦₁₂₈ v128) ∗
  OpaqueWidgetState 0 ∗
  (roTbl ↦₆₄ᵣ v64) ∗
  (p6 ↦₃₂ᵣ v32) ∗
  (p7 ↦₁₆ᵣ v16) ∗
  (p8 ↦₁₂₈ᵣ v128) ∗
  memRegion hd 16 ∗
  ProofLib.cells poolBase 8 ∗
  stackFrame32At sp ∗
  FreeListInv cs ∗
  TreeNodePool tree ∗
  (p9 ↦ₛ bs) ∗
  (p10 ↦ᵣ bs) ∗
  (p11 ↦₆₄* ws) ∗
  (p12 ↦₆₄ᵣ* ws) ∗
  (p13 ↦₆₄ v64) ∗
  (p14 ↦₆₄ v64) ∗
  memRegion (poolBase + 64#64) 32 ∗
  OpaqueWidgetState 1

theorem spine24_mem_exclusion_and_nodup
    (m : Arm64.Memory) (hd sp poolBase roTbl : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64)
    (v64 : BitVec 64) (v32 : BitVec 32) (v16 : BitVec 16) (v8 : BitVec 8) (v128 : BitVec 128)
    (bs : List (BitVec 8)) (ws : List (BitVec 64))
    (hnodup : cs.Nodup)
    (hm : m ⊨ Spine24 hd sp poolBase roTbl cs tree
      p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 v64 v32 v16 v8 v128 bs ws) :
    (hd :: cs).Nodup ∧ ¬ PtrTree.Mem hd tree ∧ hd ≠ 0#64 ∧ hd ≠ p14 ∧
      OutsideRegion poolBase 64 roTbl ∧ DisjointRegions hd 16 (sp - 32#64) 32 := by
  have hnotMem : hd ∉ cs := by sep_disjoint
  have hnotTree : ¬ PtrTree.Mem hd tree := by sep_disjoint
  have hnonNull : hd ≠ 0#64 := by sep_disjoint
  have hne14 : hd ≠ p14 := by sep_disjoint
  have houtRo : OutsideRegion poolBase 64 roTbl := by sep_disjoint
  have hdisjStk : DisjointRegions hd 16 (sp - 32#64) 32 := by sep_disjoint
  exact ⟨List.nodup_cons.mpr ⟨hnotMem, hnodup⟩, hnotTree, hnonNull, hne14, houtRo, hdisjStk⟩

theorem spine24_mid_wp_disjoint
    (prog : Program) (target_pc : BitVec 64) (s : Arm64.State)
    (hd sp poolBase roTbl : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree)
    (p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 : BitVec 64)
    (v64 : BitVec 64) (v32 : BitVec 32) (v16 : BitVec 16) (v8 : BitVec 8) (v128 : BitVec 128)
    (bs : List (BitVec 8)) (ws : List (BitVec 64))
    (post : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp)
    (hstep : hd ∉ cs → ¬ PtrTree.Mem hd tree → hd ≠ roTbl → hd + 8#64 ≠ p13 →
      SepWP prog target_pc s
        (Spine24 hd sp poolBase roTbl cs tree
          p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 v64 v32 v16 v8 v128 bs ws)
        post oom) :
    SepWP prog target_pc s
      (Spine24 hd sp poolBase roTbl cs tree
        p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 v64 v32 v16 v8 v128 bs ws)
      post oom := by
  wp_disjoint h1 : hd ∉ cs
  wp_disjoint h2 : ¬ PtrTree.Mem hd tree
  wp_disjoint h3 : hd ≠ roTbl
  wp_disjoint h4 : hd + 8#64 ≠ p13
  exact hstep h1 h2 h3 h4

theorem rw_vs_ro_slices_disjoint
    (h : Heap) (rwPtr roBytesPtr roWordsPtr : BitVec 64)
    (bs : List (BitVec 8)) (ws : List (BitVec 64))
    (hbsPos : 0 < bs.length) (_hbsLe : bs.length ≤ 2 ^ 64)
    (hwsPos : 0 < ws.length)
    (hh : (memRegion rwPtr 32 ∗ (roBytesPtr ↦ᵣ bs) ∗ (roWordsPtr ↦₆₄ᵣ* ws)).holds h) :
    DisjointRegions rwPtr 32 roBytesPtr bs.length ∧ rwPtr ≠ roWordsPtr := by
  refine ⟨by sep_disjoint, by sep_disjoint⟩

theorem pigeonhole_two_pos_symbolic
    (m : Arm64.Memory) (p1 p2 p3 roPtr : BitVec 64) (a b c : Nat) (rv : BitVec 64)
    (ha : 0 < a) (hb : 0 < b)
    (hm : m ⊨ memRegion p1 a ∗ (roPtr ↦₆₄ᵣ rv) ∗ memRegion p2 b ∗ OpaqueWidgetState 7 ∗ memRegion p3 c) :
    a + b + c ≤ 2 ^ 64 := by
  sep_disjoint

theorem pigeonhole_single_bounded_anchor
    (m : Arm64.Memory) (p1 p2 p3 anchor : BitVec 64) (a b c : Nat) (av : BitVec 64)
    (hm : m ⊨ memRegion p1 a ∗ (anchor ↦₆₄ av) ∗ memRegion p2 b ∗ memRegion p3 c) :
    a + b + c + 8 ≤ 2 ^ 64 := by
  sep_disjoint

theorem pigeonhole_byte_slices_unconditional
    (h : Heap) (p1 p2 p3 : BitVec 64) (bs1 bs2 bs3 : List (BitVec 8))
    (hh : ((p1 ↦ₛ bs1) ∗ (p2 ↦ₛ bs2) ∗ (p3 ↦ₛ bs3)).holds h) :
    bs1.length + bs2.length + bs3.length ≤ 2 ^ 64 := by
  sep_disjoint

/-! ## 3. IPM Named Dual Context (`Γ_□`, `Σ_∗`), Delaborator, & `sep_accu` -/

-- InfoView delaborator check: `sepHyp nm true P` renders as `□ nm : P`.
/-- info: □ "ro_cfg" : 0#64 ↦₆₄ᵣ 42#64 : SepProp -/
#guard_msgs in
#check (□ "ro_cfg" : (0#64 ↦₆₄ᵣ 42#64))

-- InfoView delaborator check: `sepHyp nm false P` renders as `∗ nm : P`.
/-- info: ∗ "stk_slot" : 16#64 ↦₆₄ 99#64 : SepProp -/
#guard_msgs in
#check (∗ "stk_slot" : (16#64 ↦₆₄ 99#64))

/-- Semireducibility check: `simp` cancels `emp` without unfolding `sepHyp` or erasing labels. -/
theorem sepHyp_preserved_under_simp (p q : BitVec 64) (vp vq : BitVec 64) :
    ((∗ "keep_label" : (p ↦₆₄ vp)) ∗ emp ∗ (q ↦₆₄ vq)) ⊢ (q ↦₆₄ vq) ∗ (p ↦₆₄ vp) := by
  simp only [emp_sepConj]
  guard_target =ₛ (∗ "keep_label" : (p ↦₆₄ vp)) ∗ (q ↦₆₄ vq) ⊢ (q ↦₆₄ vq) ∗ (p ↦₆₄ vp)
  sframe

/-- Custom persistent read-only table invariant (`SepDup`) retained in `Γ_□` across framing. -/
def RoTableInv (base : BitVec 64) (words : List (BitVec 64)) : SepProp :=
  base ↦₆₄ᵣ* words

instance instSepDupRoTableInv (base : BitVec 64) (words : List (BitVec 64)) :
    SepDup (RoTableInv base words) where
  dup_eq := by
    unfold RoTableInv
    exact SepDup.dup_eq

/-- Persistent `Γ_□` hypotheses (`RoTableInv`, `↦₆₄ᵣ`, `⌜φ⌝`) duplicate automatically across
    multiple framing steps while linear `Σ_∗` slots are consumed once. -/
theorem persistent_gamma_dup_across_sframe
    (tbl hdr pa pb : BitVec 64) (words : List (BitVec 64)) (magic va vb : BitVec 64) (n : Nat) :
    (RoTableInv tbl words ∗ (hdr ↦₆₄ᵣ magic) ∗ ⌜n < 128⌝ ∗ (pa ↦₆₄ va) ∗ (pb ↦₆₄ vb)) ⊢
      ((RoTableInv tbl words ∗ (hdr ↦₆₄ᵣ magic) ∗ ⌜n < 128⌝ ∗ (pa ↦₆₄ va)) ∗
       (RoTableInv tbl words ∗ (hdr ↦₆₄ᵣ magic) ∗ ⌜n < 128⌝ ∗ (pb ↦₆₄ vb))) := by
  sintro "ro_tbl" "ro_hdr" "bound" "slot_a" "slot_b"
  sframe

/-- `sep_accu` symbolic loop-invariant frame discovery: partitions active loop footprint vs
    synthesized `?LoopFrame` while retaining persistent `Γ_□` facts in both. -/
theorem sep_accu_loop_frame_discovery
    (roTbl iterPtr accPtr f1 f2 f3 f4 f5 f6 : BitVec 64)
    (words : List (BitVec 64)) (itVal accVal v1 v2 v3 v4 v5 v6 : BitVec 64) (len : Nat) :
    ∃ LoopFrame : SepProp,
      (RoTableInv roTbl words ∗ ⌜len ≤ 1024⌝ ∗
        (iterPtr ↦₆₄ itVal) ∗ (f1 ↦₆₄ v1) ∗ (f2 ↦₆₄ v2) ∗ (accPtr ↦₆₄ accVal) ∗
        (f3 ↦₆₄ v3) ∗ (f4 ↦₆₄ v4) ∗ (f5 ↦₆₄ v5) ∗ (f6 ↦₆₄ v6)) ⊢
      ((RoTableInv roTbl words ∗ ⌜len ≤ 1024⌝ ∗ (iterPtr ↦₆₄ itVal) ∗ (accPtr ↦₆₄ accVal)) ∗
        LoopFrame) ∧
      (LoopFrame ⊢ RoTableInv roTbl words ∗ ⌜len ≤ 1024⌝ ∗ (f6 ↦₆₄ v6) ∗ (f3 ↦₆₄ v3) ∗
        (f1 ↦₆₄ v1) ∗ (f2 ↦₆₄ v2) ∗ (f4 ↦₆₄ v4) ∗ (f5 ↦₆₄ v5)) := by
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · sintro "tbl" "len_ok" "iter" "f1" "f2" "acc" "f3" "f4" "f5" "f6"
    sep_accu
  · sframe

/-! ## 4. 25-Atom `wp_if_join_auto` Diamond Branch Join -/

/-- Nullable read-only C-string invariant: null pointer carries `⌜bytes = []⌝`, non-null
    pointer carries read-only NUL-terminated bytes `ptr ↦ᵣ (bytes ++ [0#8])`. -/
def OptCString (ptr : BitVec 64) (bytes : List (BitVec 8)) : SepProp :=
  if ptr == 0#64 then
    ⌜bytes = []⌝
  else
    ptr ↦ᵣ (bytes ++ [0#8])

theorem optCString_nonnull {ptr : BitVec 64} (hne : ptr ≠ 0#64) (bytes : List (BitVec 8)) :
    (ptr ↦ᵣ (bytes ++ [0#8])) ⊢ OptCString ptr bytes := by
  have hbeq : (ptr == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  unfold OptCString
  rw [hbeq]
  exact Entails.refl _

theorem optCString_null : emp ⊢ OptCString 0#64 [] := by
  simpa [OptCString, sepConj_emp] using
    Entails.pure_right (rfl : ([] : List (BitVec 8)) = []) (Entails.refl emp)

/-- Local proposition wrapper used as a typeclass precondition for `SepJoinLub`. -/
class TagFact (P : Prop) : Prop where
  out : P

/-- Custom `SepJoinLub` instance folding `(urlPtr ↦ᵣ (urlBytes ++ [0#8]))` (in `then`) against
    omitted `emp` (null in `else`) into `OptCString`. -/
instance instSepJoinLubOptCStringThen (cond : Bool) (urlPtr : BitVec 64) (urlBytes : List (BitVec 8))
    [h : TagFact (urlPtr ≠ 0#64)] :
    SepJoinLub cond (urlPtr ↦ᵣ (urlBytes ++ [0#8])) emp
      (OptCString (if cond then urlPtr else 0#64) (if cond then urlBytes else [])) where
  entails_then hc := by
    rw [hc]; simp only [↓reduceIte]
    exact optCString_nonnull h.out urlBytes
  entails_else hc := by
    rw [hc]; simp only [Bool.false_eq_true, ↓reduceIte]
    exact optCString_null

/-- 22 untouched spatial frame conjuncts carried unchanged across both diamond branches. -/
abbrev Frame22
    (f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11
     f12 f13 f14 f15 f16 f17 f18 f19 f20 : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree) (fv : BitVec 64) : SepProp :=
  (f01 ↦₆₄ fv) ∗ (f02 ↦₆₄ fv) ∗ (f03 ↦₆₄ fv) ∗ (f04 ↦₆₄ fv) ∗ (f05 ↦₆₄ fv) ∗
  (f06 ↦₆₄ fv) ∗ (f07 ↦₆₄ fv) ∗ (f08 ↦₆₄ fv) ∗ (f09 ↦₆₄ fv) ∗ (f10 ↦₆₄ fv) ∗
  (f11 ↦₆₄ᵣ fv) ∗ (f12 ↦₆₄ᵣ fv) ∗ (f13 ↦₆₄ fv) ∗ (f14 ↦₆₄ fv) ∗ (f15 ↦₆₄ fv) ∗
  (f16 ↦₆₄ fv) ∗ (f17 ↦₆₄ fv) ∗ (f18 ↦₆₄ fv) ∗ (f19 ↦₆₄ fv) ∗ (f20 ↦₆₄ fv) ∗
  FreeListInv cs ∗ TreeNodePool tree

/-- Permuted presentation of the same 22 frame conjuncts in the `else` branch. -/
abbrev Frame22Permuted
    (f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11
     f12 f13 f14 f15 f16 f17 f18 f19 f20 : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree) (fv : BitVec 64) : SepProp :=
  TreeNodePool tree ∗ FreeListInv cs ∗
  (f11 ↦₆₄ᵣ fv) ∗ (f12 ↦₆₄ᵣ fv) ∗
  (f20 ↦₆₄ fv) ∗ (f19 ↦₆₄ fv) ∗ (f18 ↦₆₄ fv) ∗ (f17 ↦₆₄ fv) ∗ (f16 ↦₆₄ fv) ∗
  (f15 ↦₆₄ fv) ∗ (f14 ↦₆₄ fv) ∗ (f13 ↦₆₄ fv) ∗ (f10 ↦₆₄ fv) ∗ (f09 ↦₆₄ fv) ∗
  (f08 ↦₆₄ fv) ∗ (f07 ↦₆₄ fv) ∗ (f06 ↦₆₄ fv) ∗ (f05 ↦₆₄ fv) ∗ (f04 ↦₆₄ fv) ∗
  (f03 ↦₆₄ fv) ∗ (f02 ↦₆₄ fv) ∗ (f01 ↦₆₄ fv)

/-- 9-piece carved stack scratch region covering `[sp - 352, sp - 96)` = 256 bytes:
    `8 + 8 + 4 + 4 + 16 + 32 + 64 + 32 + 88 = 256`. -/
abbrev CarvedStack256
    (sp : BitVec 64) (w0 w1 : BitVec 64) (d0 d1 : BitVec 32) (q0 : BitVec 128) : SepProp :=
  ((sp - 352#64) ↦₆₄ w0) ∗
  ((sp - 344#64) ↦₆₄ w1) ∗
  ((sp - 336#64) ↦₃₂ d0) ∗
  ((sp - 332#64) ↦₃₂ d1) ∗
  ((sp - 328#64) ↦₁₂₈ q0) ∗
  ProofLib.cells (sp - 312#64) 4 ∗
  memRegion (sp - 280#64) 64 ∗
  stackFrame32At (sp - 184#64) ∗
  memRegion (sp - 184#64) 88

/-- Full 25-atom `wp_if_join_auto` diamond branch join reconciling:
    1. Value difference `(statusPtr ↦₆₄ 1#64)` vs `(statusPtr ↦₆₄ 0#64)` → `∃∗ v, statusPtr ↦₆₄ v`,
    2. Whole `memRegion (sp - 352#64) 256` vs 9-piece `CarvedStack256` → `memRegion (sp - 352#64) 256`,
    3. Non-null `(urlPtr ↦ᵣ (urlBytes ++ [0#8]))` vs omitted `emp` → `OptCString`,
    4. 22 untouched frame conjuncts (`Frame22` vs `Frame22Permuted`) with zero restated frame atoms. -/
theorem diamond_25atom_wp_if_join_auto
    (prog : Program) (pc_then pc_else pc_join target_pc : BitVec 64)
    (s : Arm64.State) (cond : Bool)
    (statusPtr sp urlPtr : BitVec 64) [TagFact (urlPtr ≠ 0#64)]
    (urlBytes : List (BitVec 8))
    (w0 w1 initStatus fv : BitVec 64) (d0 d1 : BitVec 32) (q0 : BitVec 128)
    (f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11
     f12 f13 f14 f15 f16 f17 f18 f19 f20 : BitVec 64)
    (cs : List (BitVec 64)) (tree : PtrTree)
    (J : Arm64.State → Prop)
    (post : Arm64.State → SepProp → Prop) (oom : Arm64.State → SepProp)
    (hpc : s.pc = if cond then pc_then else pc_else)
    (hthen : cond = true →
      SepWP prog pc_join (s.setPC pc_then)
        ((statusPtr ↦₆₄ initStatus) ∗ memRegion (sp - 352#64) 256 ∗
          OptCString urlPtr urlBytes ∗
          Frame22 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv)
        (sepPost J
          ((statusPtr ↦₆₄ 1#64) ∗ memRegion (sp - 352#64) 256 ∗
            (urlPtr ↦ᵣ (urlBytes ++ [0#8])) ∗
            Frame22 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv))
        oom)
    (helse : cond = false →
      SepWP prog pc_join (s.setPC pc_else)
        ((statusPtr ↦₆₄ initStatus) ∗ memRegion (sp - 352#64) 256 ∗
          OptCString urlPtr urlBytes ∗
          Frame22 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv)
        (sepPost J
          (CarvedStack256 sp w0 w1 d0 d1 q0 ∗ (statusPtr ↦₆₄ 0#64) ∗
            Frame22Permuted f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv))
        oom)
    (hjoin : ∀ sj, sj.pc = pc_join → sj.status = .Running → J sj →
      SepWP prog target_pc sj
        (memRegion (sp - 352#64) 256 ∗
          (∃∗ v : BitVec 64, statusPtr ↦₆₄ v) ∗
          OptCString (if cond then urlPtr else 0#64) (if cond then urlBytes else []) ∗
          Frame22 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv)
        post oom) :
    SepWP prog target_pc s
      ((statusPtr ↦₆₄ initStatus) ∗ memRegion (sp - 352#64) 256 ∗
        OptCString urlPtr urlBytes ∗
        Frame22 f01 f02 f03 f04 f05 f06 f07 f08 f09 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 cs tree fv)
      post oom := by
  wp_if_join_auto J, hpc then
    intro hc; exact hthen hc
  else
    intro hc; exact helse hc
  exact hjoin

/-! ## 5. Negative Soundness Tests (`#guard_msgs` & `fail_if_success`) -/

section NegativeTests

set_option linter.unusedVariables false

-- RO-vs-RO permissions CAN alias in `Arm64`: `sep_disjoint` MUST reject `p ≠ q` on two RO cells.
/--
error: sep_disjoint: could not derive `p ≠ q` from any spatial hypothesis in context
-/
#guard_msgs in
example (h : Heap) (p q : BitVec 64) (v1 v2 : BitVec 64)
    (hh : ((p ↦₆₄ᵣ v1) ∗ (q ↦₆₄ᵣ v2)).holds h) : p ≠ q := by
  sep_disjoint

/-- RO-vs-RO `DisjointRegions` must also be rejected. -/
example (h : Heap) (p q : BitVec 64) (v1 v2 : BitVec 64)
    (hh : ((p ↦₆₄ᵣ v1) ∗ (q ↦₆₄ᵣ v2)).holds h) : True := by
  fail_if_success
    have : DisjointRegions p 8 q 8 := by sep_disjoint
  trivial

-- Zero-length `memRegion` owns no bytes, so `p ≠ q` is unprovable and must be rejected.
/--
error: sep_disjoint: could not derive `p ≠ q` from any spatial hypothesis in context
-/
#guard_msgs in
example (h : Heap) (p q : BitVec 64) (hh : (memRegion p 0 ∗ memRegion q 8).holds h) :
    p ≠ q := by
  sep_disjoint

-- Unrelated pointers not backed by spatial footprints must be rejected.
/--
error: sep_disjoint: could not derive `r ≠ q` from any spatial hypothesis in context
-/
#guard_msgs in
example (h : Heap) (p q r : BitVec 64) (v1 v2 : BitVec 64)
    (hh : ((p ↦₆₄ v1) ∗ (q ↦₆₄ v2)).holds h) : r ≠ q := by
  sep_disjoint

/-- When `b` may be `0` and `a` has no `a ≤ 2 ^ 64` bound, `memRegion p a ∗ memRegion q b` is
    satisfiable with `a > 2 ^ 64` and `b = 0` in `Arm64`; `sep_disjoint` must reject `a + b ≤ 2 ^ 64`. -/
example (h : Heap) (p q : BitVec 64) (a b : Nat) (ha : 0 < a)
    (hh : (memRegion p a ∗ memRegion q b).holds h) : True := by
  fail_if_success
    have : a + b ≤ 2 ^ 64 := by sep_disjoint
  trivial

-- Incompatible `memRegion` lengths (`16` vs `32`) must NOT be turned into `∃∗ n, memRegion p n`.
/--
error: sep_join_lub: unreconciled `then` spatial atom `memRegion p 16`
-/
#guard_msgs in
example (cond : Bool) (p : BitVec 64) :
    ∃ J : SepProp, SepJoinLub cond (memRegion p 16) (memRegion p 32) J := by
  apply Exists.intro
  sep_join_lub

-- Distinct pointers `(p ↦₆₄ v1)` vs `(q ↦₆₄ v2)` have incompatible footprints and must fail.
/--
error: sep_join_lub: unreconciled `then` spatial atom `p ↦₆₄ v1`
-/
#guard_msgs in
example (cond : Bool) (p q v1 v2 : BitVec 64) :
    ∃ J : SepProp, SepJoinLub cond (p ↦₆₄ v1) (q ↦₆₄ v2) J := by
  apply Exists.intro
  sep_join_lub

-- Mismatched cell widths `(p ↦₆₄ v1)` vs `(p ↦₃₂ v2)` must fail.
/--
error: sep_join_lub: unreconciled `then` spatial atom `p ↦₆₄ v1`
-/
#guard_msgs in
example (cond : Bool) (p v1 : BitVec 64) (v2 : BitVec 32) :
    ∃ J : SepProp, SepJoinLub cond (p ↦₆₄ v1) (p ↦₃₂ v2) J := by
  apply Exists.intro
  sep_join_lub

/-- Leaked extra linear spatial atom in one branch must fail. -/
example (cond : Bool) (p leak v1 v2 w : BitVec 64) : True := by
  fail_if_success
    have : ∃ J : SepProp, SepJoinLub cond ((p ↦₆₄ v1) ∗ (leak ↦₆₄ w)) (p ↦₆₄ v2) J := by
      apply Exists.intro
      sep_join_lub
  trivial

end NegativeTests

/-! ## 6. Axiom Cone Audit (`#print axioms`) -/

#guard_msgs in
#eval show Lean.CoreM Unit from do
  let axs ← Lean.collectAxioms ``SepConsolidateNoOpenTests.noOpen_if_join_and_join_auto
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "unexpected axioms: {axs.toList}"

/--
info: 'SepConsolidateTests.spine24_mem_exclusion_and_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms spine24_mem_exclusion_and_nodup

/--
info: 'SepConsolidateTests.pigeonhole_two_pos_symbolic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms pigeonhole_two_pos_symbolic

/--
info: 'SepConsolidateTests.persistent_gamma_dup_across_sframe' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms persistent_gamma_dup_across_sframe

/--
info: 'SepConsolidateTests.diamond_25atom_wp_if_join_auto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms diamond_25atom_wp_if_join_auto

end SepConsolidateTests

end
