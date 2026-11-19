/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Interval

/-!
# Regression Tests for `ProofLib.Sep.Interval` (`sep_interval` & `sep_interval_eq`)

Covers:
1. Unqualified invocation of `sep_interval` and `sep_interval_eq` without `open ProofLib.Sep`.
2. Multi-region stack and buffer carving/coalescing across positive and negative signed 64-bit offsets.
3. `let`-bound base pointers, local pointer equality hypotheses, stack wrappers, and zero-length slices.
4. Dynamic `BitVec.ofNat 64 b.toNat` and `b.zeroExtend 64` offset expressions.
5. Unaligned multi-cell carving/folding, 8/16/32/64/128-bit endian split/pack, `@[expose]` spatial
   bundle unfolding, and prenex `∃∗` pushing, elimination, and witness synthesis.
6. `.rodata` (`pointsToBytesRO` / `pointsTo*RO`) subslice carving, duplication, and absorption.
7. Equality mode (`sep_interval_eq` proving `LHS = RHS` over `SepProp`).
8. Negative `#guard_msgs` and `fail_if_success` soundness tests rejecting out-of-bounds carves,
   overlapping writes, width mismatches, and RW-from-RO promotions.
9. `#print axioms` checks confirming dependence only on `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

namespace Testing.SepInterval

/-! ## 1. Unqualified Tactic Invocation (Without `open ProofLib.Sep`) -/

section Unqualified

open Arm64 ProofLib

theorem unqualified_rw_coalesce
    (sp : BitVec 64) (w0 w1 w2 : BitVec 64) (R : SepProp) :
    (((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗
     ((sp + 32#64) ↦₆₄ w2) ∗ memRegion (sp + 40#64) 16 ∗ R) ⊢
    (memRegion (sp - 64#64) 16 ∗ memRegion (sp + 32#64) 24 ∗ R) := by
  sep_interval

theorem unqualified_endian_pack_eq (p : BitVec 64) (v : BitVec 64) :
    (((p + 8#64) ↦₃₂ v.extractLsb' 0 32) ∗ ((p + 12#64) ↦₃₂ v.extractLsb' 32 32)) =
    ((p + 8#64) ↦₆₄ v) := by
  sep_interval_eq

theorem unqualified_ro_subslice_eq (tbl : BitVec 64) :
    (((tbl + 2#64) ↦ᵣ [0x30#8, 0x40#8]) ∗
     (tbl ↦ᵣ [0x10#8, 0x20#8, 0x30#8, 0x40#8, 0x50#8])) =
    (tbl ↦ᵣ [0x10#8, 0x20#8, 0x30#8, 0x40#8, 0x50#8]) := by
  sep_interval_eq

theorem unqualified_prenex_exists (p : BitVec 64) (w : BitVec 64) :
    ((∃∗ v : BitVec 64, (p ↦₆₄ v)) ∗ ((p + 8#64) ↦₆₄ w)) ⊢
    (memRegion p 8 ∗ (∃∗ u : BitVec 64, ((p + 8#64) ↦₆₄ u))) := by
  sep_interval

end Unqualified

/-! ## 2. Multi-Region Stack & Buffer Carving and Coalescing -/

open Arm64 ProofLib ProofLib.Sep

/-- A 15-word exposed user spatial bundle (intentionally without `@[sep_unfold]`). -/
def WidgetFrame15 (sp : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 : BitVec 64) : SepProp :=
  ((sp - 16#64) ↦₆₄ s0) ∗ ((sp - 8#64) ↦₆₄ s1) ∗
  ((sp - 32#64) ↦₆₄ s2) ∗ ((sp - 24#64) ↦₆₄ s3) ∗
  ((sp - 48#64) ↦₆₄ s4) ∗ ((sp - 40#64) ↦₆₄ s5) ∗
  ((sp - 64#64) ↦₆₄ s6) ∗ ((sp - 56#64) ↦₆₄ s7) ∗
  ((sp - 80#64) ↦₆₄ s8) ∗ ((sp - 72#64) ↦₆₄ s9) ∗
  ((sp - 96#64) ↦₆₄ s10) ∗ ((sp - 88#64) ↦₆₄ s11) ∗
  ((sp - 112#64) ↦₆₄ s12) ∗ ((sp - 104#64) ↦₆₄ s13) ∗
  ((sp - 120#64) ↦₆₄ s14)

theorem widget_frame_carve_coalesce
    (sp buf : BitVec 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 : BitVec 64)
    (h0 h1 h2 : BitVec 64) (q0 : BitVec 128) (bs : List (BitVec 8))
    (h_bs : bs.length = 24) (R : SepProp) :
    (memRegion (sp - 848#64) 232 ∗
     memRegion (sp - 616#64) 496 ∗
     WidgetFrame15 sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 ∗
     ((sp + 32#64) ↦₆₄ h0) ∗ ((sp + 40#64) ↦₆₄ h1) ∗ ((sp + 48#64) ↦ₛ bs) ∗
     ((buf + 0x440#64) ↦₁₂₈ q0) ∗ ((buf + 0x450#64) ↦₆₄ h2) ∗ R) ⊢
    (stackFrameAt sp 848 ∗
     memRegion (sp + 32#64) 40 ∗
     cells (buf + 0x440#64) 3 ∗ R) := by
  sep_interval

theorem packet_slots_coalesce_90_words
    (ptr : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9
     w10 w11 w12 w13 w14 w15 w16 w17 w18 w19
     w20 w21 w22 w23 w24 w25 w26 w27 w28 w29
     w30 w31 w32 w33 w34 w35 w36 w37 w38 w39
     w40 w41 w42 w43 w44 w45 w46 w47 w48 w49
     w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
     w60 w61 w62 w63 w64 w65 w66 w67 w68 w69
     w70 w71 w72 w73 w74 w75 w76 w77 w78 w79
     w80 w81 w82 w83 w84 w85 w86 w87 w88 w89 : BitVec 64) :
    ((ptr ↦₆₄* [w0, w1, w2]) ∗
     ((ptr + 24#64) ↦₆₄ w3) ∗ ((ptr + 32#64) ↦₆₄ w4) ∗
     ((ptr + 40#64) ↦₆₄ w5) ∗ ((ptr + 48#64) ↦₆₄ w6) ∗
     ((ptr + 56#64) ↦₆₄ w7) ∗ ((ptr + 64#64) ↦₆₄ w8) ∗
     ((ptr + 72#64) ↦₆₄ w9) ∗ ((ptr + 80#64) ↦₆₄ w10) ∗
     ((ptr + 88#64) ↦₆₄* [w11, w12, w13, w14]) ∗
     ((ptr + 120#64) ↦₆₄ w15) ∗ ((ptr + 128#64) ↦₆₄ w16) ∗
     ((ptr + 136#64) ↦₆₄ w17) ∗ ((ptr + 144#64) ↦₆₄ w18) ∗
     ((ptr + 152#64) ↦₆₄ w19) ∗ ((ptr + 160#64) ↦₆₄ w20) ∗
     ((ptr + 168#64) ↦₆₄* [w21, w22, w23]) ∗
     ((ptr + 192#64) ↦₆₄ w24) ∗ ((ptr + 200#64) ↦₆₄ w25) ∗
     ((ptr + 208#64) ↦₆₄ w26) ∗ ((ptr + 216#64) ↦₆₄ w27) ∗
     ((ptr + 224#64) ↦₆₄ w28) ∗ ((ptr + 232#64) ↦₆₄ w29) ∗
     ((ptr + 240#64) ↦₆₄* [w30, w31, w32, w33, w34]) ∗
     ((ptr + 280#64) ↦₆₄ w35) ∗ ((ptr + 288#64) ↦₆₄ w36) ∗
     ((ptr + 296#64) ↦₆₄ w37) ∗ ((ptr + 304#64) ↦₆₄ w38) ∗
     ((ptr + 312#64) ↦₆₄ w39) ∗ ((ptr + 320#64) ↦₆₄ w40) ∗
     ((ptr + 328#64) ↦₆₄* [w41, w42, w43, w44]) ∗
     ((ptr + 360#64) ↦₆₄ w45) ∗ ((ptr + 368#64) ↦₆₄ w46) ∗
     ((ptr + 376#64) ↦₆₄ w47) ∗ ((ptr + 384#64) ↦₆₄ w48) ∗
     ((ptr + 392#64) ↦₆₄ w49) ∗ ((ptr + 400#64) ↦₆₄ w50) ∗
     ((ptr + 408#64) ↦₆₄* [w51, w52, w53]) ∗
     ((ptr + 432#64) ↦₆₄ w54) ∗ ((ptr + 440#64) ↦₆₄ w55) ∗
     ((ptr + 448#64) ↦₆₄ w56) ∗ ((ptr + 456#64) ↦₆₄ w57) ∗
     ((ptr + 464#64) ↦₆₄ w58) ∗ ((ptr + 472#64) ↦₆₄ w59) ∗
     ((ptr + 480#64) ↦₆₄* [w60, w61, w62, w63, w64]) ∗
     ((ptr + 520#64) ↦₆₄ w65) ∗ ((ptr + 528#64) ↦₆₄ w66) ∗
     ((ptr + 536#64) ↦₆₄ w67) ∗ ((ptr + 544#64) ↦₆₄ w68) ∗
     ((ptr + 552#64) ↦₆₄ w69) ∗ ((ptr + 560#64) ↦₆₄ w70) ∗
     ((ptr + 568#64) ↦₆₄* [w71, w72, w73, w74]) ∗
     ((ptr + 600#64) ↦₆₄* [w75, w76, w77, w78, w79, w80, w81, w82, w83, w84, w85, w86, w87, w88, w89])) ⊢
    cells ptr 90 := by
  sep_interval

theorem multi_root_split_and_coalesce_eq (sp scratch : BitVec 64) :
    (memRegion (sp - 616#64) 40 ∗ memRegion (sp - 576#64) 24 ∗
     memRegion (sp + 32#64) 64 ∗
     cells (scratch + 16#64) 4) =
    (memRegion (sp - 616#64) 16 ∗ memRegion (sp - 600#64) 48 ∗
     cells (sp + 32#64) 3 ∗ memRegion (sp + 56#64) 40 ∗
     memRegion (scratch + 16#64) 24 ∗ stackAt (scratch + 48#64) 8) := by
  sep_interval_eq

/-! ## 3. `let`-Bound Base Pointers, Local Equalities, Stack Wrappers & Zero-Length Slices -/

theorem let_bound_base_and_local_sp_eq
    (sp s_sp slot : BitVec 64) (v0 v1 v2 v3 v4 : BitVec 64)
    (h_sp : s_sp = sp - 64#64)
    (h_slot : slot = (sp + 16#64) + 16#64) :
    let base := sp + 16#64
    let scratch := base - 632#64
    (((s_sp + 0#64) ↦₆₄ v0) ∗ ((s_sp + 8#64) ↦₆₄ v1) ∗
     (scratch ↦₆₄ v2) ∗ memRegion (scratch + 8#64) 16 ∗
     (base ↦₆₄ v3) ∗ ((base + 8#64) ↦₆₄ v4) ∗ (slot ↦₆₄ v0)) ⊢
    (memRegion (sp - 616#64) 24 ∗
     memRegion (sp - 64#64) 16 ∗
     memRegion (sp + 16#64) 24) := by
  sep_interval

theorem stack_wrappers_coalesce_eq (s : State) :
    (stackFrameAt (s.sp - 112#64) 16 ∗
     stackFrame16At (s.sp - 96#64) ∗
     stackFrame32At (s.sp - 64#64) ∗
     stackAt (s.sp - 40#64) 24 ∗
     cells (s.sp - 40#64) 3 ∗
     stackFrame16 s) =
    stackFrame s 128 := by
  sep_interval_eq

theorem stack_state_frame32_eq (s : State) :
    (memRegion (s.sp - 32#64) 16 ∗ stackFrame16 s) = stackFrame32 s := by
  sep_interval_eq

theorem zero_length_slices_eq
    (p : BitVec 64) (v : BitVec 64) (emptyBs : List (BitVec 8))
    (h_empty : emptyBs.length = 0) :
    (memRegion (p - 32#64) 0 ∗ cells (p + 64#64) 0 ∗
     (p ↦ₛ ([] : List (BitVec 8))) ∗ ((p + 16#64) ↦ₛ emptyBs) ∗
     ((p + 24#64) ↦₆₄* ([] : List (BitVec 64))) ∗
     ((p + 32#64) ↦ᵣ ([] : List (BitVec 8))) ∗
     ((p + 40#64) ↦₆₄ᵣ* ([] : List (BitVec 64))) ∗
     (p ↦₆₄ v)) =
    (p ↦₆₄ v) := by
  sep_interval_eq

theorem opaque_symbolic_framing_rebase
    (p p' : BitVec 64) (dynBuf : List (BitVec 8)) (dynWords : List (BitVec 64))
    (dynLen dynCells : Nat) (v0 v1 : BitVec 64)
    (h_p : p' = p + 32#64) :
    (((p' + 8#64) ↦ₛ dynBuf) ∗
     ((p' + 64#64) ↦₆₄* dynWords) ∗
     memRegion (p' + 128#64) dynLen ∗
     cells (p' + 256#64) dynCells ∗
     (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)) ⊢
    (memRegion p 16 ∗
     ((p + 40#64) ↦ₛ dynBuf) ∗
     ((p + 96#64) ↦₆₄* dynWords) ∗
     memRegion (p + 160#64) dynLen ∗
     cells (p + 288#64) dynCells) := by
  sep_interval

/-! ## 4. Dynamic `BitVec.ofNat 64 b.toNat` and `b.zeroExtend 64` Offset Expressions -/

theorem dynamic_ofNat_toNat_eq_zeroExtend
    (tbl scratch : BitVec 64) (b8 : BitVec 8) (b16 : BitVec 16) (b32 : BitVec 32)
    (x8 : BitVec 8) (x16 : BitVec 16) (x64 : BitVec 64) :
    (((tbl + BitVec.ofNat 64 b8.toNat) ↦₈ᵣ x8) ∗
     ((tbl + 0x100#64 + BitVec.ofNat 64 b16.toNat) ↦₁₆ᵣ x16) ∗
     ((scratch + BitVec.ofNat 64 b32.toNat) ↦₆₄ x64)) =
    (((tbl + b8.zeroExtend 64) ↦₈ᵣ x8) ∗
     ((tbl + b16.zeroExtend 64 + 0x100#64) ↦₁₆ᵣ x16) ∗
     ((scratch + b32.zeroExtend 64) ↦₆₄ x64)) := by
  sep_interval_eq

theorem dynamic_offset_shifted_cells
    (base : BitVec 64) (idx : BitVec 8) (w0 w1 : BitVec 64) :
    let off := idx.toNat
    (((base + BitVec.ofNat 64 off + 16#64) ↦₆₄ w0) ∗
     ((base + idx.zeroExtend 64 + 24#64) ↦₆₄ w1)) ⊢
    cells (base + idx.zeroExtend 64 + 16#64) 2 := by
  sep_interval

/-! ## 5. Unaligned Multi-Cell Carve/Fold, Endian Split/Pack, Bundles & Prenex `∃∗` -/

theorem unaligned_37_cell_carve_eq (buf : BitVec 64) :
    memRegion buf 160 =
    ((∃∗ v : BitVec 32, (buf + 0#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 32, (buf + 4#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 64, (buf + 8#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 8,  (buf + 16#64) ↦₈ v) ∗
     (∃∗ v : BitVec 8,  (buf + 17#64) ↦₈ v) ∗
     (∃∗ v : BitVec 16, (buf + 18#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 32, (buf + 20#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 64, (buf + 24#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 64, (buf + 32#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 16, (buf + 40#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 8,  (buf + 42#64) ↦₈ v) ∗
     memRegion (buf + 43#64) 5 ∗
     (∃∗ v : BitVec 64, (buf + 48#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 32, (buf + 56#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 16, (buf + 60#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 8,  (buf + 62#64) ↦₈ v) ∗
     (∃∗ v : BitVec 8,  (buf + 63#64) ↦₈ v) ∗
     (∃∗ v : BitVec 64, (buf + 64#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 64, (buf + 72#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 32, (buf + 80#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 32, (buf + 84#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 8,  (buf + 88#64) ↦₈ v) ∗
     memRegion (buf + 89#64) 7 ∗
     (∃∗ v : BitVec 64, (buf + 96#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 16, (buf + 104#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 16, (buf + 106#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 32, (buf + 108#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 64, (buf + 112#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 64, (buf + 120#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 8,  (buf + 128#64) ↦₈ v) ∗
     (∃∗ v : BitVec 8,  (buf + 129#64) ↦₈ v) ∗
     (∃∗ v : BitVec 16, (buf + 130#64) ↦₁₆ v) ∗
     (∃∗ v : BitVec 32, (buf + 132#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 64, (buf + 136#64) ↦₆₄ v) ∗
     (∃∗ v : BitVec 32, (buf + 144#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 32, (buf + 148#64) ↦₃₂ v) ∗
     (∃∗ v : BitVec 64, (buf + 152#64) ↦₆₄ v)) := by
  sep_interval_eq

theorem unaligned_37_cell_fold
    (buf : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 h1 h2 h3 h4 h5 : BitVec 16)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 : BitVec 32)
    (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 : BitVec 64) :
    (((buf + 152#64) ↦₆₄ q10) ∗
     ((buf + 8#64) ↦₆₄ q0) ∗
     ((buf + 0#64) ↦₃₂ d0) ∗
     ((buf + 4#64) ↦₃₂ d1) ∗
     ((buf + 18#64) ↦₁₆ h0) ∗
     ((buf + 16#64) ↦₈ b0) ∗
     ((buf + 17#64) ↦₈ b1) ∗
     ((buf + 20#64) ↦₃₂ d2) ∗
     ((buf + 32#64) ↦₆₄ q2) ∗
     ((buf + 24#64) ↦₆₄ q1) ∗
     memRegion (buf + 43#64) 5 ∗
     ((buf + 40#64) ↦₁₆ h1) ∗
     ((buf + 42#64) ↦₈ b2) ∗
     ((buf + 48#64) ↦₆₄ q3) ∗
     ((buf + 62#64) ↦₈ b3) ∗
     ((buf + 63#64) ↦₈ b4) ∗
     ((buf + 56#64) ↦₃₂ d3) ∗
     ((buf + 60#64) ↦₁₆ h2) ∗
     ((buf + 72#64) ↦₆₄ q5) ∗
     ((buf + 64#64) ↦₆₄ q4) ∗
     ((buf + 84#64) ↦₃₂ d5) ∗
     ((buf + 80#64) ↦₃₂ d4) ∗
     memRegion (buf + 89#64) 7 ∗
     ((buf + 88#64) ↦₈ b5) ∗
     ((buf + 96#64) ↦₆₄ q6) ∗
     ((buf + 108#64) ↦₃₂ d6) ∗
     ((buf + 104#64) ↦₁₆ h3) ∗
     ((buf + 106#64) ↦₁₆ h4) ∗
     ((buf + 120#64) ↦₆₄ q8) ∗
     ((buf + 112#64) ↦₆₄ q7) ∗
     ((buf + 132#64) ↦₃₂ d7) ∗
     ((buf + 130#64) ↦₁₆ h5) ∗
     ((buf + 128#64) ↦₈ b6) ∗
     ((buf + 129#64) ↦₈ b7) ∗
     ((buf + 136#64) ↦₆₄ q9) ∗
     ((buf + 148#64) ↦₃₂ d8) ∗
     ((buf + 144#64) ↦₃₂ d0)) ⊢
    memRegion buf 160 := by
  sep_interval

theorem simd_128_shifted_pack_and_split_eq
    (p : BitVec 64) (hdr : BitVec 32) (q0 q1 : BitVec 128) (tail : BitVec 32) :
    ((p ↦₃₂ hdr) ∗
     ((p + 4#64) ↦₆₄ q0.extractLsb' 0 64) ∗
     ((p + 12#64) ↦₆₄ q0.extractLsb' 64 64) ∗
     ((p + 20#64) ↦₁₂₈ q1) ∗
     ((p + 36#64) ↦₃₂ tail)) =
    ((p ↦₃₂ hdr) ∗
     ((p + 4#64) ↦₁₂₈ q0) ∗
     ((p + 20#64) ↦₆₄ q1.extractLsb' 0 64) ∗
     ((p + 28#64) ↦₆₄ q1.extractLsb' 64 64) ∗
     ((p + 36#64) ↦₃₂ tail)) := by
  sep_interval_eq

theorem endian_full_cascade_128_to_8_eq
    (a : BitVec 64) (v : BitVec 128)
    (b0 b1 : BitVec 8) (h1 : BitVec 16) (d1 : BitVec 32) :
    ((a ↦₁₂₈ v) ∗
     ((a + 16#64) ↦₈ b0) ∗
     ((a + 17#64) ↦₈ b1) ∗
     ((a + 18#64) ↦₁₆ h1) ∗
     ((a + 20#64) ↦₃₂ d1)) =
    ((((a + 0#64) ↦₈ (((v.extractLsb' 0 64).extractLsb' 0 32).extractLsb' 0 16).extractLsb' 0 8) ∗
      ((a + 1#64) ↦₈ (((v.extractLsb' 0 64).extractLsb' 0 32).extractLsb' 0 16).extractLsb' 8 8) ∗
      ((a + 2#64) ↦₁₆ ((v.extractLsb' 0 64).extractLsb' 0 32).extractLsb' 16 16) ∗
      ((a + 4#64) ↦₃₂ (v.extractLsb' 0 64).extractLsb' 32 32) ∗
      ((a + 8#64) ↦₆₄ v.extractLsb' 64 64)) ∗
     ((a + 16#64) ↦₆₄ (d1 ++ (h1 ++ (b1 ++ b0))))) := by
  sep_interval_eq

def AlphaSlot (p : BitVec 64) (v : BitVec 64) : SepProp :=
  (p ↦₃₂ v.extractLsb' 0 32) ∗ ((p + 4#64) ↦₃₂ v.extractLsb' 32 32)

def AlphaPair (p : BitVec 64) (v0 v1 : BitVec 64) : SepProp :=
  AlphaSlot p v0 ∗ AlphaSlot (p + 8#64) v1

theorem nested_bundle_pack_eq (p : BitVec 64) (v0 v1 : BitVec 64) :
    AlphaPair p v0 v1 = ((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)) := by
  sep_interval_eq

theorem exists_nested_bundle_coalesce (p : BitVec 64) :
    (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, AlphaPair p v0 v1) ⊢ memRegion p 16 := by
  sep_interval

theorem prenex_push_eq (p : BitVec 64) (R : SepProp) :
    ((∃∗ v : BitVec 64, (p ↦₆₄ v)) ∗ R) =
    (∃∗ u : BitVec 64, R ∗ (p ↦₆₄ u)) := by
  sep_interval_eq

theorem lhs_exists_pure_len_carve (p : BitVec 64) :
    (∃∗ bs : List (BitVec 8), (p ↦ₛ bs) ∗ ⌜bs.length = 24⌝) ⊢
    (cells p 2 ∗ memRegion (p + 16#64) 8) := by
  sep_interval

theorem rhs_exists_witness_dependent (p : BitVec 64) (k : BitVec 64) :
    ((p ↦₆₄ k) ∗ ((p + 8#64) ↦₆₄ (k + 1#64))) ⊢
    (∃∗ v : BitVec 64, (p ↦₆₄ v) ∗ ((p + 8#64) ↦₆₄ (v + 1#64))) := by
  sep_interval

theorem rhs_exists_bytes_witness (p : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (w : BitVec 64) :
    ((p ↦ₛ [b0, b1, b2, b3]) ∗ ((p + 4#64) ↦₆₄ w)) ⊢
    (∃∗ bs : List (BitVec 8), (p ↦ₛ bs) ∗ memRegion (p + 4#64) 8) := by
  sep_interval

/-! ## 6. `.rodata` (`pointsToBytesRO` / `pointsTo*RO`) Subslice Carving, Duplication & Absorption -/

def RoTable18 (tbl : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (d0 : BitVec 32) : SepProp :=
  ((tbl + 0x00#64) ↦₆₄ᵣ c0) ∗ ((tbl + 0x08#64) ↦₆₄ᵣ c1) ∗
  ((tbl + 0x10#64) ↦₆₄ᵣ c2) ∗ ((tbl + 0x18#64) ↦₆₄ᵣ c3) ∗
  ((tbl + 0x20#64) ↦₆₄ᵣ c4) ∗ ((tbl + 0x28#64) ↦₆₄ᵣ c5) ∗
  ((tbl + 0x30#64) ↦₆₄ᵣ c6) ∗ ((tbl + 0x38#64) ↦₆₄ᵣ c7) ∗
  ((tbl + 0x40#64) ↦₆₄ᵣ c8) ∗ ((tbl + 0x48#64) ↦₆₄ᵣ c9) ∗
  ((tbl + 0x50#64) ↦₆₄ᵣ c10) ∗ ((tbl + 0x58#64) ↦₆₄ᵣ c11) ∗
  ((tbl + 0x60#64) ↦₆₄ᵣ c12) ∗ ((tbl + 0x68#64) ↦₆₄ᵣ c13) ∗
  ((tbl + 0x70#64) ↦₆₄ᵣ c14) ∗ ((tbl + 0x78#64) ↦₆₄ᵣ c15) ∗
  ((tbl + 0x80#64) ↦ᵣ [b0, b1, b2, b3, b4, b5, b6, b7]) ∗
  ((tbl + 0x88#64) ↦₃₂ᵣ d0)

theorem ro_table_absorb_duplicates_eq
    (tbl : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (d0 : BitVec 32) (R : SepProp) :
    (((tbl + 0x78#64) ↦₆₄ᵣ c15) ∗
     ((tbl + 0x18#64) ↦₆₄ᵣ c3) ∗
     ((tbl + 0x00#64) ↦₆₄ᵣ c0) ∗
     ((tbl + 0x82#64) ↦ᵣ [b2, b3, b4]) ∗
     ((tbl + 0x88#64) ↦₃₂ᵣ d0) ∗
     ((tbl + 0x40#64) ↦₆₄ᵣ c8) ∗
     ((tbl + 0x18#64) ↦₆₄ᵣ c3) ∗
     ((tbl + 0x58#64) ↦₆₄ᵣ c11) ∗
     ((tbl + 0x20#64) ↦₆₄ᵣ c4) ∗
     ((tbl + 0x70#64) ↦₆₄ᵣ c14) ∗
     ((tbl + 0x08#64) ↦₆₄ᵣ c1) ∗
     ((tbl + 0x60#64) ↦₆₄ᵣ c12) ∗
     ((tbl + 0x30#64) ↦₆₄ᵣ c6) ∗
     ((tbl + 0x84#64) ↦ᵣ [b4, b5, b6, b7]) ∗
     ((tbl + 0x48#64) ↦₆₄ᵣ c9) ∗
     RoTable18 tbl c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
       b0 b1 b2 b3 b4 b5 b6 b7 d0 ∗ R) =
    (RoTable18 tbl c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
       b0 b1 b2 b3 b4 b5 b6 b7 d0 ∗ R) := by
  sep_interval_eq

theorem ro_bytes_subslice_carve_and_dup (tbl : BitVec 64) :
    (tbl ↦ᵣ [0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8, 0x06#8, 0x07#8, 0x08#8]) ⊢
    ((tbl ↦ᵣ [0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8, 0x06#8, 0x07#8, 0x08#8]) ∗
     ((tbl + 1#64) ↦ᵣ [0x02#8, 0x03#8, 0x04#8]) ∗
     ((tbl + 3#64) ↦ᵣ [0x04#8, 0x05#8, 0x06#8, 0x07#8])) := by
  sep_interval

theorem ro_symbolic_buf_subslice_eq
    (tbl : BitVec 64) (buf : List (BitVec 8)) (ws : List (BitVec 64))
    (h_len : buf.length = 32)
    (_h_sub_len : ((buf.drop 4).take 8).length = 8) :
    (((tbl + 4#64) ↦ᵣ (buf.drop 4).take 8) ∗ (tbl ↦ᵣ buf) ∗
     ((tbl + 64#64) ↦₆₄ᵣ* ws) ∗ ((tbl + 64#64) ↦₆₄ᵣ* ws)) =
    ((tbl ↦ᵣ buf) ∗ ((tbl + 64#64) ↦₆₄ᵣ* ws)) := by
  sep_interval_eq

theorem ro_typed_cells_from_bytes_and_quadword
    (tbl : BitVec 64) (q : BitVec 128) :
    (((tbl + 1#64) ↦₈ᵣ 0x22#8) ∗
     ((tbl + 2#64) ↦₁₆ᵣ 0x4433#16) ∗
     ((tbl + 4#64) ↦₃₂ᵣ 0x88776655#32) ∗
     (tbl ↦ᵣ [0x11#8, 0x22#8, 0x33#8, 0x44#8, 0x55#8, 0x66#8, 0x77#8, 0x88#8]) ∗
     ((tbl + 16#64) ↦₆₄ᵣ q.extractLsb' 0 64) ∗
     ((tbl + 24#64) ↦₆₄ᵣ q.extractLsb' 64 64) ∗
     ((tbl + 16#64) ↦₁₂₈ᵣ q)) =
    ((tbl ↦ᵣ [0x11#8, 0x22#8, 0x33#8, 0x44#8, 0x55#8, 0x66#8, 0x77#8, 0x88#8]) ∗
     ((tbl + 16#64) ↦₁₂₈ᵣ q)) := by
  sep_interval_eq

/-! ## 7. Negative `#guard_msgs` and `fail_if_success` Soundness Regression Tests -/

/-- error: sep_interval: gap in LHS covering [0, 16) at offset 8 -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 64) :
    (p ↦₆₄ v) ⊢ memRegion p 16 := by
  sep_interval

/-- error: sep_interval: gap in LHS covering [-64, 0) at offset -8 -/
#guard_msgs (error, substring := true) in
example (sp : BitVec 64) :
    memRegion (sp - 64#64) 56 ⊢ stackFrameAt sp 64 := by
  sep_interval

/-- error: sep_interval: `.ro` bucket count mismatch -/
#guard_msgs (error, substring := true) in
example (tbl : BitVec 64) :
    (tbl ↦ᵣ [1#8, 2#8, 3#8, 4#8]) ⊢
    ((tbl ↦ᵣ [1#8, 2#8, 3#8, 4#8]) ∗ ((tbl + 4#64) ↦ᵣ [3#8, 4#8])) := by
  sep_interval

/-- error: sep_interval: overlapping LHS intervals -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v0 v1 : BitVec 64) :
    ((p ↦₆₄ v0) ∗ ((p + 4#64) ↦₆₄ v1)) ⊢ memRegion p 12 := by
  sep_interval

/-- error: sep_interval: overlapping RHS intervals -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) :
    memRegion p 16 ⊢ (memRegion p 8 ∗ memRegion (p + 4#64) 8) := by
  sep_interval

/-- error: sep_interval: gap in LHS covering [0, 8) at offset 4 -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 32) :
    (p ↦₃₂ v) ⊢ memRegion p 8 := by
  sep_interval

/-- error: sep_interval_eq: cannot weaken concrete typed cells -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 64) :
    (p ↦₆₄ v) = memRegion p 8 := by
  sep_interval_eq

/-- error: sep_interval: cannot strengthen uninitialized memory -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 64) :
    memRegion p 8 ⊢ (p ↦₆₄ v) := by
  sep_interval

/-- error: sep_interval: `.ro` bucket count mismatch -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 64) :
    (p ↦₆₄ᵣ v) ⊢ (p ↦₆₄ v) := by
  sep_interval

/-- error: sep_interval: unmatched RHS interval -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) (v : BitVec 64) :
    (p ↦₆₄ᵣ v) ⊢ ((p ↦₆₄ᵣ v) ∗ memRegion p 8) := by
  sep_interval

/-- error: sep_interval: unmatched RHS interval -/
#guard_msgs (error, substring := true) in
example (p : BitVec 64) :
    (p ↦ᵣ [1#8, 2#8, 3#8, 4#8]) ⊢
    ((p ↦ᵣ [1#8, 2#8, 3#8, 4#8]) ∗ (p ↦ₛ [1#8, 2#8, 3#8, 4#8])) := by
  sep_interval

theorem negative_fail_if_success_suite
    (p tbl : BitVec 64) (v0 v1 : BitVec 64) (v32 : BitVec 32) :
    (((p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₃₂ v32) ∗ (tbl ↦ᵣ [1#8, 2#8])) ⊢
     (memRegion p 20 ∗ (tbl ↦ᵣ [1#8, 2#8]))) := by
  -- Out-of-bounds RW carve
  fail_if_success (have : (p ↦₆₄ v0) ⊢ memRegion p 16 := by sep_interval)
  -- Out-of-bounds RO carve
  fail_if_success (have : (tbl ↦ᵣ [1#8, 2#8]) ⊢ ((tbl ↦ᵣ [1#8, 2#8]) ∗ ((tbl + 1#64) ↦ᵣ [2#8, 3#8])) := by sep_interval)
  -- Overlapping RW writes
  fail_if_success (have : ((p ↦₆₄ v0) ∗ ((p + 4#64) ↦₆₄ v1)) ⊢ memRegion p 12 := by sep_interval)
  -- Width mismatch (32-bit vs 64-bit)
  fail_if_success (have : (p ↦₃₂ v32) = (p ↦₆₄ v0) := by sep_interval_eq)
  -- Equality mode rejects irreversible weakening
  fail_if_success (have : (p ↦₆₄ v0) = memRegion p 8 := by sep_interval_eq)
  -- RW-from-RO promotion rejected for typed cells, byte slices, and uninitialized regions
  fail_if_success (have : (p ↦₆₄ᵣ v0) ⊢ (p ↦₆₄ v0) := by sep_interval)
  fail_if_success (have : (p ↦₆₄ᵣ v0) ⊢ memRegion p 8 := by sep_interval)
  fail_if_success (have : (tbl ↦ᵣ [1#8, 2#8]) ⊢ (tbl ↦ₛ [1#8, 2#8]) := by sep_interval)
  fail_if_success (have : (tbl ↦ᵣ [1#8, 2#8]) ⊢ memRegion tbl 2 := by sep_interval)
  sep_interval

/-- Nested prenex existential peeling on both right-associated and left-associated `∗`-trees inside
exposed bundles (`∃∗ w, A ∗ (B ∗ C w)` and `∃∗ w, ((A w ∗ B) ∗ C)`), exercising recursive
`peelOne` in `pushPrenexSepExists` across `sep_interval` and `sep_interval_eq`. -/
def RightNestedCellBundle (p a b : BitVec 64) : SepProp :=
  ∃∗ w : BitVec 64, (p ↦₆₄ a) ∗ (((p + 8#64) ↦₆₄ b) ∗ ((p + 16#64) ↦₆₄ w))

def LeftNestedCellBundle (p b c : BitVec 64) : SepProp :=
  ∃∗ w : BitVec 64, (((p ↦₆₄ w) ∗ ((p + 8#64) ↦₆₄ b)) ∗ ((p + 16#64) ↦₆₄ c))

theorem prenex_peel_right_nested_eq (p a b : BitVec 64) :
    ((p ↦₆₄ a) ∗ ((p + 8#64) ↦₆₄ b) ∗ memRegion (p + 16#64) 8) =
    RightNestedCellBundle p a b := by
  sep_interval_eq

theorem prenex_peel_left_nested_eq (p b c : BitVec 64) :
    (memRegion p 8 ∗ ((p + 8#64) ↦₆₄ b) ∗ ((p + 16#64) ↦₆₄ c)) =
    LeftNestedCellBundle p b c := by
  sep_interval_eq

theorem prenex_peel_right_nested_coalesce (p a b : BitVec 64) :
    RightNestedCellBundle p a b ⊢ memRegion p 24 := by
  sep_interval

/-! ## 8. Axiom Footprint Checks -/

/-- info: 'Testing.SepInterval.prenex_peel_right_nested_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prenex_peel_right_nested_eq

/-- info: 'Testing.SepInterval.unqualified_rw_coalesce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unqualified_rw_coalesce

/-- info: 'Testing.SepInterval.widget_frame_carve_coalesce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms widget_frame_carve_coalesce

/-- info: 'Testing.SepInterval.packet_slots_coalesce_90_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms packet_slots_coalesce_90_words

/-- info: 'Testing.SepInterval.let_bound_base_and_local_sp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms let_bound_base_and_local_sp_eq

/-- info: 'Testing.SepInterval.dynamic_offset_shifted_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dynamic_offset_shifted_cells

/-- info: 'Testing.SepInterval.unaligned_37_cell_carve_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unaligned_37_cell_carve_eq

/-- info: 'Testing.SepInterval.simd_128_shifted_pack_and_split_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms simd_128_shifted_pack_and_split_eq

/-- info: 'Testing.SepInterval.ro_table_absorb_duplicates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ro_table_absorb_duplicates_eq

/-- info: 'Testing.SepInterval.ro_typed_cells_from_bytes_and_quadword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ro_typed_cells_from_bytes_and_quadword

end Testing.SepInterval
