/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# Separation-Logic & Stack-Frame Automation Regression Suite

Positive and negative (`#guard_msgs`) regression tests for:
1. Transparent spatial-bundle unfolding (`@[expose] def`, `@[sep_unfold]`, `abbrev`) vs. non-exposed
   opaque `def` and recursive `def`, plus folded-frame preservation in `sep_frame`.
2. `let`-transparent 64-bit address normalization (`let sp := s0.sp - 848#64; sp + 616#64 = s0.sp - 232#64`)
   and leading `let`-telescope handling in `sep_eq`, `sep_entail`, `sep_focus`, `sep_frame`, and `wp_reframe`.
3. Contiguous `memRegion` coalescing across scattered `↦₈`..`↦₁₂₈`, `↦ₛ` (concrete and symbolic
   length), and carved `memRegion` slices, existential witness synthesis, `Judg.eq` weakening rejection,
   and 160-atom iterative `∗`-tree stack safety.
4. `wp_steps` auto-carving over `memRegion`, `stackFrameAt`, `↦₁₂₈`, and `@[expose] def` bundles,
   covering GPR and 8/16/32/64/128-bit SIMD scalar + 32/64/128-bit SIMD pair loads/stores.
5. `wp_reframe` and `stack_frame` on `SepWP` and `SepWPp` goals.
-/

namespace Testing.SepStackAutomation

open Arm64 ProofLib

public section

/-- Non-exposed `def` spatial bundle: stays opaque unless tagged `@[sep_unfold]` or `@[expose]`. -/
def opaqueSlotPair (p : BitVec 64) (v0 v1 : BitVec 64) : SepProp :=
  (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)

/-- Non-exposed `def` explicitly opted in via `@[sep_unfold]`. -/
@[sep_unfold]
def taggedSlotPair (p : BitVec 64) (v0 v1 : BitVec 64) : SepProp :=
  (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)

end

@[expose] public section

/-- Helper for inspecting inferred frames with `sep_frame?`. -/
theorem frame_exists_of {m : Memory} {Q F : SepProp} (h : m ⊨ Q ∗ F) : ∃ F', m ⊨ Q ∗ F' :=
  ⟨F, h⟩

/-- 15-word (120-byte) stack-slot bundle `[sp + 496 .. sp + 616)` defined as an `@[expose] def`. -/
def slotWindow15 (sp : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) : SepProp :=
  ((sp + 496#64) ↦₆₄ w0) ∗ ((sp + 504#64) ↦₆₄ w1) ∗ ((sp + 512#64) ↦₆₄ w2) ∗
  ((sp + 520#64) ↦₆₄ w3) ∗ ((sp + 528#64) ↦₆₄ w4) ∗ ((sp + 536#64) ↦₆₄ w5) ∗
  ((sp + 544#64) ↦₆₄ w6) ∗ ((sp + 552#64) ↦₆₄ w7) ∗ ((sp + 560#64) ↦₆₄ w8) ∗
  ((sp + 568#64) ↦₆₄ w9) ∗ ((sp + 576#64) ↦₆₄ w10) ∗ ((sp + 584#64) ↦₆₄ w11) ∗
  ((sp + 592#64) ↦₆₄ w12) ∗ ((sp + 600#64) ↦₆₄ w13) ∗ ((sp + 608#64) ↦₆₄ w14)

/-- Single-atom `@[expose] def` wrapper: unfolded when matched against a raw cell, kept folded in `?F`. -/
def singleExposedSlot (sp v : BitVec 64) : SepProp :=
  (sp + 616#64) ↦₆₄ v

/-- Two-slot `@[expose] def` header bundle. -/
def headerSlots (sp h0 h1 : BitVec 64) : SepProp :=
  ((sp + 16#64) ↦₆₄ h0) ∗ ((sp + 24#64) ↦₆₄ h1)

/-- Abbreviation two-slot bundle. -/
abbrev abbrevSlotPair (p v0 v1 : BitVec 64) : SepProp :=
  (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1)

/-- Recursive `@[expose] def` over a symbolic count: bounded fuel prevents non-termination. -/
def recSlotChain : Nat → BitVec 64 → SepProp
  | 0, _ => emp
  | n + 1, p => (p ↦₆₄ 0#64) ∗ recSlotChain n (p + 8#64)

/-! ## 1. Transparent Bundle Unfolding & `let`-Bound Frame-Pointer Offsets -/

section BundlesAndLetAddrs

variable (m : Memory) (s0 : State)
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 h0 h1 : BitVec 64)

-- `sep_eq` unfolds `@[expose] def slotWindow15` and `singleExposedSlot` across `let sp := s0.sp - 848#64`
-- (`sp + 616#64 = s0.sp - 232#64` and `sp + 608#64 = s0.sp - 240#64`).
example :
    let sp : BitVec 64 := s0.sp - 848#64
    slotWindow15 sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗ singleExposedSlot sp w15 =
      ((s0.sp - 232#64) ↦₆₄ w15) ∗ ((s0.sp - 240#64) ↦₆₄ w14) ∗
      ((sp + 496#64) ↦₆₄ w0) ∗ ((sp + 504#64) ↦₆₄ w1) ∗ ((sp + 512#64) ↦₆₄ w2) ∗
      ((sp + 520#64) ↦₆₄ w3) ∗ ((sp + 528#64) ↦₆₄ w4) ∗ ((sp + 536#64) ↦₆₄ w5) ∗
      ((sp + 544#64) ↦₆₄ w6) ∗ ((sp + 552#64) ↦₆₄ w7) ∗ ((sp + 560#64) ↦₆₄ w8) ∗
      ((sp + 568#64) ↦₆₄ w9) ∗ ((sp + 576#64) ↦₆₄ w10) ∗ ((sp + 584#64) ↦₆₄ w11) ∗
      ((sp + 592#64) ↦₆₄ w12) ∗ ((sp + 600#64) ↦₆₄ w13) := by
  sep_eq

-- `sep_entail` across leading `let`-telescopes and `@[expose] def` + `@[sep_unfold]` + `abbrev`.
example :
    let sp : BitVec 64 := s0.sp - 848#64
    let hiPair : BitVec 64 := sp + 616#64
    slotWindow15 sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 ∗
      taggedSlotPair hiPair w15 h0 ∗ abbrevSlotPair (sp + 632#64) h1 w0 ⊢
      ((s0.sp - 232#64) ↦₆₄ w15) ∗ ((s0.sp - 224#64) ↦₆₄ h0) ∗
      ((s0.sp - 216#64) ↦₆₄ h1) ∗ ((s0.sp - 208#64) ↦₆₄ w0) ∗
      slotWindow15 (s0.sp - 848#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 := by
  sep_entail

-- `sep_focus` focuses a raw `s0.sp - 240#64` slot out of `slotWindow15 sp` under a leading `let`.
example :
    ∃ F : SepProp,
      let sp : BitVec 64 := s0.sp - 848#64
      slotWindow15 sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 =
        ((s0.sp - 240#64) ↦₆₄ w14) ∗ F :=
  ⟨_, by sep_focus⟩

-- `sep_frame` keeps untouched `@[expose] def` multi-atom and single-atom bundles folded in `?F`
-- even on the same stack pointer `sp` when their byte intervals do not overlap the target cells.
/-- info: sep_frame: frame := headerSlots sp h0 h1 ∗ singleExposedSlot sp w15 -/
#guard_msgs in
example (sp : BitVec 64)
    (h : m ⊨ headerSlots sp h0 h1 ∗ taggedSlotPair (sp + 64#64) w0 w1 ∗ singleExposedSlot sp w15) :
    ∃ F, m ⊨ (((sp + 72#64) ↦₆₄ w1) ∗ ((sp + 64#64) ↦₆₄ w0)) ∗ F :=
  frame_exists_of (by sep_frame?)

-- Single-atom `@[expose] def` still unfolds when matched against a raw cell.
example (sp : BitVec 64) (h : m ⊨ singleExposedSlot sp w15 ∗ headerSlots sp h0 h1) :
    m ⊨ ((sp + 616#64) ↦₆₄ w15) ∗ headerSlots sp h0 h1 := by
  sep_frame

-- Negative: non-exposed `def opaqueSlotPair` is NOT unfolded and suggests `@[sep_unfold]`.
/--
error: sep_frame: no hypothesis atom matches goal atom
  p ↦₆₄ w0
unmatched hypothesis atoms: opaqueSlotPair p w0 w1
hint: context atom `opaqueSlotPair p w0
  w1` uses composite definition `Testing.SepStackAutomation.opaqueSlotPair` while target atom `p ↦₆₄
  w0` is a raw spatial atom; mark `Testing.SepStackAutomation.opaqueSlotPair` with `@[sep_unfold]` (or `@[expose]` / `abbrev`), or unfold/fold `Testing.SepStackAutomation.opaqueSlotPair` so both sides are at the same abstraction level
-/
#guard_msgs in
example (p : BitVec 64) (h : m ⊨ opaqueSlotPair p w0 w1) : m ⊨ (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) := by
  sep_frame

-- Negative: recursive `def recSlotChain` over symbolic `n` terminates cleanly without diverging.
example (n : Nat) (p : BitVec 64) (hfalse : False) (_h : m ⊨ recSlotChain (n + 1) p) :
    m ⊨ (p ↦₆₄ 1#64) := by
  fail_if_success sep_frame
  fail_if_success sep_entail
  exact hfalse.elim

end BundlesAndLetAddrs

/-! ## 2. Contiguous `memRegion` Coalescing & Deep `∗`-Tree Stack Safety -/

section CoalescingAndDeepTrees

-- Coalesce a 15-word `@[expose] def` bundle directly into `memRegion (sp + 496#64) 120` across `let sp`.
example (m : Memory) (s0 : State)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 h0 h1 : BitVec 64) :
    let sp : BitVec 64 := s0.sp - 848#64
    m ⊨ headerSlots sp h0 h1 ∗ slotWindow15 sp w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 →
    m ⊨ memRegion (s0.sp - 352#64) 120 ∗ headerSlots (s0.sp - 848#64) h0 h1 := by
  intro sp h
  sep_frame

-- Coalesce heterogeneous widths (`↦₈`, `↦₁₆`, `↦₃₂`, `↦₆₄`, `↦₁₂₈`, concrete `↦ₛ`, symbolic-length
-- `↦ₛ`, and a carved `memRegion` prefix) into one 64-byte `memRegion` while synthesizing `∃∗` witnesses!
example (m : Memory) (p : BitVec 64)
    (b0 b1 b2 b3 b4 b5 : BitVec 8) (v16 : BitVec 16) (v32 : BitVec 32)
    (v64 : BitVec 64) (v128 : BitVec 128) (bs : List (BitVec 8)) (hbs : bs.length = 16)
    (h : m ⊨ ((p + 16#64) ↦₁₂₈ v128) ∗
             (p ↦₈ b0) ∗ ((p + 1#64) ↦₈ b1) ∗ ((p + 2#64) ↦₁₆ v16) ∗
             ((p + 4#64) ↦ₛ [b2, b3, b4, b5]) ∗
             ((p + 8#64) ↦₆₄ v64) ∗
             ((p + 32#64) ↦ₛ bs) ∗
             memRegion (p + 48#64) 24 ∗
             ((p + 80#64) ↦₃₂ v32)) :
    m ⊨ memRegion p 64 ∗ memRegion (p + 64#64) 8 ∗ (∃∗ u : BitVec 32, (p + 80#64) ↦₃₂ u) := by
  sep_frame

-- Negative: `Judg.eq` (`P = Q`) MUST reject value-forgetting weakening `(a ↦₆₄ v) = memRegion a 8`.
/--
error: sep_frame: no hypothesis atom matches goal atom
  memRegion a 8
unmatched hypothesis atoms: a ↦₆₄ v
-/
#guard_msgs in
example (a v : BitVec 64) : (a ↦₆₄ v) = memRegion a 8 := by
  sep_frame

-- Build 160-atom left-nested and right-nested `∗`-trees to verify $O(1)$ stack depth (zero `maxRecDepth`).
private def chainRight (base : BitVec 64) : Nat → SepProp
  | 0 => base ↦₆₄ 0#64
  | n + 1 => ((base + BitVec.ofNat 64 (8 * (n + 1))) ↦₆₄ BitVec.ofNat 64 (n + 1)) ∗ chainRight base n

private def chainLeft (base : BitVec 64) : Nat → SepProp
  | 0 => base ↦₆₄ 0#64
  | n + 1 => chainLeft base n ∗ ((base + BitVec.ofNat 64 (8 * (n + 1))) ↦₆₄ BitVec.ofNat 64 (n + 1))

set_option maxRecDepth 512 in
example (p : BitVec 64) :
    chainLeft p 159 = chainRight p 159 := by
  dsimp only [chainLeft, chainRight]
  sep_eq

set_option maxRecDepth 512 in
example (m : Memory) (p : BitVec 64) (h : m ⊨ chainLeft p 159) :
    m ⊨ chainRight p 159 := by
  dsimp only [chainLeft, chainRight] at h ⊢
  sep_frame

end CoalescingAndDeepTrees

/-! ## 3. `wp_steps` Auto-Carving & Full SIMD Scalar/Pair Coverage + `wp_reframe` -/

section WpStepsCarveAndReframe

-- `wp_steps` carves cells on demand out of `memRegion (sp + 496#64) 120` across GPR `stur` (`x29`-relative),
-- 128-bit SIMD scalar (`ldr/str q2`), 256-bit SIMD pair (`ldp/stp q0, q1`), 64-bit SIMD scalar (`ldr/str d7`),
-- 16-bit SIMD scalar (`ldr/str h3`), 8-bit SIMD scalar (`ldr/str b4`), and 32-bit SIMD pair (`ldp/stp s5, s6`),
-- and `wp_reframe` coalesces the entire fragmented 120-byte scratch window back into `memRegion (sp + 496#64) 120`!
set_option maxHeartbeats 400000 in
theorem wp_steps_simd_and_reframe (prog : Program) (s0 : State) (sp0 h0 h1 : BitVec 64)
    (h_code : prog.hasWords 0x40000#64
      [ 0xf81103a8#32 -- 0x40000: stur x8, [x29, #-240]   (sp + 608, 8B)
      , 0x3dc083e2#32 -- 0x40004: ldr  q2, [sp, #512]     (sp + 512, 16B)
      , 0x3d8087e2#32 -- 0x40008: str  q2, [sp, #528]     (sp + 528, 16B)
      , 0xad5107e0#32 -- 0x4000c: ldp  q0, q1, [sp, #544] (sp + 544, 32B)
      , 0xad1207e0#32 -- 0x40010: stp  q0, q1, [sp, #576] (sp + 576, 32B)
      , 0xfd40ffe7#32 -- 0x40014: ldr  d7, [sp, #504]     (sp + 504, 8B)
      , 0xfd00ffe7#32 -- 0x40018: str  d7, [sp, #504]     (sp + 504, 8B)
      , 0x7d43e3e3#32 -- 0x4001c: ldr  h3, [sp, #496]     (sp + 496, 2B)
      , 0x7d03e7e3#32 -- 0x40020: str  h3, [sp, #498]     (sp + 498, 2B)
      , 0x3d47d3e4#32 -- 0x40024: ldr  b4, [sp, #500]     (sp + 500, 1B)
      , 0x3d07d7e4#32 -- 0x40028: str  b4, [sp, #501]     (sp + 501, 1B)
      , 0x2d611ba5#32 -- 0x4002c: ldp  s5, s6, [x29, #-248] (sp + 600, 8B)
      , 0x2d221ba5#32 -- 0x40030: stp  s5, s6, [x29, #-240] (sp + 608, 8B)
      ])
    (hpc : s0.pc = 0x40000#64)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hsp : s0.sp = sp0 - 848#64)
    (hfp : s0.readReg64 .x29 = sp0) :
    let sp : BitVec 64 := sp0 - 848#64
    SepWP prog 0x40034#64 s0
      (headerSlots sp h0 h1 ∗ memRegion (sp + 496#64) 120)
      (fun sf Pf => sf.pc = 0x40034#64 ∧
        (Pf ⊢ memRegion (sp + 496#64) 120 ∗ headerSlots sp h0 h1)) := by
  intro sp
  wp_step -- carves 8B at `sp0 - 240` (`sp + 608`) for GPR `stur x8, [x29, #-240]`
  wp_steps -- auto-carves all 12 SIMD scalar/pair loads/stores (`q`/`d`/`s`/`h`/`b`) with default options!
  wp_reframe [memRegion (sp + 496#64) 120, headerSlots sp h0 h1]
  refine SepWP.done rfl (by simp [wp_norm, arm64_norm, hrun]) ⟨rfl, Entails.refl _⟩

-- `wp_steps` (with `proofLib.wpAutoFocusInSteps`) auto-splits `↦₁₂₈` and `@[expose] def` spatial
-- bundles on demand for GPR loads while keeping sibling `@[expose] def` bundles folded, then `stack_frame` refolds!
set_option maxHeartbeats 200000 in
set_option proofLib.wpAutoFocusInSteps true in
example (prog : Program) (s0 : State) (p sp : BitVec 64) (v128 : BitVec 128) (h0 h1 u0 u1 : BitVec 64)
    (h_code : prog.hasWords 0x50000#64
      [ 0xf9400020#32 -- 0x50000: ldr x0, [x1]      (carves lo 64b of p ↦₁₂₈ v128)
      , 0xb9400822#32 -- 0x50004: ldr w2, [x1, #8]  (carves lo 32b of hi 64b of p ↦₁₂₈ v128)
      , 0xf9400883#32 -- 0x50008: ldr x3, [x4, #16] (unfolds headerSlots sp h0 h1)
      ])
    (hpc : s0.pc = 0x50000#64)
    (hrun : s0.status = .Running)
    (hx1 : s0.readReg64 .x1 = p)
    (hx4 : s0.readReg64 .x4 = sp) :
    SepWP prog 0x5000c#64 s0
      ((p ↦₁₂₈ v128) ∗ headerSlots sp h0 h1 ∗ headerSlots (sp + 64#64) u0 u1)
      (fun sf Pf => sf.readReg64 .x0 = v128.extractLsb' 0 64 ∧
        sf.readReg64 .x3 = h0 ∧
        (Pf ⊢ memRegion p 16 ∗ headerSlots sp h0 h1 ∗ headerSlots (sp + 64#64) u0 u1)) := by
  wp_steps
  stack_frame [memRegion p 16, headerSlots sp h0 h1]
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ⟨?_, ?_, ?_⟩
  · simp [wp_norm, arm64_norm]
  · simp [wp_norm, arm64_norm]
  · sep_entail

-- `wp_reframe` (no args), `wp_reframe [focus]`, and `wp_reframe Q` on both `SepWP` and `SepWPp`.
example (prog : Program) (target : BitVec 64) (s : State) (sp v0 v1 v2 : BitVec 64)
    (Q Qp : State → SepProp → Prop)
    (h : SepWPp prog target s (headerSlots sp v0 v1 ∗ ((sp + 64#64) ↦₆₄ v2)) Q Qp) :
    let fp : BitVec 64 := sp + 848#64
    SepWPp prog target s
      (((fp - 784#64) ↦₆₄ v2) ∗ emp ∗ ((sp + 24#64) ↦₆₄ v1) ∗ ((sp + 16#64) ↦₆₄ v0)) Q Qp := by
  wp_reframe
  wp_reframe [headerSlots sp _ _]
  exact h

example (prog : Program) (target : BitVec 64) (s : State) (sp v0 v1 : BitVec 64)
    (post : State → SepProp → Prop)
    (h : SepWP prog target s (memRegion (sp + 16#64) 16) post) :
    SepWP prog target s (headerSlots sp v0 v1) post := by
  wp_reframe (memRegion (sp + 16#64) 16)
  exact h

-- Negative `#guard_msgs` for `wp_reframe` on non-WP goal and missing spatial atom.
/--
error: wp_reframe: expected a `SepWP` or `SepWPp` goal, got:
  True
-/
#guard_msgs in
example : True := by
  wp_reframe

/--
error: wp_reframe: failed to derive focused spatial prefix
  b ↦₆₄ y
from precondition:
  a ↦₆₄ x
(sep_frame: no hypothesis atom matches goal atom
  b ↦₆₄ y
unmatched hypothesis atoms: a ↦₆₄ x)
-/
#guard_msgs in
example (prog : Program) (target : BitVec 64) (s : State) (a b x y : BitVec 64)
    (post : State → SepProp → Prop) :
    SepWP prog target s (a ↦₆₄ x) post := by
  wp_reframe [b ↦₆₄ y]

-- Regression checks for width-exact `BitVec 64` guards, non-constant `let` preservation in `?F`,
-- disjoint `abbrev` preservation, and post-MVar-instantiation offset folding `(?sp - c2)` -> `s0.sp - (c1 + c2)`.
section EdgeCaseRegressions

/-- Non-64-bit `BitVec` `let` bindings (`BitVec 32`, `BitVec 128`) are ignored by 64-bit address/bundle passes. -/
def slotWithWidths (sp : BitVec 64) (tag32 : BitVec 32) (vec128 : BitVec 128) : SepProp :=
  ((sp + 16#64) ↦₃₂ tag32) ∗ ((sp + 32#64) ↦₁₂₈ vec128)

example (s0 : State) (w32 : BitVec 32) (w128 : BitVec 128) :
    let tag32 : BitVec 32 := w32 + 4#32
    let vec128 : BitVec 128 := w128 - 8#128
    let sp : BitVec 64 := s0.sp - 128#64
    slotWithWidths sp tag32 vec128 ⊢
      ((s0.sp - 112#64) ↦₃₂ tag32) ∗ ((s0.sp - 96#64) ↦₁₂₈ vec128) := by
  sep_entail

-- Symbolic / conditional `BitVec 64` `let` bindings and disjoint `abbrev` bundles stay syntactically
-- unexpanded (`=ₛ`) in `?F` under `sep_focus`.
private theorem eq_trans_focus {P Sub F R : SepProp} (h1 : P = Sub ∗ F) (h2 : Sub ∗ F = R) :
    P = R := h1.trans h2

example (base v0 v1 a b : BitVec 64) (k : Nat) (flag : Bool) :
    let symPtr : BitVec 64 := base + BitVec.ofNat 64 k
    let pickedVal : BitVec 64 := if flag then a else b
    ((base ↦₆₄ v0) ∗ (symPtr ↦₆₄ pickedVal) ∗ abbrevSlotPair (base + 128#64) v0 v1) =
      ((base ↦₆₄ v0) ∗ ((symPtr ↦₆₄ pickedVal) ∗ abbrevSlotPair (base + 128#64) v0 v1)) := by
  intro symPtr pickedVal
  apply eq_trans_focus (Sub := base ↦₆₄ v0)
  · sep_focus
  · guard_target =ₛ
      (base ↦₆₄ v0) ∗ ((symPtr ↦₆₄ pickedVal) ∗ abbrevSlotPair (base + 128#64) v0 v1) =
        (base ↦₆₄ v0) ∗ ((symPtr ↦₆₄ pickedVal) ∗ abbrevSlotPair (base + 128#64) v0 v1)
    rfl

-- Instantiating `?sp := s0.sp - 80#64` on an earlier atom folds `(?sp - 4160#64)` to `s0.sp - 4240#64`
-- for subsequent atoms in `sep_focus`.
example (s0 : State) (v : BitVec 64) :
    ∃ (spSub : BitVec 64) (F : SepProp),
      (((s0.sp - 80#64) ↦₆₄ v) ∗ memRegion (s0.sp - 4240#64) 64 ∗ abbrevSlotPair s0.sp v v) =
        (((spSub ↦₆₄ v) ∗ memRegion (spSub - 4160#64) 64) ∗ F) :=
  ⟨_, _, by sep_focus⟩

/-- `wp_frame_split` on frame-inference goals (`?F`) delegates `abbrev` / `@[expose] def` bundle
    matching to `SepFrameInfer`, keeping disjoint `@[expose] def` bundles folded in `?F` and
    zeta-reducing local `let` expressions consistently with `sep_frame`. -/
abbrev calleeRegion64 (sp : BitVec 64) : SepProp :=
  memRegion (sp - 64#64) 64

example (m : Memory) (sp p a b h0 h1 : BitVec 64) (flag : Bool) :
    let sel : BitVec 64 := if flag then a else b
    m ⊨ stackAt sp 64 ∗ (p ↦₆₄ sel) ∗ headerSlots sp h0 h1 →
    ∃ F, m ⊨ calleeRegion64 sp ∗ F ∧
      F = (p ↦₆₄ (if flag then a else b)) ∗ headerSlots sp h0 h1 := by
  intro sel h
  refine ⟨_, by wp_frame_split, ?_⟩
  rfl

-- `sep_focus` rolls back partial metavariable assignments when an earlier `abbrev` region candidate
-- fails on a subsequent atom, allowing backtracking `SepFrameInfer` to resolve `?q := p`.
abbrev calleeRegion56 (sp : BitVec 64) : SepProp :=
  memRegion (sp - 56#64) 56

example (sp p : BitVec 64) :
    ∃ (q : BitVec 64) (F : SepProp),
      (calleeRegion56 sp ∗ memRegion p 56 ∗ ((p + 56#64) ↦₆₄ 0#64)) =
        ((memRegion q 56 ∗ ((q + 56#64) ↦₆₄ 0#64)) ∗ F) :=
  ⟨_, _, by sep_focus⟩

-- Deep (> 16) nested offset chains generated by `open_cells` / `close_cells` (`k = 24`, 192 bytes)
-- fold completely on Pass 2 (`addrFuel = 64`) against pre-normalized `(sp - k)#64` cells, while
-- Pass 1 (`splitRegions = false`, `addrFuel = 16`) preserves `fuel = 16` normal forms for callers.
example (prog : Program) (target : BitVec 64) (s0 : State) (post : State → SepProp → Prop)
    (h : SepWP prog target s0 (memRegion (s0.sp - 192#64) 192) post) :
    SepWP prog target s0 (memRegion (s0.sp - 192#64) 192) post := by
  open_cells (s0.sp - 192#64) 192 24
  close_cells (s0.sp - 192#64) 192 24
  rwa [sepConj_emp]

example (prog : Program) (target : BitVec 64) (s0 : State) (post : State → SepProp → Prop)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64)
    (h : SepWP prog target s0 (memRegion (s0.sp - 192#64) 192) post) :
    SepWP prog target s0
      (((s0.sp - 192#64) ↦₆₄ v0) ∗ ((s0.sp - 184#64) ↦₆₄ v1) ∗
       ((s0.sp - 176#64) ↦₆₄ v2) ∗ ((s0.sp - 168#64) ↦₆₄ v3) ∗
       ((s0.sp - 160#64) ↦₆₄ v4) ∗ ((s0.sp - 152#64) ↦₆₄ v5) ∗
       ((s0.sp - 144#64) ↦₆₄ v6) ∗ ((s0.sp - 136#64) ↦₆₄ v7) ∗
       ((s0.sp - 128#64) ↦₆₄ v8) ∗ ((s0.sp - 120#64) ↦₆₄ v9) ∗
       ((s0.sp - 112#64) ↦₆₄ v10) ∗ ((s0.sp - 104#64) ↦₆₄ v11) ∗
       ((s0.sp - 96#64) ↦₆₄ v12) ∗ ((s0.sp - 88#64) ↦₆₄ v13) ∗
       ((s0.sp - 80#64) ↦₆₄ v14) ∗ ((s0.sp - 72#64) ↦₆₄ v15) ∗
       ((s0.sp - 64#64) ↦₆₄ v16) ∗ ((s0.sp - 56#64) ↦₆₄ v17) ∗
       ((s0.sp - 48#64) ↦₆₄ v18) ∗ ((s0.sp - 40#64) ↦₆₄ v19) ∗
       ((s0.sp - 32#64) ↦₆₄ v20) ∗ ((s0.sp - 24#64) ↦₆₄ v21) ∗
       ((s0.sp - 16#64) ↦₆₄ v22) ∗ ((s0.sp - 8#64) ↦₆₄ v23)) post := by
  close_cells (s0.sp - 192#64) 192 24
  rwa [sepConj_emp]

example (prog : Program) (target : BitVec 64) (s0 : State) (post : State → SepProp → Prop)
    (v : BitVec 64) (φ : Prop)
    (h : φ → SepWP prog target s0 ((s0.sp - 24#64) ↦₆₄ v) post) :
    SepWP prog target s0
      (⌜φ⌝ ∗ (((((((((((((((((((s0.sp - 160#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) +
        8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) + 8#64) ↦₆₄ v))
      post := by
  wp_focus_pure
  intro hφ
  have h24 : s0.sp - 160#64 + 136#64 = s0.sp - 24#64 := by bv_omega
  simp only [h24]
  exact h hφ

-- `sep_frame` with unnormalized `((sp - k) + 8)` cell offsets skips `preSplitPointsToBytes`
-- immediately when normalized cells already match in `full`, without running `disch` across
-- unrelated earlier `pointsToBytes` stack slots.
set_option maxHeartbeats 25000 in
example (sp x0 x1 x2 x3 : BitVec 64) (s0 s1 s2 s3 s4 s5 s6 s7 : List (BitVec 8))
    (_hs0 : s0.length = 32) (_hs1 : s1.length = 32) (_hs2 : s2.length = 32) (_hs3 : s3.length = 32)
    (_hs4 : s4.length = 32) (_hs5 : s5.length = 32) (_hs6 : s6.length = 32) (_hs7 : s7.length = 32) :
    ∃ F : SepProp,
      (((sp - 552#64) ↦ₛ s0) ∗ ((sp - 520#64) ↦ₛ s1) ∗ ((sp - 488#64) ↦ₛ s2) ∗
       ((sp - 456#64) ↦ₛ s3) ∗ ((sp - 424#64) ↦ₛ s4) ∗ ((sp - 392#64) ↦ₛ s5) ∗
       ((sp - 360#64) ↦ₛ s6) ∗ ((sp - 328#64) ↦ₛ s7) ∗
       ((sp - 296#64) ↦₆₄ x0) ∗ ((sp - 288#64) ↦₆₄ x1) ∗
       ((sp - 280#64) ↦₆₄ x2) ∗ ((sp - 272#64) ↦₆₄ x3)) =
      ((((sp - 296#64) ↦₆₄ x0) ∗ (((sp - 296#64) + 8#64) ↦₆₄ x1) ∗
        (((sp - 296#64) + 16#64) ↦₆₄ x2) ∗ (((sp - 296#64) + 24#64) ↦₆₄ x3)) ∗ F) :=
  ⟨_, by sep_frame⟩

-- `arm64_sep_close` (`proveSepSide?`) splits and decides disjunctive `ite` postconditions cleanly
-- after splitting > 32 `memRegion` cells (`272` bytes = 34 cells).
example (m : Memory) (sp : BitVec 64) (flag : BitVec 8)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : BitVec 64)
    (v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 : BitVec 64)
    (hm : m ⊨
      ((sp - 8#64) ↦₆₄ v0) ∗ ((sp - 16#64) ↦₆₄ v1) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 32#64) ↦₆₄ v3) ∗
      ((sp - 40#64) ↦₆₄ v4) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 64#64) ↦₆₄ v7) ∗
      ((sp - 72#64) ↦₆₄ v8) ∗ ((sp - 80#64) ↦₆₄ v9) ∗ ((sp - 88#64) ↦₆₄ v10) ∗ ((sp - 96#64) ↦₆₄ v11) ∗
      ((sp - 104#64) ↦₆₄ v12) ∗ ((sp - 112#64) ↦₆₄ v13) ∗ ((sp - 120#64) ↦₆₄ v14) ∗ ((sp - 128#64) ↦₆₄ v15) ∗
      ((sp - 136#64) ↦₆₄ v16) ∗ ((sp - 144#64) ↦₆₄ v17) ∗ ((sp - 152#64) ↦₆₄ v18) ∗ ((sp - 160#64) ↦₆₄ v19) ∗
      ((sp - 168#64) ↦₆₄ v20) ∗ ((sp - 176#64) ↦₆₄ v21) ∗ ((sp - 184#64) ↦₆₄ v22) ∗ ((sp - 192#64) ↦₆₄ v23) ∗
      ((sp - 200#64) ↦₆₄ v24) ∗ ((sp - 208#64) ↦₆₄ v25) ∗ ((sp - 216#64) ↦₆₄ v26) ∗ ((sp - 224#64) ↦₆₄ v27) ∗
      ((sp - 232#64) ↦₆₄ v28) ∗ ((sp - 240#64) ↦₆₄ v29) ∗ ((sp - 248#64) ↦₆₄ v30) ∗ ((sp - 256#64) ↦₆₄ v31) ∗
      ((sp - 264#64) ↦₆₄ v32) ∗ ((sp - 272#64) ↦₆₄ v33)) :
    m ⊨ stackFrameAt sp 272 ∗
      ⌜(if flag &&& 1#8 = 0#8 then 0#32 else 23#32) = 0#32 ∨
       (if flag &&& 1#8 = 0#8 then 0#32 else 23#32) = 23#32⌝ := by
  arm64_sep_close

-- `arm64_sep_close` rejects stale `m ⊨ ... ∗ R` hypotheses lacking an opaque goal frame `R'` in
-- $O(1)$ without running near-miss solvers across unconstrained stack cells, and prefers the
-- newest matching `m ⊨ ...` hypothesis while still falling back to older ones when needed.
set_option maxHeartbeats 25000 in
example (m : Memory) (sp p q : BitVec 64) (R R' : SepProp)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (_hOld : m ⊨
      ((sp - 8#64) ↦₆₄ v0) ∗ ((sp - 16#64) ↦₆₄ v1) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 32#64) ↦₆₄ v3) ∗
      ((sp - 40#64) ↦₆₄ v4) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 64#64) ↦₆₄ v7) ∗ R)
    (_hNew : m ⊨
      ((p + 16#64) ↦₆₄ 0#64) ∗ ((p + 24#64) ↦₆₄ 0#64) ∗
      ((q + 32#64) ↦₆₄ 0#64) ∗ ((q + 40#64) ↦₆₄ 0#64) ∗ R') :
    m ⊨ ((p + 16#64) ↦₆₄ 0#64) ∗ ((q + 32#64) ↦₆₄ 0#64) ∗ R' := by
  arm64_sep_close

set_option linter.unusedVariables false in
set_option maxHeartbeats 25000 in
example (m : Memory) (sp p q : BitVec 64) (R R' : SepProp)
    (v0 v1 v2 v3 v4 v5 v6 v7 : BitVec 64)
    (hOld : m ⊨
      ((sp - 8#64) ↦₆₄ v0) ∗ ((sp - 16#64) ↦₆₄ v1) ∗ ((sp - 24#64) ↦₆₄ v2) ∗ ((sp - 32#64) ↦₆₄ v3) ∗
      ((sp - 40#64) ↦₆₄ v4) ∗ ((sp - 48#64) ↦₆₄ v5) ∗ ((sp - 56#64) ↦₆₄ v6) ∗ ((sp - 64#64) ↦₆₄ v7) ∗ R) :
    True := by
  fail_if_success
    have _ : m ⊨ ((p + 16#64) ↦₆₄ 0#64) ∗ ((p + 24#64) ↦₆₄ 0#64) ∗
        ((q + 32#64) ↦₆₄ 0#64) ∗ ((q + 40#64) ↦₆₄ 0#64) ∗ R' := by arm64_sep_close
  trivial

-- `arm64_sep_close` extracts pure `⌜φ⌝` conjuncts still embedded inside a `m ⊨ ...` hypothesis
-- (both direct definitional matches and arithmetic consequences via `satisfies_pure_sepConj`).
example (sf : State) (addr sp : BitVec 64) (inv R : SepProp)
    (_hpost : sf.mem ⊨
      (⌜sf.readReg32 Reg.x0 = 1#32⌝ ∗
        ((addr + 8#64) ↦₈ᵣ 3#8 ∗ (addr + 24#64) ↦₃₂ᵣ 0#32 ∗ stackFrameAt sp 16)) ∗ inv ∗ R) :
    sf.mem ⊨
      (⌜sf.readReg32 Reg.x0 = 1#32⌝ ∗
        (((addr + 8#64) ↦₈ᵣ 3#8 ∗ (addr + 24#64) ↦₃₂ᵣ 0#32 ∗ inv) ∗ stackFrameAt sp 16)) ∗ R := by
  arm64_sep_close

example (sf : State) (addr sp : BitVec 64) (inv R : SepProp)
    (_hpost : sf.mem ⊨
      (⌜sf.readReg32 Reg.x0 = 1#32 ∧ sf.sp = sp⌝ ∗
        ((addr + 8#64) ↦₈ᵣ 3#8 ∗ stackFrameAt sp 16)) ∗ inv ∗ R) :
    sf.mem ⊨
      (⌜sf.readReg32 Reg.x0 ≤ 5#32⌝ ∗
        (((addr + 8#64) ↦₈ᵣ 3#8 ∗ inv) ∗ stackFrameAt sp 16)) ∗ R := by
  arm64_sep_close

structure Record8 where
  f0 : BitVec 32
  f1 : BitVec 32
  f2 : BitVec 32
  f3 : BitVec 32
  f4 : BitVec 32
  f5 : BitVec 32
  f6 : BitVec 32
  f7 : BitVec 32

def record8At (w : BitVec 64) (r : Record8) : SepProp :=
  (w ↦₃₂ r.f0) ∗ ((w + 4#64) ↦₃₂ r.f1) ∗ ((w + 8#64) ↦₃₂ r.f2) ∗ ((w + 12#64) ↦₃₂ r.f3) ∗
  ((w + 16#64) ↦₃₂ r.f4) ∗ ((w + 20#64) ↦₃₂ r.f5) ∗ ((w + 24#64) ↦₃₂ r.f6) ∗ ((w + 28#64) ↦₃₂ r.f7)

def roTableBundle (base : BitVec 64) : SepProp :=
  (base ↦₆₄ᵣ 1#64) ∗ ((base + 8#64) ↦₆₄ᵣ 2#64) ∗ ((base + 16#64) ↦₆₄ᵣ 3#64) ∗ ((base + 24#64) ↦₆₄ᵣ 4#64)

-- Full-field structure existential (`∃∗ r' : Record8` and pre-instantiated `∃ r' : Record8`) where
-- 7 fields retain `r.f0 .. r.f6` and the 8th field is updated: `arm64_sep_close` and `wp_frame_split`
-- eta-expand `r'` instead of greedily unifying `?r' := r` on `f0`.
set_option maxHeartbeats 25000 in
example (sf : State) (w tbl sp : BitVec 64) (r : Record8) (R : SepProp)
    (_hm : sf.mem ⊨
      (w ↦₃₂ r.f0) ∗ ((w + 4#64) ↦₃₂ r.f1) ∗ ((w + 8#64) ↦₃₂ r.f2) ∗ ((w + 12#64) ↦₃₂ r.f3) ∗
      ((w + 16#64) ↦₃₂ r.f4) ∗ ((w + 20#64) ↦₃₂ r.f5) ∗ ((w + 24#64) ↦₃₂ r.f6) ∗
      ((w + 28#64) ↦₃₂ BitVec.truncate 32 (sf.readReg64 Reg.x0)) ∗
      roTableBundle tbl ∗ stackFrameAt sp 64 ∗ R) :
    sf.mem ⊨
      (∃∗ r' : Record8, record8At w r') ∗ roTableBundle tbl ∗ stackFrameAt sp 64 ∗ R := by
  dsimp only [record8At]
  arm64_sep_close

set_option maxHeartbeats 25000 in
example (sf : State) (w tbl sp : BitVec 64) (r : Record8) (R : SepProp)
    (_hm : sf.mem ⊨
      (w ↦₃₂ r.f0) ∗ ((w + 4#64) ↦₃₂ r.f1) ∗ ((w + 8#64) ↦₃₂ r.f2) ∗ ((w + 12#64) ↦₃₂ r.f3) ∗
      ((w + 16#64) ↦₃₂ r.f4) ∗ ((w + 20#64) ↦₃₂ r.f5) ∗ ((w + 24#64) ↦₃₂ r.f6) ∗
      ((w + 28#64) ↦₃₂ BitVec.truncate 32 (sf.readReg64 Reg.x0)) ∗
      roTableBundle tbl ∗ stackFrameAt sp 64 ∗ R) :
    ∃ r' : Record8,
      sf.mem ⊨ record8At w r' ∗ roTableBundle tbl ∗ stackFrameAt sp 64 ∗ R := by
  arm64_instantiate_sep_exists
  dsimp only [record8At]
  wp_frame_split

structure Record4 where
  a : BitVec 32
  b : BitVec 32
  c : BitVec 32
  d : BitVec 32

-- Partial-field structure projection shared across a spatial goal (`a`, `b`) and pure sibling goals
-- (`c`, `d`): `wp_frame_split` falls back cleanly to `SepFrameInfer` within a tight heartbeat cap.
set_option maxHeartbeats 35000 in
example (sf : State) (w tbl : BitVec 64) (r : Record4) (R : SepProp)
    (_hm : sf.mem ⊨
      (w ↦₃₂ r.a) ∗ ((w + 4#64) ↦₃₂ BitVec.truncate 32 (sf.readReg64 Reg.x0)) ∗
      roTableBundle tbl ∗ R) :
    ∃ r' : Record4,
      (sf.mem ⊨ (w ↦₃₂ r'.a) ∗ ((w + 4#64) ↦₃₂ r'.b) ∗ roTableBundle tbl ∗ R) ∧
      r'.c = 10#32 ∧ r'.d = 20#32 := by
  arm64_instantiate_sep_exists
  refine ⟨?_, ?_, ?_⟩
  · wp_frame_split
  · rfl
  · rfl

-- Genuine value mismatch fails cleanly with `frame_split:` diagnostic without exhausting heartbeats.
/--
error: frame_split: no match for (w + 28#64) ↦₃₂ r.f7 in precondition
  near-miss at same address: target expects `(w + 28#64) ↦₃₂
  r.f7`, but context has `(w + 28#64) ↦₃₂
  BitVec.truncate 32
    (sf.readReg64 Reg.x0)` (prove the values equal with `rw`/`simp` before matching, or split/coalesce cell widths)
candidates: (w + 28#64) ↦₃₂ BitVec.truncate 32 (sf.readReg64 Reg.x0)
-/
#guard_msgs in
set_option maxHeartbeats 40000 in
example (sf : State) (w tbl : BitVec 64) (r : Record8) (R : SepProp)
    (_hm : sf.mem ⊨
      (w ↦₃₂ r.f0) ∗ ((w + 4#64) ↦₃₂ r.f1) ∗ ((w + 8#64) ↦₃₂ r.f2) ∗ ((w + 12#64) ↦₃₂ r.f3) ∗
      ((w + 16#64) ↦₃₂ r.f4) ∗ ((w + 20#64) ↦₃₂ r.f5) ∗ ((w + 24#64) ↦₃₂ r.f6) ∗
      ((w + 28#64) ↦₃₂ BitVec.truncate 32 (sf.readReg64 Reg.x0)) ∗
      roTableBundle tbl ∗ R) :
    sf.mem ⊨ record8At w r ∗ roTableBundle tbl ∗ R := by
  dsimp only [record8At]
  wp_frame_split

end EdgeCaseRegressions

end WpStepsCarveAndReframe

end

end Testing.SepStackAutomation
