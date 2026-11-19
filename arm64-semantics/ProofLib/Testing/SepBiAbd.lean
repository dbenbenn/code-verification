/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.BiAbd

/-!
# `ProofLib.Sep.BiAbd` Regression Test Suite

Positive, negative, and axiom-audit regression tests for `ProofLib/Sep/BiAbd.lean` (`bi_entail`,
`bi_frame`, `@[sep_key ...]`, `@[biabd_rule]`, `register_sep_key`, `register_biabd_rule`), verified
without opening `ProofLib.Sep`:
1. Namespace-free registration commands, attribute wrappers, `bi_entail`, and `bi_frame`.
2. Large spatial spines ($N = 24$ atoms) with `∃∗` skolemization, witness synthesis, and pure guards.
3. `?Frame` inference (`P ⊢ Goal ∗ ?Frame` and `m ⊨ Goal ∗ ?Frame`), `let`-bound addresses, local
   pointer equalities, unequal symbolic-base offsets, multi-atom `memRegion` covers, and symbolic
   `idx == 0` address deferral (`Q_addr`).
4. Dynamic runtime-offset 3-way `ByteSlice` / `pointsToBytes` splitting and coalescing (including
   `BitVec.ofNat 64 u.toNat` and `u.zeroExtend 64` contiguity).
5. Deep `ByteSlice.write8` / `ByteSlice.write64` chains with `∃∗` framing.
6. User-defined composite representation packing via `@[sep_key]` and `@[biabd_rule]`.
7. Negative `#guard_msgs` and `fail_if_success` soundness checks.
8. `#guard_msgs` `#print axioms` checks confirming standard axioms only.
-/

public section

namespace Testing.SepBiAbd

/-! ## 1. Namespace-Free Smoke Tests (Without `open ProofLib` or `open ProofLib.Sep`) -/

section NoOpenSmoke

open Arm64

@[sep_key 0]
/-- Attribute-registered two-word spatial pair. -/
def SlotPair (p v1 v2 : BitVec 64) : SepProp :=
  (p ↦₆₄ v1) ∗ ((p + 8#64) ↦₆₄ v2)

@[biabd_rule 1050]
/-- Attribute-registered carve rule with explicit priority (written naturally with shared `p`). -/
theorem slotPair_carve_first (p v1 v2 : BitVec 64) :
    SlotPair p v1 v2 ⊢ ((p ↦₆₄ v1) ∗ ((p + 8#64) ↦₆₄ v2)) :=
  Entails.refl _

@[sep_key 0, 1]
abbrev IndexedCell (tag : Nat) (p v : BitVec 64) : SepProp :=
  ⌜tag < 256⌝ ∗ (p ↦₆₄ v)

def CommandRegPair (p v1 v2 : BitVec 64) : SepProp :=
  (p ↦₆₄ v1) ∗ ((p + 8#64) ↦₆₄ v2)

theorem commandRegPair_carve_second (p q v1 v2 : BitVec 64) (h : p + 8#64 = q) :
    CommandRegPair p v1 v2 ⊢ ((q ↦₆₄ v2) ∗ (p ↦₆₄ v1)) := by
  subst h
  unfold CommandRegPair
  rw [sepConj_comm]
  exact Entails.refl _

register_sep_key CommandRegPair [0]
register_biabd_rule commandRegPair_carve_second 1040

@[sep_key 0]
def BoxedWord (p v : BitVec 64) : SepProp :=
  p ↦₆₄ v

@[biabd_rule]
theorem boxedWord_expose (p v : BitVec 64) :
    BoxedWord p v ⊢ (p ↦₆₄ v) :=
  Entails.refl _

theorem smoke_no_open_entail (p q x1 x2 y1 y2 z : BitVec 64) :
    let qOff := q + 8#64
    (SlotPair p x1 x2 ∗ CommandRegPair q y1 y2 ∗ BoxedWord (p + 32#64) z ∗
      IndexedCell 7 (p + 64#64) z) ⊢
    ((p ↦₆₄ x1) ∗ (qOff ↦₆₄ y2) ∗ ((p + 32#64) ↦₆₄ z) ∗
      IndexedCell 7 (p + 64#64) z ∗ ((p + 8#64) ↦₆₄ x2) ∗ (q ↦₆₄ y1)) := by
  bi_entail

theorem smoke_no_open_frame (p x1 x2 y : BitVec 64) :
    ∃ Frame : SepProp,
      ((SlotPair p x1 x2 ∗ ((p + 24#64) ↦₆₄ y)) ⊢ ((p ↦₆₄ x1) ∗ Frame)) ∧
      Frame = (((p + 8#64) ↦₆₄ x2) ∗ ((p + 24#64) ↦₆₄ y)) := by
  refine ⟨?_, ?_, ?_⟩
  case refine_2 => bi_frame
  case refine_3 => rfl

end NoOpenSmoke

open Arm64 ProofLib

/-! ## 2. Large Spatial Spine ($N = 24$ Atoms, `∃∗` Skolemization & Synthesis, Pure Guards) -/

theorem spine24_exists_pure_entail
    (base v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
          v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 : BitVec 64) :
    (∃∗ s18 : BitVec 64, ∃∗ s19 : BitVec 64,
      ⌜s18 = v18 ∧ s19 = v19⌝ ∗
      (((base + 184#64) ↦₆₄ v23) ∗
       ((base + 176#64) ↦₆₄ v22) ∗
       ((base + 168#64) ↦₆₄ v21) ∗
       ((base + 160#64) ↦₆₄ v20) ∗
       ((base + 152#64) ↦₆₄ s19) ∗
       ((base + 144#64) ↦₆₄ s18) ∗
       ((base + 136#64) ↦₆₄ v17) ∗
       ((base + 128#64) ↦₆₄ v16) ∗
       ((base + 120#64) ↦₆₄ v15) ∗
       ((base + 112#64) ↦₆₄ v14) ∗
       ((base + 104#64) ↦₆₄ v13) ∗
       ((base + 96#64) ↦₆₄ v12) ∗
       ((base + 88#64) ↦₆₄ v11) ∗
       ((base + 80#64) ↦₆₄ v10) ∗
       ((base + 72#64) ↦₆₄ v9) ∗
       ((base + 64#64) ↦₆₄ v8) ∗
       ((base + 56#64) ↦₆₄ v7) ∗
       ((base + 48#64) ↦₆₄ v6) ∗
       ((base + 40#64) ↦₆₄ v5) ∗
       ((base + 32#64) ↦₆₄ v4) ∗
       ((base + 24#64) ↦₆₄ v3) ∗
       ((base + 16#64) ↦₆₄ v2) ∗
       ((base + 8#64) ↦₆₄ v1) ∗
       ((base + 0#64) ↦₆₄ v0))) ⊢
    (((base + 0#64) ↦₆₄ v0) ∗
     ((base + 8#64) ↦₆₄ v1) ∗
     ((base + 16#64) ↦₆₄ v2) ∗
     ((base + 24#64) ↦₆₄ v3) ∗
     ((base + 32#64) ↦₆₄ v4) ∗
     ((base + 40#64) ↦₆₄ v5) ∗
     ((base + 48#64) ↦₆₄ v6) ∗
     ((base + 56#64) ↦₆₄ v7) ∗
     ((base + 64#64) ↦₆₄ v8) ∗
     ((base + 72#64) ↦₆₄ v9) ∗
     ((base + 80#64) ↦₆₄ v10) ∗
     ((base + 88#64) ↦₆₄ v11) ∗
     ((base + 96#64) ↦₆₄ v12) ∗
     ((base + 104#64) ↦₆₄ v13) ∗
     ((base + 112#64) ↦₆₄ v14) ∗
     ((base + 120#64) ↦₆₄ v15) ∗
     ((base + 128#64) ↦₆₄ v16) ∗
     ((base + 136#64) ↦₆₄ v17) ∗
     (∃∗ w0 : BitVec 64, ⌜w0 = v18⌝ ∗ ((base + 144#64) ↦₆₄ w0)) ∗
     (∃∗ w1 : BitVec 64, ⌜w1 = v19⌝ ∗ ((base + 152#64) ↦₆₄ w1)) ∗
     (∃∗ w2 : BitVec 64, ⌜w2 = v20⌝ ∗ ((base + 160#64) ↦₆₄ w2)) ∗
     (∃∗ w3 : BitVec 64, ⌜w3 = v21⌝ ∗ ((base + 168#64) ↦₆₄ w3)) ∗
     (∃∗ w4 : BitVec 64, ((base + 176#64) ↦₆₄ w4)) ∗
     (∃∗ w5 : BitVec 64, ((base + 184#64) ↦₆₄ w5))) := by
  bi_entail

/-! ## 3. `?Frame` Inference, `let`-Bound Addresses, `Q_addr` Deferral, & Symbolic Offsets -/

@[expose] def UnifiedFramePre (sp ptr fp cPtr gKey1 gKey2 v0 slotVal c1 c2 : BitVec 64)
    (i : Nat) (γ : GhostName) (g1 g2 : Nat) : SepProp :=
  ∃∗ padBs : List (BitVec 8),
    ⌜padBs.length = 24⌝ ∗
    (ProofLib.ghostMapElem γ gKey1 g1 ∗
     ((ptr + BitVec.ofNat 64 (8 * (i + 1))) ↦₆₄ slotVal) ∗
     (sp ↦₆₄ v0) ∗
     SlotPair cPtr c1 c2 ∗
     ProofLib.ghostMapElem γ gKey2 g2 ∗
     ((sp + 8#64) ↦ₛ padBs) ∗
     stackFrameAt fp 64)

@[expose] def UnifiedFrameGoal (s0 : State) (ptr cPtr gKey2 slotVal c1 : BitVec 64)
    (i : Nat) (γ : GhostName) (g2 : Nat) : SepProp :=
  ∃∗ wSlot : BitVec 64, ∃∗ wGhost : Nat, ∃∗ wPair1 : BitVec 64,
    ⌜wSlot = slotVal ∧ wGhost = g2 ∧ wPair1 = c1⌝ ∗
    (memRegion (s0.sp - 848#64) 32 ∗
     ((ptr + BitVec.ofNat 64 (8 * i) + 8#64) ↦₆₄ wSlot) ∗
     ProofLib.ghostMapElem γ gKey2 wGhost ∗
     (cPtr ↦₆₄ wPair1))

/-- Unified `bi_frame` synthesis: `let sp`, symbolic `idx == 0` `Q_addr` deferral, multi-atom
    `memRegion` cover, `(0, 1)` multi-key `ghostMapElem` disambiguation, and custom rule carving. -/
theorem unified_bi_frame_synthesis (s0 : State)
    (ptr fp cPtr gKey1 gKey2 v0 slotVal c1 c2 : BitVec 64)
    (i : Nat) (γ : GhostName) (g1 g2 : Nat) :
    ∃ Frame : SepProp,
      (let sp := s0.sp - 848#64
       UnifiedFramePre sp ptr fp cPtr gKey1 gKey2 v0 slotVal c1 c2 i γ g1 g2 ⊢
         (UnifiedFrameGoal s0 ptr cPtr gKey2 slotVal c1 i γ g2 ∗ Frame)) ∧
      Frame = (ProofLib.ghostMapElem γ gKey1 g1 ∗ ((cPtr + 8#64) ↦₆₄ c2) ∗ stackFrameAt fp 64) := by
  refine ⟨?_, ?_, ?_⟩
  case refine_2 => bi_frame
  case refine_3 => rfl

/-- `m ⊨ Goal ∗ ?Frame` satisfaction mode with local `s.sp = fp - 64#64` pointer equality. -/
theorem satisfies_frame_with_sp_eq (m : Memory) (s : State) (fp x y z : BitVec 64)
    (hsp : s.sp = fp - 64#64)
    (hm : m ⊨ (((s.sp + 16#64) ↦₆₄ x) ∗ ((fp - 32#64) ↦₆₄ y) ∗ (fp ↦₆₄ z))) :
    ∃ Frame : SepProp,
      (m ⊨ (((fp - 48#64) ↦₆₄ x) ∗ Frame)) ∧
      Frame = (((fp - 32#64) ↦₆₄ y) ∗ (fp ↦₆₄ z)) := by
  refine ⟨?_, ?_, ?_⟩
  case refine_2 => bi_frame
  case refine_3 => rfl

/-- Unequal symbolic-base offsets (`ptr + u.zeroExtend 64 + k#64` vs `BitVec.ofNat 64 u.toNat`)
    canonicalize in 1 step and reject non-matching offsets without `whnf` or `isDefEq`. -/
theorem symbolic_base_offsets_ofNat_zeroExtend
    (ptr x0 x1 x2 x3 : BitVec 64) (u : BitVec 8) :
    let offNat := u.toNat
    (((ptr + BitVec.ofNat 64 offNat + 24#64) ↦₆₄ x3) ∗
     ((ptr + BitVec.ofNat 64 u.toNat + 16#64) ↦₆₄ x2) ∗
     ((ptr + u.zeroExtend 64 + 8#64) ↦₆₄ x1) ∗
     ((ptr + BitVec.ofNat 64 u.toNat) ↦₆₄ x0)) ⊢
    (((ptr + u.zeroExtend 64) ↦₆₄ x0) ∗
     ((ptr + BitVec.ofNat 64 u.toNat + 8#64) ↦₆₄ x1) ∗
     ((ptr + u.zeroExtend 64 + 16#64) ↦₆₄ x2) ∗
     ((ptr + u.zeroExtend 64 + 24#64) ↦₆₄ x3)) := by
  bi_entail

/-! ## 4. Dynamic Runtime-Offset 3-Way `ByteSlice` / `pointsToBytes` Split & Merge -/

@[expose] def padPacketBuf (buf : List (BitVec 8)) : List (BitVec 8) :=
  buf.take (buf.getD 127 0#8).toNat ++ [0x80#8] ++
    List.replicate (127 - (buf.getD 127 0#8).toNat) 0#8

/-- Dynamic runtime-offset 3-way `pointsToBytes` split across `SepWP` continuation weakening,
    bridging `BitVec.ofNat 64 (buf.getD 127 0#8).toNat` and `BitVec.zeroExtend 64 (buf.getD 127 0#8)`. -/
theorem packetBuf_dynamic_split3_sepwp (a : BitVec 64) (buf : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (a ↦ₛ buf) ∗ P)
    (hbuf : buf.length = 128) (hpos : (buf.getD 127 0#8).toNat < 128)
    (hnext : ProofLib.SepWP prog target_pc s
      (((a ↦ₛ buf.take (buf.getD 127 0#8).toNat) ∗
        ((a + BitVec.zeroExtend 64 (buf.getD 127 0#8)) ↦ₛ
          (buf.drop (buf.getD 127 0#8).toNat).take 1) ∗
        ((a + BitVec.zeroExtend 64 (buf.getD 127 0#8) + 1#64) ↦ₛ
          buf.drop ((buf.getD 127 0#8).toNat + 1))) ∗ P) post oom) :
    ProofLib.SepWP prog target_pc s Full post oom := by
  bi_entail

/-- Dynamic runtime-offset 3-way `pointsToBytes` coalescing after `ByteSlice.write8` and zero-fill. -/
theorem packetBuf_dynamic_merge3_sepwp (a : BitVec 64) (buf : List (BitVec 8))
    {prog : Program} {target_pc : BitVec 64} {s : State} {Full P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hf : Full = (((a ↦ₛ buf.take (buf.getD 127 0#8).toNat) ∗
      ((a + BitVec.zeroExtend 64 (buf.getD 127 0#8)) ↦ₛ
        ProofLib.ByteSlice.write8 ((buf.drop (buf.getD 127 0#8).toNat).take 1) 0 0x80#8) ∗
      ((a + BitVec.zeroExtend 64 (buf.getD 127 0#8) + 1#64) ↦ₛ
        List.replicate (127 - (buf.getD 127 0#8).toNat) 0#8)) ∗ P))
    (hbuf : buf.length = 128) (hpos : (buf.getD 127 0#8).toNat < 128)
    (hnext : ProofLib.SepWP prog target_pc s ((a ↦ₛ padPacketBuf buf) ∗ P) post oom) :
    ProofLib.SepWP prog target_pc s Full post oom := by
  bi_entail

/-- Carving a 64-bit little-endian word (`↦₆₄`) at runtime offset `u.zeroExtend 64` from `a ↦ₛ bs`
    while inferring the prefix and suffix slices in `?Frame`. -/
theorem slotSlice_focus64_frame (a : BitVec 64) (bs : List (BitVec 8)) (u : BitVec 8)
    (hbs : bs.length = 64) (hu : u.toNat + 8 ≤ 64) :
    ∃ Frame : SepProp,
      ((a ↦ₛ bs) ⊢
        ((∃∗ w : BitVec 64, ⌜w = ProofLib.ByteSlice.readLE bs u.toNat 8⌝ ∗
          ((a + u.zeroExtend 64) ↦₆₄ w)) ∗ Frame)) ∧
      Frame = ((a ↦ₛ bs.take u.toNat) ∗
               ((a + BitVec.ofNat 64 (u.toNat + 8)) ↦ₛ bs.drop (u.toNat + 8))) := by
  refine ⟨?_, ?_, ?_⟩
  case refine_2 => bi_frame
  case refine_3 => rfl

/-! ## 5. Deep `ByteSlice` Byte/Word Write Chains + `∃∗` Framing -/

@[expose] def AlphaHeaderPost (outPtr inPtr : BitVec 64) (inBytes : List (BitVec 8))
    (expectedOff expectedTag : BitVec 64) : SepProp :=
  ∃∗ outBs : List (BitVec 8),
  ∃∗ kind : BitVec 8,
  ∃∗ flags : BitVec 8,
  ∃∗ errOff : BitVec 64,
  ∃∗ bufPtr : BitVec 64,
  ∃∗ bufLen : BitVec 64,
  ∃∗ tagOut : BitVec 64,
    ⌜outBs.length = 48 ∧
     outBs.getD 0 0#8 = 1#8 ∧
     outBs.getD 1 0#8 = kind ∧
     outBs.getD 2 0#8 = flags ∧
     ProofLib.ByteSlice.readLE outBs 8 8 = errOff ∧
     ProofLib.ByteSlice.readLE outBs 16 8 = bufPtr ∧
     ProofLib.ByteSlice.readLE outBs 24 8 = bufLen ∧
     ProofLib.ByteSlice.readLE outBs 32 8 = tagOut ∧
     kind = 3#8 ∧
     flags = 2#8 ∧
     errOff = expectedOff ∧
     bufPtr = inPtr ∧
     bufLen = BitVec.ofNat 64 inBytes.length ∧
     tagOut = expectedTag⌝ ∗
    (outPtr ↦ₛ outBs) ∗
    (inPtr ↦ᵣ inBytes)

abbrev alphaHeaderWrites8 (initBs : List (BitVec 8))
    (off inPtr inLen tag : BitVec 64) : List (BitVec 8) :=
  ProofLib.ByteSlice.write64
    (ProofLib.ByteSlice.write64
      (ProofLib.ByteSlice.write64
        (ProofLib.ByteSlice.write64
          (ProofLib.ByteSlice.write8
            (ProofLib.ByteSlice.write8
              (ProofLib.ByteSlice.write8
                (ProofLib.ByteSlice.write8 initBs 0 1#8)
                1 3#8)
              2 2#8)
            3 0#8)
          8 off)
        16 inPtr)
      24 inLen)
    32 tag

theorem alphaHeader_write8_chain_entail (outPtr inPtr sp off inLen tag : BitVec 64)
    (initBs inBytes : List (BitVec 8)) (F : SepProp)
    (hinit : initBs.length = 48)
    (hin : inLen = BitVec.ofNat 64 inBytes.length) :
    ((inPtr ↦ᵣ inBytes) ∗
     stackFrameAt sp 64 ∗
     (outPtr ↦ₛ alphaHeaderWrites8 initBs off inPtr inLen tag) ∗
     F) ⊢
    (AlphaHeaderPost outPtr inPtr inBytes off tag ∗ stackFrameAt sp 64 ∗ F) := by
  bi_entail

/-! ## 6. User-Defined Composite Representation Packing via `@[sep_key]` + `@[biabd_rule]` -/

structure WidgetPlacement where
  rodataAddr    : BitVec 64
  emptyCtrlAddr : BitVec 64

structure WidgetPool where
  Block : BitVec 64 → Nat → Nat → SepProp

abbrev EntryList64 := List (BitVec 64 × BitVec 64)

def EntryListWf (entries : EntryList64) : Prop := entries.Nodup

def maskToSlotQuota (bm : BitVec 64) : Nat := ((bm.toNat + 1) * 7) / 8

structure NonZeroMask (bm : BitVec 64) : Prop where
  ne_zero : bm ≠ 0#64

structure WidgetTableInv (bm quotaLeft count : BitVec 64)
    (ctrl : List (BitVec 8)) (slots : List (BitVec 64 × BitVec 64))
    (entries : EntryList64) : Prop where
  validMask : NonZeroMask bm
  wf        : EntryListWf entries
  ctrlLen   : ctrl.length = bm.toNat + 1 + 16
  slotsLen  : slots.length = bm.toNat + 1
  countEq   : count.toNat = entries.length
  quotaLe   : quotaLeft.toNat ≤ maskToSlotQuota bm

structure WidgetMapWitness where
  allocPtr  : BitVec 64
  ctrlPtr   : BitVec 64
  quotaLeft : BitVec 64
  count     : BitVec 64
  ctrl      : List (BitVec 8)
  slots     : List (BitVec 64 × BitVec 64)

@[sep_key 0]
def widgetRodata (pl : WidgetPlacement) : SepProp :=
  (pl.rodataAddr ↦ᵣ List.replicate 16 0xff#8)

@[sep_key 0]
def WidgetHeader (hdrPtr ctrlPtr bm quotaLeft count : BitVec 64) : SepProp :=
  (hdrPtr ↦₆₄ ctrlPtr) ∗
  ((hdrPtr + 8#64) ↦₆₄ bm) ∗
  ((hdrPtr + 16#64) ↦₆₄ quotaLeft) ∗
  ((hdrPtr + 24#64) ↦₆₄ count)

@[biabd_rule 1020]
theorem widgetHeader_pack (hdrPtr ctrlPtr bm quotaLeft count : BitVec 64) :
    ((hdrPtr ↦₆₄ ctrlPtr) ∗
     ((hdrPtr + 8#64) ↦₆₄ bm) ∗
     ((hdrPtr + 16#64) ↦₆₄ quotaLeft) ∗
     ((hdrPtr + 24#64) ↦₆₄ count)) ⊢
    WidgetHeader hdrPtr ctrlPtr bm quotaLeft count :=
  Entails.refl _

@[sep_key 0]
def widgetSlotsDown (ctrlPtr : BitVec 64) : List (BitVec 64 × BitVec 64) → SepProp
  | [] => emp
  | (k, v) :: rest =>
    ((ctrlPtr - 16#64) ↦₆₄ k) ∗ ((ctrlPtr - 8#64) ↦₆₄ v) ∗ widgetSlotsDown (ctrlPtr - 16#64) rest

@[expose] def WidgetMapRep (pl : WidgetPlacement) (pool : WidgetPool) (hdrPtr : BitVec 64)
    (entries : EntryList64) (bm : BitVec 64) (bound : Nat) : SepProp :=
  ⌜hdrPtr.toNat % 8 = 0 ∧ hdrPtr.toNat + 32 ≤ 2 ^ 64 ∧ EntryListWf entries⌝ ∗
  widgetRodata pl ∗
  if bm = 0#64 then
    ⌜entries = []⌝ ∗
    WidgetHeader hdrPtr pl.emptyCtrlAddr 0#64 0#64 0#64
  else
    ∃∗ w : WidgetMapWitness,
      ⌜WidgetTableInv bm w.quotaLeft w.count w.ctrl w.slots entries ∧
       maskToSlotQuota bm - w.quotaLeft.toNat ≤ bound ∧
       w.allocPtr ≠ 0#64 ∧
       w.allocPtr.toNat % 8 = 0 ∧
       w.allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64 ∧
       w.ctrlPtr = w.allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))⌝ ∗
      WidgetHeader hdrPtr w.ctrlPtr bm w.quotaLeft w.count ∗
      pool.Block w.allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      widgetSlotsDown w.ctrlPtr w.slots ∗
      (w.ctrlPtr ↦ₛ w.ctrl)

theorem pack_widgetMapRep_nonempty {pl : WidgetPlacement} {pool : WidgetPool}
    {hdrPtr bm allocPtr ctrlPtr ql cnt : BitVec 64}
    {ctrl : List (BitVec 8)} {slots : List (BitVec 64 × BitVec 64)}
    {entries : EntryList64} {bound : Nat}
    (hal : hdrPtr.toNat % 8 = 0) (hnw : hdrPtr.toNat + 32 ≤ 2 ^ 64)
    (hinv : WidgetTableInv bm ql cnt ctrl slots entries)
    (hbnd : maskToSlotQuota bm - ql.toNat ≤ bound)
    (ha_ne : allocPtr ≠ 0#64) (ha_al : allocPtr.toNat % 8 = 0)
    (ha_nw : allocPtr.toNat + (17 * (bm.toNat + 1) + 8) ≤ 2 ^ 64)
    (hctrl : ctrlPtr = allocPtr + BitVec.ofNat 64 (16 * (bm.toNat + 1))) :
    widgetRodata pl ∗ WidgetHeader hdrPtr ctrlPtr bm ql cnt ∗
      pool.Block allocPtr (17 * (bm.toNat + 1) + 8) 8 ∗
      widgetSlotsDown ctrlPtr slots ∗ (ctrlPtr ↦ₛ ctrl) ⊢
    WidgetMapRep pl pool hdrPtr entries bm bound := by
  bi_entail

/-! ## 7. Negative Soundness Tests (`#guard_msgs` & `fail_if_success`) -/

-- Missing spatial resource on RHS is soundly rejected by `bi_entail`.
/--
error: bi_entail: could not match spatial goal atom:
  b ↦₆₄ y
-/
#guard_msgs in
example (a b x y : BitVec 64) : (a ↦₆₄ x) ⊢ ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) := by
  bi_entail

-- Missing spatial resource on RHS is soundly rejected by `bi_frame` even when synthesizing `?Frame`.
/--
error: bi_frame: could not match spatial goal atom:
  b ↦₆₄ y
-/
#guard_msgs in
example (m : Memory) (a b x y : BitVec 64) (hm : m ⊨ (a ↦₆₄ x)) :
    m ⊨ ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) := by
  bi_frame

-- Linear leftover spatial atom without `?Frame` is soundly rejected by `bi_entail`.
/--
error: bi_entail: linear `SepProp` has unmatched LHS spatial atoms and no `?Frame` metavariable:
  b ↦₆₄ y
-/
#guard_msgs in
example (a b x y : BitVec 64) : ((a ↦₆₄ x) ∗ (b ↦₆₄ y)) ⊢ (a ↦₆₄ x) := by
  bi_entail

-- Mismatched constant-offset spatial keys (`+ 8#64` vs `+ 16#64`) are soundly rejected.
/--
error: bi_entail: could not match spatial goal atom:
  (a + 16#64) ↦₆₄ x
-/
#guard_msgs in
example (a x : BitVec 64) : ((a + 8#64) ↦₆₄ x) ⊢ ((a + 16#64) ↦₆₄ x) := by
  bi_entail

-- Mismatched symbolic-base offsets (`ptr + u.zeroExtend 64 + 8#64` vs `+ 16#64`) are rejected
-- immediately without `whnf`/`isDefEq`.
/--
error: bi_frame: could not match spatial goal atom:
  (ptr + BitVec.zeroExtend 64 u + 16#64) ↦₆₄ x
-/
#guard_msgs in
example (m : Memory) (ptr x : BitVec 64) (u : BitVec 8)
    (hm : m ⊨ ((ptr + BitVec.ofNat 64 u.toNat + 8#64) ↦₆₄ x)) :
    m ⊨ ((ptr + u.zeroExtend 64 + 16#64) ↦₆₄ x) := by
  bi_frame

-- Mismatched multi-key `ghostMapElem` keys (`p1` vs `p2`) are soundly rejected.
/--
error: bi_entail: could not match spatial goal atom:
  ghostMapElem γ p2 v
-/
#guard_msgs in
example (γ : GhostName) (p1 p2 : BitVec 64) (v : Nat) :
    ProofLib.ghostMapElem γ p1 v ⊢ ProofLib.ghostMapElem γ p2 v := by
  bi_entail

-- Unprovable pure side-condition (`x = y`) is soundly rejected in Phase 5.
/--
error: bi_entail (Phase 5): failed to discharge pure side condition:
  x = y
-/
#guard_msgs in
example (a x y : BitVec 64) : (a ↦₆₄ x) ⊢ (⌜x = y⌝ ∗ (a ↦₆₄ x)) := by
  bi_entail

-- Out-of-bounds `ByteSlice` carve (`64 ≤ bs.length` when `bs.length = 32`) is soundly rejected.
example (a : BitVec 64) (bs : List (BitVec 8)) (hbs : bs.length = 32) :
    (a ↦ₛ bs) ⊢ (a ↦ₛ bs) := by
  fail_if_success (
    have : ∃ F : SepProp, (a ↦ₛ bs) ⊢ ((a ↦ₛ bs.take 64) ∗ F) := by
      refine ⟨?_, ?_⟩
      case refine_2 => bi_frame)
  let _ := hbs
  bi_entail

-- Unprovable deferred symbolic address equality (`Q_addr`) is soundly rejected in Phase 5.
/--
error: bi_entail (Phase 5 `Q_addr`): failed to prove deferred address equality:
  ptr + BitVec.ofNat 64 (8 * i) = ptr + BitVec.ofNat 64 (8 * j)
-/
#guard_msgs in
example (ptr v : BitVec 64) (i j : Nat) :
    ((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ v) ⊢
      ((ptr + BitVec.ofNat 64 (8 * j)) ↦₆₄ v) := by
  bi_entail

/-- Nested prenex existential peeling on both left and right nested `∗`-trees inside exposed
bundles (`∃∗ w, (A ∗ (B ∗ C w))` and `∃∗ w, ((A w ∗ B) ∗ C)`). -/
def RightNestedBundle (p q r a b : BitVec 64) : SepProp :=
  ∃∗ w : BitVec 64, (p ↦₆₄ a) ∗ ((q ↦₆₄ b) ∗ (r ↦₆₄ w))

def LeftNestedBundle (p q r b c : BitVec 64) : SepProp :=
  ∃∗ w : BitVec 64, ((p ↦₆₄ w) ∗ (q ↦₆₄ b)) ∗ (r ↦₆₄ c)

theorem prenex_peel_nested_right_entail (p q r a b w0 : BitVec 64) :
    (p ↦₆₄ a) ∗ (q ↦₆₄ b) ∗ (r ↦₆₄ w0) ⊢ RightNestedBundle p q r a b := by
  bi_entail

theorem prenex_peel_nested_left_entail (p q r b c w0 : BitVec 64) :
    (p ↦₆₄ w0) ∗ (q ↦₆₄ b) ∗ (r ↦₆₄ c) ⊢ LeftNestedBundle p q r b c := by
  bi_entail

/-! ## 8. Axiom Cone Audit (`#guard_msgs` `#print axioms`) -/

/--
info: 'Testing.SepBiAbd.smoke_no_open_entail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms smoke_no_open_entail

/--
info: 'Testing.SepBiAbd.spine24_exists_pure_entail' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms spine24_exists_pure_entail

/--
info: 'Testing.SepBiAbd.unified_bi_frame_synthesis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms unified_bi_frame_synthesis

/--
info: 'Testing.SepBiAbd.symbolic_base_offsets_ofNat_zeroExtend' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms symbolic_base_offsets_ofNat_zeroExtend

/--
info: 'Testing.SepBiAbd.packetBuf_dynamic_split3_sepwp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms packetBuf_dynamic_split3_sepwp

/--
info: 'Testing.SepBiAbd.packetBuf_dynamic_merge3_sepwp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms packetBuf_dynamic_merge3_sepwp

/--
info: 'Testing.SepBiAbd.alphaHeader_write8_chain_entail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms alphaHeader_write8_chain_entail

/--
info: 'Testing.SepBiAbd.pack_widgetMapRep_nonempty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms pack_widgetMapRep_nonempty

end Testing.SepBiAbd
