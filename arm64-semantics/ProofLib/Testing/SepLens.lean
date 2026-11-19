/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Sep.Lens

/-!
# Algebraic Separation-Logic Lens & `StructLayout` Regression Tests

Regression suite for `ProofLib.Sep.Lens`:
1. Namespace-hygiene tests verifying `@[sep_lens]`, `lens_open`, `lens_switch`, `lens_close`,
   `wp_lens_step`, and `wp_lens_auto` resolve without `open ProofLib.Sep`.
2. Adaptive small flat scalar `StructLayout` (`isSmallFlatScalar = true`) and large padded
   `StructLayout` (`PacketHeader48`, 15-field `ArenaPageHeader`) with 1-step `struct_to_memRegion`
   stack reclaim.
3. Multi-width scatter writes (`STRH`/`STRW`/`STR`) into symbolic-index struct arrays
   (`pointsToArray`) and dynamic trailing arrays (`DecodeEntryTable`).
4. Width-polymorphic `OwnByteMap` (`u8`/`u16`/`u32`/`u64`) loads and stores without custom
   per-width helper lemmas, plus lawful read-only `put_get` re-closure.
5. Downward `slotsDownFrom` bucket stores combined with double byte-slice window switching
   (`BucketSlotTable`).
6. Negative `#guard_msgs` and `fail_if_success` tests confirming rejection of overlapping struct
   fields, out-of-bounds struct/slice offsets, and unmatching addresses.
7. Kernel `#print axioms` audits on representative theorems.
-/

@[expose] public section

set_option linter.unusedVariables false

/-! ## 1. Global Resolution Without `open ProofLib.Sep` -/

namespace Testing.SepLensNoOpen

open Arm64 ProofLib

/-- Two-word widget snapshot tested without opening `ProofLib.Sep`. -/
structure WidgetPair where
  first  : BitVec 64
  second : BitVec 64
  deriving Inhabited, DecidableEq, Repr

/-- Spatial representation for `WidgetPair`. -/
def WidgetPairRep (p : BitVec 64) (w : WidgetPair) : SepProp :=
  (p ↦₆₄ w.first) ∗ ((p + 8#64) ↦₆₄ w.second)

@[sep_lens]
theorem widgetPair_first_lens (p : BitVec 64) :
    ProofLib.Sep.LawfulSepLens (WidgetPairRep p) (fun v => p ↦₆₄ v)
      (fun w => (p + 8#64) ↦₆₄ w.second)
      (·.first) (fun w v' => { w with first := v' }) where
  open_entails _ := Entails.refl _
  close_entails _ _ := Entails.refl _
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

@[sep_lens]
theorem widgetPair_second_lens (p : BitVec 64) :
    ProofLib.Sep.LawfulSepLens (WidgetPairRep p) (fun v => (p + 8#64) ↦₆₄ v)
      (fun w => p ↦₆₄ w.first)
      (·.second) (fun w v' => { w with second := v' }) where
  open_entails _ := by unfold WidgetPairRep; exact Entails.of_eq (sepConj_comm _ _)
  close_entails _ _ := by unfold WidgetPairRep; exact Entails.of_eq (sepConj_comm _ _)
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

/-- `str x1, [x0] ; str x2, [x0, #8]` -/
def widgetPairWriteCode : FnCode :=
  .atAddr "widget_pair_write" 0x100000#64
    ("f9000001 " ++ -- 0x100000: str x1, [x0]
     "f9000402")    -- 0x100004: str x2, [x0, #8]

theorem test_no_open_manual (prog : Program) (st : State) (p v1 v2 : BitVec 64) (w : WidgetPair)
    (hcode : widgetPairWriteCode.holds prog)
    (hpc : st.pc = 0x100000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = v1)
    (hx2 : st.readReg64 .x2 = v2) :
    SepWP prog 0x100008#64 st (WidgetPairRep p w)
      (fun _ Pf => Pf ⊢ WidgetPairRep p { first := v1, second := v2 }) := by
  lens_open
  wp_step
  lens_switch
  wp_step
  lens_close
  wp_done

theorem test_no_open_step (prog : Program) (st : State) (p v1 v2 : BitVec 64) (w : WidgetPair)
    (hcode : widgetPairWriteCode.holds prog)
    (hpc : st.pc = 0x100000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = v1)
    (hx2 : st.readReg64 .x2 = v2) :
    SepWP prog 0x100008#64 st (WidgetPairRep p w)
      (fun _ Pf => Pf ⊢ WidgetPairRep p { first := v1, second := v2 }) := by
  wp_lens_step
  wp_lens_step
  lens_close
  wp_done

theorem test_no_open_auto (prog : Program) (st : State) (p v1 v2 : BitVec 64) (w : WidgetPair)
    (hcode : widgetPairWriteCode.holds prog)
    (hpc : st.pc = 0x100000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = v1)
    (hx2 : st.readReg64 .x2 = v2) :
    SepWP prog 0x100008#64 st (WidgetPairRep p w)
      (fun _ Pf => Pf ⊢ WidgetPairRep p { first := v1, second := v2 }) := by
  wp_lens_auto

/-- `ldr x1, [x0]` read-only access closing `WidgetPairRep p w` back to unchanged `w`. -/
def widgetPairReadCode : FnCode :=
  .atAddr "widget_pair_read" 0x100100#64
    "f9400001" -- 0x100100: ldr x1, [x0]

theorem test_no_open_ro (prog : Program) (st : State) (p : BitVec 64) (w : WidgetPair)
    (hcode : widgetPairReadCode.holds prog)
    (hpc : st.pc = 0x100100#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p) :
    SepWP prog 0x100104#64 st (WidgetPairRep p w)
      (fun sf Pf => (Pf ⊢ WidgetPairRep p w) ∧ sf.readReg64 .x1 = w.first) := by
  lens_open
  wp_step
  lens_close
  wp_done

end Testing.SepLensNoOpen

/-! ## 2. Small Flat Scalar & Large Padded `StructLayout` + Stack Reclaim -/

namespace Testing.SepLens

open Arm64 ProofLib ProofLib.Sep

/-- 24-byte small flat scalar snapshot (`x`, `y`, `tag` + implicit 4-byte trailing alignment gap). -/
structure SmallPoint2D where
  x   : BitVec 64
  y   : BitVec 64
  tag : BitVec 32
  deriving Inhabited, DecidableEq, Repr

def SmallPoint2DLayout : StructLayout SmallPoint2D where
  totalSz := 24
  fields := [
    .u64 0  (·.x),
    .u64 8  (·.y),
    .u32 16 (·.tag)
  ]

theorem smallPoint2D_isSmallFlatScalar :
    SmallPoint2DLayout.isSmallFlatScalar = true := rfl

/-- `ldr x3, [x0] ; add x3, x3, x1 ; str x3, [x0, #8] ; str w2, [x0, #16]` -/
def smallPointUpdateCode : FnCode :=
  .atAddr "small_point_update" 0x180000#64
    ("f9400003 " ++ -- 0x180000: ldr x3, [x0]
     "8b010063 " ++ -- 0x180004: add x3, x3, x1
     "f9000403 " ++ -- 0x180008: str x3, [x0, #8]
     "b9001002")    -- 0x18000c: str w2, [x0, #16]

theorem test_smallPoint_auto (prog : Program) (st : State)
    (p dx : BitVec 64) (tag' : BitVec 32) (m : SmallPoint2D)
    (hcode : smallPointUpdateCode.holds prog)
    (hpc : st.pc = 0x180000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = dx)
    (hx2 : (st.readReg64 .x2).setWidth 32 = tag') :
    SepWP prog 0x180010#64 st (SmallPoint2DLayout.own p m)
      (fun _ Pf => Pf ⊢ SmallPoint2DLayout.own p { m with y := m.x + dx, tag := tag' }) := by
  wp_lens_auto

/-- Single-instruction `wp_lens_step` on a small flat scalar struct. -/
def smallPointSingleStoreCode : FnCode :=
  .atAddr "small_point_store_y" 0x180100#64
    "f9000401" -- 0x180100: str x1, [x0, #8]

theorem test_smallPoint_step (prog : Program) (st : State)
    (p ny : BitVec 64) (m : SmallPoint2D)
    (hcode : smallPointSingleStoreCode.holds prog)
    (hpc : st.pc = 0x180100#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = ny) :
    SepWP prog 0x180104#64 st (SmallPoint2DLayout.own p m)
      (fun _ Pf => Pf ⊢ SmallPoint2DLayout.own p { m with y := ny }) := by
  wp_lens_step
  try lens_close
  wp_done

theorem test_smallPoint_reclaim (p : BitVec 64) (m : SmallPoint2D) :
    SmallPoint2DLayout.own p m ⊢ memRegion p 24 :=
  SmallPoint2DLayout.struct_to_memRegion p m

/-- 48-byte heterogeneous padded packet header (`u64 × 3 + u8 + pad[7] + u64 × 2`). -/
structure PacketHeader48 where
  bufPtr : BitVec 64
  bufEnd : BitVec 64
  cursor : BitVec 64
  flags  : BitVec 8
  items  : BitVec 64
  depth  : BitVec 64
  deriving Inhabited, DecidableEq, Repr

def PacketHeader48Layout : StructLayout PacketHeader48 where
  totalSz := 48
  fields := [
    .u64 0  (·.bufPtr),
    .u64 8  (·.bufEnd),
    .u64 16 (·.cursor),
    .u8  24 (·.flags),
    .pad PacketHeader48 25 7,
    .u64 32 (·.items),
    .u64 40 (·.depth)
  ]

theorem packetHeader48_not_smallFlat :
    PacketHeader48Layout.isSmallFlatScalar = false := rfl

/-- `ldr x4, [x0, #16] ; add x4, x4, x1 ; str x4, [x0, #16] ; strb w2, [x0, #24] ; str x3, [x0, #32]` -/
def packetHeaderAdvanceCode : FnCode :=
  .atAddr "packet_header_advance" 0x200000#64
    ("f9400804 " ++ -- 0x200000: ldr x4, [x0, #16]
     "8b010084 " ++ -- 0x200004: add x4, x4, x1
     "f9000804 " ++ -- 0x200008: str x4, [x0, #16]
     "39006002 " ++ -- 0x20000c: strb w2, [x0, #24]
     "f9001003")    -- 0x200010: str x3, [x0, #32]

theorem test_packet48_auto (prog : Program) (st : State)
    (p delta items' : BitVec 64) (flags' : BitVec 8) (m : PacketHeader48)
    (hcode : packetHeaderAdvanceCode.holds prog)
    (hpc : st.pc = 0x200000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = delta)
    (hx2 : (st.readReg64 .x2).setWidth 8 = flags')
    (hx3 : st.readReg64 .x3 = items') :
    SepWP prog 0x200014#64 st (PacketHeader48Layout.own p m)
      (fun _ Pf => Pf ⊢ PacketHeader48Layout.own p
        { m with cursor := m.cursor + delta, flags := flags', items := items' }) := by
  wp_lens_auto

/-- 1-step stack epilogue reclaim on 48-byte padded `PacketHeader48Layout`. -/
theorem test_packet48_reclaim (p : BitVec 64) (m : PacketHeader48) :
    PacketHeader48Layout.own p m ⊢ memRegion p 48 :=
  PacketHeader48Layout.struct_to_memRegion p m

/-- 15-field `ArenaPageHeader` (120 bytes) exercising spine-parked opening (`> 6` fields). -/
structure ArenaPageHeader where
  f0  : BitVec 64
  f1  : BitVec 64
  f2  : BitVec 64
  f3  : BitVec 64
  f4  : BitVec 64
  f5  : BitVec 64
  f6  : BitVec 64
  f7  : BitVec 64
  f8  : BitVec 64
  f9  : BitVec 64
  f10 : BitVec 64
  f11 : BitVec 64
  f12 : BitVec 64
  f13 : BitVec 64
  f14 : BitVec 64
  deriving Inhabited, DecidableEq, Repr

def ArenaPageHeaderLayout : StructLayout ArenaPageHeader where
  totalSz := 120
  fields := [
    .u64 0   (·.f0),  .u64 8   (·.f1),  .u64 16  (·.f2),
    .u64 24  (·.f3),  .u64 32  (·.f4),  .u64 40  (·.f5),
    .u64 48  (·.f6),  .u64 56  (·.f7),  .u64 64  (·.f8),
    .u64 72  (·.f9),  .u64 80  (·.f10), .u64 88  (·.f11),
    .u64 96  (·.f12), .u64 104 (·.f13), .u64 112 (·.f14)
  ]

def arenaPageStoreF9Code : FnCode :=
  .atAddr "arena_page_store_f9" 0x200100#64
    "f9002401" -- 0x200100: str x1, [x0, #72]

theorem test_arenaPage_spine (prog : Program) (st : State)
    (p v9 : BitVec 64) (m : ArenaPageHeader)
    (hcode : arenaPageStoreF9Code.holds prog)
    (hpc : st.pc = 0x200100#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p) (hx1 : st.readReg64 .x1 = v9) :
    SepWP prog 0x200104#64 st (ArenaPageHeaderLayout.own p m)
      (fun _ Pf => Pf ⊢ ArenaPageHeaderLayout.own p { m with f9 := v9 }) := by
  wp_lens_auto

theorem test_arenaPage_reclaim (p : BitVec 64) (m : ArenaPageHeader) :
    ArenaPageHeaderLayout.own p m ⊢ memRegion p 120 :=
  ArenaPageHeaderLayout.to_memRegion p m

/-! ## 3. Multi-Width Scatter Writes into Symbolic-Index `pointsToArray` & `DecodeEntryTable` -/

/-- 16-byte heterogeneous array element (`u16` at `+0`, 2B pad at `+2`, `u32` at `+4`, `u64` at `+8`). -/
structure DecodeEntry where
  tag     : BitVec 16
  weight  : BitVec 32
  payload : BitVec 64
  deriving Inhabited, DecidableEq, Repr

def DecodeEntryLayout : StructLayout DecodeEntry where
  totalSz := 16
  fields := [
    .u16 0 (·.tag),
    .pad DecodeEntry 2 2,
    .u32 4 (·.weight),
    .u64 8 (·.payload)
  ]

/-- `add x5, x0, x1, lsl #4 ; strh w2, [x5] ; str w3, [x5, #4] ; str x4, [x5, #8]` -/
def decodeScatterMultiWidthCode : FnCode :=
  .atAddr "decode_scatter_multiwidth" 0x300000#64
    ("8b011005 " ++ -- 0x300000: add x5, x0, x1, lsl #4
     "790000a2 " ++ -- 0x300004: strh w2, [x5]
     "b90004a3 " ++ -- 0x300008: str w3, [x5, #4]
     "f90004a4")    -- 0x30000c: str x4, [x5, #8]

theorem test_scatter_array_auto (prog : Program) (st : State)
    (base : BitVec 64) (idx : Nat) (v16 : BitVec 16) (v32 : BitVec 32) (v64 : BitVec 64)
    (entries : List DecodeEntry)
    (hcode : decodeScatterMultiWidthCode.holds prog)
    (hpc : st.pc = 0x300000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = base)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx2 : (st.readReg64 .x2).setWidth 16 = v16)
    (hx3 : (st.readReg64 .x3).setWidth 32 = v32)
    (hx4 : st.readReg64 .x4 = v64)
    (hidx : idx < entries.length)
    (hov : 16 * idx < 2 ^ 64) :
    SepWP prog 0x300010#64 st (pointsToArray 16 DecodeEntryLayout.own base entries)
      (fun _ Pf => Pf ⊢ pointsToArray 16 DecodeEntryLayout.own base
        (entries.set idx { tag := v16, weight := v32, payload := v64 })) := by
  let s1 := entries.set idx { entries.getD idx default with tag := v16 }
  let s2 := s1.set idx { s1.getD idx default with weight := v32 }
  let s3 := s2.set idx { s2.getD idx default with payload := v64 }
  have hs1g : s1.getD idx default = { entries.getD idx default with tag := v16 } := by
    simp only [s1, List.getD_eq_getElem?_getD, List.getElem?_set_self hidx, Option.getD_some]
  have hs2 : s2 = entries.set idx { entries.getD idx default with tag := v16, weight := v32 } := by
    simp only [s2, hs1g, s1, List.set_set]
  have hs2g : s2.getD idx default =
      { entries.getD idx default with tag := v16, weight := v32 } := by
    simp only [hs2, List.getD_eq_getElem?_getD, List.getElem?_set_self hidx, Option.getD_some]
  have hs3 : s3 = entries.set idx { tag := v16, weight := v32, payload := v64 } := by
    change s2.set idx { s2.getD idx default with payload := v64 } = _
    rw [hs2g, hs2, List.set_set]
  rw [← hs3]
  wp_lens_auto

/-- Single-step `wp_lens_step` on `STRW` into a symbolic-index struct array element. -/
def decodeScatterStepWCode : FnCode :=
  .atAddr "decode_scatter_step_w" 0x300100#64
    ("8b011005 " ++ -- 0x300100: add x5, x0, x1, lsl #4
     "b90004a3")    -- 0x300104: str w3, [x5, #4]

theorem test_scatter_array_step (prog : Program) (st : State)
    (base : BitVec 64) (idx : Nat) (v32 : BitVec 32) (entries : List DecodeEntry)
    (hcode : decodeScatterStepWCode.holds prog)
    (hpc : st.pc = 0x300100#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = base)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx3 : (st.readReg64 .x3).setWidth 32 = v32)
    (hidx : idx < entries.length)
    (hov : 16 * idx < 2 ^ 64) :
    SepWP prog 0x300108#64 st (pointsToArray 16 DecodeEntryLayout.own base entries)
      (fun _ Pf => Pf ⊢ pointsToArray 16 DecodeEntryLayout.own base
        (entries.set idx { entries.getD idx default with weight := v32 })) := by
  wp_step
  wp_lens_step
  lens_close
  wp_done

/-- Header + trailing dynamic array `DecodeEntryTable` with scatter writes at two symbolic indices. -/
structure DecodeEntryTable where
  hdr0    : BitVec 32
  hdr4    : BitVec 32
  entries : List (BitVec 64)
  deriving Inhabited, DecidableEq, Repr

def DecodeEntryTableLayout : StructLayout DecodeEntryTable where
  totalSz := 12
  fields := [
    .u32 0 (·.hdr0),
    .u32 4 (·.hdr4),
    .pad DecodeEntryTable 8 4,
    .dynArray 12 8 (fun a v => a ↦₆₄ v) (·.entries)
  ]

/-- `add x5, x0, #12 ; str x3, [x5, x1, lsl #3] ; str x4, [x5, x2, lsl #3]` -/
def decodeTableScatter2Code : FnCode :=
  .atAddr "decode_table_scatter2" 0x300200#64
    ("91003005 " ++ -- 0x300200: add x5, x0, #12
     "f82178a3 " ++ -- 0x300204: str x3, [x5, x1, lsl #3]
     "f82278a4")    -- 0x300208: str x4, [x5, x2, lsl #3]

theorem test_decodeTable_scatter2 (prog : Program) (st : State)
    (tblPtr v0 v1 : BitVec 64) (p0 p1 : Nat) (m : DecodeEntryTable)
    (hcode : decodeTableScatter2Code.holds prog)
    (hpc : st.pc = 0x300200#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = tblPtr)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 p0)
    (hx2 : st.readReg64 .x2 = BitVec.ofNat 64 p1)
    (hx3 : st.readReg64 .x3 = v0)
    (hx4 : st.readReg64 .x4 = v1)
    (hp0 : p0 < m.entries.length) (hp0_ov : 8 * p0 < 2 ^ 64)
    (hp1 : p1 < m.entries.length) (hp1_ov : 8 * p1 < 2 ^ 64) :
    SepWP prog 0x30020c#64 st (DecodeEntryTableLayout.own tblPtr m)
      (fun _ Pf => Pf ⊢ DecodeEntryTableLayout.own tblPtr
        { m with entries := (m.entries.set p0 v0).set p1 v1 }) := by
  wp_lens_auto

/-- Algebraic `LawfulSepLens.trans` composition check over nested pure snapshots. -/
structure OuterBox where
  pt       : SmallPoint2D
  metaWord : BitVec 64
  deriving Inhabited, DecidableEq, Repr

def OuterBoxRep (p : BitVec 64) (b : OuterBox) : SepProp :=
  SmallPoint2DLayout.own p b.pt ∗ ((p + 24#64) ↦₆₄ b.metaWord)

theorem outerBox_pt_lawful (p : BitVec 64) :
    LawfulSepLens (OuterBoxRep p) (SmallPoint2DLayout.own p)
      (fun b => (p + 24#64) ↦₆₄ b.metaWord)
      (·.pt) (fun b pt' => { b with pt := pt' }) where
  open_entails _ := Entails.refl _
  close_entails _ _ := Entails.refl _
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

theorem test_lawful_lens_trans (p : BitVec 64) :
    LawfulSepLens (OuterBoxRep p) (fun v => (p + 8#64) ↦₆₄ v)
      (fun b => ((p + 24#64) ↦₆₄ b.metaWord) ∗ SmallPoint2DLayout.hole 1 p b.pt)
      (fun b => b.pt.y)
      (fun b y' => { b with pt := { b.pt with y := y' } }) :=
  (outerBox_pt_lawful p).trans
    (SmallPoint2DLayout.lawfulFieldLens 1 p (fun v => (p + 8#64) ↦₆₄ v)
      (·.y) (fun m y' => { m with y := y' }))

/-! ## 4. Width-Polymorphic `OwnByteMap` (`u8`/`u16`/`u32`/`u64`) Loads, Stores, & `put_get` -/

/-- `strb w1, [x0] ; strh w2, [x0, #2] ; str w3, [x0, #4] ; str x4, [x0, #8]` -/
def byteMapStoreCode : FnCode :=
  .atAddr "bytemap_multiwidth_store" 0x400000#64
    ("39000001 " ++ -- 0x400000: strb w1, [x0]
     "79000402 " ++ -- 0x400004: strh w2, [x0, #2]
     "b9000403 " ++ -- 0x400008: str w3, [x0, #4]
     "f9000404")    -- 0x40000c: str x4, [x0, #8]

abbrev byteMapAfter4 (bv : BitVec 64 → BitVec 8) (p : BitVec 64)
    (v8 : BitVec 8) (v16 : BitVec 16) (v32 : BitVec 32) (v64 : BitVec 64) :
    BitVec 64 → BitVec 8 :=
  let bv1 := writeMapBytes bv p [v8]
  let bv2 := writeMapBytes bv1 (p + 2#64) (ProofLib.ByteSlice.unpackLE 2 v16)
  let bv3 := writeMapBytes bv2 (p + 4#64) (ProofLib.ByteSlice.unpackLE 4 v32)
  writeMapBytes bv3 (p + 8#64) (ProofLib.ByteSlice.unpackLE 8 v64)

theorem test_byteMap_stores
    (prog : Program) (st : State) (dom : BitVec 64 → Bool) (bv : BitVec 64 → BitVec 8)
    (p : BitVec 64) (v8 : BitVec 8) (v16 : BitVec 16) (v32 : BitVec 32) (v64 : BitVec 64)
    (hcode : byteMapStoreCode.holds prog)
    (hpc : st.pc = 0x400000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hx1 : st.readReg64 .x1 = v8.setWidth 64)
    (hx2 : st.readReg64 .x2 = v16.setWidth 64)
    (hx3 : st.readReg64 .x3 = v32.setWidth 64)
    (hx4 : st.readReg64 .x4 = v64)
    (hb : p.toNat + 16 ≤ 2 ^ 64)
    (hdom : ∀ a, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → dom a = true) :
    SepWP prog 0x400010#64 st (OwnByteMap dom bv)
      (fun _ Pf => Pf ⊢ OwnByteMap dom (byteMapAfter4 bv p v8 v16 v32 v64)) := by
  wp_lens_auto

/-- `ldrb w1, [x0] ; ldr w2, [x0, #4] ; ldr x3, [x0, #8]` exercising read-only `u8`/`u32`/`u64`
    loads and automatic lawful `put_get` re-closure back to unchanged `OwnByteMap dom bv`. -/
def byteMapMultiLoadCode : FnCode :=
  .atAddr "bytemap_multiwidth_load" 0x400100#64
    ("39400001 " ++ -- 0x400100: ldrb w1, [x0]
     "b9400402 " ++ -- 0x400104: ldr w2, [x0, #4]
     "f9400403")    -- 0x400108: ldr x3, [x0, #8]

theorem test_byteMap_loads_ro
    (prog : Program) (st : State) (dom : BitVec 64 → Bool) (bv : BitVec 64 → BitVec 8)
    (p : BitVec 64)
    (hcode : byteMapMultiLoadCode.holds prog)
    (hpc : st.pc = 0x400100#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hb : p.toNat + 16 ≤ 2 ^ 64)
    (hdom : ∀ a, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → dom a = true) :
    SepWP prog 0x40010c#64 st (OwnByteMap dom bv)
      (fun sf Pf => (Pf ⊢ OwnByteMap dom bv) ∧
        sf.readReg64 .x3 = ProofLib.ByteSlice.readLE (readMapBytes bv (p + 8#64) 8) 0 8) := by
  wp_lens_auto

/-- Explicit `lens_open` + `wp_step` + `lens_close` read-only round-trip on `OwnByteMap`. -/
def byteMapSingleLoad64Code : FnCode :=
  .atAddr "bytemap_load64" 0x400200#64
    "f9400401" -- 0x400200: ldr x1, [x0, #8]

theorem test_byteMap_manual_ro
    (prog : Program) (st : State) (dom : BitVec 64 → Bool) (bv : BitVec 64 → BitVec 8)
    (p : BitVec 64)
    (hcode : byteMapSingleLoad64Code.holds prog)
    (hpc : st.pc = 0x400200#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = p)
    (hb : p.toNat + 16 ≤ 2 ^ 64)
    (hdom : ∀ a, p.toNat ≤ a.toNat → a.toNat < p.toNat + 16 → dom a = true) :
    SepWP prog 0x400204#64 st (OwnByteMap dom bv)
      (fun sf Pf => (Pf ⊢ OwnByteMap dom bv) ∧
        sf.readReg64 .x1 = ProofLib.ByteSlice.readLE (readMapBytes bv (p + 8#64) 8) 0 8) := by
  lens_open
  wp_step
  lens_close
  wp_done

/-! ## 5. Downward `slotsDownFrom` Bucket Store + Double Byte-Slice Window Switch -/

/-- Pure snapshot of a hash-bucket slot table (`slots` below `ctrlPtr`, `ctrl` bytes at `ctrlPtr`). -/
structure BucketSlotSnap where
  len        : BitVec 64
  growthLeft : BitVec 64
  slots      : List (BitVec 64 × BitVec 64)
  ctrl       : List (BitVec 8)
  deriving Inhabited, DecidableEq, Repr

def BucketSlotTable (tblPtr ctrlPtr bucketMask : BitVec 64) (allocMeta : SepProp)
    (w : BucketSlotSnap) : SepProp :=
  (tblPtr ↦₆₄ ctrlPtr) ∗
  ((tblPtr + 8#64) ↦₆₄ bucketMask) ∗
  ((tblPtr + 16#64) ↦₆₄ w.len) ∗
  ((tblPtr + 24#64) ↦₆₄ w.growthLeft) ∗
  allocMeta ∗
  slotsDownFrom ctrlPtr w.slots ∗
  (ctrlPtr ↦ₛ w.ctrl)

@[sep_lens]
theorem bucketSlotTable_slots_lens (tblPtr ctrlPtr bucketMask : BitVec 64) (allocMeta : SepProp) :
    LawfulSepLens (BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta)
      (slotsDownFrom ctrlPtr)
      (fun w => (tblPtr ↦₆₄ ctrlPtr) ∗ ((tblPtr + 8#64) ↦₆₄ bucketMask) ∗
        ((tblPtr + 16#64) ↦₆₄ w.len) ∗ ((tblPtr + 24#64) ↦₆₄ w.growthLeft) ∗
        allocMeta ∗ (ctrlPtr ↦ₛ w.ctrl))
      (·.slots)
      (fun w s' => { w with slots := s' }) where
  open_entails _ := by unfold BucketSlotTable; refine Entails.of_eq ?_; ac_rfl
  close_entails _ _ := by unfold BucketSlotTable; refine Entails.of_eq ?_; ac_rfl
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

@[sep_lens]
theorem bucketSlotTable_ctrl_lens (tblPtr ctrlPtr bucketMask : BitVec 64) (allocMeta : SepProp) :
    LawfulSepLens (BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta)
      (pointsToBytes ctrlPtr)
      (fun w => (tblPtr ↦₆₄ ctrlPtr) ∗ ((tblPtr + 8#64) ↦₆₄ bucketMask) ∗
        ((tblPtr + 16#64) ↦₆₄ w.len) ∗ ((tblPtr + 24#64) ↦₆₄ w.growthLeft) ∗
        allocMeta ∗ slotsDownFrom ctrlPtr w.slots)
      (·.ctrl)
      (fun w c' => { w with ctrl := c' }) where
  open_entails _ := by unfold BucketSlotTable; refine Entails.of_eq ?_; ac_rfl
  close_entails _ _ := by unfold BucketSlotTable; refine Entails.of_eq ?_; ac_rfl
  put_get _ := rfl
  get_put _ _ := rfl
  put_put _ _ _ := rfl

/-- `sub x6, x0, x1, lsl #4 ; stp x3, x4, [x6, #-16] ; strb w2, [x0, x1] ; strb w2, [x0, x7]` -/
def bucketSlotInsertCode : FnCode :=
  .atAddr "bucket_slot_insert" 0x500000#64
    ("cb011006 " ++ -- 0x500000: sub x6, x0, x1, lsl #4
     "a93f10c3 " ++ -- 0x500004: stp x3, x4, [x6, #-16]
     "38216802 " ++ -- 0x500008: strb w2, [x0, x1]
     "38276802")    -- 0x50000c: strb w2, [x0, x7]

theorem test_bucketTable_auto
    (prog : Program) (st : State) (tblPtr ctrlPtr bucketMask key val : BitVec 64)
    (tag : BitVec 8) (idx mirror : Nat) (allocMeta : SepProp) (w : BucketSlotSnap)
    (hcode : bucketSlotInsertCode.holds prog)
    (hpc : st.pc = 0x500000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = ctrlPtr)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx7 : st.readReg64 .x7 = BitVec.ofNat 64 mirror)
    (hx2 : (st.readReg64 .x2).setWidth 8 = tag)
    (hx3 : st.readReg64 .x3 = key)
    (hx4 : st.readReg64 .x4 = val)
    (hidx : idx < w.slots.length) (h16 : idx * 16 < 2 ^ 64)
    (hc_idx : idx + 1 ≤ w.ctrl.length)
    (hc_mir : mirror + 1 ≤ w.ctrl.length) :
    SepWP prog 0x500010#64 st (BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta w)
      (fun _ Pf => Pf ⊢ BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta
        { w with
          slots := w.slots.set idx (key, val),
          ctrl := ProofLib.ByteSlice.write
            (ProofLib.ByteSlice.write w.ctrl idx [tag]) mirror [tag] }) := by
  wp_lens_auto

theorem test_bucketTable_switch
    (prog : Program) (st : State) (tblPtr ctrlPtr bucketMask key val : BitVec 64)
    (tag : BitVec 8) (idx mirror : Nat) (allocMeta : SepProp) (w : BucketSlotSnap)
    (hcode : bucketSlotInsertCode.holds prog)
    (hpc : st.pc = 0x500000#64) (hrun : st.status = .Running)
    (hx0 : st.readReg64 .x0 = ctrlPtr)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 idx)
    (hx7 : st.readReg64 .x7 = BitVec.ofNat 64 mirror)
    (hx2 : (st.readReg64 .x2).setWidth 8 = tag)
    (hx3 : st.readReg64 .x3 = key)
    (hx4 : st.readReg64 .x4 = val)
    (hidx : idx < w.slots.length) (h16 : idx * 16 < 2 ^ 64)
    (hc_idx : idx + 1 ≤ w.ctrl.length)
    (hc_mir : mirror + 1 ≤ w.ctrl.length) :
    SepWP prog 0x500010#64 st (BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta w)
      (fun _ Pf => Pf ⊢ BucketSlotTable tblPtr ctrlPtr bucketMask allocMeta
        { w with
          slots := w.slots.set idx (key, val),
          ctrl := ProofLib.ByteSlice.write
            (ProofLib.ByteSlice.write w.ctrl idx [tag]) mirror [tag] }) := by
  wp_step
  lens_open
  wp_step
  lens_switch
  wp_step
  lens_switch
  wp_step
  lens_close
  wp_done

/-! ## 6. Negative Soundness Tests (`#guard_msgs` & `fail_if_success`) -/

/-- Overlapping fields (`[0, 8)` and `[4, 12)`) must be rejected by `StructLayout.wf` and `lens_open`. -/
structure BadPair where
  a : BitVec 64
  b : BitVec 64
  deriving Inhabited, DecidableEq, Repr

def OverlappingPairLayout : StructLayout BadPair where
  totalSz := 16
  fields := [
    .u64 0 (·.a),
    .u64 4 (·.b)
  ]

theorem overlappingPairLayout_wf_false :
    OverlappingPairLayout.wf = false := rfl

theorem overlappingPairLayout_not_smallFlat :
    OverlappingPairLayout.isSmallFlatScalar = false := rfl

/-- is ill-formed (overlapping or out-of-bounds fields) -/
#guard_msgs (error, substring := true) in
example (prog : Program) (st : State) (p : BitVec 64) (m : BadPair) :
    SepWP prog st.pc st (OverlappingPairLayout.own p m) (fun _ _ => True) := by
  lens_open at p width 8

example (prog : Program) (st : State) (p : BitVec 64) (m : BadPair) : True := by
  fail_if_success
    have : OverlappingPairLayout.own p m ⊢ memRegion p 16 :=
      OverlappingPairLayout.struct_to_memRegion p m
  fail_if_success
    have : SepWP prog (st.pc + 4#64) st (OverlappingPairLayout.own p m) (fun _ _ => True) := by
      wp_lens_step
  trivial

/-- Out-of-bounds field (`8 + 8 = 16 > totalSz = 12`) must be rejected by `StructLayout.wf` and `lens_open`. -/
def OutOfBoundsFieldLayout : StructLayout BadPair where
  totalSz := 12
  fields := [
    .u64 0 (·.a),
    .u64 8 (·.b)
  ]

theorem outOfBoundsFieldLayout_wf_false :
    OutOfBoundsFieldLayout.wf = false := rfl

/-- is ill-formed (overlapping or out-of-bounds fields) -/
#guard_msgs (error, substring := true) in
example (prog : Program) (st : State) (p : BitVec 64) (m : BadPair) :
    SepWP prog st.pc st (OutOfBoundsFieldLayout.own p m) (fun _ _ => True) := by
  lens_open at (p + 8#64) width 8

-- Runtime out-of-bounds slice access (`off + 8 ≤ bs.length` unprovable) must be rejected by `lens_open`.
/-- lens_open: no composite predicate in spine owns address -/
#guard_msgs (error, substring := true) in
example (prog : Program) (st : State) (p : BitVec 64) (bs : List (BitVec 8)) (off : Nat) :
    SepWP prog st.pc st (p ↦ₛ bs) (fun _ _ => True) := by
  lens_open at (p + BitVec.ofNat 64 off) width 8

-- Unmatching base address (`otherPtr + 16#64` vs `PacketHeader48Layout.own p m`) must be rejected.
/-- lens_open: no composite predicate in spine owns address -/
#guard_msgs (error, substring := true) in
example (prog : Program) (st : State) (p otherPtr : BitVec 64) (m : PacketHeader48) :
    SepWP prog st.pc st (PacketHeader48Layout.own p m) (fun _ _ => True) := by
  lens_open at (otherPtr + 16#64) width 8

/-! ## 7. Kernel Axiom Audits (`#guard_msgs` `#print axioms`) -/

/-- info: 'Testing.SepLensNoOpen.test_no_open_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Testing.SepLensNoOpen.test_no_open_auto

/-- info: 'Testing.SepLens.test_smallPoint_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_smallPoint_auto

/-- info: 'Testing.SepLens.test_packet48_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_packet48_auto

/-- info: 'Testing.SepLens.test_packet48_reclaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_packet48_reclaim

/-- info: 'Testing.SepLens.test_scatter_array_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_scatter_array_auto

/-- info: 'Testing.SepLens.test_decodeTable_scatter2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_decodeTable_scatter2

/-- info: 'Testing.SepLens.test_byteMap_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_byteMap_stores

/-- info: 'Testing.SepLens.test_byteMap_loads_ro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_byteMap_loads_ro

/-- info: 'Testing.SepLens.test_bucketTable_auto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms test_bucketTable_auto

end Testing.SepLens

end
