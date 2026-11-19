/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import ProofLib.Hoare.SubroutineHook
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cells
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.GhostToken
public import VerifiedLibraries.Mallocng.Proofs.Defs
public import VerifiedLibraries.Mallocng.Proofs.Cost.GroupTable

/-!
# Layered `mallocng` Heap Invariant and `MallocngIface` Witness

Defines the L0-L5 machine-level heap well-formedness predicates (`MallocngWFInflight`, `MallocngWF`),
the sealed separation-logic invariants (`MallocngCoreImpl`, `MallocngHeapImpl`), and the concrete
`mallocngIface : MallocngIface` witness together with its startup, runtime-split, and read-only-split
laws.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Helper Predicates for `MallocngWF` -/

/-- Auxiliary `svc` handler used inside `SVC #0`-free instruction segments (`SepWP.lift_noSyscalls`). -/
def mallocngFaultSvc (s : State) : State :=
  s.setStatus (.Exception "unexpected SVC")

def allMetaSlots (st : MallocngSt) : List (BitVec 64) :=
  st.metaAreas.flatMap fun ma => (List.range 101).map ma.slotAddr

def slotEffCost : SlotState → Nat
  | .liveUser _ _ effCost => effCost
  | _ => 0

def SlotState.isFree : SlotState → Bool
  | .freeAvail | .freeInactive => true
  | _ => false

def SlotState.isClaimed : SlotState → Bool
  | .claimed => true
  | _ => false

def totalClaimedSlots (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.filter SlotState.isClaimed).length).sum

def GroupDesc.isEmpty (g : GroupDesc) : Bool :=
  g.slots.all SlotState.isFree

def totalLiveEffCost (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotEffCost).sum).sum

def slotLiveCount : SlotState → Nat
  | .liveUser _ _ _ => 1
  | _ => 0

def totalLiveCount (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotLiveCount).sum).sum

def PairwiseDisjointRegions : List (BitVec 64 × Nat) → Prop
  | [] => True
  | (b, n) :: rest =>
    (∀ x ∈ rest, DisjointRegions b n x.1 x.2) ∧ PairwiseDisjointRegions rest

def dynamicRootRegions (st : MallocngSt) : List (BitVec 64 × Nat) :=
  st.metaAreas.map (fun ma => (ma.base, 4096)) ++
  st.guardPages.map (fun gp => (gp, 4096)) ++
  st.availMetaPages.map (fun ap => (ap, 4096)) ++
  (st.groups.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))

def MallocngCountIvsWF (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (st : MallocngSt) : Prop :=
  b.liveCount ≤ b.peakCount ∧
  totalLiveCount st ≤ b.liveCount ∧
  ivs = dynamicRootRegions st ∧
  ivs.length ≤ 48 + 2 * b.peakCount ∧
  st.metaAreas.length ≤ 1 + (88 + 8 * b.peakCount) / 101 ∧
  Cost.GroupsGrpBound (b.peakCount + 6) st.groups

/-- Well-formedness of slot `idx` inside `g` (`L3` bitmaps and in-band `IB = 4` headers/trailers). -/
def SlotWf (st : MallocngSt) (g : GroupDesc) (idx : Nat) (s : SlotState) : Prop :=
  let start := g.slotStart idx
  let slotEnd := g.slotEnd idx
  st.byteVal (start - 4#64) = 0#8 ∧
  (g.availMask.getLsbD idx = true ↔ s = .freeAvail) ∧
  (g.freedMask.getLsbD idx = true ↔ s = .freeInactive) ∧
  (g.activeIdx < idx → s = .freeInactive) ∧
  match s with
  | .freeAvail | .freeInactive | .claimed => True
  | .liveNested cm =>
    g.sc < 48 ∧
    ∃ cg ∈ st.groups,
      cg.metaPtr = cm ∧ cg.parentMeta = some g.metaPtr ∧
      start.toNat ≤ cg.mem.toNat ∧
      (cg.mem.toNat - start.toNat) % 16 = 0 ∧
      cg.mem.toNat + cg.nestedCap ≤ slotEnd.toNat ∧
      cg.nestedCap = slotStride g.sc - 4 ∧
      let totalOffUnits := (cg.mem.toNat - g.storage.toNat) / 16
      totalOffUnits ≤ 0xffff ∧
      st.byteVal (cg.mem - 4#64) = 0#8 ∧
      st.byteVal (cg.mem - 3#64) = BitVec.ofNat 8 ((6 <<< 5) ||| idx) ∧
      readBytesFromMap st.byteVal (cg.mem - 2#64) 2 =
        unpack16 (BitVec.ofNat 16 totalOffUnits)
  | .liveUser userPtr reqSize effCost =>
    MallocngBlockWf userPtr reqSize ∧
    start.toNat ≤ userPtr.toNat ∧
    userPtr.toNat + reqSize ≤ slotEnd.toNat ∧
    let offBytes := userPtr.toNat - start.toNat
    let totalOffUnits := (userPtr.toNat - g.storage.toNat) / 16
    let reserved := slotEnd.toNat - (userPtr.toNat + reqSize)
    let r5 := min reserved 5
    max reqSize MallocngMinBlockCost ≤ effCost ∧
    (offBytes ≤ (effCost - max reqSize MallocngMinBlockCost) + 255 * 16 ∧
      effCost - max reqSize MallocngMinBlockCost ≤ MaxAlignedAllocAlign - 16 ∧
      effCost - max reqSize MallocngMinBlockCost ≤ st.liveMap.ov userPtr) ∧
    reserved < 2 ^ 31 ∧
    ((2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < effCost) ∧
      (g.sc < 48 → totalOffUnits < (idx + 1) * sizeClass g.sc)) ∧
    (g.sc = 63 → g.maplen * 4096 ≤ effCost + 8195) ∧
    st.byteVal (userPtr - 3#64) = BitVec.ofNat 8 ((r5 <<< 5) ||| idx) ∧
    (if totalOffUnits ≤ 0xffff then
       st.byteVal (userPtr - 4#64) = 0#8 ∧
       readBytesFromMap st.byteVal (userPtr - 2#64) 2 =
         unpack16 (BitVec.ofNat 16 totalOffUnits)
     else
       g.sc = 63 ∧ idx = 0 ∧ totalOffUnits < 2 ^ 27 ∧
       st.byteVal (userPtr - 4#64) = 1#8 ∧
       readBytesFromMap st.byteVal (userPtr - 2#64) 2 = [0#8, 0#8] ∧
       readBytesFromMap st.byteVal (userPtr - 8#64) 4 =
         unpack32 (BitVec.ofNat 32 totalOffUnits)) ∧
    (1 ≤ reserved → st.byteVal (userPtr + BitVec.ofNat 64 reqSize) = 0#8) ∧
    (5 ≤ reserved →
       st.byteVal (slotEnd - 5#64) = 0#8 ∧
       readBytesFromMap st.byteVal (slotEnd - 4#64) 4 =
         unpack32 (BitVec.ofNat 32 reserved))

/-- Well-formedness of a single active `GroupDesc` (`L2` + `L3`). -/
def GroupWf (st : MallocngSt) (g : GroupDesc) : Prop :=
  (g.sc < 48 ∨ g.sc = 63) ∧
  g.lastIdx ≤ 31 ∧
  g.slots.length = g.cnt ∧
  (g.sc = 63 → g.lastIdx = 0 ∧ 0 < g.maplen ∧ g.prev = 0#64 ∧ g.next = 0#64) ∧
  4096 ≤ g.mem.toNat ∧
  g.mem.toNat % 16 = 0 ∧
  g.mem.toNat + g.totalBytes ≤ 2 ^ 48 ∧
  12 + g.cnt * g.stride ≤ g.totalBytes ∧
  (0 < g.maplen → 12 + g.cnt * g.stride < g.totalBytes) ∧
  st.byteVal (g.slotEnd g.lastIdx) = 0#8 ∧
  (0 < g.maplen ↔ g.parentMeta = none) ∧
  (0 < g.maplen →
    g.mem.toNat % 4096 = 0 ∧ g.nestedCap = 0 ∧
    (g.sc ≤ 25 → g.maplen * 4096 ≤ 65536) ∧
    (g.sc < 48 → g.maplen * 4096 ≤ 1048576 ∧
      (g.lastIdx = 0 → g.stride ≤ slotStride g.sc ∨
        (24 ≤ g.sc ∧ g.maplen * 4096 = pageAlignUp (slotStride g.sc + 16))))) ∧
  (g.maplen = 0 →
    1 ≤ g.lastIdx ∧
    ∃ pg ∈ st.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
      g.parentMeta = some pg.metaPtr ∧
      pg.sc < 48 ∧ g.sc < pg.sc ∧
      pg.sc ≤ 24 ∧
      pg.slots[pIdx]'hp = .liveNested g.metaPtr ∧
      (pg.slotStart pIdx).toNat ≤ g.mem.toNat ∧
      g.mem.toNat + g.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
      g.nestedCap = slotStride pg.sc - 4) ∧
  g.availMask &&& g.freedMask = 0#32 ∧
  (g.availMask ||| g.freedMask).toNat < 2 ^ g.cnt ∧
  g.activeIdx ≤ g.lastIdx ∧
  readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes ∧
  readBytesFromMap st.byteVal g.mem 8 = unpack64 g.metaPtr ∧
  st.byteVal (g.mem + 8#64) = g.activeByte ∧
  ∀ idx : Nat, (hIdx : idx < g.slots.length) → SlotWf st g idx (g.slots[idx]'hIdx)

def findGroupByMeta (st : MallocngSt) (m : BitVec 64) : Option GroupDesc :=
  st.groups.find? (·.metaPtr == m)

/-- Well-formedness of `ctx.active[sc]` (`L4`) for size class `sc < 48`. -/
def ActiveClassWf (st : MallocngSt) (sc : Nat) (head : BitVec 64) (ms : List (BitVec 64)) : Prop :=
  (∀ m ∈ ms, ∃ g ∈ st.groups, g.metaPtr = m ∧ g.sc = sc) ∧
  CircularDllWf head
    (ms.filterMap fun m =>
      (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)) ∧
  (ms.filterMap fun m => (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)).length =
    ms.length ∧
  (∀ g ∈ st.groups, g.sc = sc →
    (g.metaPtr ∉ ms ↔ (g.prev = 0#64 ∧ g.next = 0#64)) ∧
    (g.metaPtr ∉ ms → g.availMask = 0#32 ∧ g.freedMask = 0#32 ∧ g.activeIdx = g.lastIdx)) ∧
  (∀ i : Nat, (hi : i < ms.length) → 0 < i →
    ∀ g ∈ st.groups, g.metaPtr = ms[i]'hi → g.availMask = 0#32 ∧ g.freedMask ≠ 0#32) ∧
  (∀ g₁ ∈ st.groups, ∀ g₂ ∈ st.groups,
    g₁.sc = sc → g₂.sc = sc →
    g₁.activeIdx < g₁.lastIdx → g₂.activeIdx < g₂.lastIdx → g₁.metaPtr = g₂.metaPtr) ∧
  (∀ g ∈ st.groups, g.sc = sc → g.activeIdx < g.lastIdx → g.metaPtr ∈ ms ∧ 0 < sc)

/-! ## Layered Heap Invariant (`MallocngWFInflight` and `MallocngWF`) -/

/-- Machine-level heap invariant (`L0`-`L5` and virtual-memory accounting) for `mallocng` loaded at
    `base` with break segment `[brkStart, brk)`, cost counters `(liveCost, peakCost)`, and at most
    `inflight` carved-out `40`-byte `struct meta` slots (`inflight = 0` at API boundaries). -/
structure MallocngWFInflight (inflight : Nat) (base brkStart brk : BitVec 64)
    (liveCost peakCost : Nat) (st : MallocngSt) : Prop where
  /-- `L0`: break segment alignment/bounds (`MallocngBrkStartWf brkStart`). -/
  base_wf : True
  brk_bounds :
    0x10000 ≤ brkStart.toNat ∧
    brkStart.toNat % 4096 = 0 ∧
    brk.toNat % 4096 = 0 ∧
    brkStart.toNat ≤ brk.toNat ∧
    brk.toNat ≤ 2 ^ 48
  /-- `L0`: fixed array lengths inside `struct malloc_context`. -/
  ctx_lens :
    st.ctx.active.length = 48 ∧
    st.ctx.usageByClass.length = 48 ∧
    st.ctx.unmapSeq.length = 32 ∧
    st.ctx.bounces.length = 32 ∧
    st.ctx.seqPad = List.replicate 7 0#8 ∧
    st.activeLists.length = 48
  /-- `L0`: `init_done ∈ {0, 1}`, and when `0` the entire dynamic state is empty. -/
  initDone_wf : st.ctx.initDone = 0#32 ∨ st.ctx.initDone = 1#32
  initZero_wf :
    st.ctx.initDone = 0#32 →
      st.ctx = { emptyCtxFields with seq := st.ctx.seq } ∧
      st.metaAreas = [] ∧ st.mmapMetaAreas = [] ∧
      st.guardPages = [] ∧ st.mmapGuardPages = [] ∧
      st.availMetaPages = [] ∧ st.freeMetas = [] ∧
      st.bumpMetas = [] ∧ st.reservedMetas = [] ∧
      st.groups = [] ∧ st.masterDom = [] ∧ brk = brkStart
  /-- `L0`: bounce counters capped at `150` and `usage_by_class[sc]` equals total slots in `sc`. -/
  bounces_wf : ∀ b ∈ st.ctx.bounces, b.toNat ≤ 150
  usage_wf :
    ∀ sc : Nat, (hsc : sc < st.ctx.usageByClass.length) →
      (st.ctx.usageByClass[sc]'hsc).toNat =
        ((st.groups.filter (·.sc == sc)).map GroupDesc.cnt).sum
  /-- `L0`/`L1`: `brk` state vs `mmap` fallback (`ctx.brk == -1`). -/
  brk_mode_wf :
    (st.ctx.initDone = 1#32 ∧ st.ctx.brk ≠ (-1#64) →
      st.ctx.brk = brk ∧
      brkStart.toNat + 8192 ≤ brk.toNat ∧
      st.ctx.availMetaAreaCount = 0#64 ∧
      st.ctx.metaAllocShift = 0#64 ∧
      st.availMetaPages = []) ∧
    st.mmapMetaAreas =
      (st.metaAreas.map (·.base)).filter (fun mb => !decide (InRegion brkStart (brk.toNat - brkStart.toNat) mb)) ∧
    st.mmapGuardPages =
      st.guardPages.filter (fun gp => !decide (InRegion brkStart (brk.toNat - brkStart.toNat) gp)) ∧
    (brkStart.toNat < brk.toNat →
      brkStart ∈ st.guardPages ∧
      ∀ k : Nat, 1 ≤ k → k < (brk.toNat - brkStart.toNat) / 4096 →
        ∃ ma ∈ st.metaAreas, ma.base = brkStart + BitVec.ofNat 64 (4096 * k))
  /-- `L1`: `meta_area` pages, chain links, headers (`check == secret`, `nslots == 101`),
      `avail_meta_areas`, `guardPages`, `freeMetas`, `bumpMetas`, `reservedMetas`, and exact
      `101`-slot partition. -/
  metaAreas_wf :
    (st.metaAreas.map (·.base)).Nodup ∧
    (∀ ma ∈ st.metaAreas,
      4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48 ∧
      readBytesFromMap st.byteVal ma.base 24 =
        unpack64 st.ctx.secret ++ unpack64 ma.next ++ unpack32 101#32 ++ unpack32 0#32) ∧
    (match st.metaAreas with
     | [] => st.ctx.metaAreaHead = 0#64 ∧ st.ctx.metaAreaTail = 0#64
     | hd :: _ =>
       st.ctx.metaAreaHead = hd.base ∧
       (∀ hne : st.metaAreas ≠ [],
         st.ctx.metaAreaTail = (st.metaAreas.getLast hne).base ∧
         (st.metaAreas.getLast hne).next = 0#64) ∧
       ∀ i : Nat, (hi : i + 1 < st.metaAreas.length) →
         (st.metaAreas[i]'(Nat.lt_of_succ_lt hi)).next = (st.metaAreas[i + 1]'hi).base)
  guard_avail_wf :
    st.guardPages.Nodup ∧
    (∀ gp ∈ st.guardPages, 4096 ≤ gp.toNat ∧ gp.toNat % 4096 = 0 ∧ gp.toNat + 4096 ≤ 2 ^ 48) ∧
    st.availMetaPages =
      (List.range st.ctx.availMetaAreaCount.toNat).map
        (fun i => st.ctx.availMetaAreas + BitVec.ofNat 64 (4096 * i)) ∧
    (∀ ap ∈ st.availMetaPages,
      4096 ≤ ap.toNat ∧ ap.toNat % 4096 = 0 ∧ ap.toNat + 4096 ≤ 2 ^ 48 ∧
      readBytesFromMap st.byteVal ap 4096 = List.replicate 4096 0#8)
  inflight_wf : st.reservedMetas.length + totalClaimedSlots st ≤ inflight
  free_bump_metas_wf :
    CircularDllWf st.ctx.freeMetaHead
      (st.freeMetas.map fun fm => (fm.ptr, fm.prev, fm.next)) ∧
    (∀ fm ∈ st.freeMetas, readBytesFromMap st.byteVal fm.ptr 40 = fm.toBytes) ∧
    ((st.ctx.availMetaCount = 0#64 ∧ st.bumpMetas = []) ∨
     (0 < st.ctx.availMetaCount.toNat ∧ st.ctx.availMetaCount.toNat ≤ 101 ∧
      ∃ hne : st.metaAreas ≠ [],
        let tail := st.metaAreas.getLast hne
        let k0 := 101 - st.ctx.availMetaCount.toNat
        st.ctx.availMeta = tail.slotAddr k0 ∧
        st.bumpMetas = (List.range st.ctx.availMetaCount.toNat).map (fun j => tail.slotAddr (k0 + j)))) ∧
    (∀ bm ∈ st.bumpMetas, readBytesFromMap st.byteVal bm 40 = List.replicate 40 0#8) ∧
    let usedAndFree :=
      st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
    usedAndFree.Nodup ∧
    (∀ m, m ∈ usedAndFree ↔ m ∈ allMetaSlots st)
  /-- `L2` and `L3`: active groups, nesting forest, and pairwise disjointness of root regions. -/
  groups_nodup : (st.groups.map (·.metaPtr)).Nodup ∧ (st.groups.map (·.mem)).Nodup
  groups_wf : ∀ g ∈ st.groups, GroupWf st g
  regions_disjoint :
    PairwiseDisjointRegions (dynamicRootRegions st) ∧ True
  /-- `L4`: `ctx.active[0..47]` circular DLLs. -/
  active_wf :
    ∀ sc : Nat, (h1 : sc < st.ctx.active.length) → (h2 : sc < st.activeLists.length) →
      ActiveClassWf st sc (st.ctx.active[sc]'h1) (st.activeLists[sc]'h2)
  /-- `L5`: ghost live map correspondence. -/
  liveMap_wf :
    ∀ (p : BitVec 64) (n : Nat),
      st.liveMap p = some n ↔
        ∃ g ∈ st.groups, ∃ idx : Nat, ∃ hIdx : idx < g.slots.length, ∃ effCost : Nat,
          g.slots[idx]'hIdx = .liveUser p n effCost
  /-- `L5` and accounting: cost monotonicity, `effCost` sum, structural page/empty-group bounds, and
      `masterDom` coverage within `dynamicRootRegions`. -/
  live_le_peak : liveCost ≤ peakCost
  effCost_le_live : totalLiveEffCost st ≤ liveCost
  meta_pages_bound :
    st.metaAreas.length ≤ 2 + peakCost / 655360 ∧
    (st.ctx.metaAllocShift = 0#64 → st.availMetaPages = [] ∧ st.guardPages.length ≤ 1) ∧
    (∀ m : Nat, 1 ≤ m → st.ctx.metaAllocShift.toNat = m →
      m ≤ 40 ∧ 2 ^ m - m ≤ st.metaAreas.length ∧
      2 ^ (m + 1) - 2 - m ≤ st.metaAreas.length + st.availMetaPages.length ∧
      st.guardPages.length ≤ m + 1 ∧ st.availMetaPages.length ≤ 2 ^ m - 2)
  empty_groups_bound :
    ∀ g ∈ st.groups, g.isEmpty = true →
      0 < g.maplen ∧ 7 ≤ g.sc ∧ g.sc ≤ 38 ∧ g.maplen * 4096 ≤ 1048576 ∧
      (∀ h : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'h) ∧
      (∀ g' ∈ st.groups, g'.isEmpty = true → g'.sc = g.sc → g'.metaPtr = g.metaPtr) ∧
      (g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
  masterDom_wf :
    st.masterDom.Nodup ∧
    (∀ a : BitVec 64,
      (OwnedRwByte st a ∨ OwnedProtNoneByte st a ∨ OwnedMappedByte st a) → a ∈ st.masterDom) ∧
    (∀ a ∈ st.masterDom, ∃ r ∈ dynamicRootRegions st, InRegion r.1 r.2 a)

/-- Quiescent API-boundary heap invariant (`0` in-flight carved `struct meta` slots). -/
abbrev MallocngWF := MallocngWFInflight 0

/-! ## Startup Non-Vacuity (`emptyMallocngSt_wf`) -/

def emptyMallocngStOpt (auxvPtr : BitVec 64) (snapOpt : Option MallocngAuxvSnap) : MallocngSt :=
  { emptyMallocngSt auxvPtr with auxvSnap := snapOpt }

theorem emptyMallocngStOpt_wf {base brkStart : BitVec 64} (auxvPtr : BitVec 64)
    (snapOpt : Option MallocngAuxvSnap)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngWF base brkStart brkStart 0 0 (emptyMallocngStOpt auxvPtr snapOpt) where
  base_wf := trivial
  brk_bounds :=
    ⟨by simpa [MMAP_MIN_ADDR] using hBrkWf.1,
     by simpa [PAGE_SIZE] using hBrkWf.2.1,
     by simpa [PAGE_SIZE] using hBrkWf.2.1,
     Nat.le_refl _,
     hBrkWf.2.2⟩
  ctx_lens := by simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields]
  initDone_wf := Or.inl rfl
  initZero_wf := fun _ => by simp [emptyMallocngStOpt, emptyMallocngSt]
  bounces_wf := by
    intro b hb
    simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at hb
    subst hb; decide
  usage_wf := by
    intro sc hsc
    simp only [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields, List.getElem_replicate,
      BitVec.toNat_ofNat, Nat.zero_mod, List.filter_nil, List.map_nil, List.sum_nil]
  brk_mode_wf := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨h1, _⟩; simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at h1
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · intro hlt; omega
  metaAreas_wf := by simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields]
  guard_avail_wf := by
    refine ⟨List.nodup_nil, ?_, rfl, ?_⟩
    · intro _ h; cases h
    · intro _ h; cases h
  inflight_wf := by simp [emptyMallocngStOpt, emptyMallocngSt, totalClaimedSlots]
  free_bump_metas_wf := by
    refine ⟨rfl, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro fm hfm; cases hfm
    · intro bm hbm; cases hbm
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · intro m; simp [emptyMallocngStOpt, emptyMallocngSt, allMetaSlots]
  groups_nodup := ⟨List.nodup_nil, List.nodup_nil⟩
  groups_wf := fun _ hg => by cases hg
  regions_disjoint := ⟨trivial, trivial⟩
  active_wf := by
    intro sc h1 h2
    simp only [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields, List.getElem_replicate]
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro _ hm; cases hm
    · intro _ hg; cases hg
    · intro _ hi; cases hi
    · intro _ hg; cases hg
    · intro _ hg; cases hg
  liveMap_wf := by
    intro p n
    simp [emptyMallocngStOpt, emptyMallocngSt]
  live_le_peak := Nat.le_refl 0
  effCost_le_live := by simp [totalLiveEffCost, emptyMallocngStOpt, emptyMallocngSt]
  meta_pages_bound := by
    refine ⟨by simp [emptyMallocngStOpt, emptyMallocngSt],
      fun _ => ⟨rfl, by simp [emptyMallocngStOpt, emptyMallocngSt]⟩, ?_⟩
    intro m hm hEq
    simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at hEq
    omega
  empty_groups_bound := fun _ hg => by cases hg
  masterDom_wf := by
    refine ⟨List.nodup_nil, ?_, ?_⟩
    · intro a h
      simp [OwnedRwByte, OwnedProtNoneByte, OwnedMappedByte, emptyMallocngStOpt, emptyMallocngSt] at h
    · intro _ ha; cases ha

theorem emptyMallocngSt_wf {base brkStart : BitVec 64} (auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngWF base brkStart brkStart 0 0 (emptyMallocngSt auxvPtr) :=
  emptyMallocngStOpt_wf auxvPtr none hBrkWf

/-- No individually `mmap`ped (`isMmapped = true`) group in `st.groups` contains a free slot
    (`.freeAvail` or `.freeInactive`). -/
theorem not_isFree_of_isMmapped {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hMmap : g.isMmapped = true)
    {s : SlotState} (hs : s ∈ g.slots) :
    s.isFree = false := by
  cases hFree : s.isFree with
  | false => rfl
  | true =>
    exfalso
    have hGWf := hwf.groups_wf g hg
    have hLast0 : g.lastIdx = 0 := by
      unfold GroupDesc.isMmapped at hMmap
      rcases Bool.or_eq_true_iff.mp hMmap with h63 | hSlack
      · exact (hGWf.2.2.2.1 (beq_iff_eq.mp h63)).1
      · exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hSlack).1).1
    have hLen1 : g.slots.length = 1 := by
      have hL := hGWf.2.2.1
      unfold GroupDesc.cnt at hL
      omega
    have hSlotsEq : g.slots = [s] := by
      rcases hSlots : g.slots with _ | ⟨x, _ | _⟩
      · simp [hSlots] at hs
      · simp only [hSlots, List.mem_singleton] at hs
        rw [hs]
      · simp [hSlots] at hLen1
    have hEmpty : g.isEmpty = true := by
      simp [GroupDesc.isEmpty, hSlotsEq, hFree]
    have ⟨_, _, hScLe38, _, _, _, hNoSlack⟩ := hwf.empty_groups_bound g hg hEmpty
    have hGe := hNoSlack hLast0
    unfold GroupDesc.isMmapped at hMmap
    rcases Bool.or_eq_true_iff.mp hMmap with h63 | hSlack
    · have hEq63 := beq_iff_eq.mp h63; omega
    · have hLt : g.maplen * 4096 - 16 < slotStride g.sc :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hSlack).2
      omega

/-! ## Sealed Separation-Logic Invariants and `mallocngIface` -/

def MallocngAuxvConcreteWf (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) : Prop :=
  (∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
  (∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
  preEntries.length + sufEntries.length ≤ 64 ∧
  auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48 ∧
  randPtr.toNat + 16 ≤ 2 ^ 48

def MallocngAuxvAuthMap (auxvPtr : BitVec 64) : Option MallocngAuxvSnap → BitVec 64 → Option Nat
  | none => fun _ => none
  | some snap => fun k => if k = 0#64 then some (encodeAuxvSnap auxvPtr snap) else none

/-- Authoritative `auxv` ghost map paired with either the untracked `MallocngAuxvAt auxvPtr`
    existential (`snap = none`) or the concrete `auxv` table and `AT_RANDOM` secret word
    (`snap = some (...)`). -/
def MallocngAuxvState (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) : SepProp :=
  ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr snap) ∗
  match snap with
  | none => MallocngAuxvAt auxvPtr
  | some (preEntries, randPtr, sufEntries, nullVal, sec) =>
    ⌜MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries⌝ ∗
    (auxvPtr ↦₆₄*
      ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v])) ∗
    ((randPtr + 8#64) ↦₆₄ sec)

/-- Read-only (`.ro`) counterpart of `MallocngAuxvAt`: duplicable ELF auxiliary vector table at
    `auxvPtr` containing `AT_RANDOM` (`25#64`) before `AT_NULL` (`0#64`) and the 8-byte random
    secret slice at `randPtr + 8#64`. -/
def MallocngAuxvRoAt (auxvPtr : BitVec 64) : SepProp :=
  ∃∗ preEntries : List (BitVec 64 × BitVec 64),
  ∃∗ sufEntries : List (BitVec 64 × BitVec 64),
  ∃∗ randPtr : BitVec 64,
  ∃∗ nullVal : BitVec 64,
  ∃∗ secretBytes : List (BitVec 8),
    ⌜(∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
     (∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
     preEntries.length + sufEntries.length ≤ 64 ∧
     auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48 ∧
     randPtr.toNat + 16 ≤ 2 ^ 48 ∧
     secretBytes.length = 8⌝ ∗
    (auxvPtr ↦₆₄ᵣ*
      ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v])) ∗
    ((randPtr + 8#64) ↦ᵣ secretBytes)

/-- Duplicable read-only `__libc.auxv` pointer and `auxv` table bundle at placement `A`. -/
def MallocngLibcAuxvRoAt (A : MallocngAddrs) : SepProp :=
  ∃∗ auxvPtr : BitVec 64, ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr

/-- Mode-parameterized `__libc.auxv` pointer cell: `.ro` when `ro = true`, `.rw` when `ro = false`. -/
def MallocngAuxvPtrCell (ro : Bool) (libc auxvPtr : BitVec 64) : SepProp :=
  if ro then (libc + 8#64) ↦₆₄ᵣ auxvPtr else (libc + 8#64) ↦₆₄ auxvPtr

/-- Mode-parameterized `auxv` table assertion: `MallocngAuxvRoAt` when `ro = true`,
    `MallocngAuxvState` when `ro = false`. -/
def MallocngAuxvStateRo (ro : Bool) (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) : SepProp :=
  if ro then MallocngAuxvRoAt auxvPtr else MallocngAuxvState γ auxvPtr snap

private theorem pointsToBytes_freeze_ro_aux (a : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦ₛ bs) ⊢ |==> (a ↦ᵣ bs) := by
  induction bs generalizing a with
  | nil =>
    rw [pointsToBytes_nil, pointsToBytesRO_nil]
    exact bupd_intro _
  | cons b bs ih =>
    rw [pointsToBytes_cons, pointsToBytesRO_cons]
    exact bupd_sep (pointsTo8_freeze_ro a b) (ih (a + 1#64))

private theorem pointsToWords64_freeze_ro_aux (a : BitVec 64) (ws : List (BitVec 64)) :
    (a ↦₆₄* ws) ⊢ |==> (a ↦₆₄ᵣ* ws) := by
  induction ws generalizing a with
  | nil =>
    rw [pointsToWords64_nil, pointsToWords64RO_nil]
    exact bupd_intro _
  | cons w ws ih =>
    rw [pointsToWords64_cons, pointsToWords64RO_cons]
    exact bupd_sep (pointsTo64_freeze_ro a w) (ih (a + 8#64))

/-- Freeze a read-write `MallocngAuxvAt` table into its duplicable `.ro` counterpart. -/
theorem mallocngAuxvAt_freeze_ro (auxvPtr : BitVec 64) :
    MallocngAuxvAt auxvPtr ⊢ |==> MallocngAuxvRoAt auxvPtr := by
  unfold MallocngAuxvAt MallocngAuxvRoAt
  refine Entails.sepExists_elim fun pre => Entails.sepExists_elim fun suf =>
    Entails.sepExists_elim fun randPtr => Entails.sepExists_elim fun nullVal =>
      Entails.sepExists_elim fun secretBytes => Entails.pure_left fun hwf => ?_
  refine Entails.trans
    (bupd_sep (pointsToWords64_freeze_ro_aux _ _) (pointsToBytes_freeze_ro_aux _ _))
    (bupd_mono ?_)
  exact Entails.sepExists_right pre (Entails.sepExists_right suf
    (Entails.sepExists_right randPtr (Entails.sepExists_right nullVal
      (Entails.sepExists_right secretBytes (Entails.pure_right hwf (Entails.refl _))))))

/-- Freeze both `__libc.auxv` and `MallocngAuxvAt` into the duplicable `MallocngLibcAuxvRoAt`. -/
theorem mallocngLibcAuxv_freeze_ro (A : MallocngAddrs) (auxvPtr : BitVec 64) :
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗ MallocngAuxvAt auxvPtr ⊢ |==> MallocngLibcAuxvRoAt A := by
  unfold MallocngLibcAuxvRoAt
  refine Entails.trans
    (bupd_sep (pointsTo64_freeze_ro (A.libc + 8#64) auxvPtr) (mallocngAuxvAt_freeze_ro auxvPtr))
    (bupd_mono (Entails.sepExists_right auxvPtr (Entails.refl _)))

private theorem pointsTo8RO_agree_entails (a : BitVec 64) (b₁ b₂ : BitVec 8) :
    (a ↦₈ᵣ b₁) ∗ (a ↦₈ᵣ b₂) ⊢ ⌜b₁ = b₂⌝ ∗ (a ↦₈ᵣ b₁) := by
  refine Entails.trans (Entails.extract_heap_fact (φ := b₁ = b₂) fun h hh => ?_) ?_
  · have h1 := ownsCell_sepConj_left (ownsCell_pointsTo8RO a b₁) h hh
    have h2 := ownsCell_sepConj_right (ownsCell_pointsTo8RO a b₂) h hh
    rw [h1, Option.some.injEq, HeapCell.ro.injEq] at h2
    exact h2
  · refine Entails.pure_left fun hEq => ?_
    subst hEq
    rw [pointsTo8RO_dup]
    exact Entails.pure_right rfl (Entails.refl _)

private theorem pointsToBytesRO_agree_entails (a : BitVec 64) (bs₁ bs₂ : List (BitVec 8))
    (hlen : bs₁.length = bs₂.length) :
    (a ↦ᵣ bs₁) ∗ (a ↦ᵣ bs₂) ⊢ ⌜bs₁ = bs₂⌝ ∗ (a ↦ᵣ bs₁) := by
  induction bs₁ generalizing a bs₂ with
  | nil =>
    cases bs₂ with
    | nil =>
      rw [pointsToBytesRO_nil, emp_sepConj, pure_sepConj_of_true rfl]
      exact Entails.refl _
    | cons _ _ => simp at hlen
  | cons b₁ tl₁ ih =>
    cases bs₂ with
    | nil => simp at hlen
    | cons b₂ tl₂ =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [pointsToBytesRO_cons, pointsToBytesRO_cons]
      have hSwap :
          (((a ↦₈ᵣ b₁) ∗ ((a + 1#64) ↦ᵣ tl₁)) ∗ ((a ↦₈ᵣ b₂) ∗ ((a + 1#64) ↦ᵣ tl₂))) =
          (((a ↦₈ᵣ b₁) ∗ (a ↦₈ᵣ b₂)) ∗ (((a + 1#64) ↦ᵣ tl₁) ∗ ((a + 1#64) ↦ᵣ tl₂))) := by ac_rfl
      rw [hSwap]
      refine Entails.trans (sepConj_mono (pointsTo8RO_agree_entails a b₁ b₂) (ih (a + 1#64) tl₂ hlen)) ?_
      rw [sepConj_assoc, sepConj_comm (a ↦₈ᵣ b₁), sepConj_assoc]
      refine Entails.pure_left fun hb => Entails.pure_left fun htl => ?_
      subst hb; subst htl
      refine Entails.pure_right rfl ?_
      rw [sepConj_comm]
      exact Entails.refl _

private theorem unpack64_inj_aux {v₁ v₂ : BitVec 64} (h : unpack64 v₁ = unpack64 v₂) : v₁ = v₂ := by
  simp only [unpack64, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmod : i % 8 < 8 := Nat.mod_lt i (by decide)
  have hEqBit : ∀ (s : Nat), v₁.extractLsb' s 8 = v₂.extractLsb' s 8 →
      s + (i % 8) = i → v₁.getLsbD i = v₂.getLsbD i := by
    intro s hs hsum
    have := congrArg (fun x => x.getLsbD (i % 8)) hs
    simp only [BitVec.getLsbD_extractLsb', hmod, decide_true, Bool.true_and, hsum] at this
    exact this
  have : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 ∨
         i / 8 = 4 ∨ i / 8 = 5 ∨ i / 8 = 6 ∨ i / 8 = 7 := by omega
  rcases this with hd | hd | hd | hd | hd | hd | hd | hd
  · exact hEqBit 0 h0 (by omega)
  · exact hEqBit 8 h1 (by omega)
  · exact hEqBit 16 h2 (by omega)
  · exact hEqBit 24 h3 (by omega)
  · exact hEqBit 32 h4 (by omega)
  · exact hEqBit 40 h5 (by omega)
  · exact hEqBit 48 h6 (by omega)
  · exact hEqBit 56 h7 (by omega)

private theorem pointsTo64RO_agree_entails (a v₁ v₂ : BitVec 64) :
    (a ↦₆₄ᵣ v₁) ∗ (a ↦₆₄ᵣ v₂) ⊢ ⌜v₁ = v₂⌝ ∗ (a ↦₆₄ᵣ v₁) := by
  rw [pointsTo64RO_eq_pointsToBytesRO, pointsTo64RO_eq_pointsToBytesRO]
  refine Entails.trans (pointsToBytesRO_agree_entails a (unpack64 v₁) (unpack64 v₂) (by simp)) ?_
  refine Entails.pure_left fun hEq => ?_
  exact Entails.pure_right (unpack64_inj_aux hEq) (Entails.refl _)

private theorem pointsToWords64RO_prefix_agree (a : BitVec 64) (ws₁ ws₂ : List (BitVec 64)) :
    (a ↦₆₄ᵣ* ws₁) ∗ (a ↦₆₄ᵣ* ws₂) ⊢
      ⌜∀ i, i < ws₁.length → i < ws₂.length → ws₁[i]? = ws₂[i]?⌝ ∗
      ((a ↦₆₄ᵣ* ws₁) ∗ (a ↦₆₄ᵣ* ws₂)) := by
  induction ws₁ generalizing a ws₂ with
  | nil =>
    exact Entails.pure_right (fun _ hi _ => absurd hi (Nat.not_lt_zero _)) (Entails.refl _)
  | cons w₁ rest₁ ih =>
    cases ws₂ with
    | nil =>
      exact Entails.pure_right (fun _ _ hi => absurd hi (Nat.not_lt_zero _)) (Entails.refl _)
    | cons w₂ rest₂ =>
      rw [pointsToWords64RO_cons, pointsToWords64RO_cons]
      have hSwap :
          (((a ↦₆₄ᵣ w₁) ∗ ((a + 8#64) ↦₆₄ᵣ* rest₁)) ∗ ((a ↦₆₄ᵣ w₂) ∗ ((a + 8#64) ↦₆₄ᵣ* rest₂))) =
          (((a ↦₆₄ᵣ w₁) ∗ (a ↦₆₄ᵣ w₂)) ∗ (((a + 8#64) ↦₆₄ᵣ* rest₁) ∗ ((a + 8#64) ↦₆₄ᵣ* rest₂))) := by
        ac_rfl
      rw [hSwap]
      refine Entails.trans (sepConj_mono (pointsTo64RO_agree_entails a w₁ w₂) (ih (a + 8#64) rest₂)) ?_
      rw [sepConj_assoc, sepConj_comm (a ↦₆₄ᵣ w₁), sepConj_assoc]
      refine Entails.pure_left fun hw => Entails.pure_left fun hrest => ?_
      subst hw
      refine Entails.pure_right (fun i hi1 hi2 => ?_) ?_
      · cases i with
        | zero => rfl
        | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi1 hi2
          simpa using hrest j hi1 hi2
      · refine Entails.of_eq ?_
        conv => lhs; rw [← pointsTo64RO_dup a w₁]
        ac_rfl

private theorem flatMap_pair_getElem? (L : List (BitVec 64 × BitVec 64)) (k : Nat)
    (hk : k < L.length) :
    (L.flatMap fun (t, v) => [t, v])[2 * k]? = some (L[k]'hk).1 ∧
    (L.flatMap fun (t, v) => [t, v])[2 * k + 1]? = some (L[k]'hk).2 := by
  induction L generalizing k with
  | nil => simp at hk
  | cons hd tl ih =>
    rcases hd with ⟨t, v⟩
    cases k with
    | zero => simp
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      have h1 : 2 * (j + 1) = (2 * j) + 2 := by omega
      have h2 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      simpa [List.flatMap_cons, h1, h2] using ih j hk

private theorem flatMap_pair_length (L : List (BitVec 64 × BitVec 64)) :
    (L.flatMap fun (t, v) => [t, v]).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons _ tl ih => simp [List.flatMap_cons, ih]; omega

private theorem auxv_entries_eq_of_prefix_agree
    {pre₁ suf₁ pre₂ suf₂ : List (BitVec 64 × BitVec 64)}
    {rand₁ null₁ rand₂ null₂ : BitVec 64}
    (hPre₁ : ∀ e ∈ pre₁, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSuf₁ : ∀ e ∈ suf₁, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hPre₂ : ∀ e ∈ pre₂, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSuf₂ : ∀ e ∈ suf₂, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hAgree : ∀ i,
      i < ((pre₁ ++ [(25#64, rand₁)] ++ suf₁ ++ [(0#64, null₁)]).flatMap fun (t, v) => [t, v]).length →
      i < ((pre₂ ++ [(25#64, rand₂)] ++ suf₂ ++ [(0#64, null₂)]).flatMap fun (t, v) => [t, v]).length →
      ((pre₁ ++ [(25#64, rand₁)] ++ suf₁ ++ [(0#64, null₁)]).flatMap fun (t, v) => [t, v])[i]? =
      ((pre₂ ++ [(25#64, rand₂)] ++ suf₂ ++ [(0#64, null₂)]).flatMap fun (t, v) => [t, v])[i]?) :
    pre₁ = pre₂ ∧ rand₁ = rand₂ ∧ suf₁ = suf₂ ∧ null₁ = null₂ := by
  let L₁ := pre₁ ++ [(25#64, rand₁)] ++ suf₁ ++ [(0#64, null₁)]
  let L₂ := pre₂ ++ [(25#64, rand₂)] ++ suf₂ ++ [(0#64, null₂)]
  have hPairAgree : ∀ k, (hk1 : k < L₁.length) → (hk2 : k < L₂.length) → L₁[k]'hk1 = L₂[k]'hk2 := by
    intro k hk1 hk2
    have hLen1 : (L₁.flatMap fun (t, v) => [t, v]).length = 2 * L₁.length := flatMap_pair_length L₁
    have hLen2 : (L₂.flatMap fun (t, v) => [t, v]).length = 2 * L₂.length := flatMap_pair_length L₂
    have hk1' : 2 * k < (L₁.flatMap fun (t, v) => [t, v]).length := by omega
    have hk2' : 2 * k < (L₂.flatMap fun (t, v) => [t, v]).length := by omega
    have hk1'' : 2 * k + 1 < (L₁.flatMap fun (t, v) => [t, v]).length := by omega
    have hk2'' : 2 * k + 1 < (L₂.flatMap fun (t, v) => [t, v]).length := by omega
    have h0 := hAgree (2 * k) hk1' hk2'
    have h1 := hAgree (2 * k + 1) hk1'' hk2''
    have ⟨h0a, h1a⟩ := flatMap_pair_getElem? L₁ k hk1
    have ⟨h0b, h1b⟩ := flatMap_pair_getElem? L₂ k hk2
    dsimp only [L₁, L₂] at h0a h1a h0b h1b
    rw [h0a, h0b, Option.some.injEq] at h0
    rw [h1a, h1b, Option.some.injEq] at h1
    exact Prod.ext h0 h1
  have hNonZeroPrefix : ∀ (pre suf : List (BitVec 64 × BitVec 64)) (rand : BitVec 64)
      (_ : ∀ e ∈ pre, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) (_ : ∀ e ∈ suf, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64),
      ∀ e ∈ pre ++ [(25#64, rand)] ++ suf, e.1 ≠ 0#64 := by
    intro pre suf rand hp hs e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (h | rfl) | h
    · exact (hp e h).1
    · intro hc; dsimp only at hc; exact absurd hc (by decide)
    · exact (hs e h).1
  have hLastTag : ∀ (pre suf : List (BitVec 64 × BitVec 64)) (rand nv : BitVec 64),
      let L := pre ++ [(25#64, rand)] ++ suf ++ [(0#64, nv)]
      ∀ (h : L.length - 1 < L.length), (L[L.length - 1]'h) = (0#64, nv) := by
    intro pre suf rand nv L h
    dsimp only [L]
    rw [List.getElem_append_right (by simp)]
    simp
  have hLenEq : L₁.length = L₂.length := by
    rcases Nat.lt_trichotomy L₁.length L₂.length with hLt | hEq | hGt
    · exfalso
      have hk1 : L₁.length - 1 < L₁.length := by simp [L₁]
      have hk2 : L₁.length - 1 < L₂.length := by omega
      have hEq := hPairAgree (L₁.length - 1) hk1 hk2
      have h1 := hLastTag pre₁ suf₁ rand₁ null₁ hk1
      rw [h1] at hEq
      have hInPref : L₂[L₁.length - 1]'hk2 ∈ pre₂ ++ [(25#64, rand₂)] ++ suf₂ := by
        have hLtP : L₁.length - 1 < (pre₂ ++ [(25#64, rand₂)] ++ suf₂).length := by
          simp [L₂] at hLt ⊢; omega
        have hGet : L₂[L₁.length - 1]'hk2 = (pre₂ ++ [(25#64, rand₂)] ++ suf₂)[L₁.length - 1]'hLtP := by
          dsimp only [L₂]; exact List.getElem_append_left hLtP
        rw [hGet]; exact List.getElem_mem hLtP
      have hNe0 := hNonZeroPrefix pre₂ suf₂ rand₂ hPre₂ hSuf₂ _ hInPref
      rw [← hEq] at hNe0; exact hNe0 rfl
    · exact hEq
    · exfalso
      have hk2 : L₂.length - 1 < L₂.length := by simp [L₂]
      have hk1 : L₂.length - 1 < L₁.length := by omega
      have hEq := hPairAgree (L₂.length - 1) hk1 hk2
      have h2 := hLastTag pre₂ suf₂ rand₂ null₂ hk2
      rw [h2] at hEq
      have hInPref : L₁[L₂.length - 1]'hk1 ∈ pre₁ ++ [(25#64, rand₁)] ++ suf₁ := by
        have hLtP : L₂.length - 1 < (pre₁ ++ [(25#64, rand₁)] ++ suf₁).length := by
          simp [L₁] at hGt ⊢; omega
        have hGet : L₁[L₂.length - 1]'hk1 = (pre₁ ++ [(25#64, rand₁)] ++ suf₁)[L₂.length - 1]'hLtP := by
          dsimp only [L₁]; exact List.getElem_append_left hLtP
        rw [hGet]; exact List.getElem_mem hLtP
      have hNe0 := hNonZeroPrefix pre₁ suf₁ rand₁ hPre₁ hSuf₁ _ hInPref
      rw [hEq] at hNe0; exact hNe0 rfl
  have hLEq : L₁ = L₂ := List.ext_getElem hLenEq (fun i hi1 hi2 => hPairAgree i hi1 hi2)
  have hSplitNull := List.append_inj_left' hLEq (by simp)
  have hNullPair := List.append_inj_right' hLEq (by simp)
  have hNullEq : null₁ = null₂ := by
    have := List.cons.inj hNullPair
    exact (Prod.mk.inj this.1).2
  have hPreLenEq : pre₁.length = pre₂.length := by
    rcases Nat.lt_trichotomy pre₁.length pre₂.length with hLt | hEq | hGt
    · exfalso
      have hMem : (25#64, rand₁) ∈ pre₂ := by
        have hk1 : pre₁.length < (pre₁ ++ [(25#64, rand₁)] ++ suf₁).length := by simp
        have hk2 : pre₁.length < (pre₂ ++ [(25#64, rand₂)] ++ suf₂).length := by
          rw [← hSplitNull]; exact hk1
        have hGetEq : (pre₁ ++ [(25#64, rand₁)] ++ suf₁)[pre₁.length]'hk1 =
            (pre₂ ++ [(25#64, rand₂)] ++ suf₂)[pre₁.length]'hk2 := by
          simp only [hSplitNull]
        have hLhs : (pre₁ ++ [(25#64, rand₁)] ++ suf₁)[pre₁.length]'hk1 = (25#64, rand₁) := by
          simp [List.append_assoc]
        have hRhs : (pre₂ ++ [(25#64, rand₂)] ++ suf₂)[pre₁.length]'hk2 = pre₂[pre₁.length]'hLt := by
          simp [List.append_assoc, List.getElem_append_left hLt]
        rw [hLhs, hRhs] at hGetEq
        rw [hGetEq]; exact List.getElem_mem hLt
      exact (hPre₂ _ hMem).2 rfl
    · exact hEq
    · exfalso
      have hMem : (25#64, rand₂) ∈ pre₁ := by
        have hk2 : pre₂.length < (pre₂ ++ [(25#64, rand₂)] ++ suf₂).length := by simp
        have hk1 : pre₂.length < (pre₁ ++ [(25#64, rand₁)] ++ suf₁).length := by
          rw [hSplitNull]; exact hk2
        have hGetEq : (pre₁ ++ [(25#64, rand₁)] ++ suf₁)[pre₂.length]'hk1 =
            (pre₂ ++ [(25#64, rand₂)] ++ suf₂)[pre₂.length]'hk2 := by
          simp only [hSplitNull]
        have hRhs : (pre₂ ++ [(25#64, rand₂)] ++ suf₂)[pre₂.length]'hk2 = (25#64, rand₂) := by
          simp [List.append_assoc]
        have hLhs : (pre₁ ++ [(25#64, rand₁)] ++ suf₁)[pre₂.length]'hk1 = pre₁[pre₂.length]'hGt := by
          simp [List.append_assoc, List.getElem_append_left hGt]
        rw [hLhs, hRhs] at hGetEq
        rw [← hGetEq]; exact List.getElem_mem hGt
      exact (hPre₁ _ hMem).2 rfl
  rw [List.append_assoc, List.append_assoc] at hSplitNull
  have hPreEq := List.append_inj_left hSplitNull hPreLenEq
  have hTailEq := List.append_inj_right hSplitNull hPreLenEq
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq] at hTailEq
  exact ⟨hPreEq, hTailEq.1.2, hTailEq.2, hNullEq⟩

/-- `MallocngAuxvRoAt` is duplicable (`P ∗ P = P`). -/
theorem mallocngAuxvRoAt_dup (auxvPtr : BitVec 64) :
    (MallocngAuxvRoAt auxvPtr ∗ MallocngAuxvRoAt auxvPtr) = MallocngAuxvRoAt auxvPtr := by
  apply SepProp.eq_of_entails
  · unfold MallocngAuxvRoAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun pre₁ => Entails.sepExists_elim fun suf₁ =>
      Entails.sepExists_elim fun rand₁ => Entails.sepExists_elim fun null₁ =>
        Entails.sepExists_elim fun sec₁ =>
          Entails.sepExists_elim fun pre₂ => Entails.sepExists_elim fun suf₂ =>
            Entails.sepExists_elim fun rand₂ => Entails.sepExists_elim fun null₂ =>
              Entails.sepExists_elim fun sec₂ => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hwf₁ => ?_
    rw [sepConj_comm _ (⌜_⌝ ∗ _), sepConj_assoc]
    refine Entails.pure_left fun hwf₂ => ?_
    let ws₁ := (pre₁ ++ [(25#64, rand₁)] ++ suf₁ ++ [(0#64, null₁)]).flatMap fun (t, v) => [t, v]
    let ws₂ := (pre₂ ++ [(25#64, rand₂)] ++ suf₂ ++ [(0#64, null₂)]).flatMap fun (t, v) => [t, v]
    have hSwap :
        (((auxvPtr ↦₆₄ᵣ* ws₁) ∗ ((rand₁ + 8#64) ↦ᵣ sec₁)) ∗
         ((auxvPtr ↦₆₄ᵣ* ws₂) ∗ ((rand₂ + 8#64) ↦ᵣ sec₂))) =
        (((auxvPtr ↦₆₄ᵣ* ws₁) ∗ (auxvPtr ↦₆₄ᵣ* ws₂)) ∗
         (((rand₁ + 8#64) ↦ᵣ sec₁) ∗ ((rand₂ + 8#64) ↦ᵣ sec₂))) := by ac_rfl
    change (((auxvPtr ↦₆₄ᵣ* ws₁) ∗ ((rand₁ + 8#64) ↦ᵣ sec₁)) ∗
            ((auxvPtr ↦₆₄ᵣ* ws₂) ∗ ((rand₂ + 8#64) ↦ᵣ sec₂))) ⊢ _
    rw [hSwap]
    refine Entails.trans (sepConj_mono_left (pointsToWords64RO_prefix_agree auxvPtr ws₁ ws₂)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hAgree => ?_
    obtain ⟨hPreEq, hRandEq, hSufEq, hNullEq⟩ :=
      auxv_entries_eq_of_prefix_agree hwf₂.1 hwf₂.2.1 hwf₁.1 hwf₁.2.1 hAgree
    subst hPreEq; subst hRandEq; subst hSufEq; subst hNullEq
    have hWsEq : ws₂ = ws₁ := rfl
    rw [hWsEq, pointsToWords64RO_dup]
    refine Entails.trans (sepConj_mono_right
      (pointsToBytesRO_agree_entails (rand₁ + 8#64) sec₁ sec₂ (by omega))) ?_
    rw [sepConj_comm (auxvPtr ↦₆₄ᵣ* ws₁), sepConj_assoc]
    refine Entails.pure_left fun hSecEq => ?_
    subst hSecEq
    rw [sepConj_comm]
    exact Entails.sepExists_right pre₁ (Entails.sepExists_right suf₁
      (Entails.sepExists_right rand₁ (Entails.sepExists_right null₁
        (Entails.sepExists_right sec₁ (Entails.pure_right hwf₂ (Entails.refl _))))))
  · unfold MallocngAuxvRoAt
    refine Entails.sepExists_elim fun pre => Entails.sepExists_elim fun suf =>
      Entails.sepExists_elim fun randPtr => Entails.sepExists_elim fun nullVal =>
        Entails.sepExists_elim fun sec => Entails.pure_left fun hwf => ?_
    let ws := (pre ++ [(25#64, randPtr)] ++ suf ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v]
    have hDup :
        ((auxvPtr ↦₆₄ᵣ* ws) ∗ ((randPtr + 8#64) ↦ᵣ sec)) =
        (((auxvPtr ↦₆₄ᵣ* ws) ∗ ((randPtr + 8#64) ↦ᵣ sec)) ∗
         ((auxvPtr ↦₆₄ᵣ* ws) ∗ ((randPtr + 8#64) ↦ᵣ sec))) := by
      conv => lhs; rw [← pointsToWords64RO_dup auxvPtr ws, ← pointsToBytesRO_dup (randPtr + 8#64) sec]
      ac_rfl
    change ((auxvPtr ↦₆₄ᵣ* ws) ∗ ((randPtr + 8#64) ↦ᵣ sec)) ⊢ _
    rw [hDup]
    have hOne :
        ((auxvPtr ↦₆₄ᵣ* ws) ∗ ((randPtr + 8#64) ↦ᵣ sec)) ⊢
        (∃∗ preEntries : List (BitVec 64 × BitVec 64),
         ∃∗ sufEntries : List (BitVec 64 × BitVec 64),
         ∃∗ randPtr : BitVec 64,
         ∃∗ nullVal : BitVec 64,
         ∃∗ secretBytes : List (BitVec 8),
           ⌜(∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
            (∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
            preEntries.length + sufEntries.length ≤ 64 ∧
            auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48 ∧
            randPtr.toNat + 16 ≤ 2 ^ 48 ∧
            secretBytes.length = 8⌝ ∗
           (auxvPtr ↦₆₄ᵣ*
             ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
               fun (t, v) => [t, v])) ∗
           ((randPtr + 8#64) ↦ᵣ secretBytes)) :=
      Entails.sepExists_right pre (Entails.sepExists_right suf
        (Entails.sepExists_right randPtr (Entails.sepExists_right nullVal
          (Entails.sepExists_right sec (Entails.pure_right hwf (Entails.refl _))))))
    exact sepConj_mono hOne hOne

/-- `MallocngLibcAuxvRoAt` is duplicable (`P ∗ P = P`). -/
theorem mallocngLibcAuxvRoAt_dup (A : MallocngAddrs) :
    (MallocngLibcAuxvRoAt A ∗ MallocngLibcAuxvRoAt A) = MallocngLibcAuxvRoAt A := by
  apply SepProp.eq_of_entails
  · unfold MallocngLibcAuxvRoAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p₁ => Entails.sepExists_elim fun p₂ => ?_
    have hSwap :
        ((((A.libc + 8#64) ↦₆₄ᵣ p₂) ∗ MallocngAuxvRoAt p₂) ∗
         (((A.libc + 8#64) ↦₆₄ᵣ p₁) ∗ MallocngAuxvRoAt p₁)) =
        ((((A.libc + 8#64) ↦₆₄ᵣ p₁) ∗ ((A.libc + 8#64) ↦₆₄ᵣ p₂)) ∗
         (MallocngAuxvRoAt p₁ ∗ MallocngAuxvRoAt p₂)) := by ac_rfl
    rw [hSwap]
    refine Entails.trans (sepConj_mono_left (pointsTo64RO_agree_entails (A.libc + 8#64) p₁ p₂)) ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hEq => ?_
    subst hEq
    rw [mallocngAuxvRoAt_dup]
    exact Entails.sepExists_right p₁ (Entails.refl _)
  · unfold MallocngLibcAuxvRoAt
    refine Entails.sepExists_elim fun p => ?_
    have hDup :
        (((A.libc + 8#64) ↦₆₄ᵣ p) ∗ MallocngAuxvRoAt p) =
        ((((A.libc + 8#64) ↦₆₄ᵣ p) ∗ MallocngAuxvRoAt p) ∗
         (((A.libc + 8#64) ↦₆₄ᵣ p) ∗ MallocngAuxvRoAt p)) := by
      conv => lhs; rw [← pointsTo64RO_dup (A.libc + 8#64) p, ← mallocngAuxvRoAt_dup p]
      ac_rfl
    rw [hDup]
    exact sepConj_mono (Entails.sepExists_right p (Entails.refl _))
      (Entails.sepExists_right p (Entails.refl _))

theorem BoundedFootprint_mallocngLiveAuth (γ : GhostName) (L : MallocngLiveMap) :
    SepProp.BoundedFootprint (MallocngLiveAuth γ L) 0 :=
  BoundedFootprint_ghostMapAuth (liveGhost γ) L.enc

theorem footprintIn_mallocngLiveAuth {S : BitVec 64 → Prop}
    (γ : GhostName) (L : MallocngLiveMap) :
    SepProp.FootprintIn (MallocngLiveAuth γ L) S :=
  SepProp.FootprintIn.ghostMapAuth (liveGhost γ) L.enc

def MallocngCoreStInflightA (inflight : Nat) (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) : SepProp :=
  ⌜MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st⌝ ∗
  MallocngLiveAuth γ st.liveMap ∗
  (A.ctx ↦ₛ st.ctx.toBytes) ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
  MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

abbrev MallocngCoreStA := MallocngCoreStInflightA 0

/-- Mode-parameterized core state (`ro = false` is definitionally `MallocngCoreStInflightA`;
    `ro = true` holds `.ro` `__libc.auxv` and `MallocngAuxvRoAt`). -/
def MallocngCoreStInflightModeA (ro : Bool) (inflight : Nat) (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) : SepProp :=
  ⌜MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st⌝ ∗
  MallocngLiveAuth γ st.liveMap ∗
  (A.ctx ↦ₛ st.ctx.toBytes) ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
  MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

abbrev MallocngCoreStModeA (ro : Bool) := MallocngCoreStInflightModeA ro 0

theorem MallocngCoreStInflightModeA_false (inflight : Nat) (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    MallocngCoreStInflightModeA false inflight γ A brkStart brk liveCost peakCost st =
      MallocngCoreStInflightA inflight γ A brkStart brk liveCost peakCost st :=
  rfl

theorem MallocngCoreStModeA_false (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    MallocngCoreStModeA false γ A brkStart brk liveCost peakCost st =
      MallocngCoreStA γ A brkStart brk liveCost peakCost st :=
  rfl

/-- Allocator core state excluding the `__libc.auxv` pointer and `auxv` table (all RW/ghost). -/
def MallocngCoreStNoAuxvA (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    SepProp :=
  ⌜MallocngWFInflight 0 A.base brkStart brk liveCost peakCost st⌝ ∗
  MallocngLiveAuth γ st.liveMap ∗
  (A.ctx ↦ₛ st.ctx.toBytes) ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

abbrev MallocngRoTablesA (A : MallocngAddrs) : SepProp :=
  MallocngRoTablesAt A

/-- Allocator-private separation-logic invariant (`MallocngCore`). -/
@[irreducible] def MallocngCoreImpl
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt,
    ⌜MallocngCountIvsWF b ivs st⌝ ∗
    MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st

/-- Allocator and single-threaded runtime separation-logic invariant (`MallocngHeap`). -/
@[irreducible] def MallocngHeapImpl
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp

/-- Allocator-private separation-logic invariant with read-only (`.ro`) `__libc.auxv` and `auxv`. -/
@[irreducible] def MallocngCoreRoImpl
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt,
    ⌜MallocngCountIvsWF b ivs st⌝ ∗
    MallocngCoreStModeA true γ A brkStart brk b.liveCost b.peakCost st

/-- Allocator and runtime separation-logic invariant with read-only (`.ro`) `auxv`. -/
@[irreducible] def MallocngHeapRoImpl
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngCoreRoImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp

theorem MallocngCoreImpl_eq (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngCoreImpl γ A brkStart brk b ivs =
      (MallocngRoTablesA A ∗
       ∃∗ st : MallocngSt,
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st) := by
  unfold MallocngCoreImpl
  rfl

theorem MallocngHeapImpl_eq (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngHeapImpl γ A tp brkStart brk b ivs =
      (MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp) := by
  unfold MallocngHeapImpl
  rfl

theorem MallocngCoreRoImpl_eq (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngCoreRoImpl γ A brkStart brk b ivs =
      (MallocngRoTablesA A ∗
       ∃∗ st : MallocngSt,
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStModeA true γ A brkStart brk b.liveCost b.peakCost st) := by
  unfold MallocngCoreRoImpl
  rfl

theorem MallocngHeapRoImpl_eq (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngHeapRoImpl γ A tp brkStart brk b ivs =
      (MallocngCoreRoImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp) := by
  unfold MallocngHeapRoImpl
  rfl

/-- Concrete `MallocngIface` witness for `musl` v1.2.5 `mallocng`. -/
def mallocngIface : MallocngIface where
  MallocngHeap := MallocngHeapImpl
  MallocngCore := MallocngCoreImpl
  Block        := MallocngBlockToken
  block_noWrap := mallocngBlock_noWrap

/-- Concrete `MallocngIface` witness with duplicable read-only (`.ro`) `__libc.auxv` and `auxv`. -/
def mallocngRoIface : MallocngIface where
  MallocngHeap := MallocngHeapRoImpl
  MallocngCore := MallocngCoreRoImpl
  Block        := MallocngBlockToken
  block_noWrap := mallocngBlock_noWrap

/-- Mode-parameterized `MallocngIface` (`false` = RW `mallocngIface`, `true` = RO `mallocngRoIface`). -/
def mallocngModeIface : Bool → MallocngIface
  | false => mallocngIface
  | true  => mallocngRoIface

theorem mallocngModeIface_core_eq (ro : Bool)
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    (mallocngModeIface ro).MallocngCore γ A brkStart brk b ivs =
      (MallocngRoTablesA A ∗
       ∃∗ st : MallocngSt,
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStModeA ro γ A brkStart brk b.liveCost b.peakCost st) := by
  cases ro
  · exact MallocngCoreImpl_eq γ A brkStart brk b ivs
  · exact MallocngCoreRoImpl_eq γ A brkStart brk b ivs

theorem mallocngModeIface_heap_eq (ro : Bool)
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    (mallocngModeIface ro).MallocngHeap γ A tp brkStart brk b ivs =
      ((mallocngModeIface ro).MallocngCore γ A brkStart brk b ivs ∗ MallocngRuntime A tp) := by
  cases ro
  · exact MallocngHeapImpl_eq γ A tp brkStart brk b ivs
  · exact MallocngHeapRoImpl_eq γ A tp brkStart brk b ivs

theorem mallocngModeIface_block_eq (ro : Bool) :
    (mallocngModeIface ro).Block = MallocngBlockToken := by
  cases ro <;> rfl

/-! ## `MallocngIfaceFacts` Structural and Startup Laws -/

theorem mallocngHeap_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs =
      (mallocngIface.MallocngCore γ A brkStart brk b ivs ∗ MallocngRuntime A tp) :=
  MallocngHeapImpl_eq γ A tp brkStart brk b ivs

private theorem noRO_mallocngAuxvAt (auxvPtr : BitVec 64) :
    SepProp.NoRO (MallocngAuxvAt auxvPtr) := by
  unfold MallocngAuxvAt
  exact SepProp.NoRO.sepExists fun _ =>
    SepProp.NoRO.sepExists fun _ =>
      SepProp.NoRO.sepExists fun _ =>
        SepProp.NoRO.sepExists fun _ =>
          SepProp.NoRO.sepExists fun _ =>
            SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
              (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToWords64 _ _)
                (SepProp.NoRO.pointsToBytes _ _))

private theorem noRO_mallocngAuxvState (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) :
    SepProp.NoRO (MallocngAuxvState γ auxvPtr snap) := by
  unfold MallocngAuxvState
  refine SepProp.NoRO.sepConj (SepProp.NoRO.ghostMapAuth _ _) ?_
  rcases snap with _ | ⟨preEntries, randPtr, sufEntries, nullVal, sec⟩
  · exact noRO_mallocngAuxvAt auxvPtr
  · exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToWords64 _ _)
        (SepProp.NoRO.pointsTo64 _ _))

private theorem noRO_mallocngRuntime (A : MallocngAddrs) (tp : BitVec 64) :
    SepProp.NoRO (MallocngRuntime A tp) := by
  unfold MallocngRuntime
  exact SepProp.NoRO.sepConj
    (SepProp.NoRO.sepExists fun _ => SepProp.NoRO.pointsTo32 _ _)
    (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo8 _ _) (SepProp.NoRO.pointsTo64 _ _))

private theorem noRO_mallocngCoreStA (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (liveCost peakCost : Nat) (st : MallocngSt) :
    SepProp.NoRO (MallocngCoreStA γ A brkStart brk liveCost peakCost st) := by
  unfold MallocngCoreStA MallocngCoreStInflightA
  exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
    (SepProp.NoRO.sepConj (noRO_mallocngLiveAuth _ _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToBytes _ _)
        (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
          (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
            (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
              (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo64 _ _)
                (SepProp.NoRO.sepConj (noRO_mallocngAuxvState _ _ _)
                  (SepProp.NoRO.sepConj (ByteMap_noRO _ _ _)
                    (SepProp.NoRO.sepConj (ProtNoneByteMap_noRO _ _ _)
                      (MappedSet_noRO _ _))))))))))

private theorem mallocngRoTablesAt_dup (A : MallocngAddrs) :
    (MallocngRoTablesAt A ∗ MallocngRoTablesAt A) = MallocngRoTablesAt A := by
  unfold MallocngRoTablesAt
  have h1 := pointsToBytesRO_dup A.sizeClasses mallocngSizeClassBytes
  have h2 := pointsToBytesRO_dup A.debruijnFree mallocngDebruijn32Table
  have h3 := pointsToBytesRO_dup A.medCntTab mallocngMedCntTabBytes
  have h4 := pointsToBytesRO_dup A.smallCntTab mallocngSmallCntTabBytes
  have h5 := pointsToBytesRO_dup A.debruijnAlloc mallocngDebruijn32Table
  have hPair :
      (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)) ∗
       ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table))) =
      (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗ (A.sizeClasses ↦ᵣ mallocngSizeClassBytes)) ∗
       ((A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗ (A.debruijnFree ↦ᵣ mallocngDebruijn32Table)) ∗
       ((A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗ (A.medCntTab ↦ᵣ mallocngMedCntTabBytes)) ∗
       ((A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗ (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes)) ∗
       ((A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table))) := by
    generalize (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) = R1
    generalize (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) = R2
    generalize (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) = R3
    generalize (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = R4
    generalize (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = R5
    ac_rfl
  rw [hPair, h1, h2, h3, h4, h5]

theorem mallocngHeap_roSplit
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    ∃ Ro Rw : SepProp,
      mallocngIface.MallocngHeap γ A tp brkStart brk b ivs = (Ro ∗ Rw) ∧
      (Ro ∗ Ro) = Ro ∧
      ∀ (h : Heap) (a : BitVec 64) (v : BitVec 8), SepProp.Holds Rw h → h a ≠ some (.ro v) := by
  refine ⟨MallocngRoTablesA A,
    (∃∗ st : MallocngSt,
      ⌜MallocngCountIvsWF b ivs st⌝ ∗
      MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st) ∗
      MallocngRuntime A tp,
    ?_, mallocngRoTablesAt_dup A, ?_⟩
  · show MallocngHeapImpl γ A tp brkStart brk b ivs = _
    rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq, sepConj_assoc]
  · exact SepProp.NoRO.sepConj
      (SepProp.NoRO.sepExists fun st =>
        SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
          (noRO_mallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st))
      (noRO_mallocngRuntime A tp)

theorem emptyMallocngStOpt_countIvs_wf (auxvPtr : BitVec 64)
    (snapOpt : Option MallocngAuxvSnap) :
    MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngStOpt auxvPtr snapOpt) := by
  refine ⟨Nat.le_refl 0, ?_, rfl, Nat.zero_le _, by simp [emptyMallocngStOpt, emptyMallocngSt], ?_⟩
  · simp [totalLiveCount, emptyMallocngStOpt, emptyMallocngSt]
  · intro g hg; simp [emptyMallocngStOpt, emptyMallocngSt] at hg

theorem emptyMallocngSt_countIvs_wf (auxvPtr : BitVec 64) :
    MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngSt auxvPtr) :=
  emptyMallocngStOpt_countIvs_wf auxvPtr none

private theorem bupd_sepExists {α : Type} (P : α → SepProp) :
    (∃∗ x : α, |==> P x) ⊢ |==> (∃∗ x : α, P x) :=
  Entails.sepExists_elim fun x => bupd_mono (Entails.sepExists_intro x)

private theorem ghostPair_init_untracked :
    emp ⊢ |==> (∃∗ γ : GhostName,
      MallocngLiveAuth γ .empty ∗
      ghostMapAuth (auxvGhost γ) (fun _ => none)) := by
  have h1 : emp ⊢ |==> (∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2 : emp ⊢ |==> (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h12 : emp ⊢ |==> ((∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ => none)) ∗
      (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ => none))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h1 h2
  refine Entails.trans h12 (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun γ1 => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun γ2 => ?_
  have hLive : liveGhost (natPair γ1 γ2) = γ1 := by simp [liveGhost, natUnpair_natPair]
  have hAuxv : auxvGhost (natPair γ1 γ2) = γ2 := by simp [auxvGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun γ => MallocngLiveAuth γ .empty ∗ ghostMapAuth (auxvGhost γ) (fun _ => none))
      (natPair γ1 γ2))
  unfold MallocngLiveAuth
  rw [hLive, hAuxv]
  exact Entails.refl _

theorem mallocngStartup_packA (γ : GhostName) (A : MallocngAddrs) (tp brkStart auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    (MallocngLiveAuth γ .empty ∗
     ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr ⊢
      mallocngIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget [] := by
  show _ ⊢ MallocngHeapImpl γ A tp brkStart brkStart mallocngZeroBudget []
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
  have hWf : MallocngWF A.base brkStart brkStart 0 0 (emptyMallocngSt auxvPtr) :=
    emptyMallocngSt_wf auxvPtr hBrkWf
  have hCountIvs : MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngSt auxvPtr) :=
    emptyMallocngSt_countIvs_wf auxvPtr
  let st0 := emptyMallocngSt auxvPtr
  have hStep1 :
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr ⊢
      (MallocngRoTablesA A ∗
        (⌜MallocngCountIvsWF mallocngZeroBudget [] st0⌝ ∗
          MallocngCoreStA γ A brkStart brkStart 0 0 st0)) ∗ MallocngRuntime A tp := by
    rw [pure_sepConj_of_true hCountIvs]
    unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState ByteMap ProtNoneByteMap MappedSet SetSep
    rw [pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = .empty := rfl
    have hSnap : st0.auxvSnap = none := rfl
    rw [hDom, hMap, hSnap]
    dsimp only [MallocngAuxvAuthMap]
    simp only [BigSep_nil, sepConj_emp]
    generalize (MallocngLiveAuth γ .empty) = P1
    generalize (ghostMapAuth (auxvGhost γ) (fun _ => none)) = P1b
    generalize (MallocngRoTablesA A) = P2
    generalize (A.ctx ↦ₛ st0.ctx.toBytes) = P3
    generalize (A.lock ↦₃₂ 0#32) = P4
    generalize (A.replaced ↦₃₂ 0#32) = P5
    generalize (A.aaReplaced ↦₃₂ 0#32) = P6
    generalize (MallocngRuntime A tp) = P7
    generalize ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) = P8
    generalize (MallocngAuxvAt st0.auxvPtr) = P9
    exact Entails.of_eq (by ac_rfl)
  have hEqLhs :
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesAt A ∗
      (A.ctx ↦ₛ List.replicate 928 0#8) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr =
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr := by
    simp only [MallocngRoTablesA, st0, emptyMallocngSt, emptyCtxFields_toBytes]
  rw [hEqLhs]
  refine Entails.trans hStep1 ?_
  exact sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_intro
      (P := fun st =>
        ⌜MallocngCountIvsWF mallocngZeroBudget [] st⌝ ∗
        MallocngCoreStA γ A brkStart brkStart 0 0 st)
      st0))

theorem mallocngInitResources_ok
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (_hTpGe : 0xa4 ≤ tp.toNat)
    (_hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName,
        mallocngIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget []) := by
  unfold MallocngStartupResources
  refine Entails.sepExists_elim fun auxvPtr => ?_
  let body :=
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr
  have h1 : body ⊢
      (|==> (∃∗ γ : GhostName,
        MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (fun _ => none))) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left ghostPair_init_untracked
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun γ => ?_
  exact mallocngStartup_packA γ A tp brkStart auxvPtr hBrkWf

set_option maxRecDepth 100000 in
private theorem mallocngMultiData_eq :
    VerifiedLibraries.mallocngMultiData = [
      { sym := "__malloc_size_classes", align := 4, readOnly := true, zeroTail := 0, bytes := mallocngSizeClassBytes },
      { sym := "debruijn32.4681", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngDebruijn32Table },
      { sym := "med_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngMedCntTabBytes },
      { sym := "small_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngSmallCntTabBytes },
      { sym := "debruijn32.5048", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngDebruijn32Table },
      { sym := "__malloc_lock", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__aligned_alloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__malloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__malloc_context", align := 8, readOnly := false, bytes := [], zeroTail := 928 }] := by
  decide +kernel

theorem mallocngLib_dataInit_eq (mpl : Obj.MultiPlacement) :
    let A := mallocngAddrsOfPlacement mpl
    VerifiedLibraries.mallocngLib.dataInit mpl =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32)) := by
  intro A
  have h32 : ∀ a : BitVec 64, (a ↦ₛ List.replicate 4 0#8) = (a ↦₃₂ 0#32) := by
    intro a; rw [pointsTo32_eq_pointsToBytes]; rfl
  have hData : VerifiedLibraries.mallocngLib.data = VerifiedLibraries.mallocngMultiData := rfl
  unfold Obj.MultiPlacedLib.dataInit
  rw [hData, mallocngMultiData_eq]
  unfold Obj.MultiPlacedLib.patchedData Obj.sepAll MallocngRoTablesAt
  simp only [List.map, List.foldl, List.append_nil, List.nil_append, List.replicate_zero, ↓reduceIte, h32]
  change
    ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
     (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
     (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
     (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
     (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.ctx ↦ₛ List.replicate 928 0#8)) =
    (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
      (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
      (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
      (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
      (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)) ∗
     (A.ctx ↦ₛ List.replicate 928 0#8) ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32))
  generalize (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) = D0
  generalize (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) = D1
  generalize (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) = D2
  generalize (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = D3
  generalize (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = D4
  generalize (A.lock ↦₃₂ 0#32) = D5
  generalize (A.aaReplaced ↦₃₂ 0#32) = D6
  generalize (A.replaced ↦₃₂ 0#32) = D7
  generalize (A.ctx ↦ₛ List.replicate 928 0#8) = D8
  ac_rfl

theorem mallocngPlacedInit_ok : mallocngInitStmt mallocngIface := by
  intro mpl tp brkStart auxvPtr R m A hTpGe hTpLe hBrkWf hSat
  have hStartup :
      (VerifiedLibraries.mallocngLib.dataInit mpl ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R := by
    rw [mallocngLib_dataInit_eq mpl]
    change
      ((MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32)) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R
    have hAssoc :
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32)) ∗
         MallocngRuntime A tp ∗
         ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
         MallocngAuxvAt auxvPtr ∗ R) =
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32) ∗
          MallocngRuntime A tp ∗
          ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr) ∗ R) := by ac_rfl
    rw [hAssoc]
    refine sepConj_mono_left ?_
    unfold MallocngStartupResources
    exact Entails.sepExists_intro
      (P := fun av =>
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ av) ∗
        MallocngAuxvAt av)
      auxvPtr
  have hSatStartup := Satisfies.of_entails hSat hStartup
  have hInit :=
    Satisfies.of_bupd_frame_left
      (mallocngInitResources_ok A tp brkStart hTpGe hTpLe hBrkWf)
      hSatStartup
  rw [sepExists_sepConj_left, satisfies_sepExists] at hInit
  obtain ⟨γ, hγ⟩ := hInit
  refine ⟨γ, ?_⟩
  rw [satisfies_bupd]
  exact hγ

/-! ## Tracked Startup `auxv` Initialization and Teardown -/

private theorem ghostPair_init_tracked (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) :
    emp ⊢ |==> (∃∗ γ : GhostName,
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
      MallocngAuxvTicket γ auxvPtr snap) := by
  have h1 : emp ⊢ |==> (∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2_0 : emp ⊢ |==> (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2_step :
      (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ => none)) ⊢
      |==> (∃∗ γ2 : GhostName,
        ghostMapAuth γ2 (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
        ghostMapElem γ2 0#64 (encodeAuxvSnap auxvPtr snap)) :=
    Entails.trans
      (Entails.sepExists_mono fun γ2 =>
        ghostMap_alloc γ2 (fun _ => none) 0#64 (encodeAuxvSnap auxvPtr snap) rfl)
      (bupd_sepExists _)
  have h2 := Entails.trans h2_0 (Entails.trans (bupd_mono h2_step) (bupd_trans _))
  have h12 : emp ⊢ |==> ((∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ => none)) ∗
      (∃∗ γ2 : GhostName,
        ghostMapAuth γ2 (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
        ghostMapElem γ2 0#64 (encodeAuxvSnap auxvPtr snap))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h1 h2
  refine Entails.trans h12 (bupd_mono ?_)
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun γ1 => ?_
  rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun γ2 => ?_
  have hLive : liveGhost (natPair γ1 γ2) = γ1 := by simp [liveGhost, natUnpair_natPair]
  have hAuxv : auxvGhost (natPair γ1 γ2) = γ2 := by simp [auxvGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun γ => (MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
        MallocngAuxvTicket γ auxvPtr snap)
      (natPair γ1 γ2))
  unfold MallocngLiveAuth MallocngAuxvTicket
  rw [hLive, hAuxv, sepConj_assoc]
  exact Entails.refl _

/-- Tracked startup initialization for `mallocngIface.MallocngCore`: preserves the concrete
    startup `auxv` table `(auxvPtr, preEntries, randPtr, sufEntries, nullVal, sec)` via an
    agreement ticket `MallocngAuxvTicket γ auxvPtr (...)` recoverable at teardown. -/
theorem mallocngInitCore_tracked
    (A : MallocngAddrs) (brkStart auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hPreTags : ∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSufTags : ∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hLen64 : preEntries.length + sufEntries.length ≤ 64)
    (hAuxvFit : auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48)
    (hRandFit : randPtr.toNat + 16 ≤ 2 ^ 48) :
    MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v])) ∗ ((randPtr + 8#64) ↦₆₄ sec) ⊢
      |==> (∃∗ γ : GhostName,
        mallocngIface.MallocngCore γ A brkStart brkStart mallocngZeroBudget [] ∗
        MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec)) := by
  let snap : MallocngAuxvSnap := (preEntries, randPtr, sufEntries, nullVal, sec)
  let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v]
  let body := MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ws) ∗ ((randPtr + 8#64) ↦₆₄ sec)
  have h1 : body ⊢ (|==> (∃∗ γ : GhostName, (MallocngLiveAuth γ .empty ∗
      ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
      MallocngAuxvTicket γ auxvPtr snap)) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left (ghostPair_init_tracked auxvPtr snap)
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun γ => ?_
  show _ ⊢ MallocngCoreImpl γ A brkStart brkStart mallocngZeroBudget [] ∗ MallocngAuxvTicket γ auxvPtr snap
  rw [MallocngCoreImpl_eq]
  let st0 := emptyMallocngStOpt auxvPtr (some snap)
  have hWf := emptyMallocngStOpt_wf (base := A.base) auxvPtr (some snap) hBrkWf
  have hCountIvs := emptyMallocngStOpt_countIvs_wf auxvPtr (some snap)
  have hAuxvWf : MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries :=
    ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit⟩
  have hPack :
      ((MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
       MallocngAuxvTicket γ auxvPtr snap) ∗ body ⊢
      (MallocngRoTablesA A ∗ (⌜MallocngCountIvsWF mallocngZeroBudget [] st0⌝ ∗
        MallocngCoreStA γ A brkStart brkStart 0 0 st0)) ∗ MallocngAuxvTicket γ auxvPtr snap := by
    dsimp only [body]; rw [pure_sepConj_of_true hCountIvs]
    unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState ByteMap ProtNoneByteMap MappedSet SetSep
    rw [pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = .empty := rfl
    have hPtr : st0.auxvPtr = auxvPtr := rfl
    have hSnap : st0.auxvSnap = some snap := rfl
    have hCtx : st0.ctx.toBytes = List.replicate 928 0#8 := emptyCtxFields_toBytes
    rw [hDom, hMap, hPtr, hSnap, hCtx]; dsimp only [snap, ws]; rw [pure_sepConj_of_true hAuxvWf]
    simp only [BigSep_nil, sepConj_emp, MallocngRoTablesA]; exact Entails.of_eq (by ac_rfl)
  exact Entails.trans hPack (sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_intro (P := fun st =>
      ⌜MallocngCountIvsWF mallocngZeroBudget [] st⌝ ∗ MallocngCoreStA γ A brkStart brkStart 0 0 st) st0)))

/-- Teardown of `mallocngIface.MallocngCore` paired with `MallocngAuxvTicket`: recovers the exact
    startup `__libc.auxv` pointer, `auxv` table words, and `AT_RANDOM` secret word. -/
theorem mallocngCore_teardown_auxv
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64) :
    mallocngIface.MallocngCore γ A brkStart brk b ivs ∗
    MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec) ⊢
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      (auxvPtr ↦₆₄*
        ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
          fun (t, v) => [t, v])) ∗
      ((randPtr + 8#64) ↦₆₄ sec) ∗
      ∃∗ R_dead : SepProp, R_dead := by
  let snap : MallocngAuxvSnap := (preEntries, randPtr, sufEntries, nullVal, sec)
  show MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngAuxvTicket γ auxvPtr snap ⊢ _
  rw [MallocngCoreImpl_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun st => ?_
  unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState MallocngAuxvTicket
  let auxvBody : SepProp :=
    match st.auxvSnap with
    | none => MallocngAuxvAt st.auxvPtr
    | some (pe, rp, se, nv, sc) =>
      ⌜MallocngAuxvConcreteWf st.auxvPtr pe rp se⌝ ∗
      (st.auxvPtr ↦₆₄* ((pe ++ [(25#64, rp)] ++ se ++ [(0#64, nv)]).flatMap fun (t, v) => [t, v])) ∗
      ((rp + 8#64) ↦₆₄ sc)
  let restCore : SepProp :=
    MallocngRoTablesA A ∗ ⌜MallocngCountIvsWF b ivs st⌝ ∗
    ⌜MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
    MallocngLiveAuth γ st.liveMap ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
    (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  refine Entails.trans (Q :=
      (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr st.auxvSnap) ∗
       ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)) ∗
      (((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ auxvBody ∗ restCore))
    (Entails.of_eq (by dsimp only [auxvBody, restCore]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (ghostMap_lookup (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr st.auxvSnap)
      0#64 (encodeAuxvSnap auxvPtr snap))) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hLookup => ?_
  dsimp only [auxvBody]
  rcases hSnap : st.auxvSnap with _ | ⟨pe, rp, se, nv, sc⟩
  · rw [hSnap] at hLookup
    simp [MallocngAuxvAuthMap] at hLookup
  · rw [hSnap] at hLookup
    simp only [MallocngAuxvAuthMap, ↓reduceIte, Option.some.injEq] at hLookup
    have hDec := congrArg decodeAuxvSnap hLookup
    rw [decodeAuxvSnap_encodeAuxvSnap, decodeAuxvSnap_encodeAuxvSnap] at hDec
    have ⟨hPtrEq, hSnapEq⟩ := Prod.mk.inj hDec
    dsimp only [snap] at hSnapEq
    have ⟨hPe, h1⟩ := Prod.mk.inj hSnapEq
    have ⟨hRp, h2⟩ := Prod.mk.inj h1
    have ⟨hSe, h3⟩ := Prod.mk.inj h2
    have ⟨hNv, hSc⟩ := Prod.mk.inj h3
    rw [hPtrEq, hPe, hRp, hSe, hNv, hSc]
    let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v]
    let R_dead : SepProp :=
      (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
       ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)) ∗
      ⌜MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries⌝ ∗ restCore
    refine Entails.trans (Q :=
        ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗ (auxvPtr ↦₆₄* ws) ∗ ((randPtr + 8#64) ↦₆₄ sec) ∗ R_dead)
      (Entails.of_eq (by dsimp only [R_dead, ws, snap]; ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.sepExists_intro (P := fun R => R) R_dead)))

/-! ## Read-Only (`mallocngRoIface`) Structural, Splitting, and Startup Laws -/

private theorem noRO_mallocngCoreStNoAuxvA (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) :
    SepProp.NoRO (MallocngCoreStNoAuxvA γ A brkStart brk liveCost peakCost st) := by
  unfold MallocngCoreStNoAuxvA
  exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
    (SepProp.NoRO.sepConj (noRO_mallocngLiveAuth _ _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToBytes _ _)
        (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
          (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
            (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
              (SepProp.NoRO.sepConj (ByteMap_noRO _ _ _)
                (SepProp.NoRO.sepConj (ProtNoneByteMap_noRO _ _ _)
                  (MappedSet_noRO _ _))))))))

private theorem mallocngWFInflight_with_auxvPtr {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {p : BitVec 64} :
    MallocngWFInflight inflight base brkStart brk liveCost peakCost { st with auxvPtr := p } =
      MallocngWFInflight inflight base brkStart brk liveCost peakCost st := by
  have hRw : OwnedRwByte { st with auxvPtr := p } = OwnedRwByte st := by
    funext a; rfl
  have hPn : OwnedProtNoneByte { st with auxvPtr := p } = OwnedProtNoneByte st := by
    funext a; rfl
  have hMp : OwnedMappedByte { st with auxvPtr := p } = OwnedMappedByte st := by
    funext a; rfl
  have hDyn : dynamicRootRegions { st with auxvPtr := p } = dynamicRootRegions st := rfl
  apply propext
  constructor
  · intro h
    exact {
      base_wf := h.base_wf
      brk_bounds := h.brk_bounds
      ctx_lens := h.ctx_lens
      initDone_wf := h.initDone_wf
      initZero_wf := h.initZero_wf
      bounces_wf := h.bounces_wf
      usage_wf := h.usage_wf
      brk_mode_wf := h.brk_mode_wf
      metaAreas_wf := h.metaAreas_wf
      guard_avail_wf := h.guard_avail_wf
      inflight_wf := h.inflight_wf
      free_bump_metas_wf := h.free_bump_metas_wf
      groups_nodup := h.groups_nodup
      groups_wf := h.groups_wf
      regions_disjoint := h.regions_disjoint
      active_wf := h.active_wf
      liveMap_wf := h.liveMap_wf
      live_le_peak := h.live_le_peak
      effCost_le_live := h.effCost_le_live
      meta_pages_bound := h.meta_pages_bound
      empty_groups_bound := h.empty_groups_bound
      masterDom_wf := by simpa only [hRw, hPn, hMp, hDyn] using h.masterDom_wf
    }
  · intro h
    exact {
      base_wf := h.base_wf
      brk_bounds := h.brk_bounds
      ctx_lens := h.ctx_lens
      initDone_wf := h.initDone_wf
      initZero_wf := h.initZero_wf
      bounces_wf := h.bounces_wf
      usage_wf := h.usage_wf
      brk_mode_wf := h.brk_mode_wf
      metaAreas_wf := h.metaAreas_wf
      guard_avail_wf := h.guard_avail_wf
      inflight_wf := h.inflight_wf
      free_bump_metas_wf := h.free_bump_metas_wf
      groups_nodup := h.groups_nodup
      groups_wf := h.groups_wf
      regions_disjoint := h.regions_disjoint
      active_wf := h.active_wf
      liveMap_wf := h.liveMap_wf
      live_le_peak := h.live_le_peak
      effCost_le_live := h.effCost_le_live
      meta_pages_bound := h.meta_pages_bound
      empty_groups_bound := h.empty_groups_bound
      masterDom_wf := by simpa only [hRw, hPn, hMp, hDyn] using h.masterDom_wf
    }

/-- Factoring equivalence for `MallocngCoreRoImpl`: separates the duplicable RO tables and RO
    `__libc.auxv`/`auxv` bundle outside the `∃∗ st` quantifier. -/
theorem mallocngCoreRo_factor
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngCoreRoImpl γ A brkStart brk b ivs =
      ((MallocngRoTablesA A ∗ MallocngLibcAuxvRoAt A) ∗
       (∃∗ st : MallocngSt,
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStNoAuxvA γ A brkStart brk b.liveCost b.peakCost st)) := by
  rw [MallocngCoreRoImpl_eq]
  apply SepProp.eq_of_entails
  · rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun st => ?_
    unfold MallocngCoreStModeA MallocngCoreStInflightModeA MallocngAuxvPtrCell MallocngAuxvStateRo
      MallocngCoreStNoAuxvA MallocngLibcAuxvRoAt
    simp only [↓reduceIte]
    refine Entails.trans
      (Entails.of_eq (show _ =
        (MallocngRoTablesA A ∗ (((A.libc + 8#64) ↦₆₄ᵣ st.auxvPtr) ∗ MallocngAuxvRoAt st.auxvPtr)) ∗
        (⌜MallocngCountIvsWF b ivs st⌝ ∗
         ⌜MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
         MallocngLiveAuth γ st.liveMap ∗
         (A.ctx ↦ₛ st.ctx.toBytes) ∗
         (A.lock ↦₃₂ 0#32) ∗
         (A.replaced ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32) ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st)) by ac_rfl))
      ?_
    refine sepConj_mono (sepConj_mono_right (Entails.sepExists_right st.auxvPtr (Entails.refl _))) ?_
    exact Entails.sepExists_right st (Entails.refl _)
  · unfold MallocngLibcAuxvRoAt
    rw [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun st => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_left]
    refine Entails.sepExists_elim fun auxvPtr => ?_
    let st' : MallocngSt := { st with auxvPtr := auxvPtr }
    have hCountEq : MallocngCountIvsWF b ivs st' = MallocngCountIvsWF b ivs st := rfl
    have hWfEq : MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st' =
        MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st :=
      mallocngWFInflight_with_auxvPtr
    have hBM : ByteMap st.masterDom (OwnedRwByte st') st.byteVal =
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal := rfl
    have hPN : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st') st.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := rfl
    have hMS : MappedSet st.masterDom (OwnedMappedByte st') =
        MappedSet st.masterDom (OwnedMappedByte st) := rfl
    have hStep :
        ((MallocngRoTablesA A ∗ (((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr)) ∗
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStNoAuxvA γ A brkStart brk b.liveCost b.peakCost st) =
        (MallocngRoTablesA A ∗
         (⌜MallocngCountIvsWF b ivs st'⌝ ∗
          MallocngCoreStModeA true γ A brkStart brk b.liveCost b.peakCost st')) := by
      unfold MallocngCoreStModeA MallocngCoreStInflightModeA MallocngAuxvPtrCell MallocngAuxvStateRo
        MallocngCoreStNoAuxvA
      simp only [↓reduceIte]
      have hPtr : st'.auxvPtr = auxvPtr := rfl
      have hMap : st'.liveMap = st.liveMap := rfl
      have hCtx : st'.ctx = st.ctx := rfl
      have hDom : st'.masterDom = st.masterDom := rfl
      have hBv : st'.byteVal = st.byteVal := rfl
      rw [hCountEq, hWfEq, hPtr, hMap, hCtx, hDom, hBv, hBM, hPN, hMS]
      ac_rfl
    rw [hStep]
    exact sepConj_mono_right (Entails.sepExists_right st' (Entails.refl _))

theorem mallocngHeapRo_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngRoIface.MallocngHeap γ A tp brkStart brk b ivs =
      (mallocngRoIface.MallocngCore γ A brkStart brk b ivs ∗ MallocngRuntime A tp) :=
  MallocngHeapRoImpl_eq γ A tp brkStart brk b ivs

theorem mallocngHeapRo_roSplit
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    ∃ Ro Rw : SepProp,
      mallocngRoIface.MallocngHeap γ A tp brkStart brk b ivs = (Ro ∗ Rw) ∧
      (Ro ∗ Ro) = Ro ∧
      ∀ (h : Heap) (a : BitVec 64) (v : BitVec 8), SepProp.Holds Rw h → h a ≠ some (.ro v) := by
  refine ⟨MallocngRoTablesA A ∗ MallocngLibcAuxvRoAt A,
    (∃∗ st : MallocngSt,
      ⌜MallocngCountIvsWF b ivs st⌝ ∗
      MallocngCoreStNoAuxvA γ A brkStart brk b.liveCost b.peakCost st) ∗
      MallocngRuntime A tp,
    ?_, sepConj_dup (mallocngRoTablesAt_dup A) (mallocngLibcAuxvRoAt_dup A), ?_⟩
  · show MallocngHeapRoImpl γ A tp brkStart brk b ivs = _
    rw [MallocngHeapRoImpl_eq, mallocngCoreRo_factor, sepConj_assoc]
  · exact SepProp.NoRO.sepConj
      (SepProp.NoRO.sepExists fun st =>
        SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
          (noRO_mallocngCoreStNoAuxvA γ A brkStart brk b.liveCost b.peakCost st))
      (noRO_mallocngRuntime A tp)

theorem mallocngRoStartup_packA (γ : GhostName) (A : MallocngAddrs) (tp brkStart auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngLiveAuth γ .empty ∗
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
    MallocngAuxvRoAt auxvPtr ⊢
      mallocngRoIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget [] := by
  show _ ⊢ MallocngHeapRoImpl γ A tp brkStart brkStart mallocngZeroBudget []
  rw [MallocngHeapRoImpl_eq, MallocngCoreRoImpl_eq]
  let st0 := emptyMallocngSt auxvPtr
  have hWf : MallocngWF A.base brkStart brkStart 0 0 st0 :=
    emptyMallocngSt_wf auxvPtr hBrkWf
  have hCountIvs : MallocngCountIvsWF mallocngZeroBudget [] st0 :=
    emptyMallocngSt_countIvs_wf auxvPtr
  have hStep1 :
      MallocngLiveAuth γ .empty ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ᵣ st0.auxvPtr) ∗
      MallocngAuxvRoAt st0.auxvPtr ⊢
      (MallocngRoTablesA A ∗
        (⌜MallocngCountIvsWF mallocngZeroBudget [] st0⌝ ∗
          MallocngCoreStModeA true γ A brkStart brkStart 0 0 st0)) ∗ MallocngRuntime A tp := by
    rw [pure_sepConj_of_true hCountIvs]
    unfold MallocngCoreStModeA MallocngCoreStInflightModeA MallocngAuxvPtrCell MallocngAuxvStateRo
      ByteMap ProtNoneByteMap MappedSet SetSep
    simp only [↓reduceIte]
    rw [pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = .empty := rfl
    rw [hDom, hMap]
    simp only [BigSep_nil, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)
  have hEqLhs :
      (MallocngLiveAuth γ .empty ∗
       MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
       MallocngAuxvRoAt auxvPtr) =
      (MallocngLiveAuth γ .empty ∗
       MallocngRoTablesA A ∗
       (A.ctx ↦ₛ st0.ctx.toBytes) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ᵣ st0.auxvPtr) ∗
       MallocngAuxvRoAt st0.auxvPtr) := by
    simp only [MallocngRoTablesA, st0, emptyMallocngSt, emptyCtxFields_toBytes]
  rw [hEqLhs]
  refine Entails.trans hStep1 ?_
  exact sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_intro
      (P := fun st =>
        ⌜MallocngCountIvsWF mallocngZeroBudget [] st⌝ ∗
        MallocngCoreStModeA true γ A brkStart brkStart 0 0 st)
      st0))

private theorem ghostLive_init_empty :
    emp ⊢ |==> (∃∗ γ : GhostName, MallocngLiveAuth γ .empty) := by
  have h1 : emp ⊢ |==> (∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  refine Entails.trans h1 (bupd_mono ?_)
  refine Entails.sepExists_elim fun γ1 => ?_
  have hLive : liveGhost (natPair γ1 0) = γ1 := by simp [liveGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro (P := fun γ => MallocngLiveAuth γ .empty) (natPair γ1 0))
  unfold MallocngLiveAuth
  rw [hLive]
  exact Entails.refl _

/-- Direct RO startup resource packing from already-frozen `__libc.auxv` and `MallocngAuxvRoAt`. -/
theorem mallocngRoInit_resources_ro
    (A : MallocngAddrs) (tp brkStart auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
    MallocngAuxvRoAt auxvPtr ⊢
      |==> (∃∗ γ : GhostName,
        mallocngRoIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget []) := by
  let body :=
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
    MallocngAuxvRoAt auxvPtr
  have h1 : body ⊢ (|==> (∃∗ γ : GhostName, MallocngLiveAuth γ .empty)) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left ghostLive_init_empty
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun γ => ?_
  exact mallocngRoStartup_packA γ A tp brkStart auxvPtr hBrkWf

/-- Backwards-compatible startup resource initialization for `mallocngRoIface` from RW
    `MallocngStartupResources` by freezing `__libc.auxv` and `MallocngAuxvAt` to `.ro`. -/
theorem mallocngRoInit_resources
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (_hTpGe : 0xa4 ≤ tp.toNat)
    (_hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName,
        mallocngRoIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget []) := by
  unfold MallocngStartupResources
  refine Entails.sepExists_elim fun auxvPtr => ?_
  have hFreeze :
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr) ⊢
      |==> (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
       MallocngAuxvRoAt auxvPtr) := by
    refine Entails.trans (Q :=
        (MallocngRoTablesAt A ∗
         (A.ctx ↦ₛ List.replicate 928 0#8) ∗
         (A.lock ↦₃₂ 0#32) ∗
         (A.replaced ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32) ∗
         MallocngRuntime A tp) ∗
        (|==> (((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr))) ?_ ?_
    · refine Entails.trans (Entails.of_eq (by ac_rfl))
        (sepConj_mono_right
          (bupd_sep (pointsTo64_freeze_ro (A.libc + 8#64) auxvPtr) (mallocngAuxvAt_freeze_ro auxvPtr)))
    · refine Entails.trans (bupd_frame_l _ _) (bupd_mono ?_)
      exact Entails.of_eq (by ac_rfl)
  exact Entails.trans hFreeze
    (Entails.trans (bupd_mono (mallocngRoInit_resources_ro A tp brkStart auxvPtr hBrkWf)) (bupd_trans _))

/-- Direct RO startup initialization for `mallocngRoIface` from already-frozen
    `((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗ MallocngAuxvRoAt auxvPtr`. -/
theorem mallocngRoInit_ro
    (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory)
    (_hTpGe : 0xa4 ≤ tp.toNat)
    (_hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hSat : m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
      (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
      MallocngAuxvRoAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      m ⊨ |==> (mallocngRoIface.MallocngHeap γ (mallocngAddrsOfPlacement mpl) tp brkStart brkStart
        mallocngZeroBudget [] ∗ R) := by
  let A := mallocngAddrsOfPlacement mpl
  have hPrep :
      (VerifiedLibraries.mallocngLib.dataInit mpl ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
       MallocngAuxvRoAt auxvPtr ∗ R) ⊢
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ᵣ auxvPtr) ∗
       MallocngAuxvRoAt auxvPtr) ∗ R := by
    rw [mallocngLib_dataInit_eq mpl]
    exact Entails.of_eq (by ac_rfl)
  have hSatPrep := Satisfies.of_entails hSat hPrep
  have hInit :=
    Satisfies.of_bupd_frame_left
      (mallocngRoInit_resources_ro A tp brkStart auxvPtr hBrkWf)
      hSatPrep
  rw [sepExists_sepConj_left, satisfies_sepExists] at hInit
  obtain ⟨γ, hγ⟩ := hInit
  refine ⟨γ, ?_⟩
  rw [satisfies_bupd]
  exact hγ

/-- Backwards-compatible RW startup initialization (`mallocngInitStmt mallocngRoIface`) by
    freezing `__libc.auxv` and `MallocngAuxvAt` to `.ro`. -/
theorem mallocngRoInit_ok : mallocngInitStmt mallocngRoIface := by
  intro mpl tp brkStart auxvPtr R m A hTpGe hTpLe hBrkWf hSat
  have hStartup :
      (VerifiedLibraries.mallocngLib.dataInit mpl ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R := by
    rw [mallocngLib_dataInit_eq mpl]
    have hAssoc :
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32)) ∗
         MallocngRuntime A tp ∗
         ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
         MallocngAuxvAt auxvPtr ∗ R) =
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32) ∗
          MallocngRuntime A tp ∗
          ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr) ∗ R) := by ac_rfl
    rw [hAssoc]
    refine sepConj_mono_left ?_
    unfold MallocngStartupResources
    exact Entails.sepExists_intro
      (P := fun av =>
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ av) ∗
        MallocngAuxvAt av)
      auxvPtr
  have hSatStartup := Satisfies.of_entails hSat hStartup
  have hInit :=
    Satisfies.of_bupd_frame_left
      (mallocngRoInit_resources A tp brkStart hTpGe hTpLe hBrkWf)
      hSatStartup
  rw [sepExists_sepConj_left, satisfies_sepExists] at hInit
  obtain ⟨γ, hγ⟩ := hInit
  refine ⟨γ, ?_⟩
  rw [satisfies_bupd]
  exact hγ

end VerifiedLibraries.Mallocng.Proofs
