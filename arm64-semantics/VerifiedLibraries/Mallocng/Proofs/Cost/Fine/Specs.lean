/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.FreeBridge
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupStage7
public import VerifiedLibraries.Mallocng.Proofs.PlacedLibcFreeHelpers
public import VerifiedLibraries.Mallocng.Proofs.Cost.TokSpecs
public import VerifiedLibraries.Mallocng.Proofs.Cost.ModelOom

/-!
# Shared Internal Placed Contracts for the Fine Cost Model (`…Proofs.Cost.Fine.Specs`)

- **Role**: `Role::Proof` (untrusted).
- **Purpose**: freezes the internal cross-block Hoare contracts and OOM/reserve bridge lemmas shared
  by `AllocMeta`, `AllocGroup`, `AllocSlot`, `MallocImpl`, `Free`, `Realloc`, and `Entries` under
  `VerifiedLibraries.Mallocng.Proofs.Cost.Fine`:
  - `AllocMetaFineStmt` / `call_placed_allocMeta_fine` (`blk07`, `224` B stack)
  - `AllocSlotFineStmt` / `call_placed_allocSlot_fine` (`blk08`, `(allocSlotDepthBound sc + 1) * 96 + 224` B stack)
  - `LibcMallocImplFineRawStmt` / `call_placed_libcMallocImpl_fine_raw` (`blk09`, `704` B stack,
    exposing pre-enframe `st1` for both `malloc` and `aligned_alloc` reframing)
  - `LibcMallocImplFineStmt` / `DefaultMallocFineStmt` / `call_placed_defaultMalloc_fine` (`blk09` / `blk04`)
  - `NontrivialFreeFineStmt` / `call_placed_nontrivialFree_fine` (`blk05`)
  - `LibcFreeFineStmt` / `call_placed_libcFree_fine` (`blk06`, `272` B stack)
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Step Reserve, Budget, and OOM Bridge Lemmas -/

/-- At `maxIvs = 16`, `MallocngPlacedOomCond` is definitionally `MallocngStepOomCond`. -/
theorem placedOomCond_16_eq_stepOomCond (svc : State → State) (stepB : Nat) (s0 sf : State) :
    MallocngPlacedOomCond svc 16 stepB s0 sf = MallocngStepOomCond svc stepB s0 sf :=
  rfl

theorem placedOomCond_to_stepOomCond {svc : State → State} {k b1 b2 : Nat} {s0 sf : State}
    (hk : k ≤ 16) (hb : b1 ≤ b2) (h : MallocngPlacedOomCond svc k b1 s0 sf) :
    MallocngStepOomCond svc b2 s0 sf := by
  rw [← placedOomCond_16_eq_stepOomCond]
  exact MallocngPlacedOomCond.mono hk hb h

theorem stepOomCond_mono {svc : State → State} {b1 b2 : Nat} {s0 sf : State}
    (hb : b1 ≤ b2) (h : MallocngStepOomCond svc b1 s0 sf) :
    MallocngStepOomCond svc b2 s0 sf := by
  rw [← placedOomCond_16_eq_stepOomCond] at h ⊢
  exact MallocngPlacedOomCond.mono (Nat.le_refl 16) hb h

/-- Unfolds the `if ok then stepReserve ev bgt else stepReserve (.alloc 0) bgt` guard into a single
    `FineStepBound`. -/
theorem fine_stepB_ite (ok : Bool) (ev : AllocEvent) (bgt : FineBudget) :
    (if ok then mallocngFineCostModel.stepReserve ev bgt
      else mallocngFineCostModel.stepReserve (.alloc 0) bgt) =
      FineStepBound (fineMaxMetaAreas bgt) (if ok then evReqBytes ev else 0) := by
  cases ok <;> simp [mallocngFineCostModel_stepReserve, fineStepReserve, evReqBytes]

theorem fine_step_free_ite (p : BitVec 64) (align n : Nat) (bgt : FineBudget) :
    (if (p == 0#64) = true then bgt else mallocngFineCostModel.step (.free align n) bgt) =
      if p == 0#64 then bgt else fineStepFree n bgt := by
  cases (p == 0#64) <;> simp [mallocngFineCostModel_step, fineStep]

/-- `realloc`'s exact ghost-alignment reserve `mallocngReallocRes a n` is bounded by
    `mallocngAlignedEffSize al n = evReqBytes (.realloc al oldSz n)` whenever `a ≤ max al 16`. -/
theorem fine_reallocRes_le {a al : Nat} (n : Nat) (ha : a ≤ max al 16) :
    mallocngReallocRes a n ≤ mallocngAlignedEffSize al n := by
  unfold mallocngReallocRes mallocngAlignedEffSize
  have := Nat.le_max_left al 16
  have := Nat.le_max_right al 16
  split
  · have : max al 16 = 16 := Nat.max_eq_right (by omega)
    omega
  · have : max al 16 = al := Nat.max_eq_left (by omega)
    omega

theorem fineStepBound_slot_le (maxMeta reqBytes sc : Nat) (hsc : sc < 48) :
    (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576 ≤
      FineStepBound maxMeta reqBytes := by
  have hd : allocSlotDepthBound sc ≤ 3 := allocSlotDepthBound_le_three sc
  have _ := hsc
  have hMul : (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta ≤ 4 * FineMetaStep maxMeta :=
    Nat.mul_le_mul_right _ (by omega)
  unfold FineStepBound
  omega

theorem fineStepBound_large_le (maxMeta len reqBytes : Nat) (hLen : len ≤ reqBytes + 8195) :
    FineMetaStep maxMeta + len ≤ FineStepBound maxMeta reqBytes := by
  unfold FineStepBound
  omega

/-! ## 2. Placed `nontrivial_free` (`blk05`) & `__libc_free` (`blk06`) Fine Contracts -/

/-- Internal `nontrivial_free(g, i)` (`blk05`, `224` B stack) contract preserving all structural
    postconditions of `nontrivialFreeTopPlacedSpec` plus `GroupsFreeMono st.groups st'.groups`. -/
def nontrivialFreeFinePlacedSpec [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat) (ro : Bool := false) : Spec Unit :=
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = g.metaPtr ∧
       s0.readReg64 .x1 = BitVec.ofNat 64 idx ∧
       g ∈ st.groups ∧
       ∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .claimed⌝ ∗
      stackFrame s0 224 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s0.brk b.liveCost b.peakCost st
    post := fun (_ : Unit) s0 sf =>
      ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s0 sf ∧
         sf.brk = s0.brk ∧
         sf.tpidrEl0 = s0.tpidrEl0 ∧
         sf.mem.perm = s0.mem.perm ∧
         MallocngMappedDelta 0 0 s0.mem sf.mem ∧
         totalLiveCount st' ≤ totalLiveCount st ∧
         (dynamicRootRegions st').length ≤ (dynamicRootRegions st).length ∧
         st'.metaAreas.length ≤ st.metaAreas.length ∧
         Cost.GroupsGrpMono st.groups st'.groups ∧
         GroupsFreeMono st.groups st'.groups⌝ ∗
        stackFrame s0 224 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStModeA ro γ maddrs brkStart s0.brk b.liveCost b.peakCost st' ∗
        if sf.readReg64 .x1 = 0#64 then
          ⌜dynamicRootRegions st' = dynamicRootRegions st⌝
        else
          let miBase := sf.readReg64 .x0
          let miLen := (sf.readReg64 .x1).toNat
          ⌜0 < miLen ∧
           4096 ∣ miBase.toNat ∧
           4096 ∣ miLen ∧
           miBase.toNat + miLen ≤ 2 ^ 48 ∧
           (∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
             InRegion miBase miLen a ∨ MallocngInIntervals (dynamicRootRegions st') a)⌝ ∗
          memRegion miBase miLen ∗
          memMapped miBase miLen
  }

def NontrivialFreeFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat),
    subroutine_ok (mallocngBlockProg mmpl 5 msvc) (mbase 5)
      (nontrivialFreeFinePlacedSpec γ brkStart b st g idx ro)

theorem call_placed_nontrivialFree_fine {ro : Bool} (h : NontrivialFreeFineStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (brkStart : BitVec 64) (b : MallocngBudget)
    (st : MallocngSt) (g : GroupDesc) (idx : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 5) (nontrivialFreeFinePlacedSpec γ brkStart b st g idx ro) :=
  subroutine_ok_block_to_block (j := 5) (by decide) (h γ brkStart b st g idx) hext hsvc

/-- Internal `272`-byte stack contract for placed `__libc_free(p)` (`blk06`) on
    `mallocngFineCostModel` / `mallocngFineModeIface ro`, shared by `"free"` (`blk03`) and `realloc`
    Stage 4 (`blk14`). -/
def libcFreeFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (align n : Nat)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (ro : Bool := false) : Spec Unit :=
  let bgt' := if p == 0#64 then bgt else fineStepFree n bgt
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p⌝ ∗
      stackFrame s0 272 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
      if p = 0#64 then emp
      else MallocngTightBlock γ p n (max align 16) ∗ memRegion p n
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 0 0 s0.mem sf.mem⌝ ∗
      stackFrame s0 272 ∗
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
        γ maddrs tp brkStart bgt' ivs0 s0 sf
  }

def LibcFreeFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p : BitVec 64) (align n : Nat)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)),
    subroutine_ok (mallocngBlockProg mmpl 6 msvc) (mbase 6)
      (libcFreeFineSpec γ tp brkStart p align n bgt ivs0 ro)

theorem call_placed_libcFree_fine {ro : Bool} (h : LibcFreeFineStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart p : BitVec 64) (align n : Nat)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 6) (libcFreeFineSpec γ tp brkStart p align n bgt ivs0 ro) :=
  subroutine_ok_block_to_block (j := 6) (by decide) (h γ tp brkStart p align n bgt ivs0) hext hsvc

/-! ## 3. Placed `__malloc_alloc_meta` (`blk07`) & `alloc_slot` (`blk08`) Fine Contracts -/

/-- Fine placed contract for `__malloc_alloc_meta()` (`blk07`, `224` B stack), threading both the
    coarse `peakCount` `metaAreas` bound and `(FineSplitInv bL bP, FineMetaStep maxMeta)` whenever
    `st.metaAreas.length ≤ maxMeta + 5`. -/
def AllocMetaFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (inflight : Nat) (_hInflight : inflight ≤ 7)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount)
    (_hFine : FineSplitInv bL bP st)
    (_hMaStep : st.metaAreas.length ≤ maxMeta + 5),
    subroutine_ok (mallocngBlockProg mmpl 7 msvc) (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        stackFrame s0 224 ∗
        MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧
           sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
           m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧
           st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧
           st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ st.metaAreas.length + 1 ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           FineSplitInv bL bP st' ∧
           st'.ctx.active = st.ctx.active ∧
           st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧
           st'.ctx.bounces = st.ctx.bounces ∧
           st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) →
               st'.byteVal a = st.byteVal a) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗
          MallocngRuntime maddrs tp ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝
    })

theorem call_placed_allocMeta_fine {ro : Bool} (h : AllocMetaFineStmt ro) [MallocngMultiPlacement]
    {P : Program}
    (inflight : Nat) (hInflight : inflight ≤ 7)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st)
    (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        stackFrame s0 224 ∗
        MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧
           sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
           m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧
           st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧
           st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ st.metaAreas.length + 1 ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           FineSplitInv bL bP st' ∧
           st'.ctx.active = st.ctx.active ∧
           st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧
           st'.ctx.bounces = st.ctx.bounces ∧
           st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) →
               st'.byteVal a = st.byteVal a) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗
          MallocngRuntime maddrs tp ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝
    }) :=
  subroutine_ok_block_to_block (j := 7) (by decide)
    (h inflight hInflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st
      hCount hFine hMaStep) hext hsvc

/-- Postcondition body of `AllocSlotFineAtDepthStmt` (strengthened with `st'.ctx.active[k]`
    preservation on `k < sc` for nested `alloc_group` recursion). -/
abbrev AllocSlotFinePostProp [MallocngMultiPlacement]
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st0 : MallocngSt) (s0 sf : State) (ro : Bool := false) : SepProp :=
  ∃∗ st' : MallocngSt,
  ∃∗ idx : Nat,
    ⌜MallocngProcPreserved s0 sf ∧
     st'.reservedMetas = st0.reservedMetas ∧
     st'.liveMap = st0.liveMap ∧
     totalLiveEffCost st' = totalLiveEffCost st0 ∧
     totalLiveCount st' = totalLiveCount st0 ∧
     st'.metaAreas.length ≤ st0.metaAreas.length + allocSlotDepthBound sc + 1 ∧
     st'.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
     FineSplitInv bL bP st' ∧
     (∀ k < sc, (stClassBound st' k).le (stClassBound st0 k)) ∧
     (∀ k : Nat, k < sc → ∀ hk1 : k < st'.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
       st'.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
     sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
     (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
       g.sc = sc ∧
       req + 4 ≤ g.stride ∧
       g.metaPtr = st'.ctx.active[sc]'hAct ∧
       g.slots[idx]'hIdx = .claimed ∧
       (g.isMmapped = true →
         ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
     MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
       ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0.mem sf.mem ∧
     (∀ U : Nat, peakCount ≤ U →
       Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st'.groups)⌝ ∗
    stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
    MallocngRoTablesA maddrs ∗
    MallocngRuntime maddrs tp ∗
    MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'

/-- Depth-indexed `alloc_slot(sc, req)` (`blk08`) contract used by bounded induction on
    `allocSlotDepthBound sc ≤ 3`. -/
def AllocSlotFineAtDepthStmt (sc : Nat) (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (req inflight : Nat) (_hSc : sc < 48)
    (_hReqLo : allocSlotReqLo sc ≤ req) (_hReqHi : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount)
    (_hClaim0 : totalClaimedSlots st = 0)
    (_hFine : FineSplitInv bL bP st)
    (_hRoom : AllocSlotOccRoom bP st sc)
    (_hMaStep : st.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc)),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧ (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        AllocSlotFinePostProp sc req inflight γ tp brkStart liveCost peakCost peakCount
          bL bP maxMeta st s0 sf ro
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝ })

abbrev AllocSlotFinePost [MallocngMultiPlacement]
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st0 : MallocngSt) (s0 sf : State) (P_f : SepProp)
    (ro : Bool := false) : Prop :=
  (P_f ⊢ AllocSlotFinePostProp sc req inflight γ tp brkStart liveCost peakCost peakCount
    bL bP maxMeta st0 s0 sf ro) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Cut-point contract for `alloc_group` (`blk08`, `+ allocSlotOff_ag`), allowing `AllocGroup.lean`
    and `AllocSlot.lean` to be proved with zero mutual imports. -/
def AllocGroupFineAtOffStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (sc req inflight : Nat) (_hSc : sc < 48)
    (_hReqLo : allocSlotReqLo sc ≤ req) (_hReqHi : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (_hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc →
      AllocSlotFineAtDepthStmt pSc ro)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st0 st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount)
    (_hClaim0 : totalClaimedSlots st0 = 0)
    (_hFine0 : FineSplitInv bL bP st0)
    (_hRoom0 : AllocSlotOccRoom bP st0 sc)
    (_hMaStep0 : st0.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc))
    (_hNd0 : (st0.groups.map (·.metaPtr)).Nodup)
    (_hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    (_hStRel : st.reservedMetas = st0.reservedMetas ∧ st.liveMap = st0.liveMap ∧
      totalLiveEffCost st = totalLiveEffCost st0 ∧ totalLiveCount st = totalLiveCount st0 ∧
      st.metaAreas = st0.metaAreas ∧ dynamicRootRegions st = dynamicRootRegions st0 ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
        st.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
      Cost.GroupsGrpMono st0.groups st.groups ∧
      GroupsFreeMono st0.groups st.groups ∧
      totalClaimedSlots st = 0)
    (s0 s : State) (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (_hpc : s.pc = mbase 8 + allocSlotOff_ag) (_hrun : s.status = .Running)
    (_hsp : s.sp = s0.sp - 96#64) (_hsAl : s.spAligned = true)
    (_htp : s0.tpidrEl0 = tp) (_hbrkS : s0.brkStart = brkStart)
    (_hpsp : PureStatePres s0 s) (_hperm : s.mem.perm = s0.mem.perm)
    (_hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (_hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req),
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) s
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
        (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
        (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f => AllocSlotFinePost sc req inflight γ tp brkStart liveCost peakCost peakCount
        bL bP maxMeta st0 s0 sf P_f ro)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
                   ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝)

/-- Fine placed contract for `alloc_slot(sc, req)` (`blk08`), preserving `FineSplitInv bL bP`,
    non-increasing `stClassBound` on strictly smaller classes `k < sc`, and bounding newly mapped
    bytes by `(allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576`. -/
def AllocSlotFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (sc req inflight : Nat)
    (_hSc : sc < 48)
    (_hReqLo : allocSlotReqLo sc ≤ req)
    (_hReqHi : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount)
    (_hClaim0 : totalClaimedSlots st = 0)
    (_hFine : FineSplitInv bL bP st)
    (_hRoom : AllocSlotOccRoom bP st sc)
    (_hMaStep : st.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc)),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧
         (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ idx : Nat,
          ⌜MallocngProcPreserved s0 sf ∧
           st'.reservedMetas = st.reservedMetas ∧
           st'.liveMap = st.liveMap ∧
           totalLiveEffCost st' = totalLiveEffCost st ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ st.metaAreas.length + allocSlotDepthBound sc + 1 ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           FineSplitInv bL bP st' ∧
           (∀ k < sc, (stClassBound st' k).le (stClassBound st k)) ∧
           sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
           (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
             g.sc = sc ∧
             req + 4 ≤ g.stride ∧
             g.metaPtr = st'.ctx.active[sc]'hAct ∧
             g.slots[idx]'hIdx = .claimed ∧
             (g.isMmapped = true →
               ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
             ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0.mem sf.mem ∧
           (∀ U : Nat, peakCount ≤ U →
             Cost.GroupsGrpBound U st.groups → Cost.GroupsGrpBound U st'.groups)⌝ ∗
          stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
          MallocngRoTablesA maddrs ∗
          MallocngRuntime maddrs tp ∗
          MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝
    })

theorem call_placed_allocSlot_fine {ro : Bool} (h : AllocSlotFineStmt ro) [MallocngMultiPlacement]
    {P : Program}
    (sc req inflight : Nat)
    (hSc : sc < 48)
    (hReqLo : allocSlotReqLo sc ≤ req)
    (hReqHi : req ≤ nominalSlotCap sc)
    (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (hCount : totalLiveCount st ≤ peakCount)
    (hClaim0 : totalClaimedSlots st = 0)
    (hFine : FineSplitInv bL bP st)
    (hRoom : AllocSlotOccRoom bP st sc)
    (hMaStep : st.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧
         (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ idx : Nat,
          ⌜MallocngProcPreserved s0 sf ∧
           st'.reservedMetas = st.reservedMetas ∧
           st'.liveMap = st.liveMap ∧
           totalLiveEffCost st' = totalLiveEffCost st ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ st.metaAreas.length + allocSlotDepthBound sc + 1 ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           FineSplitInv bL bP st' ∧
           (∀ k < sc, (stClassBound st' k).le (stClassBound st k)) ∧
           sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
           (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
             g.sc = sc ∧
             req + 4 ≤ g.stride ∧
             g.metaPtr = st'.ctx.active[sc]'hAct ∧
             g.slots[idx]'hIdx = .claimed ∧
             (g.isMmapped = true →
               ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
             ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0.mem sf.mem ∧
           (∀ U : Nat, peakCount ≤ U →
             Cost.GroupsGrpBound U st.groups → Cost.GroupsGrpBound U st'.groups)⌝ ∗
          stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
          MallocngRoTablesA maddrs ∗
          MallocngRuntime maddrs tp ∗
          MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝
    }) :=
  subroutine_ok_block_to_block (j := 8) (by decide)
    (h sc req inflight hSc hReqLo hReqHi hInflight γ tp brkStart liveCost peakCost peakCount
      bL bP maxMeta st hCount hClaim0 hFine hRoom hMaStep) hext hsvc

/-! ## 4. Placed `__libc_malloc_impl` (`blk09`) & `default_malloc` (`blk04`) Fine Contracts -/

/-- Pre-enframe witness relating `st'` (returned by `__libc_malloc_impl(req)`) to the pre-enframe
    state `st1` where slot `idx` of `g` is still `.claimed` and `FineSplitInv bL bP st1` holds.
    Shared by `fineGroupsInv_enframe_alloc` (`malloc`/`calloc`/`realloc`) and
    `map_ite_double_eq` + `fineGroupsInv_enframe_aligned` (`aligned_alloc`/`posix_memalign`). -/
def FinePreEnframeRel (bL bP : FineBudget) (req : Nat) (p : BitVec 64)
    (st' : MallocngSt) (g' : GroupDesc) (idx : Nat) : Prop :=
  ∃ (st1 : MallocngSt) (g : GroupDesc),
    FineSplitInv bL bP st1 ∧
    (st1.groups.map (·.metaPtr)).Nodup ∧
    g ∈ st1.groups ∧
    ∃ hIdx1 : idx < g.slots.length,
      g.slots[idx]'hIdx1 = .claimed ∧
      (req ≤ MmapThresholdReq → g.sc < 48 ∧ allowedPhysClass (nomSc req) g.sc = true) ∧
      (MmapThresholdReq < req → g.sc = 63) ∧
      g'.metaPtr = g.metaPtr ∧ g'.sc = g.sc ∧ g'.cnt = g.cnt ∧
      g'.maplen = g.maplen ∧ g'.parentMeta = g.parentMeta ∧
      g'.slots = g.slots.set idx (.liveUser p req (max req MallocngMinBlockCost)) ∧
      st'.metaAreas = st1.metaAreas ∧
      st'.groups = st1.groups.map fun h => if h.metaPtr == g.metaPtr then g' else h

/-- Raw placed `__libc_malloc_impl(req)` (`blk09`, `704` B stack) contract parameterized over
    arbitrary `(bL, bP)` with `FineSplitInv bL bP st0` (`bP = fineStepAlloc req bL` for `malloc`,
    `bP = fineStepAligned align len bL` for `aligned_alloc`). -/
def libcMallocImplFineRawSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bL bP : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (req : Nat) (ro : Bool := false) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let stepB := FineStepBound (fineMaxMetaAreas bL) (if ok then req else 0)
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req ∧
       s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      stackFrame s0 704 ∗
      MallocngRoTablesA maddrs ∗
      MallocngRuntime maddrs tp ∗
      ∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧
         FineSplitInv bL bP st0 ∧
         st0.metaAreas.length ≤ fineMaxMetaAreas bL ∧
         (req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
           ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
             stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)⌝ ∗
        MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 stepB s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
        ∃∗ bCoarse' : MallocngBudget,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8) ∧
             (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
             (g'.sc = 24 → nominalSlotCap 22 < req) ∧
             (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115) ∧
             FinePreEnframeRel bL bP req p st' g' idx⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          MallocngBlockTokenK γ p req 0
      else
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart⌝ ∗
        MallocngRoTablesA maddrs ∗
        MallocngRuntime maddrs tp ∗
        ∃∗ st' : MallocngSt, ∃∗ bCoarse' : MallocngBudget,
          ⌜MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
           FineSplitInv bL bP st' ∧
           st'.groups = st'.groups ∧
           st'.metaAreas.length ≤ fineMaxMetaAreas bL⌝ ∗
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st'
    onOom := fun _ s0 sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝
  }

def LibcMallocImplFineRawStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bL bP : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplFineRawSpec γ tp brkStart bL bP ivs0 req ro)

theorem call_placed_libcMallocImpl_fine_raw {ro : Bool} (h : LibcMallocImplFineRawStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64)
    (bL bP : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplFineRawSpec γ tp brkStart bL bP ivs0 req ro) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart bL bP ivs0 req) hext hsvc

/-- Quiescent placed `__libc_malloc_impl(req)` / `default_malloc(req)` spec over
    `mallocngFineCostModel` / `mallocngFineModeIface ro`, returning `MallocngBlockTokenK γ p req 0` +
    `(p ↦ₛ bs)` (with `bs = replicate req 0#8` when `g'.isMmapped = true` for `calloc`). -/
def libcMallocImplFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) (ro : Bool := false) : Spec Unit :=
  let ok := decide (req ≤ MallocngMaxAllocSize)
  let bgt' := if ok then fineStepAlloc req bgt else bgt
  let stepB := FineStepBound (fineMaxMetaAreas bgt) (if ok then req else 0)
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜(s0.readReg64 .x0).toNat = req⌝ ∗
      stackFrame s0 704 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngProcPreserved s0 sf ∧
       MallocngMappedDelta 16 stepB s0.mem sf.mem⌝ ∗
      stackFrame s0 704 ∗
      if req ≤ MallocngMaxAllocSize then
        ∃∗ p : BitVec 64,
        ∃∗ bs : List (BitVec 8),
        ∃∗ st' : MallocngSt,
        ∃∗ bCoarse' : MallocngBudget,
          ⌜sf.readReg64 .x0 = p ∧
           sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
           MallocngBlockWf p req ∧
           bs.length = req ∧
           MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
           MallocngFineInv bgt' (dynamicRootRegions st') st' ∧
           ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
             g'.slots[idx]'hIdx = .liveUser p req (max req MallocngMinBlockCost) ∧
             p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
             (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
          MallocngRuntime maddrs tp ∗
          (p ↦ₛ bs) ∗
          MallocngBlockTokenK γ p req 0
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
          γ maddrs tp brkStart bgt' ivs0 s0 sf
    onOom := fun _ s0 sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝
  }

def LibcMallocImplFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9)
      (libcMallocImplFineSpec γ tp brkStart bgt ivs0 req ro)

def DefaultMallocFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat),
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (libcMallocImplFineSpec γ tp brkStart bgt ivs0 req ro)

theorem call_placed_libcMallocImpl_fine {ro : Bool} (h : LibcMallocImplFineStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 9) (libcMallocImplFineSpec γ tp brkStart bgt ivs0 req ro) :=
  subroutine_ok_block_to_block (j := 9) (by decide) (h γ tp brkStart bgt ivs0 req) hext hsvc

theorem call_placed_defaultMalloc_fine {ro : Bool} (h : DefaultMallocFineStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 4) (libcMallocImplFineSpec γ tp brkStart bgt ivs0 req ro) :=
  subroutine_ok_block_to_block (j := 4) (by decide) (h γ tp brkStart bgt ivs0 req) hext hsvc

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
