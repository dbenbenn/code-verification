/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Specs
public import VerifiedLibraries.Mallocng.Proofs.PlacedAlignedAllocProof
import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `aligned_alloc` & `posix_memalign` Fine Cost Proofs (`…Proofs.Cost.Fine.AlignedAlloc`)

- **Role**: `Role::Proof` (untrusted).
- **Purpose**: verifies `"aligned_alloc"` (`blk12`) and `"posix_memalign"` (`blk11`) against
  `mallocngModelAlignedAllocSpec` and `mallocngModelPosixMemalignSpec` instantiated at
  `(mallocngFineCostModel, mallocngFineIface)`, parameterized solely over
  `(hRaw : LibcMallocImplFineRawStmt)` from `Specs.lean`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.CType Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Pure Reserve, OOM, & Separation-Logic Helpers -/

private theorem stepOomCond_of_perm_eq {svc : State → State} {stepB : Nat} {s0 s1 sf : State}
    (hFs : s1.fs = s0.fs) (hTr : s1.trace = s0.trace) (hSig : s1.sigActions = s0.sigActions)
    (hPerm : ∀ a, s0.mem.perm a = s1.mem.perm a)
    (h : MallocngStepOomCond svc stepB s1 sf) :
    MallocngStepOomCond svc stepB s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hlen, hsum, hcov, hsan⟩ := h
  exact ⟨hfs.trans hFs, htr.trans hTr, hsig.trans hSig, ivs, hlen, hsum,
    fun a ha => by rw [hPerm a]; exact hcov a ha, hsan⟩

private theorem fine_step_aligned_ite (ok : Bool) (align len : Nat) (bgt : FineBudget) :
    (if ok then mallocngFineCostModel.step (.aligned align len) bgt else bgt) =
      if ok then fineStepAligned align len bgt else bgt := by
  cases ok <;> rfl

private theorem sepWP_pure_left_aa {prog : Program} {tgt : BitVec 64} {s : State}
    {p : Prop} {Q : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : p → SepWP prog tgt s Q post oom) :
    SepWP prog tgt s (⌜p⌝ ∗ Q) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact SepWP.to_reaches_pc (h hm.1) hm.2

private theorem sepWP_inspect_aa {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {q : Prop} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hEnt : P ⊢ ⌜q⌝ ∗ P) (h : q → SepWP prog tgt s P post oom) :
    SepWP prog tgt s P post oom :=
  SepWP.weaken_pre hEnt (sepWP_pure_left_aa h)

private theorem stackFrame_eq_stackFrameAt_aa (s : State) (n : Nat) (hn : n ≤ 2 ^ 64 := by omega) :
    stackFrame s n = stackFrameAt s.sp n :=
  (stackFrameAt_eq_memRegion s.sp n hn).symm

local macro "cells_unfold_pre" : tactic =>
  `(tactic| conv => arg 4; simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp, sepExists_sepConj_right, sepExists_sepConj_left])

local macro "proc_preserved_step" : tactic =>
  `(tactic| exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
    by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩)

private theorem fineEnv_focus_replaced {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) (s : State) :
    ∃ RestEnv : SepProp,
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt ivs s =
        ((A.replaced ↦₃₂ 0#32) ∗ RestEnv) := by
  refine ⟨⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗ MallocngRoTablesA A ∗ MallocngRuntime A tp ∗
    ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
      ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
      ⌜MallocngWF A.base brkStart s.brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      MallocngLiveAuth γ st.liveMap ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st), ?_⟩
  dsimp only [MallocngModelEnv]
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  dsimp only [FineCoreModeImpl]
  have hEx :
      (∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
        MallocngCoreStModeA ro γ A brkStart s.brk bCoarse.liveCost bCoarse.peakCost st) =
      ((A.replaced ↦₃₂ 0#32) ∗ ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
         ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
         ⌜MallocngWF A.base brkStart s.brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
         MallocngLiveAuth γ st.liveMap ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗ (A.lock ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
         ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MappedSet st.masterDom (OwnedMappedByte st)) := by
    rw [sepExists_sepConj_right]; refine sepExists_congr fun st => ?_
    rw [sepExists_sepConj_right]; refine sepExists_congr fun bCoarse => ?_
    dsimp only [MallocngCoreStModeA, MallocngCoreStInflightModeA, MallocngWF]; ac_rfl
  rw [hEx]; ac_rfl

private theorem ccmp_ovf_hi_iff_aa {align len : BitVec 64} (hMax : align.toNat ≤ MaxAlignedAllocAlign) :
    ConditionHolds .HI
      (if ConditionHolds .CS (subsPState64 (~~~align) len) then subsPState64 align 0x7ffffffff#64
       else PState.ofBits4 2#4) = decide (2 ^ 64 ≤ len.toNat + align.toNat) := by
  obtain ⟨hUltFalse, hUleIff⟩ := alignedAlloc_ovf_iff (len := len) hMax
  have hHiSub : ConditionHolds .HI (subsPState64 align 0x7ffffffff#64) = false := by
    rw [show ConditionHolds .HI (subsPState64 align 0x7ffffffff#64) = (0x7ffffffff#64).ult align by simp [arm64_norm],
      hUltFalse]
  rw [conditionHolds_cs_subsPState64]
  cases hUle : len.ule (~~~align)
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true (hUleIff.mp hUle)]; rfl
  · simp only [↓reduceIte, hHiSub]
    have hNoOvf : ¬ 2 ^ 64 ≤ len.toNat + align.toNat := fun h => by
      have hf := hUleIff.mpr h; rw [hUle] at hf; cases hf
    simp [hNoOvf]

private theorem mallocngWF_boost_alloc {base brkStart brk : BitVec 64}
    {eff : Nat} {bCoarse : MallocngBudget} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk bCoarse.liveCost bCoarse.peakCost st) :
    MallocngWF base brkStart brk (mallocngAllocBudget true eff bCoarse).liveCost
      (mallocngAllocBudget true eff bCoarse).peakCost st :=
  have hDivLe : bCoarse.peakCost / 655360 ≤ (mallocngAllocBudget true eff bCoarse).peakCost / 655360 :=
    Nat.div_le_div_right (Nat.le_max_left _ _)
  { hwf with
    live_le_peak := Nat.le_max_right _ _
    effCost_le_live := Nat.le_trans hwf.effCost_le_live (by simp [mallocngAllocBudget])
    meta_pages_bound := ⟨Nat.le_trans hwf.meta_pages_bound.1 (by omega), hwf.meta_pages_bound.2⟩ }

private theorem mallocngCoreStA_boost_alloc {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (eff : Nat) (bCoarse : MallocngBudget) (st : MallocngSt) :
    MallocngCoreStModeA ro γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st ⊢
    MallocngCoreStModeA ro γ A brkStart brk (mallocngAllocBudget true eff bCoarse).liveCost
      (mallocngAllocBudget true eff bCoarse).peakCost st := by
  dsimp only [MallocngCoreStModeA, MallocngCoreStInflightModeA]
  exact sepConj_mono_left (Entails.pure_mono mallocngWF_boost_alloc)

private theorem mallocngCountIvsWF_boost_alloc {eff : Nat} {bCoarse : MallocngBudget}
    {ivs : List (BitVec 64 × Nat)} {st : MallocngSt}
    (hCnt : MallocngCountIvsWF bCoarse ivs st) :
    MallocngCountIvsWF (mallocngAllocBudget true eff bCoarse) ivs st := by
  obtain ⟨_hlp, htlc, hivs, hlen, hma, hgrp⟩ := hCnt
  have hPeakLe : bCoarse.peakCount ≤ (mallocngAllocBudget true eff bCoarse).peakCount := Nat.le_max_left _ _
  have hDivLe : (88 + 8 * bCoarse.peakCount) / 101 ≤
      (88 + 8 * (mallocngAllocBudget true eff bCoarse).peakCount) / 101 := Nat.div_le_div_right (by omega)
  exact ⟨Nat.le_max_right _ _, Nat.le_trans htlc (by simp [mallocngAllocBudget]), hivs,
    Nat.le_trans hlen (by omega), Nat.le_trans hma (by omega), GroupsGrpBound.mono hgrp (by omega)⟩

private theorem fineRoom_of_aligned {bgt : FineBudget} {ivs0 : List (BitVec 64 × Nat)} {st0 : MallocngSt}
    (hFine : MallocngFineInv bgt ivs0 st0) (align len : Nat) :
    FineSplitInv bgt (fineStepAligned align len bgt) st0 ∧
    st0.metaAreas.length ≤ fineMaxMetaAreas bgt ∧
    (mallocngAlignedEffSize align len ≤ MallocngMaxAllocSize →
      mallocngAlignedEffSize align len ≤ MmapThresholdReq →
      ∀ sc < 48, allowedPhysClass (nomSc (mallocngAlignedEffSize align len)) sc = true →
        stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget (fineStepAligned align len bgt) sc) := by
  have hFG := hFine.toGroupsInv
  refine ⟨hFG.toSplit (fineBudgetInv_step (.aligned align len) hFine.budget_inv)
      (finePeaksLe_step (.aligned align len) bgt),
    hFine.meta_le, fun _ hThr sc hsc hAllow => ?_⟩
  by_cases hLe16 : align ≤ 16
  · have hEffEq : mallocngAlignedEffSize align len = len := by simp [mallocngAlignedEffSize, hLe16]
    rw [show fineStepAligned align len bgt = fineStepAlloc len bgt by simp [fineStepAligned, hLe16]]
    exact fineLiveUser_room_alloc hFG (hEffEq ▸ hThr) hsc (hEffEq ▸ hAllow)
  · exact fineLiveUser_room_aligned hFG (by omega) hThr hsc hAllow

private theorem fineInv_after_aligned_reframe {bgt : FineBudget} {align len : Nat}
    {p new_p : BitVec 64} {st' : MallocngSt} {g' : GroupDesc} {idx : Nat} {bv : BitVec 64 → BitVec 8}
    (hRel : FinePreEnframeRel bgt (fineStepAligned align len bgt)
      (mallocngAlignedEffSize align len) p st' g' idx) :
    let st2 := mkAlignedReframedSt st' g' idx p new_p align len bv
    MallocngFineInv (fineStepAligned align len bgt) (dynamicRootRegions st2) st2 := by
  intro st2
  obtain ⟨st1, g, hSplit, hNd, hg, hIdx1, hClaimed, hSmall, hLarge, hMeta, hSc, hCnt, hMl, hPar, hSl, hMa, hGs⟩ := hRel
  let g2 := mkAlignedReframedGroup g' idx new_p align len
  have hGs2 : st2.groups = st1.groups.map fun h => if h.metaPtr == g.metaPtr then g2 else h := by
    dsimp only [st2, mkAlignedReframedSt, replaceGroupByMeta]; rw [hGs]; exact map_ite_double_eq st1.groups hMeta
  have hSl2 : g2.slots = g.slots.set idx
      (.liveUser new_p len (max len MallocngMinBlockCost + (max align 16 - 16))) := by
    dsimp only [g2, mkAlignedReframedGroup]; rw [hSl, List.set_set]
  have hFG2 : FineGroupsInv (fineStepAligned align len bgt) st2 := by
    by_cases hLe16 : align ≤ 16
    · have hEffEq : mallocngAlignedEffSize align len = len := by simp [mallocngAlignedEffSize, hLe16]
      have hStepEq : fineStepAligned align len bgt = fineStepAlloc len bgt := by simp [fineStepAligned, hLe16]
      rw [hStepEq]
      refine fineGroupsInv_enframe_alloc (hStepEq ▸ hSplit) hNd hg hIdx1 hClaimed
        (hEffEq ▸ hSmall) (hEffEq ▸ hLarge) (p := new_p) (g' := g2) hMeta hSc hCnt hMl hPar ?_ hMa hGs2
      simpa [show max align 16 - 16 = 0 by omega] using hSl2
    · exact fineGroupsInv_enframe_aligned hSplit hNd (by omega) hg hIdx1 hClaimed
        hSmall hLarge (newP := new_p) (g' := g2) hMeta hSc hCnt hMl hPar hSl2 hMa hGs2
  exact hFG2.toFineInv rfl

private theorem fineCoreImpl_to_rawPre {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (brkStart brk : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (align len : Nat) :
    let eff := mallocngAlignedEffSize align len
    let bgt' := fineStepAligned align len bgt
    FineCoreModeImpl ro γ A brkStart brk bgt ivs0 ⊢
      MallocngRoTablesA A ∗ ∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧ FineSplitInv bgt bgt' st0 ∧
         st0.metaAreas.length ≤ fineMaxMetaAreas bgt ∧
         (eff ≤ MallocngMaxAllocSize → eff ≤ MmapThresholdReq →
           ∀ sc < 48, allowedPhysClass (nomSc eff) sc = true →
             stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bgt' sc)⌝ ∗
        MallocngCoreStModeA ro γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st0 := by
  intro eff bgt'; dsimp only [FineCoreModeImpl]; refine sepConj_mono_right ?_
  refine Entails.sepExists_elim fun st0 => Entails.trans ?_ (Entails.sepExists_intro st0)
  refine Entails.sepExists_elim fun bCoarse => Entails.trans ?_ (Entails.sepExists_intro bCoarse)
  refine sepConj_mono_left (Entails.pure_mono fun ⟨hCnt0, hFine0⟩ => ?_)
  obtain ⟨hSplit, hMa, hRoom⟩ := fineRoom_of_aligned hFine0 align len
  exact ⟨hCnt0, hSplit, hMa, hRoom⟩

private theorem reframePost_to_finePostEnv {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bgt' : FineBudget) (b2 : MallocngBudget)
    (st2 : MallocngSt) (ivs0 : List (BitVec 64 × Nat)) (s0 sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hNoOrph : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem)
    (hCnt2 : MallocngCountIvsWF b2 (dynamicRootRegions st2) st2)
    (hFine2 : MallocngFineInv bgt' (dynamicRootRegions st2) st2) :
    (MallocngRoTablesA A ∗ MallocngCoreStModeA ro γ A brkStart sf.brk b2.liveCost b2.peakCost st2 ∗
      MallocngRuntime A tp) ⊢
    MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt' ivs0 s0 sf := by
  dsimp only [MallocngModelPostEnv, MallocngModelEnv]
  refine Entails.trans ?_ (Entails.sepExists_intro (dynamicRootRegions st2))
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  dsimp only [FineCoreModeImpl]
  rw [pure_sepConj_of_true hNoOrph, pure_sepConj_of_true ⟨htp, hbrks⟩]
  have hCore : MallocngCoreStModeA ro γ A brkStart sf.brk b2.liveCost b2.peakCost st2 ⊢
      ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse (dynamicRootRegions st2) st ∧ MallocngFineInv bgt' (dynamicRootRegions st2) st⌝ ∗
        MallocngCoreStModeA ro γ A brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st := by
    refine Entails.trans ?_ (Entails.sepExists_intro st2); refine Entails.trans ?_ (Entails.sepExists_intro b2)
    rw [pure_sepConj_of_true ⟨hCnt2, hFine2⟩]; exact Entails.refl _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left hCore)) (Entails.of_eq (by ac_rfl))

/-! ## 2. Internal `alignedAllocErrnoFineSpec` (`736` B Stack) & `"aligned_alloc"` Entry -/

/-- Internal `aligned_alloc(align, len)` (`blk12`, `736` B stack) contract over
    `(mallocngFineCostModel, mallocngFineModeIface ro)` exposing the concrete TLS `errno` cell
    (`22#32` when `!alignedAllocAlignOk align`, else `12#32`) on `NULL` return so
    `posix_memalign` (`blk11`) can read `*__errno_location()` directly. -/
def alignedAllocErrnoFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart align len : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (ro : Bool := false) : Spec Unit :=
  let ok := mallocngAlignedAllocOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let bgt' := if ok then fineStepAligned align.toNat len.toNat bgt else bgt
  let stepB := FineStepBound (fineMaxMetaAreas bgt) (if ok then eff else 0)
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = align ∧ s0.readReg64 .x1 = len ∧
       align.toNat ≤ MaxAlignedAllocAlign⌝ ∗
      stackFrame s0 736 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0
    post := fun _ s0 sf =>
      ⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
      stackFrame s0 736 ∗
      if ok then
        ∃∗ q : BitVec 64,
          ⌜sf.readReg64 .x0 = q ∧
           (MallocngModelBlock (mallocngFineModeIface ro) γ).pureWf q (len.toNat, max align.toNat 16)⌝ ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt' ivs0 s0 sf ∗
          (MallocngModelBlock (mallocngFineModeIface ro) γ).interp q (len.toNat, max align.toNat 16)
      else
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
         MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem⌝ ∗
        FineCoreModeImpl ro γ maddrs brkStart sf.brk bgt' ivs0 ∗
        ((tp - 0xa4#64) ↦₃₂ (if !alignedAllocAlignOk align then 22#32 else 12#32)) ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
    onOom := fun _ s0 sf =>
      ⌜MallocngStepOomCond msvc stepB s0 sf⌝
  }

set_option maxHeartbeats 400000 in
private theorem blk12_alignedAlloc_errno_fine {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart align len : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) :
    subroutine_ok (mallocngBlockProg mmpl 12 msvc) (mbase 12)
      (alignedAllocErrnoFineSpec γ tp brkStart align len bgt ivs0 ro) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b12.rebase c (fun _ => none)).fnAddr "aligned_alloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b12, PlacedLib.program]
    rw [blkSymsEq_b12]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b12).find? (·.1 == "aligned_alloc") =
        some ("aligned_alloc", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b12 (hfn (mbase 12)) fun b hb => ?_
  have hprog_b12 : blkPC_b12.rebase b (fun _ => none) = mallocngBlockProg mmpl 12 msvc := by
    rw [mallocngBlockProg_eq_b12, hb]
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b12.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [alignedAllocErrnoFineSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨rfl, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨⟨hx0, hx1, hAlignMax⟩, hpre⟩ := hpre
  have ⟨htp0, hbrks0⟩ : s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart := by
    have hm0 := hpre; dsimp only [MallocngModelEnv] at hm0
    simp only [sepConj_comm (stackFrame s0 736), sepConj_assoc, satisfies_pure_sepConj] at hm0; exact hm0.1
  refine ⟨stackFrame s0 736 ∗ MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0,
    by simpa [sepConj_assoc] using hpre, ?_⟩
  rw [stackFrame_eq_stackFrameAt_aa s0 736, stackFrameAt_736_split s0.sp]
  cells_unfold_pre
  apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
  apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
  have hspAl32 : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true := s0.spAligned_sub 32#64 hspAl0
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_if hAlignNe
  · -- Path 1: `!alignedAllocAlignOk align` (`+0x090` -> `22#32` `EINVAL`)
    have hAlignFalse : alignedAllocAlignOk align = false := by
      have h0 : (align &&& ~~~(0#64 - align) == 0#64) = false := by
        cases hb0 : (align &&& ~~~(0#64 - align) == 0#64)
        · rfl
        · exfalso; apply hAlignNe; simpa [arm64_norm, hx0, beq_iff_eq] using hb0
      rwa [bics_neg_eq_zero_iff_alignOk] at h0
    have hOkFalse : mallocngAlignedAllocOk align len = false := by simp [mallocngAlignedAllocOk, hAlignFalse]
    conv => arg 4; dsimp only [MallocngModelEnv]; rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
    conv => arg 4; rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩]; dsimp only [MallocngRuntime]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro ev; wp_step
    have hpc_bl0 : b + 0x90#64 + (mbase 0 - mbase 12 - 0x90#64) = mbase 0 := by rw [hb]; bv_arith
    conv => arg 3; simp only [hpc_bl0]
    refine sepWP_call_errno (ret_pc := b + 0x94#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
      (by simpa [arm64_norm] using hspAl32) (by simp [arm64_norm]) hcl1
      fun se hpc_e hrun_e hsp_e hcs_e hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
    have hsp_se : se.sp = s0.sp - 32#64 := by simpa [arm64_norm] using hsp_e
    have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp0] using hx0_e
    have hProc0_se : MallocngProcPreserved s0 se := alignedProcPreserved_trans (by proc_preserved_step) hproc_e
    have hbrk_se : se.brk = s0.brk := hbrk_e.trans (by simp [arm64_norm])
    wp_step; conv => arg 3; simp only [hx0_se]
    wp_step; wp_step; wp_str32_cl m2 hm2 hcl_e _hcl2
    have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
    have ha8 : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; bv_arith
    have ha32 : se.sp + 32#64 = s0.sp := by rw [hsp_se]; bv_arith
    wp_step; wp_step
    have hPermAll : m2.perm = s0.mem.perm := hm2.trans (hperm_e.trans hm1)
    refine sepWP_let_state fun sf hsf => ?_
    have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_se]
    refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hm => ?_, ?_, ?_⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignFalse, Bool.not_false, hbrk_f]
      rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
            AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
        pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm], by subst hsf; simp [arm64_norm, hProc0_se.2.2.1.trans htp0],
          by subst hsf; simp [arm64_norm, hProc0_se.2.2.2.1.trans hbrks0],
          AlignedStage1.noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
      cells_unfold; sep_frame
    · subst hsf; have _ := ha32; simp [arm64_norm]
    · subst hsf; exact ⟨by simpa [arm64_norm] using hcs_e.readReg64_x19, by simpa [arm64_norm] using hcs_e.readReg64_x20,
        by simpa [arm64_norm] using hcs_e.readReg64_x21, by simpa [arm64_norm] using hcs_e.readReg64_x22,
        by simpa [arm64_norm] using hcs_e.readReg64_x23, by simpa [arm64_norm] using hcs_e.readReg64_x24,
        by simpa [arm64_norm] using hcs_e.readReg64_x25, by simpa [arm64_norm] using hcs_e.readReg64_x26,
        by simpa [arm64_norm] using hcs_e.readReg64_x27, by simpa [arm64_norm] using hcs_e.readReg64_x28,
        by simp [arm64_norm], by simpa [arm64_norm] using hcs_e.vregs⟩
  · -- Fallthrough: `alignedAllocAlignOk align = true`
    have hAlignOk : alignedAllocAlignOk align = true := by
      rw [← bics_neg_eq_zero_iff_alignOk]; simpa [BitVec.zero_sub, beq_iff_eq] using hAlignNe
    have hNegAnd : -align &&& align = align := by simpa [BitVec.zero_sub] using neg_and_self_of_alignOk hAlignOk
    have ha16_sp : s0.sp - 32#64 + 16#64 = s0.sp - 16#64 := by bv_arith
    have ha24_sp : s0.sp - 16#64 + 8#64 = s0.sp - 8#64 := by bv_arith
    wp_step; wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hOvfHi
    · -- Path 2: `2 ^ 64 ≤ len.toNat + align.toNat` (`+0x0ac` -> `12#32` `ENOMEM`)
      have hOvf : 2 ^ 64 ≤ len.toNat + align.toNat := by
        have hCond : ConditionHolds .HI
            (if ConditionHolds .CS (subsPState64 (~~~align) len) then subsPState64 align 0x7ffffffff#64
             else PState.ofBits4 2#4) = true := by
          simpa [arm64_norm, hx0, hx1, hNegAnd] using hOvfHi
        rwa [ccmp_ovf_hi_iff_aa hAlignMax, decide_eq_true_eq] at hCond
      have hEffGt : ¬ mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
        unfold mallocngAlignedEffSize MallocngMaxAllocSize MaxAlignedAllocAlign at *; split <;> omega
      have hOkFalse : mallocngAlignedAllocOk align len = false := by
        simp [mallocngAlignedAllocOk, hEffGt]
      conv => arg 4; dsimp only [MallocngModelEnv]; rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
      conv => arg 4; rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩]
      conv => arg 4; dsimp only [MallocngRuntime]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro ev
      wp_step
      have hpc_bl0 : b + 0xac#64 + (mbase 0 - mbase 12 - 0xac#64) = mbase 0 := by rw [hb]; bv_arith
      conv => arg 3; simp only [hpc_bl0]
      refine sepWP_call_errno (ret_pc := b + 0xb0#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
        (by simpa [arm64_norm] using hspAl32) (by simp [arm64_norm]) hcl2
        fun se hpc_e hrun_e hsp_e hcs_e hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
      have hsp_se : se.sp = s0.sp - 32#64 := by simpa [arm64_norm] using hsp_e
      have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp0] using hx0_e
      have hProc0_se : MallocngProcPreserved s0 se :=
        alignedProcPreserved_trans (by proc_preserved_step) hproc_e
      have hbrk_se : se.brk = s0.brk := hbrk_e.trans (by simp [arm64_norm])
      wp_step; conv => arg 3; simp only [hx0_se]
      wp_step; wp_step
      wp_str32_cl m3 hm3 hcl_e _hcl3
      have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
      have ha16_se : se.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_se]; bv_arith
      have ha24_se : se.sp + 16#64 + 8#64 = s0.sp - 8#64 := by rw [hsp_se]; bv_arith
      have ha8 : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; bv_arith
      have ha32 : se.sp + 32#64 = s0.sp := by rw [hsp_se]; bv_arith
      wp_step; wp_step; wp_step; wp_step
      have hPermAll : m3.perm = s0.mem.perm := hm3.trans (hperm_e.trans (hm2.trans hm1))
      refine sepWP_let_state fun sf hsf => ?_
      have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_se]
      refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hm => ?_, ?_, ?_⟩
      · refine Satisfies.mono (sepConj_mono_left ?_) hm
        simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignOk, Bool.not_true, hbrk_f]
        have htp_f : se.tpidrEl0 = tp := hProc0_se.2.2.1.trans htp0
        have hbrks_f : se.brkStart = brkStart := hProc0_se.2.2.2.1.trans hbrks0
        rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
              AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
          pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm], by subst hsf; simp [arm64_norm, htp_f],
            by subst hsf; simp [arm64_norm, hbrks_f],
            AlignedStage1.noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
        cells_unfold; sep_frame
      · subst hsf; have _ := ha32; simp [arm64_norm]
      · subst hsf
        exact ⟨by simp [arm64_norm], by simp [arm64_norm],
          by simpa [arm64_norm] using hcs_e.readReg64_x21, by simpa [arm64_norm] using hcs_e.readReg64_x22,
          by simpa [arm64_norm] using hcs_e.readReg64_x23, by simpa [arm64_norm] using hcs_e.readReg64_x24,
          by simpa [arm64_norm] using hcs_e.readReg64_x25, by simpa [arm64_norm] using hcs_e.readReg64_x26,
          by simpa [arm64_norm] using hcs_e.readReg64_x27, by simpa [arm64_norm] using hcs_e.readReg64_x28,
          by simp [arm64_norm], by simpa [arm64_norm] using hcs_e.vregs⟩
    · -- Fallthrough: `len.toNat + align.toNat < 2 ^ 64` (`+0x034`)
      have hNoOvf : len.toNat + align.toNat < 2 ^ 64 := by
        refine Classical.byContradiction fun hNot => hOvfHi ?_
        have hCond := (ccmp_ovf_hi_iff_aa (len := len) hAlignMax).trans (decide_eq_true (by omega))
        simpa [arm64_norm, hx0, hx1, hNegAnd] using hCond
      obtain ⟨RestEnv, hFocusRep⟩ := fineEnv_focus_replaced (ro := ro) γ maddrs tp brkStart bgt ivs0 s0
      have _hPageRep := pageOf_add_lo12Of maddrs.replaced
      conv => arg 4; rw [hFocusRep]
      wp_step; wp_step; wp_step
      · conv => arg 4; rw [← hFocusRep]
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        have hpc_bl9 : b + 0x60#64 + (mbase 9 - mbase 12 - 0x60#64) = mbase 9 := by rw [hb]; bv_arith
        conv => arg 3; simp only [hpc_bl9]
        let eff := mallocngAlignedEffSize align.toNat len.toNat
        have ⟨_, hEffReg⟩ := alignedAlloc_effReg_toNat (align := align) (len := len) hNoOvf
        refine sepWP_let_state fun sc hsc => ?_
        have hsc_sp : sc.sp = s0.sp - 32#64 := by subst hsc; simp [arm64_norm]
        have hsc_brk : sc.brk = s0.brk := by subst hsc; simp [arm64_norm]
        have hsc_mem : sc.mem = m2 := by subst hsc; simp [arm64_norm]
        have hsc_tp : sc.tpidrEl0 = tp := by subst hsc; simp [arm64_norm, htp0]
        have hsc_brks : sc.brkStart = brkStart := by subst hsc; simp [arm64_norm, hbrks0]
        have hsc_proc : MallocngProcPreserved s0 sc := by subst hsc; proc_preserved_step
        by_cases hEffFit : eff ≤ MallocngMaxAllocSize
        · -- Path 4: `eff ≤ MallocngMaxAllocSize` (`ok = true`)
          have hOkTrue : mallocngAlignedAllocOk align len = true := by
            simp [mallocngAlignedAllocOk, hAlignOk, eff, hEffFit]
          let bgt' := fineStepAligned align.toNat len.toNat bgt
          have hMallocSub := call_placed_libcMallocImpl_fine_raw hRaw
            (P := blkPC_b12.rebase b (fun _ => none))
            γ tp brkStart bgt bgt' ivs0 eff (externAt?_placedProgram_rebase_none _ _ _ _) rfl
          refine SepWP.call_subroutine_frame (F := AlignedSpillSlots s0.sp s0) (x := ())
            (ret_pc := b + 0x64#64) hMallocSub (by subst hsc; simp [arm64_norm])
            (by subst hsc; simp [arm64_norm, hrun])
            (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
            (fun R' hm => by
              refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
              dsimp only [libcMallocImplFineRawSpec, withCL, stackFrame, AlignedSpillSlots,
                MallocngModelEnv]
              rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
              simp only [hsc_sp, hsc_brk, hsc_mem, ← stackFrameAt_eq_memRegion (s0.sp - 32#64) 704, sepConj_assoc]
              rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩,
                  pure_sepConj_of_true ⟨by subst hsc; simpa [arm64_norm, hx0, hx1] using hEffReg,
                    hsc_tp, hsc_brks⟩,
                  pure_sepConj_of_true hcl2]
              have hCorePre := fineCoreImpl_to_rawPre (ro := ro) γ maddrs brkStart s0.brk bgt ivs0 align.toNat len.toNat
              dsimp only [eff, bgt'] at hCorePre ⊢
              exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hCorePre))))))
                (Entails.of_eq (by ac_rfl)))
            (fun _ _ _ hp => not_satisfies_false_sepConj hp)
            (fun _ _ _ _ he => not_satisfies_false_sepConj he)
            (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
            (fun R' soom _ ho => by
              refine Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun hOom => ?_)) (Satisfies.drop_mid ho)
              simp only [eff, hEffFit, decide_true, ↓reduceIte] at hOom
              simp only [hOkTrue, ↓reduceIte]
              subst hsc
              exact stepOomCond_of_perm_eq (by simp [arm64_norm]) (by simp [arm64_norm])
                (by simp [arm64_norm]) (fun _ => by simp only [arm64_norm]; rw [hm2.trans hm1]) hOom)
          dsimp only [libcMallocImplFineRawSpec, withCL, stackFrame] at *
          rw [hsc_sp, hsc_mem, ← stackFrameAt_eq_memRegion (s0.sp - 32#64) 704]
          simp only [eff, hEffFit, decide_true, ↓reduceIte]
          have hsp_sm : sm.sp = s0.sp - 32#64 := hsp_m.trans hsc_sp
          have hx19_sm : sm.readReg64 .x19 =
              if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64 := by
            simpa [hsc, arm64_norm, hx0] using hcs_m.readReg64_x19
          have hx20_sm : sm.readReg64 .x20 = len := by simpa [hsc, arm64_norm, hx1] using hcs_m.readReg64_x20
          have hcs21_sm : CalleeSaved21_28 s0 sm :=
            ⟨by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26,
             by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
             by simpa [hsc, arm64_norm] using hcs_m.vregs⟩
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro p; apply SepWP.exists_elim; intro bs
          apply SepWP.exists_elim; intro st'; apply SepWP.exists_elim; intro bCoarse'
          let b1 := mallocngAllocBudget true eff bCoarse'
          let b2 := mallocngAlignedBudget true align.toNat len.toNat bCoarse'
          refine SepWP.weaken_pre (P' :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
            ⌜MallocngProcPreserved sc sm ∧ MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bgt) eff) m2 sm.mem⌝ ∗
            ⌜sm.readReg64 .x0 = p ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧ MallocngBlockWf p eff ∧ bs.length = eff ∧
              MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') m2 sm.mem ∧
              MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
              ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
                g'.slots[idx]'hIdx = .liveUser p eff (max eff MallocngMinBlockCost) ∧
                p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧ (g'.isMmapped = true → bs = List.replicate eff 0#8) ∧
                (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < eff) ∧ (g'.sc = 24 → nominalSlotCap 22 < eff) ∧
                (g'.sc = 63 → g'.maplen * 4096 ≤ eff + 4115) ∧ FinePreEnframeRel bgt bgt' eff p st' g' idx⌝ ∗
            (MallocngRoTablesA maddrs ∗ MallocngCoreStModeA ro γ maddrs brkStart sm.brk b1.liveCost b1.peakCost st' ∗
             MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
             stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0))
            (by
              have hBoost := mallocngCoreStA_boost_alloc (ro := ro) γ maddrs brkStart sm.brk eff bCoarse' st'
              have hTok : MallocngBlockTokenK γ p eff 0 ⊢ mallocngIface.Block γ p eff :=
                mallocngBlockTokenK_to_token γ p eff 0
              dsimp only [b1, eff] at hBoost ⊢
              refine Entails.trans (Entails.of_eq (show _ =
                  MallocngCoreStModeA ro γ maddrs brkStart sm.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
                  MallocngBlockTokenK γ p (mallocngAlignedEffSize align.toNat len.toNat) 0 ∗
                  (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
                   ⌜MallocngProcPreserved sc sm ∧ MallocngMappedDelta 16
                     (FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize align.toNat len.toNat)) m2 sm.mem⌝ ∗
                   ⌜sm.readReg64 .x0 = p ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧
                     MallocngBlockWf p (mallocngAlignedEffSize align.toNat len.toNat) ∧
                     bs.length = mallocngAlignedEffSize align.toNat len.toNat ∧
                     MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') m2 sm.mem ∧
                     MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
                     ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
                       g'.slots[idx]'hIdx = .liveUser p (mallocngAlignedEffSize align.toNat len.toNat)
                         (max (mallocngAlignedEffSize align.toNat len.toNat) MallocngMinBlockCost) ∧
                       p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
                       (g'.isMmapped = true → bs = List.replicate (mallocngAlignedEffSize align.toNat len.toNat) 0#8) ∧
                       (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < mallocngAlignedEffSize align.toNat len.toNat) ∧
                       (g'.sc = 24 → nominalSlotCap 22 < mallocngAlignedEffSize align.toNat len.toNat) ∧
                       (g'.sc = 63 → g'.maplen * 4096 ≤ mallocngAlignedEffSize align.toNat len.toNat + 4115) ∧
                       FinePreEnframeRel bgt bgt' (mallocngAlignedEffSize align.toNat len.toNat) p st' g' idx⌝ ∗
                   MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗
                   stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) by ac_rfl)) ?_
              exact Entails.trans (sepConj_mono hBoost (sepConj_mono_left hTok)) (Entails.of_eq (by ac_rfl))) ?_
          refine sepWP_pure_left_aa fun hcl_sm => sepWP_pure_left_aa fun ⟨hproc_sm, hmd_sm⟩ =>
            sepWP_pure_left_aa fun ⟨hx0_sm, _htp_sm, _hbrks_sm, hBlkP, hBsLen,
              hNoOrph_sm, hCnt', g', hg', idx, hIdx, hSlot, hOff255, _, hSc24_26, _hSc24, hSc63, hPreRel⟩ => ?_
          have hCnt1 : MallocngCountIvsWF b1 (dynamicRootRegions st') st' := mallocngCountIvsWF_boost_alloc hCnt'
          refine sepWP_inspect_aa (q := MallocngWF maddrs.base brkStart sm.brk b1.liveCost b1.peakCost st')
            (by dsimp only [MallocngCoreStModeA, MallocngCoreStInflightModeA, MallocngWF]
                have hSw1 : (MallocngRoTablesA maddrs ∗
                    (⌜MallocngWFInflight 0 maddrs.base brkStart sm.brk b1.liveCost b1.peakCost st'⌝ ∗
                     MallocngLiveAuth γ st'.liveMap ∗ (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗
                     MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
                     ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
                     MappedSet st'.masterDom (OwnedMappedByte st')) ∗
                    MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
                    stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) =
                  (⌜MallocngWFInflight 0 maddrs.base brkStart sm.brk b1.liveCost b1.peakCost st'⌝ ∗
                   (MallocngRoTablesA maddrs ∗
                    (MallocngLiveAuth γ st'.liveMap ∗ (maddrs.ctx ↦ₛ st'.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗
                     MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗
                     ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
                     MappedSet st'.masterDom (OwnedMappedByte st')) ∗
                    MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
                    stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0)) := by ac_rfl
                rw [hSw1]; refine Entails.pure_left fun hwf => ?_
                simp only [sepConj_assoc]
                rw [pure_sepConj_of_true hwf, sepConj_comm (MallocngRoTablesA maddrs), ← sepConj_assoc,
                    pure_sepConj_of_true hwf]
                exact Entails.of_eq (by ac_rfl))
            fun hwf1 => ?_
          -- `+0x064 cbz x0, +0x2e8` (not taken since `p ≠ 0#64`)
          wp_step
          wp_if hpZero
          · exfalso; exact hBlkP.1 (by simpa [arm64_norm, hx0_sm] using hpZero)
          · -- At `+0x068`: compose `alignedAlloc_getMeta_getStride_ok` -> `+0x1b4` -> `alignedAlloc_reframe_st_ok`
            let RestGM :=
              MallocngLiveAuth γ st'.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
              (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗
              MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st') ∗ MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗
              mallocngIface.Block γ p eff ∗ stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0
            have hToGM :
                (MallocngRoTablesA maddrs ∗ MallocngCoreStModeA ro γ maddrs brkStart sm.brk b1.liveCost b1.peakCost st' ∗
                 MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
                 stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) ⊢ alignedGetMetaPre maddrs st' RestGM := by
              dsimp only [alignedGetMetaPre, MallocngRoTablesA, MallocngCoreStModeA, MallocngCoreStInflightModeA, RestGM]
              rw [pure_sepConj_of_true hwf1]; sep_frame
            refine SepWP.weaken_pre hToGM ?_
            have hF := liveUserBlockFacts_of hwf1 hg' hIdx hSlot
            refine SepWP.seq (alignedAlloc_getMeta_getStride_ok (Rest := RestGM) hb hprog_b12 hF
              (by simp [arm64_norm]) (by simp [arm64_norm, hrun_m]) (by simp [arm64_norm, hx0_sm])) ?_
            rintro s4 P4 hpc4 hrun4 ⟨⟨⟨hm4, hbrk4, hproc4, hsp4, _, _, hcs4⟩, hx0_4, hx2_4, hx4_4, hx6_4⟩, hEnt4⟩
            refine SepWP.weaken_pre hEnt4 ?_
            have hbrk_eq : s4.brk = sm.brk := hbrk4
            have hFromGM : alignedGetMetaPre maddrs st' RestGM ⊢
                (MallocngRoTablesA maddrs ∗ MallocngCoreStModeA ro γ maddrs brkStart s4.brk b1.liveCost b1.peakCost st' ∗
                 MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ mallocngIface.Block γ p eff ∗
                 stackFrameAt (s0.sp - 32#64) 704 ∗ AlignedSpillSlots s0.sp s0) := by
              rw [hbrk_eq]; dsimp only [alignedGetMetaPre, MallocngRoTablesA, MallocngCoreStModeA, MallocngCoreStInflightModeA, RestGM]
              rw [pure_sepConj_of_true hwf1]; sep_frame
            refine SepWP.weaken_pre hFromGM ?_
            have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := by simpa [hm4] using hcl_sm
            have hx19_4 : s4.readReg64 .x19 =
                if ConditionHolds .CS (subsPState64 align 16#64) then align else 16#64 :=
              hcs4.1.trans ((by simp [arm64_norm] : _ = sm.readReg64 .x19).trans hx19_sm)
            have hx20_4 : s4.readReg64 .x20 = len :=
              hcs4.2.1.trans ((by simp [arm64_norm] : _ = sm.readReg64 .x20).trans hx20_sm)
            have hcs21_4 : CalleeSaved21_28 s0 s4 :=
              ⟨hcs4.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.1), hcs4.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.1),
               hcs4.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.1), hcs4.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.1),
               hcs4.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.1), hcs4.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.1), hcs4.2.2.2.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.2.1),
               hcs4.2.2.2.2.2.2.2.2.2.2.2.trans (by simpa [arm64_norm] using hcs21_sm.2.2.2.2.2.2.2.2)⟩
            have hsp4_eq : s4.sp = s0.sp - 32#64 := hsp4.trans (by simpa [arm64_norm] using hsp_sm)
            have hwf4 : MallocngWF maddrs.base brkStart s4.brk b1.liveCost b1.peakCost st' := by rwa [hbrk_eq]
            refine SepWP.mono
              (alignedAlloc_reframe_st_ok (ro := ro) (B := MallocngTightBlock) (tp := tp) hb hprog_b12
                (fun _ _ _ _ => Entails.refl _) γ hwf4 hCnt1 hg' hIdx hBsLen hSlot hOff255 hSc24_26 hSc63
                hAlignOk hAlignMax hNoOvf hpc4 hrun4 hcl4 hsp4_eq rfl hspAl0 hx0_4 hx2_4 hx4_4 hx6_4 hx19_4 hx20_4 hcs21_4) ?_
            rintro sf Pf _hpc_f _hrun_f
              ⟨⟨new_p, bv, hx0_f, _hNewEq, hDynEq, hCnt2, hPureWf, hEntF⟩, _hcl_f, hperm_f, _hbrk_f, hproc_f, hsp_f, hcs_f⟩
            refine ⟨fun hmF => ?_, hsp_f, hcs_f⟩
            refine Satisfies.mono (sepConj_mono_left (Entails.trans hEntF ?_)) hmF
            simp only [hOkTrue, ↓reduceIte]
            let st2 := mkAlignedReframedSt st' g' idx p new_p align.toNat len.toNat bv
            have hPermF_sm : sf.mem.perm = sm.mem.perm := hperm_f.trans (congrArg Memory.perm hm4)
            have hPerm2_0 : m2.perm = s0.mem.perm := hm2.trans hm1
            have hProcAll : MallocngProcPreserved s0 sf :=
              alignedProcPreserved_trans (alignedProcPreserved_trans hsc_proc hproc_sm)
                (alignedProcPreserved_trans (alignedProcPreserved_trans (by proc_preserved_step) hproc4) hproc_f)
            have hAcct : MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) eff) s0 sf :=
              ⟨hProcAll, mappedDelta_congr_perm hPerm2_0 hmd_sm hPermF_sm⟩
            have hNoOrph2 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem := by
              rw [hDynEq]; exact noOrphanMappings_congr_perm hPerm2_0 hNoOrph_sm hPermF_sm
            have hCnt2_st2 : MallocngCountIvsWF b2 (dynamicRootRegions st2) st2 := by rwa [hDynEq]
            have hFine2 : MallocngFineInv bgt' (dynamicRootRegions st2) st2 :=
              fineInv_after_aligned_reframe (new_p := new_p) (bv := bv) hPreRel
            rw [pure_sepConj_of_true hAcct, ← stackFrameAt_736_split s0.sp]
            refine Entails.trans ?_ (sepConj_mono_right (Entails.sepExists_intro new_p))
            rw [pure_sepConj_of_true ⟨hx0_f, hPureWf⟩]
            have hPostEnv := reframePost_to_finePostEnv (ro := ro) γ maddrs tp brkStart bgt' b2 st2 ivs0 s0 sf
              (hProcAll.2.2.1.trans htp0) (hProcAll.2.2.2.1.trans hbrks0) hNoOrph2 hCnt2_st2 hFine2
            simp only [mallocngFineModeIface_block_eq]
            refine Entails.trans (Entails.of_eq (show _ = stackFrameAt s0.sp 736 ∗
              ((MallocngRoTablesA maddrs ∗ MallocngCoreStModeA ro γ maddrs brkStart sf.brk b2.liveCost b2.peakCost st2 ∗
                MallocngRuntime maddrs tp) ∗
               (MallocngTightBlock γ new_p len.toNat (max align.toNat 16) ∗ memRegion new_p len.toNat)) by ac_rfl)) ?_
            exact sepConj_mono_right (sepConj_mono_left hPostEnv)
        · -- Path 3: `MallocngMaxAllocSize < eff` (`ok = false`, calls `blk09_overflow_errno`)
          have hEffGt : MallocngMaxAllocSize < eff := by omega
          have hOkFalse : mallocngAlignedAllocOk align len = false := by simp [mallocngAlignedAllocOk, eff, hEffFit]
          let sp1 := s0.sp - 32#64
          conv => arg 4; dsimp only [MallocngModelEnv]; rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
          conv => arg 4; rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩, stackFrameAt_704_split_80 sp1]
          conv => arg 4; dsimp only [MallocngRuntime]
          cells_unfold_pre
          apply SepWP.exists_elim; intro ev; apply SepWP.exists_elim; intro u0; apply SepWP.exists_elim; intro u1
          let Rest3 :=
            stackFrameAt (sp1 - 80#64) 624 ∗ stackFrameAt sp1 64 ∗ AlignedSpillSlots s0.sp s0 ∗
            FineCoreModeImpl ro γ maddrs brkStart s0.brk bgt ivs0 ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
          have hOvfSub := placed_libcMallocImpl_overflow_errno_ok
            (P := blkPC_b12.rebase b (fun _ => none)) (externAt?_placedProgram_rebase_none _ _ _ _) rfl
          refine SepWP.call_subroutine_frame (F := Rest3) (x := (tp, u0, u1, ev))
            (ret_pc := b + 0x64#64) hOvfSub (by subst hsc; simp [arm64_norm]) (by subst hsc; simp [arm64_norm, hrun])
            (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
            (fun R' hm => by
              refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
              dsimp only [withCL, Rest3, AlignedSpillSlots, sp1]; simp only [hsc_sp, hsc_mem, sepConj_assoc]
              rw [pure_sepConj_of_true hcl2, pure_sepConj_of_true ⟨hsc_tp, by
                have hEq : (sc.readReg64 .x0).toNat = eff := by subst hsc; simpa [arm64_norm, hx0, hx1] using hEffReg
                omega⟩]; sep_frame)
            (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he)
            (fun sm hpc_m hrun_m hsp_m hcs_m => ?_) (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
          dsimp only [withCL] at *
          rw [hsc_sp, hsc_brk, hsc_mem, show s0.sp - 32#64 = sp1 from rfl]
          have hsp_sm : sm.sp = sp1 := hsp_m.trans hsc_sp
          conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
          apply SepWP.exists_elim; intro w0'; apply SepWP.exists_elim; intro w1'
          refine SepWP.weaken_pre (P' :=
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
            ⌜MallocngProcPreserved sc sm ∧ sm.brk = s0.brk ∧ sm.mem.perm = m2.perm ∧ sm.readReg64 .x0 = 0#64⌝ ∗
            (((sp1 - 80#64) ↦₆₄ w0') ∗ ((sp1 - 72#64) ↦₆₄ w1') ∗ ((tp - 0xa4#64) ↦₃₂ 12#32) ∗ Rest3))
            (Entails.of_eq (by ac_rfl)) ?_
          refine sepWP_pure_left_aa fun _hcl_sm => sepWP_pure_left_aa fun ⟨hproc_sm, hbrk_sm, hperm_sm, hx0_sm⟩ => ?_
          wp_step
          conv => arg 3; simp only [arm64_norm, show sm.readReg64 (.gpr 0#5) = 0#64 from hx0_sm, beq_self_eq_true, ↓reduceIte]
          conv => arg 4; dsimp only [Rest3, AlignedSpillSlots]
          have _hspAl_sm : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_sm]; exact hspAl32
          have ha16_sm : sm.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha24_sm : sm.sp + 16#64 + 8#64 = s0.sp - 8#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha8_sm : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          have ha32_sm : sm.sp + 32#64 = s0.sp := by rw [hsp_sm]; dsimp only [sp1]; bv_arith
          wp_step; wp_step; wp_step; wp_step
          have hPermAll : sm.mem.perm = s0.mem.perm := hperm_sm.trans (hm2.trans hm1)
          have hProc0_sm : MallocngProcPreserved s0 sm := alignedProcPreserved_trans hsc_proc hproc_sm
          refine sepWP_let_state fun sf hsf => ?_
          have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm, hbrk_sm]
          refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_m]) ⟨fun hm => ?_, ?_, ?_⟩
          · refine Satisfies.mono (sepConj_mono_left ?_) hm
            simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hAlignOk, Bool.not_true, hbrk_f]
            rw [pure_sepConj_of_true ⟨alignedProcPreserved_trans hProc0_sm (by subst hsf; proc_preserved_step),
                  AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩,
              stackFrameAt_704_split_80 sp1,
              pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, hx0_sm],
                by subst hsf; simp [arm64_norm, hProc0_sm.2.2.1.trans htp0],
                by subst hsf; simp [arm64_norm, hProc0_sm.2.2.2.1.trans hbrks0],
                AlignedStage1.noOrphanMappings_refl_of_perm_eq (by subst hsf; simpa [arm64_norm] using hPermAll)⟩]
            dsimp only [sp1]; cells_unfold; sep_frame
          · subst hsf; have _ := ha32_sm; simp [arm64_norm]
          · subst hsf; exact ⟨by simp [arm64_norm], by simp [arm64_norm],
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26,
              by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
              by simp [arm64_norm], by simpa [hsc, arm64_norm] using hcs_m.vregs⟩

/-- Polymorphic cross-block `alignedAllocErrnoFineSpec` (`blk12`, `736` B stack). -/
theorem placed_alignedAlloc_errno_fine_ok {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    [MallocngMultiPlacement] {P : Program}
    (γ : GhostName) (tp brkStart align len : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 12) (alignedAllocErrnoFineSpec γ tp brkStart align len bgt ivs0 ro) :=
  subroutine_ok_block_to_block (j := 12) (by decide)
    (blk12_alignedAlloc_errno_fine hRaw γ tp brkStart align len bgt ivs0) hext hsvc

private theorem failCore_to_finePostEnv {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (evVal : BitVec 32) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (s0 sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hNoOrph : MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem) :
    (FineCoreModeImpl ro γ A brkStart sf.brk bgt ivs0 ∗
      (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64))) ⊢
    MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt ivs0 s0 sf := by
  have hRt : (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ⊢
      MallocngRuntime A tp := by
    dsimp only [MallocngRuntime]; simp only [sepExists_sepConj_left]
    exact Entails.trans (by sep_frame) (Entails.sepExists_intro evVal)
  refine Entails.trans (sepConj_mono_right hRt) ?_
  dsimp only [MallocngModelPostEnv, MallocngModelEnv]
  refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq,
      pure_sepConj_of_true hNoOrph, pure_sepConj_of_true ⟨htp, hbrks⟩]
  exact Entails.of_eq (by ac_rfl)

private theorem blk12_alignedAlloc_fine {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 12 msvc) (mbase 12)
      (withCL mmpl (ToBaseSpec.toSpec
        (mallocngModelAlignedAllocSpec mallocngFineCostModel (mallocngFineModeIface ro) msvc γ maddrs) (mbase 12))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨align, len, sp0, tp, brkStart, bgt, ivs0⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [ToBaseSpec.toSpec, mallocngModelAlignedAllocSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, ⟨hx0, hx1, hsp_eq, _, _, hCaveat⟩, hpre⟩ := hpre
  rw [← sepConj_assoc] at hpre; refine ⟨_, hpre, ?_⟩
  have hSplit1024 : stackFrameAt s0.sp mallocngStackBytes =
      (stackFrameAt (s0.sp - 736#64) 288 ∗ stackFrame s0 736) := by
    rw [stackFrame_eq_stackFrameAt_aa s0 736]
    change stackFrameAt s0.sp 1024 = (stackFrameAt (s0.sp - 736#64) 288 ∗ stackFrameAt s0.sp 736)
    rw [stackFrameAt_split s0.sp 736 288]; ac_rfl
  rw [← hsp_eq, hSplit1024]
  have hSub := blk12_alignedAlloc_errno_fine hRaw γ tp brkStart align len bgt ivs0
  refine SepWP.call_subroutine_frame (F := stackFrameAt (s0.sp - 736#64) 288) (x := ())
    (ret_pc := s0.readReg64 .x30) hSub hpc hrun hspAl0 rfl
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [alignedAllocErrnoFineSpec, withCL]
      rw [sepConj_assoc, pure_sepConj_of_true hcl0, pure_sepConj_of_true ⟨hx0, hx1, hCaveat⟩]
      exact Entails.of_eq (by ac_rfl))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp) (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' soom _ ho => by
      rw [fine_stepB_ite (mallocngAlignedAllocOk align len) (.aligned align.toNat len.toNat) bgt]
      exact Satisfies.drop_mid ho)
  dsimp only [alignedAllocErrnoFineSpec, withCL] at *
  rw [fine_stepB_ite (mallocngAlignedAllocOk align len) (.aligned align.toNat len.toNat) bgt,
      fine_step_aligned_ite (mallocngAlignedAllocOk align len) align.toNat len.toNat bgt]
  dsimp only [evReqBytes]
  by_cases hOk : mallocngAlignedAllocOk align len = true
  · simp only [hOk, ↓reduceIte]
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro q
    let bgt' := fineStepAligned align.toNat len.toNat bgt
    let eff := mallocngAlignedEffSize align.toNat len.toNat
    refine SepWP.weaken_pre (P' :=
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
      ⌜MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) eff) s0 sf⌝ ∗
      ⌜sf.readReg64 .x0 = q ∧ (MallocngModelBlock (mallocngFineModeIface ro) γ).pureWf q (len.toNat, max align.toNat 16)⌝ ∗
      (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf ∗
       (MallocngModelBlock (mallocngFineModeIface ro) γ).interp q (len.toNat, max align.toNat 16) ∗
       stackFrame s0 736 ∗ stackFrameAt (s0.sp - 736#64) 288))
      (by dsimp only [bgt', eff]; exact Entails.of_eq (by ac_rfl)) ?_
    refine sepWP_pure_left_aa fun _hcl_f => sepWP_pure_left_aa fun hAcct =>
      sepWP_pure_left_aa fun ⟨hq, hPureQ⟩ => ?_
    refine SepWP.done hpc_f hrun_f ⟨fun hmF => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hmF
    simp only [OptOwn_pureWf_some, OptOwn_interp_some]
    rw [hq, pure_sepConj_of_true ⟨⟨hPureQ.1, hPureQ⟩, hAcct⟩]; exact Entails.of_eq (by dsimp only [bgt']; ac_rfl)
  · have hOkF : mallocngAlignedAllocOk align len = false := Bool.eq_false_iff.mpr hOk
    simp only [hOkF, Bool.false_eq_true, ↓reduceIte]
    let evVal : BitVec 32 := if !alignedAllocAlignOk align then 22#32 else 12#32
    refine SepWP.weaken_pre (P' :=
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
      ⌜MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) 0) s0 sf⌝ ∗
      ⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
       MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem⌝ ∗
      ((FineCoreModeImpl ro γ maddrs brkStart sf.brk bgt ivs0 ∗
        (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗
       stackFrame s0 736 ∗ stackFrameAt (s0.sp - 736#64) 288))
      (by dsimp only [evVal]; exact Entails.of_eq (by ac_rfl)) ?_
    refine sepWP_pure_left_aa fun _hcl_f => sepWP_pure_left_aa fun hAcct =>
      sepWP_pure_left_aa fun ⟨hx0_f, htp_f, hbrks_f, hNoOrph⟩ => ?_
    refine SepWP.done hpc_f hrun_f ⟨fun hmF => ?_, hsp_f, hcs_f⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hmF
    rw [hx0_f]; simp only [OptOwn_pureWf_none, OptOwn_interp_none]
    rw [pure_sepConj_of_true ⟨True.intro, hAcct⟩, pure_sepConj_of_true True.intro]
    have hPostEnv0 := failCore_to_finePostEnv (ro := ro) γ maddrs tp brkStart evVal bgt ivs0 s0 sf htp_f hbrks_f hNoOrph
    exact Entails.trans (sepConj_mono_left hPostEnv0) (Entails.of_eq (by ac_rfl))

/-- Top-level multi-block entry contract for `"aligned_alloc"` (`blk12`) over
    `mallocngFineCostModel` / `mallocngFineModeIface ro`. -/
theorem fine_alignedAlloc_entry_ok {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngModelAlignedAllocSpec mallocngFineCostModel (mallocngFineModeIface ro)
        svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  refine ⟨by decide +kernel, 12, 0, by decide +kernel, ?_⟩
  rw [fnAddr_aligned_alloc]
  exact withCL_to_withCodeLoaded (blk12_alignedAlloc_fine hRaw γ)

/-! ## 3. `blk11` (`posix_memalign`) & `"posix_memalign"` Entry -/

private theorem posixRet_of_ge8_ok_pm {align len : BitVec 64} (hGe8 : 8 ≤ align.toNat)
    (hOk : mallocngAlignedAllocOk align len = true) :
    mallocngPosixMemalignRet align len = 0#32 := by
  have ⟨hAl, hFit⟩ : alignedAllocAlignOk align = true ∧
      mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
    simpa [mallocngAlignedAllocOk] using hOk
  have hPow2 : isPow2Align align = true := by rwa [← alignOk_eq_isPow2_of_ge8 hGe8]
  have hNotLt : ¬ align.toNat < 8 := by omega
  simp [mallocngPosixMemalignRet, hNotLt, hPow2, hFit]

private theorem posixRet_of_ge8_fail_pm {align len : BitVec 64} (hGe8 : 8 ≤ align.toNat)
    (hFail : mallocngAlignedAllocOk align len = false) :
    (if !alignedAllocAlignOk align then 22#32 else 12#32) =
      mallocngPosixMemalignRet align len := by
  have hNotLt : ¬ align.toNat < 8 := by omega
  have hEqPow := alignOk_eq_isPow2_of_ge8 hGe8
  cases hAl : alignedAllocAlignOk align
  · have hPowF : isPow2Align align = false := by rw [← hEqPow]; exact hAl
    simp [mallocngPosixMemalignRet, hNotLt, hPowF]
  · have hPowT : isPow2Align align = true := by rw [← hEqPow]; exact hAl
    have hNotFit : ¬ mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize := by
      intro hFit; simp [mallocngAlignedAllocOk, hAl, hFit] at hFail
    simp [mallocngPosixMemalignRet, hNotLt, hPowT, hNotFit]

private theorem stackFrameAt_1024_split_pm_fine (sp0 : BitVec 64) :
    stackFrameAt sp0 mallocngStackBytes =
      (stackFrameAt (sp0 - 32#64 - 736#64) 256 ∗
       stackFrameAt (sp0 - 32#64) 736 ∗
       cells (sp0 - 32#64) 4) := by
  change stackFrameAt sp0 1024 = _
  rw [stackFrameAt_split sp0 32 992, stackFrameAt_split (sp0 - 32#64) 736 256,
    stackFrameAt_eq_memRegion sp0 32, memRegion_cells (sp0 - 32#64) 4 (by decide)]
  ac_rfl

private theorem finePostEnv_congr {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bgt' : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    {s0 sc sm sf : State}
    (hPermPre : sc.mem.perm = s0.mem.perm) (hPermPost : sf.mem.perm = sm.mem.perm)
    (hBrk : sf.brk = sm.brk)
    (hTp : sf.tpidrEl0 = sm.tpidrEl0) (hBrks : sf.brkStart = sm.brkStart) :
    MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt' ivs0 sc sm ⊢
    MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt' ivs0 s0 sf := by
  dsimp only [MallocngModelPostEnv, MallocngModelEnv]
  refine Entails.sepExists_elim fun ivsf => Entails.trans ?_ (Entails.sepExists_intro ivsf)
  refine Entails.pure_left fun hNoOrph => Entails.pure_left fun ⟨htp_sm, hbrks_sm⟩ => ?_
  rw [pure_sepConj_of_true (noOrphanMappings_congr_perm hPermPre hNoOrph hPermPost),
    pure_sepConj_of_true ⟨hTp.trans htp_sm, hBrks.trans hbrks_sm⟩, hBrk]
  exact Entails.refl _

set_option maxHeartbeats 400000 in
private theorem blk11_posixMemalign_fine {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    [MallocngMultiPlacement] (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 11 msvc) (mbase 11)
      (withCL mmpl (ToBaseSpec.toSpec
        (mallocngModelPosixMemalignSpec mallocngFineCostModel (mallocngFineModeIface ro) msvc γ maddrs)
        (mbase 11))) := by
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have hfn : ∀ c, (blkPC_b11.rebase c (fun _ => none)).fnAddr "posix_memalign" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase, Program.fnOff, Program.findSymbol?, blkPC_b11, PlacedLib.program]
    rw [blkSymsEq_b11]
    have hf : (ProofLib.ProgramReflection.toStringSymbols blkSymChars_b11).find? (·.1 == "posix_memalign") =
        some ("posix_memalign", 0) := by decide
    rw [hf]; exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b11 (hfn (mbase 11)) fun b hb => ?_
  have _ := hb
  rw [hfn b]
  have herr := placed_errnoLocation_perm_ok (P := blkPC_b11.rebase b (fun _ => none))
    (externAt?_placedProgram_rebase_none _ _ _ _) rfl
  apply subroutine_ok_of_sepWP_init
  rintro ⟨res, align, len, sp0, tp, brkStart, bgt, ivs0⟩ R s0 hpc hrun hpre hspAl0
  dsimp only [ToBaseSpec.toSpec, mallocngModelPosixMemalignSpec] at hpre ⊢
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨rfl, ⟨hx0, hx1, hx2, hsp_eq, _, _, _, hCaveat⟩, hpre⟩ := hpre
  subst hsp_eq
  change s0.readReg64 (.gpr 0#5) = res at hx0; change s0.readReg64 (.gpr 1#5) = align at hx1
  change s0.readReg64 (.gpr 2#5) = len at hx2
  have ⟨htp0, hbrks0⟩ : s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart := by
    have hm0 : s0.mem ⊨ ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        ((OptOutPtr (MallocngModelBlock (mallocngFineModeIface ro) γ)).interp res none ∗
         (mallocngFineModeIface ro).HeapM γ maddrs tp brkStart s0.brk bgt ivs0 ∗
         stackFrameAt s0.sp mallocngStackBytes ∗ R) := by
      dsimp only [MallocngModelEnv] at hpre; exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre
    rw [satisfies_pure_sepConj] at hm0; exact hm0.1
  refine ⟨(OptOutPtr (MallocngModelBlock (mallocngFineModeIface ro) γ)).interp res none ∗
    MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
    stackFrameAt s0.sp mallocngStackBytes, by simpa [sepConj_assoc] using hpre, ?_⟩
  rw [fine_stepB_ite (mallocngPosixMemalignOk align len) (.aligned align.toNat len.toNat) bgt,
      fine_step_aligned_ite (mallocngPosixMemalignOk align len) align.toNat len.toNat bgt]
  dsimp only [evReqBytes]
  wp_step; wp_step
  wp_if hLs7
  · -- Early exit (`align.toNat < 8`, `+0x050 mov w0, #0x16; +0x054 ret`)
    have hLt8 : align.toNat < 8 := by
      have hUle : align.ule 7#64 = true := by simpa [arm64_norm, hx1] using hLs7
      rw [BitVec.ule, decide_eq_true_eq] at hUle; change align.toNat ≤ 7 at hUle; omega
    have hPmOkF : mallocngPosixMemalignOk align len = false := by
      simp [mallocngPosixMemalignOk, show ¬ 8 ≤ align.toNat by omega]
    have hRetEq : (22#32 : BitVec 32) = mallocngPosixMemalignRet align len := by
      simp [mallocngPosixMemalignRet, hLt8]
    wp_step; wp_step
    refine sepWP_let_state fun sf hsf => ?_
    have hbrk_f : sf.brk = s0.brk := by subst hsf; simp [arm64_norm]
    refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun]) ⟨fun hm => ?_, ?_, ?_⟩
    · refine Satisfies.mono (sepConj_mono_left ?_) hm
      simp only [hPmOkF, Bool.false_eq_true, ↓reduceIte, OptOutPtr_pureWf]
      rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRetEq,
            ⟨by subst hsf; proc_preserved_step, AlignedStage1.mappedDelta_of_perm_eq (by subst hsf; simp [arm64_norm])⟩⟩]
      have hEnvToPost :
          MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ⊢
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 sf := by
        dsimp only [MallocngModelPostEnv, MallocngModelEnv]; refine Entails.trans ?_ (Entails.sepExists_intro ivs0)
        rw [pure_sepConj_of_true (AlignedStage1.noOrphanMappings_refl_of_perm_eq (by subst hsf; simp [arm64_norm])),
          pure_sepConj_of_true ⟨htp0, hbrks0⟩, pure_sepConj_of_true ⟨by subst hsf; simp [arm64_norm, htp0],
            by subst hsf; simp [arm64_norm, hbrks0]⟩, hbrk_f]
        exact Entails.refl _
      exact Entails.trans (Entails.of_eq (by ac_rfl)) (sepConj_mono_right (sepConj_mono_left hEnvToPost))
    · subst hsf; simp [arm64_norm]
    · subst hsf; exact ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩
  · -- `8 ≤ align.toNat`: prologue + `bl aligned_alloc` (`mbase 12`)
    have hGe8 : 8 ≤ align.toNat := by
      have hNotUle : align.ule 7#64 = false := by
        cases hb7 : align.ule 7#64
        · rfl
        · exfalso; simp [arm64_norm, hb7] at hLs7
      rw [BitVec.ule, decide_eq_false_iff_not] at hNotUle; change ¬ align.toNat ≤ 7 at hNotUle; omega
    have hPmEqAa : mallocngPosixMemalignOk align len = mallocngAlignedAllocOk align len := by
      simp [mallocngPosixMemalignOk, hGe8]
    conv => arg 4; rw [stackFrameAt_1024_split_pm_fine s0.sp]
    cells_unfold_pre
    apply SepWP.exists_elim; intro w0; apply SepWP.exists_elim; intro w1
    apply SepWP.exists_elim; intro w2; apply SepWP.exists_elim; intro w3
    let sp1 := s0.sp - 32#64
    have ha16_sp : sp1 + 16#64 = s0.sp - 16#64 := by dsimp only [sp1]; bv_arith
    have ha8_sp : sp1 + 8#64 = s0.sp - 24#64 := by dsimp only [sp1]; bv_arith
    have ha32_sp : sp1 + 32#64 = s0.sp := by dsimp only [sp1]; bv_arith
    have hspAl32 : (sp1 &&& 15#64 == 0#64) = true := s0.spAligned_sub 32#64 hspAl0
    wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step; wp_str64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step
    have hpc_bl12 : b + 0x24#64 + (mbase 12 - mbase 11 - 0x24#64) = mbase 12 := by rw [hb]; bv_arith
    conv => arg 3; simp only [hpc_bl12]
    refine sepWP_let_state fun sc hsc => ?_
    have hsc_sp : sc.sp = sp1 := by subst hsc; simp [arm64_norm, sp1]
    have hsc_sf736 : stackFrame sc 736 = stackFrameAt sp1 736 := by
      unfold stackFrame; rw [hsc_sp, ← stackFrameAt_eq_memRegion sp1 736]
    have hsc_brk : sc.brk = s0.brk := by subst hsc; simp [arm64_norm]
    have hsc_mem : sc.mem = m2 := by subst hsc; simp [arm64_norm]
    have hsc_tp : sc.tpidrEl0 = tp := by subst hsc; simp [arm64_norm, htp0]
    have hsc_brks : sc.brkStart = brkStart := by subst hsc; simp [arm64_norm, hbrks0]
    have hsc_proc : MallocngProcPreserved s0 sc := by subst hsc; proc_preserved_step
    let FramePM :=
      memRegion res 8 ∗ stackFrameAt (sp1 - 736#64) 256 ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3)
    have hAaSub := placed_alignedAlloc_errno_fine_ok hRaw
      (P := blkPC_b11.rebase b (fun _ => none))
      γ tp brkStart align len bgt ivs0 (externAt?_placedProgram_rebase_none _ _ _ _) rfl
    refine SepWP.call_subroutine_frame (F := FramePM) (x := ())
      (ret_pc := b + 0x28#64) hAaSub (by subst hsc; simp [arm64_norm]) (by subst hsc; simp [arm64_norm, hrun])
      (by simpa [State.spAligned, hsc_sp] using hspAl32) (by subst hsc; simp [arm64_norm])
      (fun R' hm => by
        refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
        dsimp only [alignedAllocErrnoFineSpec, withCL, FramePM, MallocngModelEnv, OptOutPtr]
        simp only [hsc_sf736, hsc_brk, hsc_mem, sepConj_assoc]
        rw [pure_sepConj_of_true ⟨htp0, hbrks0⟩,
            pure_sepConj_of_true ⟨by subst hsc; simp [arm64_norm], by subst hsc; simp [arm64_norm], hCaveat⟩,
            pure_sepConj_of_true ⟨hsc_tp, hsc_brks⟩,
            pure_sepConj_of_true hcl2]
        dsimp only [sp1]; exact Entails.of_eq (by ac_rfl))
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
      (fun R' soom _ ho => by
        refine Satisfies.mono (sepConj_mono_left (Entails.pure_mono fun hOom => ?_)) (Satisfies.drop_mid ho)
        rw [hPmEqAa]; subst hsc
        exact stepOomCond_of_perm_eq (by simp [arm64_norm]) (by simp [arm64_norm])
          (by simp [arm64_norm]) (fun _ => by simp only [arm64_norm]; rw [hm2.trans hm1]) hOom)
    dsimp only [alignedAllocErrnoFineSpec, withCL] at *
    rw [hsc_sf736]
    have hsp_sm : sm.sp = sp1 := hsp_m.trans hsc_sp
    have _hspAl_sm : (sm.sp &&& 15#64 == 0#64) = true := by rw [hsp_sm]; exact hspAl32
    have hx19_sm : sm.readReg64 (.gpr 19#5) = res :=
      hcs_m.readReg64_x19.trans (by subst hsc; simp [arm64_norm])
    have hPerm2_0 : m2.perm = s0.mem.perm := hm2.trans hm1
    by_cases hAaOk : mallocngAlignedAllocOk align len = true
    · -- Success (`hAaOk = true`): `cbz` not taken, `str x1, [x19]`, epilogue, `ret` `0#32`
      simp only [hAaOk, ↓reduceIte]
      have hPmOkT : mallocngPosixMemalignOk align len = true := hPmEqAa.trans hAaOk
      have hRet0 := posixRet_of_ge8_ok_pm (len := len) hGe8 hAaOk
      let eff := mallocngAlignedEffSize align.toNat len.toNat
      let bgt' := fineStepAligned align.toNat len.toNat bgt
      conv => arg 4; dsimp only [FramePM]; rw [memRegion_eight res]
      conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro oldRes; apply SepWP.exists_elim; intro q
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) eff) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = q ∧ (MallocngModelBlock (mallocngFineModeIface ro) γ).pureWf q (len.toNat, max align.toNat 16)⌝ ∗
        ((res ↦₆₄ oldRes) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗ stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 sc sm ∗
         (MallocngModelBlock (mallocngFineModeIface ro) γ).interp q (len.toNat, max align.toNat 16)))
        (by dsimp only [eff, bgt']; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left_aa fun hcl_sm => sepWP_pure_left_aa fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left_aa fun ⟨hx0_sm, hPureQ⟩ => ?_
      wp_step; wp_step
      wp_if hqZero
      · exfalso; exact hPureQ.1 (by simpa [arm64_norm, hx0_sm] using hqZero)
      · have ha16_sm : sm.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_sm]; exact ha16_sp
        have ha8_sm : sm.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_sm]; exact ha8_sp
        have ha32_sm : sm.sp + 32#64 = s0.sp := by rw [hsp_sm]; exact ha32_sp
        wp_step; wp_str64_cl m3 hm3 hcl_sm _hcl3; wp_step; wp_step; wp_step
        refine sepWP_let_state fun sf hsf => ?_
        have hPerm3_sm : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hm3
        have hbrk_f : sf.brk = sm.brk := by subst hsf; simp [arm64_norm]
        have hProcAll : MallocngProcPreserved s0 sf :=
          alignedProcPreserved_trans (alignedProcPreserved_trans hsc_proc hproc_sm) (by subst hsf; proc_preserved_step)
        have hAcctAll : MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) eff) s0 sf :=
          ⟨hProcAll, mappedDelta_congr_perm (hsc_mem ▸ hPerm2_0) hmd_sm hPerm3_sm⟩
        refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_m]) ⟨fun hmF => ?_, ?_, ?_⟩
        · refine Satisfies.mono (sepConj_mono_left ?_) hmF
          simp only [hPmOkT, ↓reduceIte, OptOutPtr_interp_some, OptOutPtr_pureWf]
          rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm] using hRet0.symm, hAcctAll⟩,
            stackFrameAt_1024_split_pm_fine s0.sp]
          have hPostEnvCongr := finePostEnv_congr (ro := ro) γ maddrs tp brkStart bgt' ivs0
            (hsc_mem ▸ hPerm2_0) hPerm3_sm hbrk_f (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm])
          have hOutPtr :
              ((res ↦₆₄ q) ∗ (MallocngModelBlock (mallocngFineModeIface ro) γ).interp q (len.toNat, max align.toNat 16)) ⊢
              outPtrPost (MallocngModelBlock (mallocngFineModeIface ro) γ) res (len.toNat, max align.toNat 16) := by
            rw [outPtrPost_def]; refine Entails.trans ?_ (Entails.sepExists_intro q)
            rw [pure_sepConj_of_true hPureQ]; exact Entails.refl _
          dsimp only [sp1]; cells_unfold
          refine Entails.trans (Entails.of_eq (show _ =
              ((res ↦₆₄ q) ∗ (MallocngModelBlock (mallocngFineModeIface ro) γ).interp q (len.toNat, max align.toNat 16)) ∗
              MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 sc sm ∗
              (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
               ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((s0.sp - 8#64) ↦₆₄ w3) ∗
               stackFrameAt (s0.sp - 32#64) 736 ∗ stackFrameAt (s0.sp - 32#64 - 736#64) 256) by
            dsimp only [bgt']; ac_rfl)) ?_
          exact Entails.trans (sepConj_mono_left hOutPtr)
            (Entails.trans (sepConj_mono_right (sepConj_mono_left hPostEnvCongr)) (by sep_frame))
        · subst hsf; have _ := ha32_sm; simp [arm64_norm]
        · subst hsf; exact ⟨by simp [arm64_norm],
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x20, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26, by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27,
            by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28,
            by simp [arm64_norm], by simpa [hsc, arm64_norm] using hcs_m.vregs⟩
    · -- Failure (`hAaOk = false`): `cbz` taken -> `+0x044 bl ___errno_location; ldr w0, [x0]; b +0x038`
      have hAaF : mallocngAlignedAllocOk align len = false := Bool.eq_false_iff.mpr hAaOk
      have hPmOkF : mallocngPosixMemalignOk align len = false := hPmEqAa.trans hAaF
      have hRetFail := posixRet_of_ge8_fail_pm (len := len) hGe8 hAaF
      simp only [hAaF, Bool.false_eq_true, ↓reduceIte]
      let evVal : BitVec 32 := if !alignedAllocAlignOk align then 22#32 else 12#32
      refine SepWP.weaken_pre (P' :=
        ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
        ⌜MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) 0) sc sm⌝ ∗
        ⌜sm.readReg64 .x0 = 0#64 ∧ sm.tpidrEl0 = tp ∧ sm.brkStart = brkStart ∧
         MallocngNoOrphanMappings ivs0 ivs0 sc.mem sm.mem⌝ ∗
        (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         ((s0.sp - 8#64) ↦₆₄ w3) ∗ memRegion res 8 ∗ stackFrameAt sp1 736 ∗ stackFrameAt (sp1 - 736#64) 256 ∗
         FineCoreModeImpl ro γ maddrs brkStart sm.brk bgt ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)))
        (by dsimp only [FramePM, evVal]; exact Entails.of_eq (by ac_rfl)) ?_
      refine sepWP_pure_left_aa fun hcl_sm => sepWP_pure_left_aa fun ⟨hproc_sm, hmd_sm⟩ =>
        sepWP_pure_left_aa fun ⟨hx0_sm, htp_sm, hbrks_sm, hNoOrph_sm⟩ => ?_
      wp_step; wp_step
      conv => arg 3; simp only [arm64_norm, show sm.readReg64 (.gpr 0#5) = 0#64 from hx0_sm, beq_self_eq_true, ↓reduceIte]
      wp_step
      have hpc_bl0 : b + 0x44#64 + (mbase 0 - mbase 11 - 0x44#64) = mbase 0 := by rw [hb]; bv_arith
      conv => arg 3; simp only [hpc_bl0]
      refine sepWP_call_errno (ret_pc := b + 0x48#64) herr (by simp [arm64_norm]) (by simp [arm64_norm, hrun_m])
        (by simpa [arm64_norm, hsp_sm] using hspAl32) (by simp [arm64_norm]) hcl_sm
        fun se hpc_e hrun_e hsp_e hcs_e _hcl_e hproc_e hbrk_e hperm_e hx0_e => ?_
      have hsp_se : se.sp = sp1 := (by simpa [arm64_norm] using hsp_e : se.sp = sm.sp).trans hsp_sm
      have _hspAl_se : (se.sp &&& 15#64 == 0#64) = true := by rw [hsp_se]; exact hspAl32
      have ha16_se : se.sp + 16#64 = s0.sp - 16#64 := by rw [hsp_se]; exact ha16_sp
      have ha8_se : se.sp + 8#64 = s0.sp - 24#64 := by rw [hsp_se]; exact ha8_sp
      have ha32_se : se.sp + 32#64 = s0.sp := by rw [hsp_se]; exact ha32_sp
      have hx0_se : se.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by simpa [arm64_norm, htp_sm] using hx0_e
      have hbrk_se : se.brk = sm.brk := hbrk_e.trans (by simp [arm64_norm])
      have hperm_se : se.mem.perm = sm.mem.perm := hperm_e.trans (by simp [arm64_norm])
      have hProc0_se : MallocngProcPreserved s0 se :=
        alignedProcPreserved_trans (alignedProcPreserved_trans hsc_proc hproc_sm)
          (alignedProcPreserved_trans (by proc_preserved_step) hproc_e)
      wp_step; wp_step; wp_step; wp_step; wp_step
      refine sepWP_let_state fun sf hsf => ?_
      have hperm_f : sf.mem.perm = sm.mem.perm := by subst hsf; simpa [arm64_norm] using hperm_se
      have hbrk_f : sf.brk = sm.brk := by subst hsf; simpa [arm64_norm] using hbrk_se
      have hNoOrphAll : MallocngNoOrphanMappings ivs0 ivs0 s0.mem sf.mem :=
        noOrphanMappings_congr_perm (hsc_mem ▸ hPerm2_0) hNoOrph_sm hperm_f
      have hAcctAll : MallocngCallAccounting 16 (FineStepBound (fineMaxMetaAreas bgt) 0) s0 sf :=
        ⟨alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step),
         mappedDelta_congr_perm (hsc_mem ▸ hPerm2_0) hmd_sm hperm_f⟩
      refine SepWP.done (by subst hsf; simp [arm64_norm]) (by subst hsf; simp [arm64_norm, hrun_e]) ⟨fun hmF => ?_, ?_, ?_⟩
      · refine Satisfies.mono (sepConj_mono_left ?_) hmF
        simp only [hPmOkF, Bool.false_eq_true, ↓reduceIte, OptOutPtr_interp_none, OptOutPtr_pureWf]
        rw [pure_sepConj_of_true ⟨True.intro, by subst hsf; simpa [arm64_norm, evVal] using hRetFail, hAcctAll⟩,
          stackFrameAt_1024_split_pm_fine s0.sp]
        have htp_f : sf.tpidrEl0 = tp := (alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step)).2.2.1.trans htp0
        have hbrks_f : sf.brkStart = brkStart := (alignedProcPreserved_trans hProc0_se (by subst hsf; proc_preserved_step)).2.2.2.1.trans hbrks0
        have hPostEnv0 := failCore_to_finePostEnv (ro := ro) γ maddrs tp brkStart evVal bgt ivs0 s0 sf htp_f hbrks_f hNoOrphAll
        dsimp only [sp1]; cells_unfold
        refine Entails.trans (Entails.of_eq (show _ =
            (FineCoreModeImpl ro γ maddrs brkStart sf.brk bgt ivs0 ∗
             (((tp - 0xa4#64) ↦₃₂ evVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗
            (((s0.sp - 16#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗ ((s0.sp - 8#64) ↦₆₄ w3) ∗
             memRegion res 8 ∗ stackFrameAt (s0.sp - 32#64) 736 ∗ stackFrameAt (s0.sp - 32#64 - 736#64) 256) by
          rw [hbrk_f]; dsimp only [evVal]; ac_rfl)) ?_
        exact Entails.trans (sepConj_mono_left hPostEnv0) (by sep_frame)
      · subst hsf; have _ := ha32_se; simp [arm64_norm]
      · subst hsf; exact ⟨by simp [arm64_norm],
          by simpa [arm64_norm] using hcs_e.readReg64_x20.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x20),
          by simpa [arm64_norm] using hcs_e.readReg64_x21.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x21),
          by simpa [arm64_norm] using hcs_e.readReg64_x22.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x22),
          by simpa [arm64_norm] using hcs_e.readReg64_x23.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x23),
          by simpa [arm64_norm] using hcs_e.readReg64_x24.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x24),
          by simpa [arm64_norm] using hcs_e.readReg64_x25.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x25),
          by simpa [arm64_norm] using hcs_e.readReg64_x26.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x26),
          by simpa [arm64_norm] using hcs_e.readReg64_x27.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x27),
          by simpa [arm64_norm] using hcs_e.readReg64_x28.trans (by simpa [hsc, arm64_norm] using hcs_m.readReg64_x28),
          by simp [arm64_norm], by simpa [arm64_norm] using hcs_e.vregs.trans (by simpa [hsc, arm64_norm] using hcs_m.vregs)⟩

/-- Top-level multi-block entry contract for `"posix_memalign"` (`blk11`) over
    `mallocngFineCostModel` / `mallocngFineModeIface ro`. -/
theorem fine_posixMemalign_entry_ok {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngModelPosixMemalignSpec mallocngFineCostModel (mallocngFineModeIface ro)
        svc γ (mallocngAddrsOfPlacement mpl)) := by
  let _ : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  refine ⟨by decide +kernel, 11, 0, by decide +kernel, ?_⟩
  rw [fnAddr_posix_memalign]
  exact withCL_to_withCodeLoaded (blk11_posixMemalign_fine hRaw γ)

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
