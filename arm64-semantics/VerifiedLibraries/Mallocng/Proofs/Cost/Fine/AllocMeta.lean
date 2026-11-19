/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Specs
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullStage2
import VerifiedLibraries.Mallocng.Proofs.SyscallWrappersProof

/-!
# Fine Verification of Placed `__malloc_alloc_meta` (`blk07`)

- **Role**: `Role::Proof` (untrusted).
- **Purpose**: Proves `placed_allocMeta_fine_ok : AllocMetaFineStmt`, strengthening the full placed
  `blk07` contract with `st'.metaAreas.length ≤ st.metaAreas.length + 1`, `FineSplitInv bL bP st'`,
  and the `FineMetaStep maxMeta` (`4096 * (maxMeta + 43)`) mapped-delta and OOM step bound whenever
  `st.metaAreas.length ≤ maxMeta + 5`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost
open VerifiedLibraries.Mallocng.Proofs.AllocMetaFullH hiding
  blk07Words blk07Relocs blk07Words0 blk07Relocs0 blk07Words116 blk07Relocs116

private abbrev amfWords : List (BitVec 32) := AllocMetaFullH.blk07Words
private abbrev amfRelocs : List Obj.RelocEntry := AllocMetaFullH.blk07Relocs

local macro "AmfHasWords0" svc:term : term =>
  `(((mallocngBlockProg mmpl 7 msvc).withSvc $svc).hasWords (mbase 7)
      (Obj.patchRelocs AllocMetaFullH.blk07Relocs0 AllocMetaFullH.blk07Words0 (mbase 7)
        (VerifiedLibraries.mallocngLib.resolve mmpl)))
local macro "AmfHasWords116" svc:term : term =>
  `(((mallocngBlockProg mmpl 7 msvc).withSvc $svc).hasWords (mbase 7 + 116#64)
      (Obj.patchRelocs AllocMetaFullH.blk07Relocs116 AllocMetaFullH.blk07Words116 (mbase 7 + 116#64)
        (VerifiedLibraries.mallocngLib.resolve mmpl)))
local macro "AmfRange116" : term =>
  `(∀ r ∈ AllocMetaFullH.blk07Relocs116,
      Obj.CodeRelocInRange r.kind (mbase 7 + 116#64 + BitVec.ofNat 64 r.off)
        (Obj.addSignedAddr (VerifiedLibraries.mallocngLib.resolve mmpl r.sym) r.addend))

/-! ## 1. Fine Step Bound, Postcondition Bundle, and `brk` / `NoOrphan` Helpers -/

private theorem appendMetaArea_length (mas : List MetaAreaDesc) (ap : BitVec 64) :
    (appendMetaArea mas ap).length = mas.length + 1 := by
  have h := congrArg List.length (appendMetaArea_props mas ap).1
  simp only [List.length_map, List.length_append, List.length_singleton] at h
  exact h

private theorem metaAreas_mmap_bytes_le_fineMetaStep
    {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost maxMeta : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hInflight : inflight ≤ 7) (hNoFree : st.freeMetas = [])
    (hNoBump : st.bumpMetas = []) (hNoAvail : st.availMetaPages = [])
    (hMaStep : st.metaAreas.length ≤ maxMeta + 5) :
    let m := st.ctx.metaAllocShift.toNat
    let len := 4096 * 2 ^ (m + 1)
    m ≤ 35 ∧ 8192 ≤ len ∧ len ≤ 2 ^ 48 ∧ 4096 ∣ len ∧ len + 4096 ≤ FineMetaStep maxMeta := by
  intro m len
  obtain ⟨hmLe35, hGe8192, hLe48, hDvd, _⟩ :=
    slowPathC_prep_bounds hwf hInflight hNoFree hNoBump hNoAvail
  refine ⟨hmLe35, hGe8192, hLe48, hDvd, ?_⟩
  unfold FineMetaStep
  by_cases hm0 : m = 0
  · dsimp only [len]; rw [hm0]; omega
  · obtain ⟨_, _, hSum, _, _⟩ := hwf.meta_pages_bound.2.2 m (by omega) rfl
    have hAv0 : st.availMetaPages.length = 0 := by simp [hNoAvail]
    have hPow : 2 ^ (m + 1) ≤ maxMeta + 42 := by omega
    dsimp only [len]
    omega

private abbrev AllocMetaFinePost [MallocngMultiPlacement] {ro : Bool} (inflight : Nat) (γ : GhostName)
    (tp brkStart : BitVec 64) (liveCost peakCost peakCount : Nat)
    (bL bP : FineBudget) (maxMeta : Nat) (st : MallocngSt)
    (s0 sf : State) (P_f : SepProp) : Prop :=
  (P_f ⊢ ∃∗ st' : MallocngSt, ∃∗ m : BitVec 64,
    ⌜MallocngProcPreserved s0 sf ∧ sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
     4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
     m ∉ st.reservedMetas ∧ st'.reservedMetas = m :: st.reservedMetas ∧
     st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
     st'.liveMap = st.liveMap ∧ totalLiveCount st' = totalLiveCount st ∧
     st'.metaAreas.length ≤ st.metaAreas.length + 1 ∧
     st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
     FineSplitInv bL bP st' ∧
     st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
     st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧
     st'.ctx.seq = st.ctx.seq ∧
     (∀ g ∈ st.groups, ∀ a : BitVec 64,
       (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
     MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sf.mem⌝ ∗
    stackFrame s0 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
    MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st') ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

private theorem allocMetaFinePost_congr [MallocngMultiPlacement] {ro : Bool} {inflight : Nat} {γ : GhostName}
    {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat} {st1 st2 : MallocngSt} {s0 sf : State} {P_f : SepProp}
    (hEq : st1.reservedMetas = st2.reservedMetas ∧ st1.groups = st2.groups ∧
      st1.activeLists = st2.activeLists ∧ st1.liveMap = st2.liveMap ∧
      st1.metaAreas = st2.metaAreas ∧ st1.guardPages = st2.guardPages ∧
      st1.availMetaPages = st2.availMetaPages ∧ st1.ctx.active = st2.ctx.active ∧
      st1.ctx.usageByClass = st2.ctx.usageByClass ∧ st1.ctx.unmapSeq = st2.ctx.unmapSeq ∧
      st1.ctx.bounces = st2.ctx.bounces ∧ st1.ctx.seq = st2.ctx.seq ∧ st1.byteVal = st2.byteVal)
    (hPost : AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st1 s0 sf P_f) :
    AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st2 s0 sf P_f := by
  obtain ⟨r1, r2, r3, r4, rMa, rGp, rAv, r5, r6, r7, r8, r9, r10⟩ := hEq
  have rCnt : totalLiveCount st1 = totalLiveCount st2 := by unfold totalLiveCount; rw [r2]
  have rDyn : dynamicRootRegions st1 = dynamicRootRegions st2 := by
    unfold dynamicRootRegions; rw [rMa, rGp, rAv, r2]
  unfold AllocMetaFinePost at hPost ⊢
  rwa [r1, r2, r3, r4, rCnt, rMa, r5, r6, r7, r8, r9, r10, rDyn] at hPost

private theorem evalInst_svc0_execBrk_fine [MallocngMultiPlacement] {s : State} (hx8 : s.readReg64 .x8 = 214#64) :
    (mallocngBlockProg mmpl 7 msvc).evalInst (.system false 0#16) s = execBrk s := by
  have hAlloc : Syscall.alloc s = execBrk s := by simp [Syscall.alloc, Syscall.dispatch, Syscall.allocTable, hx8]
  have hEq : (mallocngBlockProg mmpl 7 msvc).svc s = Syscall.alloc s := ((MallocngMultiPlacement.svcValid s).1 hx8).trans hAlloc.symm
  rw [Program.evalInst_svc0]
  exact (show evalSvc (mallocngBlockProg mmpl 7 msvc).svc s = evalSvc Syscall.alloc s by unfold evalSvc; rw [hEq]).trans ((evalSvc_alloc s).trans hAlloc)

private theorem post_brk_state_fine {s0 s1 : State} (s2 : State) (pc' v : BitVec 64)
    (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1)
    (hEq : s2.pc = pc' ∧ s2.status = s1.status ∧ s2.sp = s1.sp ∧ s2.regs = (s1.writeReg64 .x0 v).regs ∧
      s2.vregs = s1.vregs ∧ s2.fs = s1.fs ∧ s2.trace = s1.trace ∧ s2.tpidrEl0 = s1.tpidrEl0 ∧
      s2.brkStart = s1.brkStart ∧ s2.oracle = s1.oracle ∧ s2.symtab = s1.symtab ∧ s2.sigActions = s1.sigActions) :
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = v ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 := by
  obtain ⟨hpc, hst, hsp, hrg, hvr, hfs, htr, htp, hbs, hor, hsy, hsig⟩ := hEq
  have hGpr : ∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n) := fun n hn0 hn31 =>
    (by simp [State.readReg64, hn31, hrg] : s2.readReg64 (.gpr n) = (s1.writeReg64 .x0 v).readReg64 (.gpr n)).trans
      (State.readReg64_writeReg64_gpr_ne s1 .x0 n v (by simp [Reg.isGprIdx, beq_eq_false_iff_ne.mpr hn0.symm]) (beq_eq_false_iff_ne.mpr hn31))
  have hx0 : s2.readReg64 .x0 = v :=
    (by simp [State.readReg64, hrg] : s2.readReg64 .x0 = (s1.writeReg64 .x0 v).readReg64 .x0).trans (State.readReg64_writeReg64_gpr_same s1 .x0 0#5 v rfl rfl)
  exact ⟨hpc, hst.trans hRun1, hsp.trans hSp1, hx0, hGpr,
    ⟨(hGpr 25#5 nofun nofun).trans hCs1.1, (hGpr 26#5 nofun nofun).trans hCs1.2.1,
     (hGpr 27#5 nofun nofun).trans hCs1.2.2.1, (hGpr 28#5 nofun nofun).trans hCs1.2.2.2.1, (by simp [calleeSavedVRegs, hvr] : calleeSavedVRegs s2 = calleeSavedVRegs s1).trans hCs1.2.2.2.2⟩,
    ⟨hfs.trans hProc1.1, htr.trans hProc1.2.1, htp.trans hProc1.2.2.1, hbs.trans hProc1.2.2.2.1,
     hor.trans hProc1.2.2.2.2.1, hsy.trans hProc1.2.2.2.2.2.1, hsig.trans hProc1.2.2.2.2.2.2⟩⟩

private theorem post_brk_grow_state_fine {s0 s1 : State} {m' : Memory} {phys' : Nat} {fn off pc' newBrk : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((((s1.setBrk newBrk).setMem m').setPhysMemAvail phys').writeReg64 .x0 newBrk).setPC (fn + off + 4#64)
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = newBrk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = newBrk ∧ s2.mem = m' := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state_fine s2 pc' newBrk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem post_brk_fail_state_fine {s0 s1 : State} {fn off pc' : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((s1.writeReg64 .x0 s1.brk).setPC (fn + off + 4#64))
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = s1.brk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk ∧ s2.mem = s1.mem := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state_fine s2 pc' s1.brk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem post_brk_query_state_fine {s0 s1 : State} {fn off pc' : BitVec 64}
    (hPcEq : fn + off + 4#64 = pc') (hRun1 : s1.status = .Running) (hSp1 : s1.sp = s0.sp - 80#64) (hCs1 : Cs25Preserved s0 s1) (hProc1 : MallocngProcPreserved s0 s1) :
    let s2 := ((s1.writeReg64 .x0 s1.brk).setPC (fn + off + 4#64))
    s2.pc = pc' ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧ s2.readReg64 .x0 = s1.brk ∧
    (∀ n : BitVec 5, n ≠ 0#5 → n ≠ 31#5 → s2.readReg64 (.gpr n) = s1.readReg64 (.gpr n)) ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk ∧ s2.mem = s1.mem := by
  intro s2; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := post_brk_state_fine s2 pc' s1.brk hRun1 hSp1 hCs1 hProc1 ⟨hPcEq, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, rfl⟩

private theorem appendMetaArea_map_pair_fine {mas mas' : List MetaAreaDesc} {ap : BitVec 64}
    (hMa' : mas' = appendMetaArea mas ap) :
    mas'.map (fun ma => (ma.base, 4096)) = mas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by
  calc mas'.map (fun ma => (ma.base, 4096)) = ((appendMetaArea mas ap).map MetaAreaDesc.base).map (fun b => (b, 4096)) := by rw [hMa', List.map_map]; rfl
    _ = mas.map (fun ma => (ma.base, 4096)) ++ [(ap, 4096)] := by rw [(appendMetaArea_props mas ap).1, List.map_append, List.map_map]; rfl

private theorem noOrphanMappings_slowPathA_fine {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st' : MallocngSt} {m0 m2 : Memory}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st) (hCntNe : st.ctx.availMetaAreaCount ≠ 0#64)
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas st.ctx.availMetaAreas) (hGp' : st'.guardPages = st.guardPages)
    (hAv' : st'.availMetaPages = (List.range (st.ctx.availMetaAreaCount - 1#64).toNat).map (fun i => (st.ctx.availMetaAreas + 4096#64) + BitVec.ofNat 64 (4096 * i)))
    (hGs' : st'.groups = st.groups) (hD02 : MallocngMappedDelta 0 0 m0 m2) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m2 := by
  let ap := st.ctx.availMetaAreas; let cnt' := st.ctx.availMetaAreaCount - 1#64
  have hCntPos : 0 < st.ctx.availMetaAreaCount.toNat := Nat.pos_of_ne_zero fun h0 => hCntNe (BitVec.eq_of_toNat_eq h0)
  have hCntEq : st.ctx.availMetaAreaCount.toNat = cnt'.toNat + 1 := by
    dsimp only [cnt']; rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; exact hCntPos), BitVec.toNat_ofNat]; omega
  have hAvEq : st.availMetaPages = ap :: st'.availMetaPages := by
    rw [hwf.guard_avail_wf.2.2.1, hCntEq, hAv', List.range_succ_eq_map, List.map_cons, Nat.mul_zero, BitVec.add_zero, List.map_map]
    exact congrArg (List.cons ap) (List.map_congr_left fun i _ => by dsimp only [Function.comp]; rw [Nat.mul_succ, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 (4096 * i)), ← BitVec.add_assoc])
  intro a hm2 hsrc; rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · rw [mapped_mono_of_mappedDelta_zero hD02 a hm2] at hm0f; cases hm0f
  · refine ⟨r, ?_, haR⟩; unfold dynamicRootRegions at hr ⊢
    rw [hAvEq, List.map_cons] at hr; rw [appendMetaArea_map_pair_fine hMa', hGp', hGs']
    rcases List.mem_append.mp hr with h123 | hRg
    · rcases List.mem_append.mp h123 with h12 | hAv
      · rcases List.mem_append.mp h12 with hMa | hGp
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hGp))
      · rcases List.mem_cons.mp hAv with rfl | hRest
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))))
        · exact List.mem_append_left _ (List.mem_append_right _ hRest)
    · exact List.mem_append_right _ hRg

private theorem noOrphanMappings_slowPathB2_fine {st st' : MallocngSt} {ap : BitVec 64} {m0 m1 m2 m3 : Memory}
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas ap) (hGp' : st'.guardPages = st.guardPages)
    (hAv' : st'.availMetaPages = st.availMetaPages) (hGs' : st'.groups = st.groups)
    (hD01 : MallocngMappedDelta 0 0 m0 m1) (hMem2 : m2 = m1.mapZero ap 4096) (hD23 : MallocngMappedDelta 0 0 m2 m3) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m3 := by
  intro a hm3 hsrc; rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · have hm2 := mapped_mono_of_mappedDelta_zero hD23 a hm3
    rw [hMem2, Memory.perm_mapZero] at hm2; split at hm2
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      unfold MallocngInIntervals dynamicRootRegions; rw [appendMetaArea_map_pair_fine hMa']
      exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))), hc.1⟩
    · rw [mapped_mono_of_mappedDelta_zero hD01 a hm2] at hm0f; cases hm0f
  · refine ⟨r, ?_, haR⟩; unfold dynamicRootRegions at hr ⊢; rw [appendMetaArea_map_pair_fine hMa', hGp', hAv', hGs']
    rcases List.mem_append.mp hr with h123 | hRg
    · rcases List.mem_append.mp h123 with h12 | hAv
      · rcases List.mem_append.mp h12 with hMa | hGp
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hGp))
      · exact List.mem_append_left _ (List.mem_append_right _ hAv)
    · exact List.mem_append_right _ hRg

private theorem noOrphanMappings_slowPathB1_fine {st st' : MallocngSt} {brkStart : BitVec 64} {m0 m3 m4 m7 : Memory}
    (hMa0 : st.metaAreas = []) (hGp0 : st.guardPages = []) (hAv0 : st.availMetaPages = []) (hGs0 : st.groups = [])
    (hBsFit8 : brkStart.toNat + 8192 ≤ 2 ^ 48)
    (hMa' : st'.metaAreas = [{ base := brkStart + 4096#64, next := 0#64 }]) (hGp' : st'.guardPages = [brkStart])
    (hD03 : MallocngMappedDelta 0 0 m0 m3) (hMem4 : m4 = m3.mapZero brkStart 8192) (hD47 : MallocngMappedDelta 0 0 m4 m7) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m7 := by
  let ap := brkStart + 4096#64
  have hApNat : ap.toNat = brkStart.toNat + 4096 := by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  intro a hm7 hsrc; rcases hsrc with hm0f | ⟨r, hr, _⟩
  · have hm4 := mapped_mono_of_mappedDelta_zero hD47 a hm7
    rw [hMem4, Memory.perm_mapZero] at hm4; split at hm4
    · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have haN := (inRegion_toNat (by omega)).mp hc.1
      unfold MallocngInIntervals dynamicRootRegions; rw [hMa', hGp']; dsimp only [List.map]
      by_cases hLt : a.toNat < brkStart.toNat + 4096
      · exact ⟨(brkStart, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _))),
          (inRegion_toNat (b := brkStart) (n := 4096) (by omega)).mpr ⟨haN.1, hLt⟩⟩
      · exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))),
          (inRegion_toNat (b := ap) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩⟩
    · rw [mapped_mono_of_mappedDelta_zero hD03 a hm4] at hm0f; cases hm0f
  · unfold dynamicRootRegions at hr; simp [hMa0, hGp0, hAv0, hGs0] at hr

/-! ## 2. Shared Exit Segments (`sepWP_epilogue_278_fine`, `sepWP_epilogue_26c_fine`, `sepWP_activate_2a0_fine`, `sepWP_mprotect_224_fine`) -/

private theorem sepWP_epilogue_278_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st st' : MallocngSt} {m w0 w1 : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : AmfHasWords116 mallocngFaultSvcAmf)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% amfWords - 16#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = m) (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hFine : FineSplitInv bL bP st)
    (hMaStep1 : st'.metaAreas.length ≤ st.metaAreas.length + 1)
    (hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMaBound : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ w0) ∗ ((m + 8#64) ↦₆₄ w1) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hSubAddSp : s0.sp - 80#64 + 80#64 = s0.sp := BitVec.sub_add_cancel s0.sp 80#64
  refine SepWP.mono (sepWP_lift_faultSvcAmf_cl
    (sepPost (fun sf => MallocngProcPreserved s0 sf ∧ sf.brk = s.brk ∧ sf.readReg64 .x0 = m ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_
  · unfold StackFrameOpen SavedRegs0
    simp only [BitVec.reduceSub] at hPc
    wp_sym_steps; simp only [hSubAddSp] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc
    obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21
    wp_done
  · intro sf P_f _ _ ⟨_, hD2, _, ⟨hProcF, hBrkF, hx0F, hSpF, hCsF⟩, hEnt⟩
    refine ⟨Entails.trans hEnt ?_, hSpF, hCsF⟩
    refine Entails.sepExists_right st' (Entails.sepExists_right m ?_)
    have hNoOrphF : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem :=
      noOrphanMappings_of_mappedDelta_zero hNoOrph hD2
    have hDeltaF : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sf.mem :=
      MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD2)
    have ⟨hActL, hUseL, hUnmapL, hBncL, hPadEq, _⟩ := hWf'.ctx_lens
    have hCtxEq := (ctx_toBytes_eq_cells maddrs.ctx st'.ctx hActL hUseL hUnmapL hBncL (by rw [hPadEq]; rfl)).symm
    have hZ40 := (zero40_eq_cells m).symm
    have hWfF : MallocngWFInflight (inflight + 1) maddrs.base brkStart sf.brk liveCost peakCost st' := hBrkF ▸ hWf'
    have hCntEq : totalLiveCount st' = totalLiveCount st := by unfold totalLiveCount; rw [hPres.2.1]
    have hFine' : FineSplitInv bL bP st' := FineSplitInv.of_eq hFine hMaFine hPres.2.1
    refine Entails.pure_right ⟨hProcF, hx0F, hmProps.1, hmProps.2.1, hmProps.2.2.1, hmProps.2.2.2.1, hmProps.2.2.2.2,
      hPres.1, hPres.2.1, hPres.2.2.1, hPres.2.2.2.1, hCntEq, hMaStep1, hMaBound, hFine', hPres.2.2.2.2.1, hPres.2.2.2.2.2.1,
      hPres.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.2, hGrpPost, hNoOrphF, hDeltaF⟩ ?_
    refine Entails.trans (sepConj_mono_left (stack224_fold s0)) ?_
    unfold StaticFrameA MallocngCoreStInflightModeA MallocngRuntime
    rw [← hCtxEq, ← hZ40, pure_sepConj_of_true hWfF]
    sep_frame

private theorem sepWP_epilogue_26c_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st st' : MallocngSt} {m oldAv oldCnt : BitVec 64} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : AmfHasWords116 mallocngFaultSvcAmf)
    (_hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% amfWords - 28#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = m) (hx0 : s.readReg64 .x0 = st'.ctx.availMetaCount)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hAvEq : st'.ctx.availMeta = m + 40#64)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hFine : FineSplitInv bL bP st)
    (hMaStep1 : st'.metaAreas.length ≤ st.metaAreas.length + 1)
    (hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMaBound : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s.mem)
    (hmProps : m ≠ 0#64 ∧ 4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
          MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0) oom := by
  rw [zero40_eq_cells m]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords - 16#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% amfWords - 16#64) ∧
      s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧ s1.readReg64 .x19 = m ∧
      Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦ₛ List.replicate 24 0#8) ∗
          CtxCells maddrs.ctx st'.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · unfold CtxCells; dsimp only [ctxMiddleBytes]
    simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; simp only [← hAvEq] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc
    obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    exact SepWP.weaken_pre hEnt1 (sepWP_epilogue_278_fine hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
      hFine hMaStep1 hMaFine hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD1)
      (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1))
      hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

private theorem sepWP_activate_2a0_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (hWords : AmfHasWords116 mallocngFaultSvcAmf)
    (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_ret_off% amfWords + 24#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = ap) (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hFine : FineSplitInv bL bP st)
    (hMaStep1 : st'.metaAreas.length ≤ st.metaAreas.length + 1)
    (hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMaBound : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₛ List.replicate 4096 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
          MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0) oom := by
  have hSpA : (s0.sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned] using hSp0
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 hSpA
  have hCntSub : st'.ctx.availMetaAreaCount + 1#64 - 1#64 = st'.ctx.availMetaAreaCount := BitVec.add_sub_cancel _ _
  have hAv64 : (ap + 24#64) + 40#64 = ap + 64#64 := by bv_arith
  rw [zeroPage_eq_metaArea_cells ap]
  refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords - 28#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + (words_ret_off% amfWords - 28#64) ∧
      s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧ s1.readReg64 .x19 = ap + 24#64 ∧
      s1.readReg64 .x0 = st'.ctx.availMetaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
      Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ((ap + 24#64) ↦ₛ List.replicate 40 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt } ∗
          MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
  · rw [← hApBm, metaHdrBytes_eq_cells]
    unfold StackFrameSlow SavedRegs21 CtxCells; dsimp only [ctxMiddleBytes]
    conv => arg 2; simp only [BitVec.reduceSub]
    cases hMaEq : st.metaAreas with
    | nil =>
      obtain ⟨hTl0, hHdAp⟩ := hCtxEqs.2.2.2.2.1 hMaEq
      rw [hNilBv hMaEq, hTl0]; wp_sym_steps
      simp only [hCntSub, ← hHdAp, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
      wp_done
    | cons hd tl =>
      have hne : st.metaAreas ≠ [] := by simp [hMaEq]
      obtain ⟨hTlEq, hHdEq, hTlBeq⟩ := hCtxEqs.2.2.2.2.2 hne
      obtain ⟨hExT, hAbsT⟩ := hTailBm hne
      rw [hExT, ← hAbsT, metaHdrBytes_eq_cells, metaHdrBytes_eq_cells, hTlEq, hHdEq]
      rw [hTlEq] at hTlBeq; simp only [hMaEq] at hTlBeq ⊢
      wp_sym_steps; simp only [hCntSub, ← hCtxEqs.2.1] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
      wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hx0_1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    have hEnt2 := Entails.trans hEnt1 (sepConj_mono_left (stackSlow_to_open s0))
    exact SepWP.weaken_pre hEnt2 (sepWP_epilogue_26c_fine hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0
      hx19_1 hx0_1 hx20_1 (hCtxEqs.1.trans hAv64.symm) hCs1 hProc1
      hFine hMaStep1 hMaFine hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD1)
      (MallocngMappedDelta.mono (by decide) (by omega) (MallocngMappedDelta.trans hDelta hD1))
      hmProps (hBrk1 ▸ hWf') hPres hGrpPost)

private theorem sepWP_mprotect_224_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st st' : MallocngSt} {ap oldAv oldCnt oldHd oldTl oldAreas : BitVec 64}
    {bv0 bv1 : BitVec 64 → BitVec 8} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : AmfHasWords116 mallocngFaultSvcAmf)
    (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (reloc_call_off% amfRelocs "mprotect" - 12#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx21 : s.readReg64 .x21 = ap) (hx24 : s.readReg64 .x24 = 4096#64)
    (hApAlign : 4096 ∣ ap.toNat) (hApFit : ap.toNat + 4096 ≤ 2 ^ 48)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hFine : FineSplitInv bL bP st)
    (hMaStep1 : st'.metaAreas.length ≤ st.metaAreas.length + 1)
    (hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMaBound : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hNoOrph : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s.mem)
    (hDelta : MallocngMappedDelta 1 (FineMetaStep maxMeta - 4096) s0.mem s.mem)
    (hCtxEqs : st'.ctx.availMeta = ap + 64#64 ∧ st'.ctx.availMetaCount = 100#64 ∧
      st'.ctx.metaAreaTail = ap ∧ st'.ctx.availMetaAreas = ap + 4096#64 ∧
      (st.metaAreas = [] → oldTl = 0#64 ∧ st'.ctx.metaAreaHead = ap) ∧
      (∀ hne : st.metaAreas ≠ [], oldTl = (st.metaAreas.getLast hne).base ∧ oldHd = st'.ctx.metaAreaHead ∧ (oldTl == 0#64) = false))
    (hTailBm : ∀ hne : st.metaAreas ≠ [], let tb := (st.metaAreas.getLast hne).base
      ByteMap st'.masterDom (OwnedRwByte st) bv0 = ((tb ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) ∧
      ((tb ↦ₛ metaHdrBytes st'.ctx.secret ap) ∗ ByteMap st'.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion tb 24 a) bv0) = ByteMap st'.masterDom (OwnedRwByte st) bv1)
    (hNilBv : st.metaAreas = [] → bv1 = bv0)
    (hApBm : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) bv1) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal)
    (hmProps : (ap + 24#64) ≠ 0#64 ∧ 4096 ≤ (ap + 24#64).toNat ∧ (ap + 24#64).toNat % 8 = 0 ∧ (ap + 24#64).toNat + 40 ≤ 2 ^ 48 ∧ (ap + 24#64) ∉ st.reservedMetas)
    (hWf' : MallocngWFInflight (inflight + 1) maddrs.base brkStart s.brk liveCost peakCost st')
    (hPres : st'.reservedMetas = (ap + 24#64) :: st.reservedMetas ∧ st'.groups = st.groups ∧ st'.activeLists = st.activeLists ∧
      st'.liveMap = st.liveMap ∧ st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
      st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq)
    (hGrpPost : ∀ g ∈ st.groups, ∀ a : BitVec 64, (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₙ List.replicate 4096 0#8) ∗
          CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
          MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
          MappedSet st'.masterDom (OwnedMappedByte st'))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  let P_rest := StaticFrameA γ maddrs st'.liveMap ∗
    CtxCells maddrs.ctx { st'.ctx with availMeta := oldAv, availMetaCount := oldCnt, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := oldHd, metaAreaTail := oldTl, availMetaAreas := oldAreas } ∗
    MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
    ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
    MappedSet st'.masterDom (OwnedMappedByte st')
  let retPc := mbase 7 + (reloc_call_off% amfRelocs "mprotect" + 4#64)
  refine SepWP.cut (mid := mbase 17)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 17 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retPc ∧ s1.readReg64 .x0 = ap ∧ s1.readReg64 .x1 = 4096#64 ∧ s1.readReg32 .x2 = 3#32 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x21 = ap ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((ap ↦ₙ List.replicate 4096 0#8) ∗ P_rest))))) hcl ?_) ?_)
  · dsimp only [P_rest, retPc] at hPc ⊢
    simp only [BitVec.reduceSub] at hPc; wp_sym_steps
    simp only [show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25
    wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx20_1, hx21_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    unfold StackFrameSlow; rw [stack64_split_48 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    have hx1Nat : (s1.readReg64 .x1).toNat = 4096 := by rw [hx1_1]; rfl
    refine call_withCL_frame_auto (x := ())
      (placed_mprotectRwWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp ap errnoVal (List.replicate 4096 0#8) 4096 List.length_replicate (by decide) (by decide) hApAlign hApFit (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
      (h_oom := fun R' sf _ hSatOom => by
        have hDrop := Satisfies.drop_mid hSatOom
        rw [satisfies_pure_sepConj] at hDrop ⊢
        obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMp, hPhysLt⟩ := hDrop.1
        exact ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
          (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta hD1) hDMp)
          (by decide) (by unfold FineMetaStep; omega)
          fun _ => ⟨4096, by decide, by decide, by unfold FineMetaStep; omega, Or.inr hPhysLt⟩, hDrop.2⟩) ?_
    intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
    dsimp only; rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hw0_2, hDCall⟩
    refine SepWP.weaken_pre (Entails.trans
      (Q := (memRegion (s0.sp - 80#64 - 64#64) 16 ∗ stackFrame s1 48) ∗
        (memRegion (s0.sp - 224#64) 80 ∗ SavedRegs0 s0 ∗ SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2 ∗
          (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest))))
      (R := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))
      (by unfold SavedRegs0 SavedRegs21; dsimp only [P_rest]; sep_frame)
      (by rw [← stack64_split_48 hSp1]; unfold StackFrameSlow; sep_frame)) ?_
    refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords + 24#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
        s3.pc = mbase 7 + (words_ret_off% amfWords + 24#64) ∧
        s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
        s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = ap ∧
        Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
        (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest)))) hcl2 ?_) ?_)
    · dsimp only [retPc] at hPc2
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = ap := hCsCall.2.2.1.trans hx21_1
      have hCs2 : Cs25Preserved s0 s2 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs1.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs1.2.1,
        hCsCall.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs1.2.2.2.2⟩
      have hProc2 : MallocngProcPreserved s0 s2 := procPreserved_trans hProc1 hProcCall
      have hw0Cond : (BitVec.zeroExtend 64 (BitVec.truncate 32 (s2.readReg64 (Reg.gpr 0#5))) == 0#64) = true := by
        change (BitVec.zeroExtend 64 (s2.readReg32 .x0) == 0#64) = true; rw [hw0_2]; rfl
      dsimp only [P_rest]; conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
      rw [← hBrk1, ← hBrk2]; wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      have hD0_s_s3 : MallocngMappedDelta 0 0 s.mem s3.mem :=
        MallocngMappedDelta.mono (by decide) (by decide)
          (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD1 hDCall) hD3)
      have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s3.mem := by
        refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans hDelta hD0_s_s3)
        all_goals omega
      exact SepWP.weaken_pre (Entails.trans hEnt3 (by dsimp only [P_rest]; sep_frame))
        (sepWP_activate_2a0_fine hWords hRange hcl3 hPc3 hRun3 hSp3 hSp0
          hx20_3 hx21_3 hCs3 hProc3 hFine hMaStep1 hMaFine hMaBound (noOrphanMappings_of_mappedDelta_zero hNoOrph hD0_s_s3)
          hDTot hCtxEqs hTailBm hNilBv hApBm hmProps (hBrk3 ▸ hWf') hPres hGrpPost)

/-! ## 3. Fast Path 1 (`sepWP_fastPath1_028_fine`) and Slow Path C (`sepWP_slowPathC_144_fine`) -/

private theorem sepWP_fastPath1_028_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st : MallocngSt} {fm0 : FreeMetaDesc} {rest : List FreeMetaDesc} {errnoVal : BitVec 32} {s0 s : State} {oom : State → SepProp}
    (_hWords0 : AmfHasWords0 mallocngFaultSvcAmf)
    (hWords : AmfHasWords116 mallocngFaultSvcAmf)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hPc : s.pc = mbase 7 + (words_insn_off% amfWords "cbz" 0 + 16#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hx1 : s.readReg64 .x1 = maddrs.ctx) (hx19 : s.readReg64 .x19 = fm0.ptr)
    (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hFine : FineSplitInv bL bP st)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (hFmEq : st.freeMetas = fm0 :: rest) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0) oom := by
  let R_inv := StackFrameOpen s0 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
    ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)
  let epOff := words_ret_off% amfWords - 16#64
  rcases rest with _ | ⟨fm1, _ | ⟨fm2, tl⟩⟩
  · obtain ⟨hLinks, hmProps, hWf', hGrpPost, hRwEx, hPnEq, hMpEq⟩ := fastPath1_singleton_trans hWf hFmEq
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := 0#64 }, freeMetas := [], reservedMetas := fm0.ptr :: st.reservedMetas }
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, hLinks.2.1, hLinks.2.2]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fm0.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm0.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ R_inv)
      (by dsimp only [R_inv]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm0.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm0.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fm0.ptr) (w1 := fm0.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hFine (Nat.le_succ _) hFine.meta_le (Nat.le_max_left _ _) (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame
  · obtain ⟨hLinks, hmProps, _, hWf', hGrpPost, hRwEx, hRwAbs, hPnEq, hMpEq⟩ := fastPath1_pair_trans hWf hFmEq
    let fm1' : FreeMetaDesc := { ptr := fm1.ptr, prev := fm1.ptr, next := fm1.ptr }
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := [fm1'], reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := writeBytesToMap st.byteVal fm1.ptr fm1'.toBytes }
    let R_mid := ByteMap st.masterDom (fun a => (OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    have hSubNe : (fm0.ptr - fm1.ptr == 0#64) = false := beq_false_of_ne (fun h => hLinks.2.2.2 (by bv_omega))
    have hBeqNe : (fm0.ptr == fm1.ptr) = false := beq_false_of_ne hLinks.2.2.2
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, freeMeta_toBytes_eq_cells fm1, hLinks.2.1, hLinks.2.2.1]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fm1.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fm1.ptr ↦₆₄ fm1.prev) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ R_mid ∗ R_inv)
      (by dsimp only [R_inv, R_mid]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fm1.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      have hPack1 : ((fm1.ptr ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fm1.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hFine (Nat.le_succ _) hFine.meta_le (Nat.le_max_left _ _) (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      rw [hPack1, ← sepConj_assoc (fm1.ptr ↦ₛ fm1'.toBytes), hRwAbs]; dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame
  · let mid := (fm2 :: tl).dropLast; let fmLast := (fm2 :: tl).getLast nofun
    have hFmEq3 : st.freeMetas = fm0 :: fm1 :: (mid ++ [fmLast]) := by rw [hFmEq]; exact congrArg (fm0 :: fm1 :: ·) (List.dropLast_concat_getLast (l := fm2 :: tl) nofun).symm
    obtain ⟨hLinks, hmProps, _, _, hWf', hGrpPost, hRwEx, hRwAbs, hPnEq, hMpEq⟩ := fastPath1_ge3_trans hWf hFmEq3
    let fm1' : FreeMetaDesc := { fm1 with prev := fmLast.ptr }; let fmLast' : FreeMetaDesc := { fmLast with next := fm1.ptr }
    let st' : MallocngSt := { st with ctx := { st.ctx with freeMetaHead := fm1.ptr }, freeMetas := fm1' :: (mid ++ [fmLast']), reservedMetas := fm0.ptr :: st.reservedMetas, byteVal := writeBytesToMap (writeBytesToMap st.byteVal fmLast.ptr fmLast'.toBytes) fm1.ptr fm1'.toBytes }
    let R_mid := ByteMap st.masterDom (fun a => ((OwnedRwByte st a ∧ ¬ InRegion fm0.ptr 40 a) ∧ ¬ InRegion fmLast.ptr 40 a) ∧ ¬ InRegion fm1.ptr 40 a) st.byteVal
    have hSubNe : (fm0.ptr - fm1.ptr == 0#64) = false := beq_false_of_ne (fun h => hLinks.2.2.2 (by bv_omega))
    have hBeqNe : (fm0.ptr == fm1.ptr) = false := beq_false_of_ne hLinks.2.2.2
    rw [hRwEx, freeMeta_toBytes_eq_cells fm0, freeMeta_toBytes_eq_cells fmLast, freeMeta_toBytes_eq_cells fm1, hLinks.2.1, hLinks.2.2.1]
    refine SepWP.weaken_pre (P' := CtxCells maddrs.ctx st.ctx ∗ (fm0.ptr ↦₆₄ fmLast.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fmLast.next) ∗
        ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ (fm1.ptr ↦₆₄ fm1.prev) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ R_mid ∗ R_inv)
      (by dsimp only [R_inv, R_mid]; sep_frame) ?_
    refine SepWP.cut_at_off (mbase 7) epOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 7 + epOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (CtxCells maddrs.ctx st'.ctx ∗ (fm0.ptr ↦₆₄ fmLast.ptr) ∗ ((fm0.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fm0.ptr + 16#64) ↦ₛ List.replicate 24 0#8) ∗ ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗
        ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ (((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗
        ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) ∗ R_mid) ∗ R_inv)) hcl ?_) ?_)
    · dsimp only [epOff, st', CtxCells, ctxMiddleBytes]; rw [hLinks.1]; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      have hD0Tot : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
      have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by omega) hD0Tot
      have hPack1 : ((fm1.ptr ↦₆₄ fmLast.ptr) ∗ ((fm1.ptr + 8#64) ↦₆₄ fm1.next) ∗ ((fm1.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fm1.ptr ↦ₛ fm1'.toBytes) := (freeMeta_toBytes_eq_cells fm1').symm
      have hPackL : ((fmLast.ptr ↦₆₄ fmLast.prev) ∗ ((fmLast.ptr + 8#64) ↦₆₄ fm1.ptr) ∗ ((fmLast.ptr + 16#64) ↦ₛ List.replicate 24 0#8)) = (fmLast.ptr ↦ₛ fmLast'.toBytes) := (freeMeta_toBytes_eq_cells fmLast').symm
      refine SepWP.weaken_pre (Entails.trans hEnt1 ?_)
        (sepWP_epilogue_278_fine (st' := st') (w0 := fmLast.ptr) (w1 := fm1.ptr) (errnoVal := errnoVal) hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hCs1 hProc1
          hFine (Nat.le_succ _) hFine.meta_le (Nat.le_max_left _ _) (noOrphanMappings_of_same_ivs_delta_zero rfl hD0Tot) hDTot hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      rw [hPack1, hPackL, ← sepConj_assoc (fm1.ptr ↦ₛ fm1'.toBytes), hRwAbs]; dsimp only [R_inv, st']; rw [← hPnEq, ← hMpEq]; sep_frame

local macro "wp_norm_mbase_pc_fine" : tactic =>
  `(tactic| conv in (mbase _ + _ + _) => rw [BitVec.add_assoc]; simp only [BitVec.reduceAdd])

private abbrev MmapNewInRegion_fine (mb : BitVec 64) (len : Nat) (m0 mf : Memory) : Prop :=
  ∀ a : BitVec 64, (mf.perm a).mapped = true → (m0.perm a).mapped = true ∨ InRegion mb len a

private theorem perm_mapZeroProtNone_inRegion_fine {m0 m3 mf : Memory} {mb : BitVec 64} {len : Nat}
    (hm3 : m3.perm = m0.perm) (hmf : mf.perm = ((m3.mapZero mb len).setPermNonFrozen mb len Perm.protNone).perm) :
    MmapNewInRegion_fine mb len m0 mf := by
  intro a ha
  have ha' : ((m3.mapZero mb len).perm a).mapped = true := by
    rw [hmf, Memory.perm_setPermNonFrozen] at ha
    split at ha
    · rename_i hc; simp only [Bool.and_eq_true] at hc; exact hc.1.2
    · exact ha
  rw [Memory.perm_mapZero] at ha'
  split at ha'
  · rename_i hc2; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2; exact Or.inr hc2.1
  · exact Or.inl (hm3 ▸ ha')

set_option maxHeartbeats 400000 in
private theorem placed_mmapProtNone_inRegion_fine_ok [MallocngMultiPlacement] {P : Program}
    (tp : BitVec 64) (errnoVal : BitVec 32) (rawLen : Nat) (hpos : 0 < rawLen) (hmax : rawLen ≤ 2 ^ 62)
    (hext : ∀ pc, P.externAt? pc = none := by intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    let len := pageAlignUp rawLen
    subroutine_ok P (mbase 16) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.readReg64 .x0 = 0#64 ∧ (s0.readReg64 .x1).toNat = rawLen ∧
         s0.readReg32 .x2 = 0#32 ∧ s0.readReg32 .x3 = 0x22#32 ∧ s0.readReg32 .x4 = BitVec.allOnes 32 ∧ s0.readReg64 .x5 = 0#64⌝ ∗
        stackFrame s0 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal)
      post := fun _ s0 sf => ∃∗ mb : BitVec 64,
        ⌜MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ sf.readReg64 .x0 = mb ∧ mb ≠ 0#64 ∧ mb ≠ BitVec.allOnes 64 ∧
         4096 ∣ mb.toNat ∧ mb.toNat + len ≤ 2 ^ 48 ∧ MallocngMappedDelta 1 len s0.mem sf.mem ∧ MmapNewInRegion_fine mb len s0.mem sf.mem⌝ ∗
        stackFrame s0 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len
      onOom := fun _ s0 sf =>
        ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.sigActions = s0.sigActions ∧
         sf.mem.perm = s0.mem.perm ∧ MallocngMappedDelta 0 0 s0.mem sf.mem ∧ (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)⌝
    }) := by
  intro len; refine subroutine_ok_block_to_block (j := 16) (by decide) ?_ hext hsvc; clear hext hsvc P
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨_hw, _hrange⟩ := hasWords_blk_of_checkSegment (i := 16) (by decide) (ws := mmapFnWords) (R := VerifiedLibraries.mallocng_blk16_mmap.relocs) (by decide +kernel)
  have hsys := placed_syscallRet_perm_ok (P := mallocngBlockProg mmpl 16 msvc) (by intro pc; simp) rfl
  simp only [stackFrame, show (64 : Nat) = 8 * 8 by rfl, memRegion_cells _ 8 (by decide)]; cells_unfold
  wp_init x s0; subst m0 tp
  wp_stp64_cl m1 hm1 hcl0 hcl1; wp_step; wp_step; wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2; wp_step; wp_step; wp_step; wp_step
  wp_if hhi
  · exfalso; rw [BitVec.ult_iff_toNat_lt, BitVec.toNat_ofNat] at hhi; omega
  wp_stp64_cl m3 hm3 hcl2 hcl3; wp_steps
  refine step_svc_mmap_protNone_rawLen (rawLen := rawLen) MallocngMultiPlacement.svcValid
    (by wp_norm_lhs) (by simp [arm64_norm, *]) (by wp_close_fetch_cl) (by simp [arm64_norm])
    (by simp only [arm64_norm]) (by simp only [arm64_norm])
    (by simp [arm64_norm, *]) (by simpa [arm64_norm] using ‹(s0.readReg64 (Reg.gpr 1#5)).toNat = rawLen›) hpos ?_ ?_
  · intro mb hmb_ne0 hmb_al hmb_fit
    clear hcl0 hcl1 hcl2; wp_norm_mbase_pc_fine; wp_step; wp_step; wp_step
    wp_if hccmn
    · wp_step; wp_step; wp_step; wp_step
      have hcl4 := hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero_protNone _ mb len)
      clear hcl3; wp_call hsys; clear hcl4
      have hmble : mb.toNat ≤ 2 ^ 64 - 4096 := by omega
      have _hmb_ne1 : mb ≠ BitVec.allOnes 64 := fun he => by
        rw [he] at hmb_fit; have : (BitVec.allOnes 64).toNat = 2 ^ 64 - 1 := (by decide); omega
      simp only [hmble, ↓reduceIte, MallocngProcPreserved] at *
      have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
      have _hdelta : MallocngMappedDelta 1 len s0.mem _ := mappedDelta_one_step hperm3 (mappedDelta_mapZeroProtNone _ mb len) ‹_›
      have _hinReg : MmapNewInRegion_fine mb len s0.mem _ := perm_mapZeroProtNone_inRegion_fine hperm3 ‹_›
      wp_done
    · exfalso; have ht := congrArg BitVec.toNat hccmn; simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht; omega
  · intro hno R' hmR
    have hperm3 : m3.perm = s0.mem.perm := Eq.trans hm3 (Eq.trans hm2 hm1)
    exact Satisfies.pure_intro ⟨rfl, rfl, rfl, hperm3, _root_.VerifiedLibraries.Mallocng.Proofs.mappedDelta_of_perm_eq hperm3, hno⟩ (Satisfies.drop_left hmR)

private theorem noOrphanMappings_slowPathC_fine {st st' : MallocngSt} {m : Nat} {mb : BitVec 64} {m0 m1 m2 m3 : Memory}
    (hAv0 : st.availMetaPages = []) (_hPowGe2 : 2 ≤ 2 ^ (m + 1)) (hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36)
    (hMbFit : mb.toNat + 4096 * 2 ^ (m + 1) ≤ 2 ^ 48)
    (hMa' : st'.metaAreas = appendMetaArea st.metaAreas (mb + 4096#64)) (hGp' : st'.guardPages = st.guardPages ++ [mb])
    (hAv' : st'.availMetaPages = (List.range (2 ^ (m + 1) - 2)).map (fun i => ((mb + 4096#64) + 4096#64) + BitVec.ofNat 64 (4096 * i)))
    (hGs' : st'.groups = st.groups) (hD01 : MallocngMappedDelta 0 0 m0 m1)
    (hInReg : MmapNewInRegion_fine mb (4096 * 2 ^ (m + 1)) m1 m2) (hD23 : MallocngMappedDelta 0 0 m2 m3) :
    MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') m0 m3 := by
  let ap := mb + 4096#64
  have hMapMaPair := appendMetaArea_map_pair_fine hMa'
  have hSubDyn : ∀ r ∈ dynamicRootRegions st, r ∈ dynamicRootRegions st' := fun r hr => by
    unfold dynamicRootRegions at hr ⊢; rw [hAv0, List.map_nil, List.append_nil] at hr; rw [hMapMaPair, hGp', List.map_append, hGs']
    rcases List.mem_append.mp hr with h12 | hRg
    · rcases List.mem_append.mp h12 with hMa | hGp
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hMa)))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hGp)))
    · exact List.mem_append_right _ hRg
  intro a hm3 hsrc; rcases hsrc with hm0f | ⟨r, hr, haR⟩
  · have hm2 := mapped_mono_of_mappedDelta_zero hD23 a hm3
    rcases hInReg a hm2 with hm1 | haMb
    · rw [mapped_mono_of_mappedDelta_zero hD01 a hm1] at hm0f; cases hm0f
    · have hApNat : ap.toNat = mb.toNat + 4096 := by dsimp only [ap]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hAp4096Nat : (ap + 4096#64).toNat = mb.toNat + 8192 := by rw [BitVec.toNat_add, hApNat, BitVec.toNat_ofNat]; omega
      have haN := (inRegion_toNat (by omega)).mp haMb; let q := (a.toNat - mb.toNat) / 4096
      have hqLt : q < 2 ^ (m + 1) := by dsimp only [q]; omega
      unfold MallocngInIntervals dynamicRootRegions; rw [hMapMaPair, hGp', List.map_append]
      by_cases hq0 : q = 0
      · exact ⟨(mb, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ (List.Mem.head _)))),
          (inRegion_toNat (b := mb) (n := 4096) (by omega)).mpr ⟨by omega, by dsimp only [q] at hq0; omega⟩⟩
      · by_cases hq1 : q = 1
        · exact ⟨(ap, 4096), List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.Mem.head _)))),
            (inRegion_toNat (b := ap) (n := 4096) (by omega)).mpr ⟨by dsimp only [q] at hq1; omega, by dsimp only [q] at hq1; omega⟩⟩
        · let p := (ap + 4096#64) + BitVec.ofNat 64 (4096 * (q - 2))
          have hpMem : p ∈ st'.availMetaPages := by rw [hAv']; exact List.mem_map_of_mem (List.mem_range.mpr (by omega))
          have hpN : p.toNat = mb.toNat + 4096 * q := by dsimp only [p]; rw [BitVec.toNat_add, hAp4096Nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
          exact ⟨(p, 4096), List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hpMem)), (inRegion_toNat (b := p) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩⟩
  · exact ⟨r, hSubDyn r hr, haR⟩

private theorem sepWP_slowPathC_144_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat} {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWords : AmfHasWords116 mallocngFaultSvcAmf) (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st) (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hPc : s.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 40#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st)
    (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hCnt0 : st.ctx.availMetaAreaCount = 0#64) (hBrkNeg1 : st.ctx.brk = -1#64) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  have hAv0 : st.availMetaPages = [] := by have h := hWf.guard_avail_wf.2.2.1; rw [hCnt0] at h; exact h
  obtain ⟨hmLe35, hLenGe, hLenLe48, hLenDvd, hLenBound⟩ :=
    metaAreas_mmap_bytes_le_fineMetaStep hWf hInflight hNoFree hNoBump hAv0 hMaStep
  let m := st.ctx.metaAllocShift.toNat; let len := 4096 * 2 ^ (m + 1)
  have hmDef : st.ctx.metaAllocShift.toNat = m := rfl; have hLenDef : 4096 * 2 ^ (m + 1) = len := rfl
  rw [hmDef] at hmLe35; rw [hmDef, hLenDef] at hLenGe hLenLe48 hLenDvd hLenBound
  have hPowGe2 : 2 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (n := 2) (i := 1) (by decide) (by omega)
  have hPowLe36 : 2 ^ (m + 1) ≤ 2 ^ 36 := Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
  let retMmap := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 + 4#64)
  let P_rest := StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  refine SepWP.cut (mid := mbase 16)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
      s1.pc = mbase 16 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
      s1.readReg64 Reg.lr = retMmap ∧ s1.readReg64 .x0 = 0#64 ∧ (s1.readReg64 .x1).toNat = len ∧
      s1.readReg32 .x2 = 0#32 ∧ s1.readReg32 .x3 = 0x22#32 ∧ s1.readReg32 .x4 = BitVec.allOnes 32 ∧ s1.readReg64 .x5 = 0#64 ∧
      s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x22 = BitVec.ofNat 64 (2 ^ (m + 1)) ∧
      s1.readReg64 .x23 = maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest))) hcl ?_) ?_)
  · dsimp only [P_rest, CtxCells, retMmap] at *
    simp only [BitVec.reduceSub] at hPc; wp_sym_steps
    have hx22Eq : (2#64 <<< (st.ctx.metaAllocShift.toNat % 64)) = BitVec.ofNat 64 (2 ^ (m + 1)) :=
      BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show st.ctx.metaAllocShift.toNat % 64 = m by omega, Nat.shiftLeft_eq, show 2 * 2 ^ m = 2 ^ (m + 1) by rw [Nat.pow_succ]; omega])
    have hx1Eq : (4096#64 * BitVec.ofNat 64 (2 ^ (m + 1))).toNat = len := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [len]; omega
    simp only [hx22Eq, hx1Eq, show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hLr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx20_1, hx22_1, hx23_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 ?_
    have hSt64 : ∀ {stx : State}, stx.sp = s0.sp - 80#64 → stackAt (s0.sp - 80#64) 64 = stackFrame stx 64 :=
      fun h => by rw [stackAt_eq_stackFrameAt (s0.sp - 80#64) 64 (by decide), stackFrameAt_eq_memRegion (s0.sp - 80#64) 64 (by decide)]; unfold stackFrame; rw [h]
    unfold StackFrameSlow; rw [hSt64 hSp1]
    have hSpA1 : s1.spAligned = true := by rw [State.spAligned, hSp1]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
    have hTp1 : s1.tpidrEl0 = tp := hProc1.2.2.1.trans hTp0
    refine call_withCL_frame_auto (x := ())
      (placed_mmapProtNone_inRegion_fine_ok (P := mallocngBlockProg mmpl 7 msvc) tp errnoVal len (by omega) (by omega) (by intro pc; simp) rfl)
      hcl1 hPc1 hRun1 hSpA1 hLr1 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_ (by sep_frame) ?_
    · intro s2 hPc2 hRun2 hSp2 hCsCall hcl2
      apply SepWP.of_sepExists_left; intro mb
      rw [pageAlignUp_of_dvd hLenDvd, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
      apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk2, hx0_2, hMbNe0, hMbNeNeg1, hMbAlign, hMbFit, hDCall, hInRegCall⟩
      rw [← hSt64 hSp1]
      refine SepWP.with_sat fun ⟨R_sat, hmSat⟩ => ?_
      obtain ⟨l1, l2, l3, l4, l5, _⟩ := hWf.ctx_lens
      have l5Len : st.ctx.seqPad.length = 7 := by rw [l5]; rfl
      have hmBatch' : s2.mem ⊨ (mb ↦ₙ List.replicate len 0#8) ∗ memMapped mb len ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st) ∗
          (stackAt (s0.sp - 80#64) 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ memRegion (s0.sp - 224#64) 80 ∗
            SavedRegs0 s0 ∗ SavedRegs21 s0 ∗ cells (s0.sp - 16#64) 2 ∗ StaticFrameA γ maddrs st.liveMap ∗
            ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗ R_sat) :=
        Satisfies.of_entails hmSat (by unfold SavedRegs0 SavedRegs21; rw [← ctx_toBytes_eq_cells _ _ l1 l2 l3 l4 l5Len]; sep_frame)
      have hDisjRoot := disjoint_protNone_batch (A := maddrs) hWf hAv0 hMbAlign hLenGe (by simpa [hmDef, hLenDef] using hMbFit) hmBatch'
      obtain ⟨hmProps, hWf', hGrpPost, hPnEq, hTailBm, hRw0Dom, hApBm, hMpEq⟩ :=
        slowPathC_trans hWf hInflight h1 hNoFree hNoBump hCnt0 hBrkNeg1 mb hMbNe0 hMbAlign (by simpa [hmDef, hLenDef] using hMbFit) (by simpa [hmDef, hLenDef] using hDisjRoot)
      let ap := mb + 4096#64; let cnt' := BitVec.ofNat 64 (2 ^ (m + 1) - 2)
      let newAv := (List.range (2 ^ (m + 1) - 2)).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
      let bv0 := writeBytesToMap st.byteVal mb (List.replicate len 0#8)
      let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else bv0
      let st' : MallocngSt := { st with
        ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAllocShift := BitVec.ofNat 64 (m + 1), metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 },
        metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := st.mmapMetaAreas ++ [ap], guardPages := st.guardPages ++ [mb], mmapGuardPages := st.mmapGuardPages ++ [mb], availMetaPages := newAv, freeMetas := [],
        bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs mb len, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
      have hApNat : ap.toNat = mb.toNat + 4096 := by dsimp [ap]; omega
      have hApAlign : 4096 ∣ ap.toNat := by rw [hApNat]; exact Nat.dvd_add hMbAlign (Nat.dvd_refl 4096)
      have hApFit : ap.toNat + 4096 ≤ 2 ^ 48 := by omega
      have hPn' : ((mb ↦ₙ List.replicate len 0#8) ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) =
          ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) := hPnEq
      have hMp' : (memMapped mb len ∗ MappedSet st.masterDom (OwnedMappedByte st)) = MappedSet st'.masterDom (OwnedMappedByte st') := hMpEq
      refine SepWP.weaken_pre (Entails.trans
        (Q := ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) ∗
          (MappedSet st'.masterDom (OwnedMappedByte st') ∗ (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st) bv0)))))
        (R := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          (ap ↦ₙ List.replicate 4096 0#8) ∗ CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
          ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))
        (by rw [← hPn', ← hMp', hRw0Dom]; unfold StackFrameSlow SavedRegs0 SavedRegs21; dsimp only [P_rest, st']; sep_frame) (by sep_frame)) ?_
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "mprotect" - 12#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (reloc_call_off% amfRelocs "mprotect" - 12#64) ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
          s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = ap ∧ s3.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s.brk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₙ List.replicate 4096 0#8) ∗
            CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := ap } ∗
            MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl2 ?_) ?_)
      · dsimp only [retMmap] at hPc2
        have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_1
        have hx22_2 : s2.readReg64 .x22 = BitVec.ofNat 64 (2 ^ (m + 1)) := hCsCall.2.2.2.1.trans hx22_1
        have hx23_2 : s2.readReg64 .x23 = maddrs.ctx := hCsCall.2.2.2.2.1.trans hx23_1
        have hx24_2 : s2.readReg64 .x24 = 4096#64 := hCsCall.2.2.2.2.2.1.trans hx24_1
        have hCs2 : Cs25Preserved s0 s2 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs1.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs1.2.1,
          hCsCall.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs1.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs1.2.2.2.2⟩
        have hProc2 : MallocngProcPreserved s0 s2 := procPreserved_trans hProc1 hProcCall
        have hMbAdd1 : (mb + 1#64 == 0#64) = false := beq_false_of_ne fun hEq => hMbNeNeg1
          (BitVec.eq_of_toNat_eq (by have h := congrArg BitVec.toNat hEq; rw [BitVec.toNat_add] at h; simp at h ⊢; omega))
        have hApMask : ((mb + 4096#64) &&& 4095#64 == 0#64) = true := beq_iff_eq.mpr (and_4095_eq_zero_of_dvd hApAlign)
        have hCntAdd : (BitVec.ofNat 64 (2 ^ (m + 1)) - 1#64) * 1#64 = cnt' + 1#64 :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.mul_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; simp; omega), BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; dsimp [cnt']; rw [BitVec.toNat_ofNat]; omega)
        have hShiftAdd : st.ctx.metaAllocShift + 1#64 = BitVec.ofNat 64 (m + 1) :=
          BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, hmDef]; simp)
        dsimp only [CtxCells, ctxMiddleBytes, st']; conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hCntAdd, hShiftAdd, ap] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2
        rw [← hBrk1, ← hBrk2]; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        have hNoOrph3 : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s3.mem :=
          noOrphanMappings_slowPathC_fine hAv0 hPowGe2 hPowLe36 hMbFit rfl rfl rfl rfl hD01 hInRegCall hD3
        have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta - 4096) s0.mem s3.mem := by
          refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD01 hDCall) hD3)
          all_goals omega
        have hMaLen : st'.metaAreas.length = st.metaAreas.length + 1 := appendMetaArea_length st.metaAreas ap
        have hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP :=
          hMaLen ▸ FineSplitInv.metaAreas_succ_le hFine hWf hInflight hNoFree hNoBump
        exact SepWP.weaken_pre hEnt3 (sepWP_mprotect_224_fine hWords hRange hcl3
          hPc3 hRun3 hSp3 hSp0 hTp0 hx20_3 hx21_3 hx24_3 hApAlign hApFit hCs3 hProc3
          hFine (Nat.le_of_eq hMaLen) hMaFine
          (appendMetaArea_len_le_max ap hWf hInflight hNoFree hNoBump hCount) hNoOrph3 hDTot
          (metaAreas_ctx_eqs hWf rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
          (hBrk3 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · intro R' sf _ hSatOom
      have hDrop := Satisfies.drop_mid hSatOom
      rw [satisfies_pure_sepConj] at hDrop ⊢
      obtain ⟨hFsEq, hTrEq, hSigEq, _, hDMmap, hNoGap⟩ := hDrop.1
      exact ⟨MallocngPlacedOomCond.of_delta (hFsEq.trans hProc1.1) (hTrEq.trans hProc1.2.1)
        (hSigEq.trans hProc1.2.2.2.2.2.2) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hDMmap)
        (by omega) (by omega)
        fun hSan => ⟨len, by dsimp [PAGE_SIZE]; omega, Nat.mod_eq_zero_of_dvd hLenDvd, by omega, by rw [← pageAlignUp_of_dvd hLenDvd]; exact hNoGap hSan⟩, hDrop.2⟩

/-! ## 4. Slow Paths B2 / B1, Post-Init Dispatch, and `placed_allocMeta_fine_ok` -/

private theorem sepWP_slowPathB2_118_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat} {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWordsSvc : AmfHasWords116 msvc) (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st) (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hPc : s.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 84#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx)
    (hx21 : s.readReg64 .x21 = s.brk) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st)
    (h1 : st.ctx.initDone = 1#32) (hNoFree : st.freeMetas = []) (hNoBump : st.bumpMetas = [])
    (hCnt0 : st.ctx.availMetaAreaCount = 0#64) (hBrkNe : st.ctx.brk ≠ -1#64) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  have hWords : AmfHasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  let P_all := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
    (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
      MappedSet st.masterDom (OwnedMappedByte st)))
  let svcOff := reloc_call_off% amfRelocs "__mmap" 0 - 72#64
  refine SepWP.cut_at_off (mbase 7) svcOff (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
    s1.pc = mbase 7 + svcOff ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
    s1.readReg64 .x0 = s.brk + 4096#64 ∧ s1.readReg64 .x8 = 214#64 ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
    s1.readReg64 .x21 = s.brk ∧ s1.readReg64 .x22 = s.brk + 4096#64 ∧ s1.readReg64 .x24 = 4096#64 ∧
    Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_all) hcl ?_) ?_)
  · dsimp only [svcOff, P_all]; simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx8_1, hx20_1, hx21_1, hx22_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    refine SepWP.weaken_pre hEnt1 (SepWP.with_sat fun ⟨R_sat, hmSat⟩ => ?_)
    have ⟨hBrkGe, _, hBrkMod, _, hBrkFit0⟩ := (hBrk1 ▸ hWf).brk_bounds
    let newBrk := s1.brk + 4096#64
    have hNewNat : newBrk.toNat = s1.brk.toNat + 4096 := by dsimp only [newBrk]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have hLenEq : newBrk.toNat - s1.brk.toNat = 4096 := by omega
    have hx0_new : s1.readReg64 .x0 = newBrk := by dsimp only [newBrk]; rw [hBrk1]; exact hx0_1
    have hFetch : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff) = some (.system false 0#16) :=
      Program.fetch_of_hasWords_getElem_decode 44 3556769793#32 hWordsSvc (by dsimp only [svcOff]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
    refine SepWP.step_svc_brk_grow (newBrk := newBrk) hPc1 hRun1 hFetch hx0_new
      (fun h0 => by rw [h0] at hNewNat; simp at hNewNat) (by rw [hProc1.2.2.2.1, hBs0]; omega) (by omega)
      (Nat.dvd_of_mod_eq_zero hBrkMod) ⟨s1.brk.toNat / 4096 + 1, by omega⟩ (evalInst_svc0_execBrk_fine hx8_1) ?_ ?_ ?_
    · intro m' hFit2 hCanMap hm' hDBrk
      have hmDom : s1.mem ⊨ ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st) ∗
          (StackFrameSlow s0 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
            ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗ R_sat) :=
        Satisfies.of_entails hmSat (by dsimp only [P_all]; sep_frame)
      have hDisjRoot : ∀ r ∈ dynamicRootRegions st, DisjointRegions r.1 r.2 s1.brk 4096 :=
        disjoint_dynamicRootRegions_of_canMap (hBrk1 ▸ hWf) (hLenEq ▸ hCanMap) (Nat.dvd_of_mod_eq_zero hBrkMod) (by decide) (by omega) hmDom
      obtain ⟨_, hmProps, hWf', hGrpPost, hTailBm, hRw0Dom, hApBm, hPnEq, hMpEq⟩ :=
        slowPathB2_trans (hBrk1 ▸ hWf) hInflight h1 hNoFree hNoBump hBrkNe hFit2 hDisjRoot
      let bv0 := writeBytesToMap st.byteVal s1.brk (List.replicate 4096 0#8)
      let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap bv0 (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret s1.brk) else bv0
      let st' : MallocngSt := { st with
        ctx := { st.ctx with availMeta := s1.brk + 64#64, availMetaCount := 100#64, availMetaAreaCount := 0#64, metaAreaHead := (match st.metaAreas with | [] => s1.brk | hd :: _ => hd.base), metaAreaTail := s1.brk, availMetaAreas := s1.brk + 4096#64, brk := s1.brk + 4096#64 },
        metaAreas := appendMetaArea st.metaAreas s1.brk, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := s1.brk, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (s1.brk + 24#64) :: st.reservedMetas, masterDom := st.masterDom ++ rangeAddrs s1.brk 4096, byteVal := writeBytesToMap bv1 s1.brk (metaHdrBytes st.ctx.secret 0#64) }
      rw [hLenEq]
      have hGrowSt := post_brk_grow_state_fine (m' := m') (phys' := s1.physMemAvail - 4096) (newBrk := newBrk) (fn := mbase 7) (off := svcOff)
        (pc' := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 68#64)) (by dsimp only [svcOff]; bv_arith) hRun1 hSp1 hCs1 hProc1
      generalize (((((s1.setBrk newBrk).setMem m').setPhysMemAvail (s1.physMemAvail - 4096)).writeReg64 .x0 newBrk).setPC (mbase 7 + svcOff + 4#64)) = s2 at hGrowSt ⊢
      obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hGrowSt
      have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem :=
        hMem2 ▸ hm' ▸ hcl1.of_keepsFrozen (Memory.keepsFrozen_mapZero s1.mem s1.brk _)
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
      have hx21_2 : s2.readReg64 .x21 = s1.brk := (hGpr2 21#5 nofun nofun).trans (hx21_1.trans hBrk1.symm)
      have hx22_2 : s2.readReg64 .x22 = newBrk := (hGpr2 22#5 nofun nofun).trans (by dsimp only [newBrk]; rw [hBrk1]; exact hx22_1)
      have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
      refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords + 24#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (words_ret_off% amfWords + 24#64) ∧
          s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x21 = s1.brk ∧
          Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = newBrk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (s1.brk ↦ₛ List.replicate 4096 0#8) ∗
              CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
              MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
              ByteMap st'.masterDom (OwnedRwByte st) bv0 ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl2 ?_) ?_)
      · have hPnEq' : ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal = ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal := hPnEq
        have hMpEq' : MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := hMpEq
        have hMidB2 : ctxMiddleBytes { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } = ctxMiddleBytes st.ctx := rfl
        have hEqNew : (newBrk - newBrk == 0#64) = true := by simp
        dsimp only [P_all, CtxCells]; rw [hRw0Dom, ← hPnEq', ← hMpEq', hMidB2]; dsimp only [st']
        rw [show s1.brk + 4096#64 = newBrk from rfl]; simp only [BitVec.reduceSub] at hPc2
        conv => arg 2; simp only [BitVec.reduceAdd]
        wp_sym_steps; simp only [hEqNew, BitVec.reduceAdd] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx21_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        have hNoOrph3 : MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem s3.mem :=
          noOrphanMappings_slowPathB2_fine rfl rfl rfl rfl hD01 (by rw [hMem2, hm', hLenEq]) hD3
        have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s3.mem := by
          refine MallocngMappedDelta.mono ?_ ?_ (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD01 (hLenEq ▸ hDBrk)) (hMem2 ▸ hD3))
          · decide
          · unfold FineMetaStep; omega
        have hMaLen : st'.metaAreas.length = st.metaAreas.length + 1 := appendMetaArea_length st.metaAreas s1.brk
        have hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP :=
          hMaLen ▸ FineSplitInv.metaAreas_succ_le hFine (hBrk1 ▸ hWf) hInflight hNoFree hNoBump
        exact SepWP.weaken_pre hEnt3 (sepWP_activate_2a0_fine hWords hRange hcl3 hPc3 hRun3 hSp3 hSp0 hx20_3 hx21_3 hCs3 hProc3
          hFine (Nat.le_of_eq hMaLen) hMaFine
          (appendMetaArea_len_le_max s1.brk (hBrk1 ▸ hWf) hInflight hNoFree hNoBump hCount) hNoOrph3 hDTot
          (metaAreas_ctx_eqs (hBrk1 ▸ hWf) rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
          (hBrk3 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · obtain ⟨hWfFail, hRwFail, hPnFail, hMpFail⟩ := brk_fail_wf (hBrk1 ▸ hWf) h1
      let stFail : MallocngSt := { st with ctx := { st.ctx with brk := -1#64 } }
      have hFailSt := post_brk_fail_state_fine (fn := mbase 7) (off := svcOff)
        (pc' := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 68#64)) (by dsimp only [svcOff]; bv_arith) hRun1 hSp1 hCs1 hProc1
      generalize ((s1.writeReg64 .x0 s1.brk).setPC (mbase 7 + svcOff + 4#64)) = s2 at hFailSt ⊢
      obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hFailSt
      have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem := hMem2 ▸ hcl1
      have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
      have hx22_2 : s2.readReg64 .x22 = s1.brk + 4096#64 := (hGpr2 22#5 nofun nofun).trans (by rw [hBrk1]; exact hx22_1)
      have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 0 - 40#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
          s3.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 40#64) ∧
          s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s1.brk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs stFail.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
              CtxCells maddrs.ctx stFail.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc stFail.auxvPtr ∗ MallocngAuxvStateRo ro γ stFail.auxvPtr stFail.auxvSnap ∗
              ByteMap stFail.masterDom (OwnedRwByte stFail) stFail.byteVal ∗ ProtNoneByteMap stFail.masterDom (OwnedProtNoneByte stFail) stFail.byteVal ∗
              MappedSet stFail.masterDom (OwnedMappedByte stFail))))) hcl2 ?_) ?_)
      · have hMidFailB2 : ctxMiddleBytes stFail.ctx = ctxMiddleBytes st.ctx := rfl
        rw [hRwFail, hPnFail, hMpFail]; dsimp only [P_all, CtxCells]; rw [hMidFailB2]; dsimp only [stFail]; rw [hCnt0]
        have hNe4096 : ((s1.brk + 4096#64) - s1.brk == 0#64) = false := by rw [show (s1.brk + 4096#64) - s1.brk = 4096#64 by bv_arith]; decide
        simp only [BitVec.reduceSub] at hPc2; conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hNe4096, BitVec.reduceNeg] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
      · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx20_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
        have hD0Tot : MallocngMappedDelta 0 0 s0.mem s3.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3))
        have hFineFail : FineSplitInv bL bP stFail := FineSplitInv.of_eq hFine hFine.meta_le rfl
        exact SepWP.mono (SepWP.weaken_pre hEnt3 (sepWP_slowPathC_144_fine hWords hRange hcl3 hInflight hCount hFineFail hMaStep
          hPc3 hRun3 hSp3 hSp0 hTp0 hx20_3 hx24_3 hCs3 hProc3 hD0Tot (hBrk3 ▸ hWfFail) h1 hNoFree hNoBump hCnt0 rfl))
          fun _ _ _ _ => allocMetaFinePost_congr ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro hPhysLt R' hmR
      exact Satisfies.pure_intro
        (MallocngPlacedOomCond.of_delta hProc1.1 hProc1.2.1 hProc1.2.2.2.2.2.2
          (MallocngMappedDelta.trans hDelta0 hD1) (by decide)
          (by unfold FineMetaStep; omega)
          fun _ => ⟨4096, by decide, by decide, by unfold FineMetaStep; omega, Or.inr (by dsimp [State.setStatus]; omega)⟩)
        (Satisfies.drop_left hmR)

set_option maxHeartbeats 400000 in
private theorem sepWP_slowPathB1_1a8_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat}
    {st : MallocngSt} {sec : BitVec 64} {errnoVal : BitVec 32} {s0 s : State}
    (hWordsSvc : AmfHasWords116 msvc) (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st) (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hPc : s.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 - 80#64))
    (hRun : s.status = .Running) (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true)
    (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart) (hx1 : s.readReg64 .x1 = maddrs.ctx)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hx24 : s.readReg64 .x24 = 4096#64)
    (hCs25 : Cs25Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (h0 : st.ctx.initDone = 0#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  have hWords : AmfHasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  obtain ⟨_, hMa0, _, hGp0, _, hAv0, hFm0, hBm0, _, hGs0, _, hBrkEq⟩ := hWf.initZero_wf h0
  have ⟨hBsGe, hBsMod, _, _, hBsFit0⟩ := hWf.brk_bounds
  let P_rest (c : CtxFields) := StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx c ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  let svcOff1 := reloc_call_off% amfRelocs "__mmap" 1 - 72#64
  let svcOff2 := reloc_call_off% amfRelocs "__mmap" 1 - 40#64
  refine SepWP.cut_at_off (mbase 7) svcOff1 (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
    s1.pc = mbase 7 + svcOff1 ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
    s1.readReg64 .x0 = 0#64 ∧ s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x8 = 214#64 ∧
    s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
    Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
    (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32 }))) hcl ?_) ?_)
  · dsimp only [svcOff1, P_rest, CtxCells]; simp only [BitVec.reduceSub] at hPc; conv => arg 2; simp only [BitVec.reduceSub]
    wp_sym_steps; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25; wp_done
  · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx0_1, hx1_1, hx8_1, hx20_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
    have hBrk1' : s1.brk = brkStart := hBrk1.trans hBrkEq
    have hFetch1 : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff1) = some (.system false 0#16) :=
      Program.fetch_of_hasWords_getElem_decode 79 3556769793#32 hWordsSvc (by dsimp only [svcOff1]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
    refine SepWP.weaken_pre hEnt1 (SepWP.step_svc_brk_query hPc1 hRun1 hFetch1 hx0_1 (evalInst_svc0_execBrk_fine hx8_1) ?_)
    have hQSt := post_brk_fail_state_fine (fn := mbase 7) (off := svcOff1)
      (pc' := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 - 68#64)) (by dsimp only [svcOff1]; bv_arith) hRun1 hSp1 hCs1 hProc1
    generalize ((s1.writeReg64 .x0 s1.brk).setPC (mbase 7 + svcOff1 + 4#64)) = s2 at hQSt ⊢
    obtain ⟨hPc2, hRun2, hSp2, hx0_2, hGpr2, hCs2, hProc2, hBrk2, hMem2⟩ := hQSt
    have hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem := hMem2 ▸ hcl1
    have hx0_2' : s2.readReg64 .x0 = brkStart := hx0_2.trans hBrk1'
    have hx1_2 : s2.readReg64 .x1 = maddrs.ctx := (hGpr2 1#5 nofun nofun).trans hx1_1
    have hx8_2 : s2.readReg64 .x8 = 214#64 := (hGpr2 8#5 nofun nofun).trans hx8_1
    have hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr2 20#5 nofun nofun).trans hx20_1
    have hx24_2 : s2.readReg64 .x24 = 4096#64 := (hGpr2 24#5 nofun nofun).trans hx24_1
    have hNegAnd : (0#64 - brkStart) &&& 4095#64 = 0#64 := by
      rw [BitVec.zero_sub]; exact and_4095_eq_zero_of_dvd ⟨(2 ^ 64 - brkStart.toNat) / 4096, by rw [BitVec.toNat_neg]; have := brkStart.isLt; omega⟩
    have hNegAnd' : (-brkStart) &&& 4095#64 = 0#64 := by simpa only [BitVec.zero_sub] using hNegAnd
    refine SepWP.cut_at_off (mbase 7) svcOff2 (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
      s3.pc = mbase 7 + svcOff2 ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
      s3.readReg64 .x0 = brkStart + 8192#64 ∧ s3.readReg64 .x1 = maddrs.ctx ∧ s3.readReg64 .x8 = 214#64 ∧
      s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x22 = brkStart + 8192#64 ∧ s3.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s2.brk)
      (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32, brk := brkStart }))) hcl2 ?_) ?_)
    · have hMidBrk : ctxMiddleBytes { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = ctxMiddleBytes { st.ctx with secret := sec, initDone := 1#32 } := rfl
      dsimp only [svcOff2, P_rest, CtxCells]; rw [hMidBrk]; simp only [BitVec.reduceSub] at hPc2; conv => arg 2; simp only [BitVec.reduceSub]
      wp_sym_steps; simp only [hNegAnd, hNegAnd', BitVec.zero_add] at *
      obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs2; wp_done
    · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx0_3, hx1_3, hx8_3, hx20_3, hx22_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
      have hBrk3' : s3.brk = brkStart := hBrk3.trans (hBrk2.trans hBrk1')
      let newBrk := brkStart + 8192#64
      have hBsFit : brkStart.toNat ≤ 2 ^ 48 := hBrkEq ▸ hBsFit0
      have hNewNat : newBrk.toNat = brkStart.toNat + 8192 := by dsimp only [newBrk]; rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have hLenEq : newBrk.toNat - s3.brk.toNat = 8192 := by rw [hBrk3']; omega
      have hFetch2 : (mallocngBlockProg mmpl 7 msvc).fetch (mbase 7 + svcOff2) = some (.system false 0#16) :=
        Program.fetch_of_hasWords_getElem_decode 87 3556769793#32 hWordsSvc (by dsimp only [svcOff2]; simp only [BitVec.reduceSub]; bv_arith) rfl rfl
      refine SepWP.weaken_pre hEnt3 (SepWP.step_svc_brk_grow (newBrk := newBrk) hPc3 hRun3 hFetch2 hx0_3
        (fun hZ => by rw [hZ] at hNewNat; simp at hNewNat) (by rw [hProc3.2.2.2.1, hBs0]; omega) (by rw [hBrk3']; omega)
        (by rw [hBrk3']; exact Nat.dvd_of_mod_eq_zero hBsMod) ⟨brkStart.toNat / 4096 + 2, by omega⟩ (evalInst_svc0_execBrk_fine hx8_3) ?_ ?_ ?_)
      · intro m' hFit2 _ hm' hDBrk
        obtain ⟨⟨_, hBs65536, hBsDvd, hBsFit8⟩, hmProps, hWf', hGrpPost, hRwEmp, hPnEmp, hApBm, hPnEq', hMpEq'⟩ :=
          slowPathB1_trans hWf hInflight h0 sec hFit2
        let ap := brkStart + 4096#64
        let st' : MallocngSt := { st with
          ctx := { st.ctx with secret := sec, initDone := 1#32, availMeta := ap + 64#64, availMetaCount := 100#64, metaAreaHead := ap, metaAreaTail := ap, availMetaAreas := ap + 4096#64, brk := newBrk },
          metaAreas := [{ base := ap, next := 0#64 }], guardPages := [brkStart], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)),
          reservedMetas := (ap + 24#64) :: st.reservedMetas, masterDom := rangeAddrs brkStart 8192, byteVal := writeBytesToMap (fun _ => 0#8) ap (metaHdrBytes sec 0#64) }
        have hSplit8 : (s3.brk ↦ₛ List.replicate (newBrk.toNat - s3.brk.toNat) 0#8) = ((brkStart ↦ₛ List.replicate 4096 0#8) ∗ (ap ↦ₛ List.replicate 4096 0#8)) := by
          rw [hLenEq, hBrk3', show (8192 : Nat) = 4096 + 4096 from rfl, List.replicate_add, pointsToBytes_append, List.length_replicate]
        rw [hSplit8]
        have hGrowSt := post_brk_grow_state_fine (m' := m') (phys' := s3.physMemAvail - (newBrk.toNat - s3.brk.toNat)) (newBrk := newBrk) (fn := mbase 7) (off := svcOff2)
          (pc' := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 - 36#64)) (by dsimp only [svcOff2]; bv_arith) hRun3 hSp3 hCs3 hProc3
        generalize (((((s3.setBrk newBrk).setMem m').setPhysMemAvail (s3.physMemAvail - (newBrk.toNat - s3.brk.toNat))).writeReg64 .x0 newBrk).setPC (mbase 7 + svcOff2 + 4#64)) = s4 at hGrowSt ⊢
        obtain ⟨hPc4, hRun4, hSp4, hx0_4, hGpr4, hCs4, hProc4, hBrk4, hMem4⟩ := hGrowSt
        have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem :=
          hMem4 ▸ hm' ▸ hcl3.of_keepsFrozen (Memory.keepsFrozen_mapZero s3.mem s3.brk _)
        have hx1_4 : s4.readReg64 .x1 = maddrs.ctx := (hGpr4 1#5 nofun nofun).trans hx1_3
        have hx20_4 : s4.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr4 20#5 nofun nofun).trans hx20_3
        have hx22_4 : s4.readReg64 .x22 = newBrk := (hGpr4 22#5 nofun nofun).trans hx22_3
        have hx24_4 : s4.readReg64 .x24 = 4096#64 := (hGpr4 24#5 nofun nofun).trans hx24_3
        let retMmap := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 + 4#64)
        refine SepWP.cut (mid := mbase 16) (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s5 =>
          s5.pc = mbase 16 ∧ s5.status = .Running ∧ s5.sp = s0.sp - 80#64 ∧ s5.readReg64 Reg.lr = retMmap ∧
          s5.readReg64 .x0 = brkStart ∧ (s5.readReg64 .x1).toNat = 4096 ∧ s5.readReg32 .x2 = 0#32 ∧ s5.readReg32 .x3 = 50#32 ∧
          s5.readReg32 .x4 = BitVec.allOnes 32 ∧ s5.readReg64 .x5 = 0#64 ∧ s5.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
          s5.readReg64 .x21 = ap ∧ s5.readReg64 .x22 = newBrk ∧ s5.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s5 ∧ MallocngProcPreserved s0 s5 ∧ s5.brk = newBrk)
          (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((brkStart ↦ₛ List.replicate 4096 0#8) ∗ ((ap ↦ₛ List.replicate 4096 0#8) ∗ P_rest { st.ctx with secret := sec, initDone := 1#32, brk := brkStart }))))) hcl4 ?_) ?_)
        · have hEqNew : (newBrk - newBrk == 0#64) = true := by simp
          have hSubAp : newBrk - 4096#64 = ap := by dsimp only [newBrk, ap]; bv_arith
          dsimp only [P_rest, CtxCells, retMmap]; simp only [BitVec.reduceSub] at hPc4
          wp_sym_steps; simp only [resolve_mmapPriv, mbase, mmpl, hEqNew, hSubAp, show ∀ x y : BitVec 64, x + (y - x) = y from fun _ _ => by bv_arith] at *
          obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc4; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs4; wp_done
        · intro s5 P5 hPc5 hRun5 ⟨_, hD5, hcl5, ⟨_, _, hSp5, hLr5, hx0_5, hx1_5, hx2_5, hx3_5, hx4_5, hx5_5, hx20_5, hx21_5, hx22_5, hx24_5, hCs5, hProc5, hBrk5⟩, hEnt5⟩
          refine SepWP.weaken_pre hEnt5 ?_
          have hSt64 : ∀ {stx : State}, stx.sp = s0.sp - 80#64 → stackAt (s0.sp - 80#64) 64 = stackFrame stx 64 :=
            fun h => by rw [stackAt_eq_stackFrameAt (s0.sp - 80#64) 64 (by decide), stackFrameAt_eq_memRegion (s0.sp - 80#64) 64 (by decide)]; unfold stackFrame; rw [h]
          unfold StackFrameSlow; rw [hSt64 hSp5]
          have hSpA5 : s5.spAligned = true := by rw [State.spAligned, hSp5]; exact spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
          have hTp5 : s5.tpidrEl0 = tp := hProc5.2.2.1.trans hTp0
          refine call_withCL_frame_auto (x := ())
            (placed_mmapFixedProtNoneWrapper_ok (P := mallocngBlockProg mmpl 7 msvc) tp brkStart errnoVal (List.replicate 4096 0#8) 4096 List.length_replicate (by decide) (Nat.dvd_refl 4096) hBs65536 hBsDvd (by omega) (by intro pc; simp) rfl)
            hcl5 hPc5 hRun5 hSpA5 hLr5 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
          intro s6 hPc6 hRun6 hSp6 hCsCall hcl6
          have hSp6Eq : s6.sp = s0.sp - 80#64 := hSp6.trans hSp5
          rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
          apply SepWP.pure_elim; rintro ⟨hProcCall, hBrk6, _, hDCall⟩
          rw [← hSt64 hSp5]
          have hRw0Emp : ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) = emp :=
            SetSep_empty _ fun _ _ ⟨hL, _⟩ => hL.elim (fun ⟨_, hm, _⟩ => by rw [hMa0] at hm; cases hm) (fun ⟨_, hg, _⟩ => by rw [hGs0] at hg; cases hg)
          have hApBm' : ((ap ↦ₛ metaHdrBytes st'.ctx.secret 0#64) ∗ ((ap + 64#64) ↦ₛ List.replicate 4032 0#8) ∗ ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8)) = ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal := by
            rw [hRw0Emp, sepConj_emp]; exact hApBm
          refine SepWP.weaken_pre (P' := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
            (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗
              CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } ∗
              MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
              ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
              MappedSet st'.masterDom (OwnedMappedByte st'))))
            (by dsimp only [P_rest, st']; rw [hRwEmp, hPnEmp, hPnEq', hRw0Emp, hMpEq']; unfold StackFrameSlow; sep_frame) ?_
          have hx20_6 : s6.readReg64 .x20 = Obj.pageOf maddrs.ctx := hCsCall.2.1.trans hx20_5
          have hx21_6 : s6.readReg64 .x21 = ap := hCsCall.2.2.1.trans hx21_5
          have hx22_6 : s6.readReg64 .x22 = newBrk := hCsCall.2.2.2.1.trans hx22_5
          have hx24_6 : s6.readReg64 .x24 = 4096#64 := hCsCall.2.2.2.2.2.1.trans hx24_5
          have hCs6 : Cs25Preserved s0 s6 := ⟨hCsCall.2.2.2.2.2.2.1.trans hCs5.1, hCsCall.2.2.2.2.2.2.2.1.trans hCs5.2.1,
            hCsCall.2.2.2.2.2.2.2.2.1.trans hCs5.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.1.trans hCs5.2.2.2.1, hCsCall.2.2.2.2.2.2.2.2.2.2.2.trans hCs5.2.2.2.2⟩
          have hProc6 : MallocngProcPreserved s0 s6 := procPreserved_trans hProc5 hProcCall
          refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords + 24#64)
            (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s7 =>
              s7.pc = mbase 7 + (words_ret_off% amfWords + 24#64) ∧
              s7.status = .Running ∧ s7.sp = s0.sp - 80#64 ∧ s7.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s7.readReg64 .x21 = ap ∧
              Cs25Preserved s0 s7 ∧ MallocngProcPreserved s0 s7 ∧ s7.brk = s6.brk)
              (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ (ap ↦ₛ List.replicate 4096 0#8) ∗
                  CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
                  MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
                  ByteMap st'.masterDom (OwnedRwByte st) (fun _ => 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗
                  MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl6 ?_) ?_)
          · have hCtxPre6 : { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } := by rw [(hWf.initZero_wf h0).1]
            have hCtxPost6 : { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } =
                { emptyCtxFields with secret := sec, initDone := 1#32, availMetaAreaCount := 1#64, brk := newBrk, seq := st.ctx.seq } := by dsimp only [st']; rw [(hWf.initZero_wf h0).1]; rfl
            have hMidPre6 : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [← hCtxPre6]; rfl
            have hMidPost6 : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, availMetaAreaCount := 1#64, brk := newBrk, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [(hWf.initZero_wf h0).1]; rfl
            rw [hCtxPre6, hCtxPost6]; dsimp only [CtxCells, retMmap] at hPc6 hx20_6 ⊢; rw [hMidPre6, hMidPost6]; dsimp only [emptyCtxFields]
            clear hCtxPre6 hCtxPost6 hMidPre6 hMidPost6; conv => arg 2; simp only [BitVec.reduceAdd]
            wp_sym_steps; simp only [BitVec.reduceAdd] at *
            obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc6; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs6; wp_done
          · intro s7 P7 hPc7 hRun7 ⟨_, hD7, hcl7, ⟨_, _, hSp7, hx20_7, hx21_7, hCs7, hProc7, hBrk7⟩, hEnt7⟩
            have hBrk7' : s7.brk = newBrk := hBrk7.trans (hBrk6.trans hBrk5)
            have hD03 : MallocngMappedDelta 0 0 s0.mem s3.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3))
            have hD47 : MallocngMappedDelta 0 0 s4.mem s7.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD5 hDCall) hD7)
            have hNoOrph7 := noOrphanMappings_slowPathB1_fine (st' := st') hMa0 hGp0 hAv0 hGs0 hBsFit8 rfl rfl hD03 (by rw [hMem4, hm', hLenEq, hBrk3']) hD47
            have hDTot : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s7.mem :=
              MallocngMappedDelta.mono (by decide) (by unfold FineMetaStep; omega) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hD03 (hLenEq ▸ hDBrk)) (hMem4 ▸ hD47))
            have hMaStep1 : st'.metaAreas.length ≤ st.metaAreas.length + 1 := by simp [st', hMa0]
            have hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP := by
              have h := FineSplitInv.metaAreas_succ_le hFine hWf hInflight hFm0 hBm0
              simpa [st', hMa0] using h
            have hMaBound1 : st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) :=
              Nat.le_trans (by change 1 ≤ 1 + (88 + 8 * peakCount) / 101; omega) (Nat.le_max_right _ _)
            exact SepWP.weaken_pre hEnt7 (sepWP_activate_2a0_fine hWords hRange hcl7 hPc7 hRun7 hSp7 hSp0 hx20_7 hx21_7 hCs7 hProc7
              hFine hMaStep1 hMaFine hMaBound1 hNoOrph7 hDTot (metaAreas_ctx_eqs hWf rfl rfl rfl rfl (by rw [hMa0])) (fun hne => False.elim (hne hMa0)) (fun _ => rfl) hApBm' hmProps
              (hBrk7' ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
      · obtain ⟨hWfFail, hFmFail, hBmFail, _, hRwFail, hPnFail, hMpFail⟩ := lazyInit_brkFail_wf (sec := sec) hWf h0
        let stFail : MallocngSt := { st with ctx := { emptyCtxFields with secret := sec, initDone := 1#32, brk := -1#64, seq := st.ctx.seq } }
        have hFailSt := post_brk_fail_state_fine (fn := mbase 7) (off := svcOff2)
          (pc' := mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 - 36#64)) (by dsimp only [svcOff2]; bv_arith) hRun3 hSp3 hCs3 hProc3
        generalize ((s3.writeReg64 .x0 s3.brk).setPC (mbase 7 + svcOff2 + 4#64)) = s4 at hFailSt ⊢
        obtain ⟨hPc4, hRun4, hSp4, hx0_4, hGpr4, hCs4, hProc4, hBrk4, hMem4⟩ := hFailSt
        have hcl4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := hMem4 ▸ hcl3
        have hx20_4 : s4.readReg64 .x20 = Obj.pageOf maddrs.ctx := (hGpr4 20#5 nofun nofun).trans hx20_3
        have hx22_4 : s4.readReg64 .x22 = newBrk := (hGpr4 22#5 nofun nofun).trans hx22_3
        have hx24_4 : s4.readReg64 .x24 = 4096#64 := (hGpr4 24#5 nofun nofun).trans hx24_3
        refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 0 - 40#64)
          (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s5 =>
            s5.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 40#64) ∧ s5.status = .Running ∧ s5.sp = s0.sp - 80#64 ∧
            s5.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s5.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s5 ∧ MallocngProcPreserved s0 s5 ∧ s5.brk = s4.brk)
            (StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs stFail.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
              CtxCells maddrs.ctx stFail.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc stFail.auxvPtr ∗ MallocngAuxvStateRo ro γ stFail.auxvPtr stFail.auxvSnap ∗
              ByteMap stFail.masterDom (OwnedRwByte stFail) stFail.byteVal ∗ ProtNoneByteMap stFail.masterDom (OwnedProtNoneByte stFail) stFail.byteVal ∗ MappedSet stFail.masterDom (OwnedMappedByte stFail))))) hcl4 ?_) ?_)
        · rw [hRwFail, hPnFail, hMpFail]
          have hNe8192 : (newBrk != brkStart) = true := by
            dsimp only [newBrk]; rw [bne_iff_ne]; intro h; have := congrArg (· - brkStart) h; simp [show brkStart + 8192#64 - brkStart = 8192#64 by bv_arith] at this
          have hCtxR : { st.ctx with secret := sec, initDone := 1#32, brk := brkStart } = { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } := by rw [(hWf.initZero_wf h0).1]
          have hMidPreF : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, brk := brkStart, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by rw [← hCtxR]; rfl
          have hMidPostF : ctxMiddleBytes stFail.ctx = ctxMiddleBytes st.ctx := by dsimp only [stFail]; rw [(hWf.initZero_wf h0).1]; rfl
          dsimp only [P_rest]; rw [hCtxR]; dsimp only [CtxCells]; rw [hMidPreF, hMidPostF]; dsimp only [stFail, emptyCtxFields]
          clear hCtxR hMidPreF hMidPostF; rw [hBrk3'] at hx0_4; simp only [BitVec.reduceSub] at hPc4; conv => arg 2; simp only [BitVec.reduceSub]
          wp_sym_steps; simp only [hNe8192, BitVec.reduceNeg] at *
          obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc4; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs4; wp_done
        · intro s5 P5 hPc5 hRun5 ⟨_, hD5, hcl5, ⟨_, _, hSp5, hx20_5, hx24_5, hCs5, hProc5, hBrk5⟩, hEnt5⟩
          have hWfFail5 : MallocngWFInflight inflight maddrs.base brkStart s5.brk liveCost peakCost stFail := by rw [hBrk5, hBrk4, hBrk3, hBrk2, hBrk1]; exact hWfFail
          have hD0Tot : MallocngMappedDelta 0 0 s0.mem s5.mem := MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3)) (hMem4 ▸ hD5))
          have hFineFail : FineSplitInv bL bP stFail := FineSplitInv.of_eq hFine hFine.meta_le rfl
          exact SepWP.mono (SepWP.weaken_pre hEnt5 (sepWP_slowPathC_144_fine hWords hRange hcl5 hInflight hCount hFineFail hMaStep
            hPc5 hRun5 hSp5 hSp0 hTp0 hx20_5 hx24_5 hCs5 hProc5 hD0Tot hWfFail5 rfl hFmFail hBmFail rfl rfl))
            fun _ _ _ _ => allocMetaFinePost_congr (by dsimp only [stFail]; rw [(hWf.initZero_wf h0).1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      · intro hPhysLt R' hmR
        exact Satisfies.pure_intro
          (MallocngPlacedOomCond.of_delta hProc3.1 hProc3.2.1 hProc3.2.2.2.2.2.2
            (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) (hMem2 ▸ hD3)) (by decide)
            (by unfold FineMetaStep; omega)
            fun _ => ⟨8192, by decide, by decide, by unfold FineMetaStep; omega, Or.inr (by dsimp [State.setStatus]; omega)⟩)
          (Satisfies.drop_left hmR)

set_option maxHeartbeats 400000 in
private theorem sepWP_postInit_01c_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {bL bP : FineBudget} {maxMeta : Nat} {st : MallocngSt} {errnoVal : BitVec 32} {s0 s : State}
    (hWords0 : AmfHasWords0 mallocngFaultSvcAmf) (hWordsSvc : AmfHasWords116 msvc) (hRange : AmfRange116)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st) (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hPc : s.pc = mbase 7 + (words_insn_off% amfWords "cbz" 0 + 4#64)) (hRun : s.status = .Running)
    (hSp : s.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20 : s.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hCs21 : Cs21Preserved s0 s) (hProc : MallocngProcPreserved s0 s)
    (hDelta0 : MallocngMappedDelta 0 0 s0.mem s.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st) (h1 : st.ctx.initDone = 1#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s
      (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st))))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  have hWords : AmfHasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  have hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  cases hFm : st.freeMetas with
  | cons fm0 rest =>
    have hDll := hWf.free_bump_metas_wf.1; simp only [hFm, List.map_cons, CircularDllWf] at hDll
    have hHdEq : st.ctx.freeMetaHead = fm0.ptr := hDll.1
    have hFmBeq : (fm0.ptr == 0#64) = false := beq_false_of_ne (hDll.2.2.1 (fm0.ptr, fm0.prev, fm0.next) (List.Mem.head _))
    let P_all := StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
      CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
    refine SepWP.cut_at_off (mbase 7) (words_insn_off% amfWords "cbz" 0 + 16#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (words_insn_off% amfWords "cbz" 0 + 16#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x19 = fm0.ptr ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_all) hcl ?_) ?_)
    · dsimp only [P_all, CtxCells, ctxMiddleBytes]; rw [hHdEq]; conv => arg 2; simp only [BitVec.reduceAdd]
      wp_sym_steps; simp only [hFmBeq] at *; obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx1_1, hx19_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre hEnt1 (sepWP_fastPath1_028_fine hWords0 hWords hcl1 hPc1 hRun1 hSp1 hSp0 hx1_1 hx19_1 hCs1 hProc1
        (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)) hFine (hBrk1 ▸ hWf) hFm)
  | nil =>
    have hHd0 : st.ctx.freeMetaHead = 0#64 := by have h := hWf.free_bump_metas_wf.1; simpa [hFm, CircularDllWf] using h
    by_cases hAvCnt0 : st.ctx.availMetaCount = 0#64
    · have hNoBump : st.bumpMetas = [] := (hWf.free_bump_metas_wf.2.2.1).elim And.right fun ⟨hPos, _⟩ => by rw [hAvCnt0] at hPos; exact absurd hPos (by decide)
      obtain ⟨hc21, hc22, hc23, hc24, hCs25_0⟩ := hCs21
      unfold StackFrameOpen; rw [cells_split_sub s0.sp 48 16 4 2, cells_sub_succ s0.sp 48 4 (by decide) (by decide), cells_sub_succ s0.sp 40 3 (by decide) (by decide), cells_sub_succ s0.sp 32 2 (by decide) (by decide), cells_sub_succ s0.sp 24 1 (by decide) (by decide)]
      simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40; apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
      let P_slow := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
        CtxCells maddrs.ctx st.ctx ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
      refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 0 - 104#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
          s1.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 104#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
          s1.readReg64 .x1 = maddrs.ctx ∧ s1.readReg64 .x2 = st.ctx.availMetaAreaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s1.readReg64 .x24 = 4096#64 ∧
          Cs25Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk) P_slow) hcl ?_) ?_)
      · dsimp only [P_slow, StackFrameSlow, SavedRegs0, SavedRegs21, CtxCells]; rw [hHd0, hAvCnt0]
        (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hc21, hc22, hc23, hc24] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25_0; wp_done
      · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx1_1, hx2_1, hx20_1, hx24_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
        refine SepWP.weaken_pre hEnt1 ?_
        have hWf1 : MallocngWFInflight inflight maddrs.base brkStart s1.brk liveCost peakCost st := hBrk1.symm ▸ hWf
        by_cases hAreaCnt0 : st.ctx.availMetaAreaCount = 0#64
        · by_cases hBrkNeg1 : st.ctx.brk = -1#64
          · refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 0 - 40#64)
              (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
                s2.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 40#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
                s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk) P_slow) hcl1 ?_) ?_)
            · dsimp only [P_slow, CtxCells]; rw [hAreaCnt0] at hx2_1; rw [hAreaCnt0, hBrkNeg1]
              simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps
              obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
            · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
              exact SepWP.weaken_pre hEnt2 (sepWP_slowPathC_144_fine hWords hRange hcl2 hInflight hCount hFine hMaStep
                hPc2 hRun2 hSp2 hSp0 hTp0 hx20_2 hx24_2 hCs2 hProc2 (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2))
                (hBrk2.symm ▸ hWf1) h1 hFm hNoBump hAreaCnt0 hBrkNeg1)
          · obtain ⟨hBrkEq, hBrkGe, _⟩ := hWf1.brk_mode_wf.1 ⟨h1, hBrkNeg1⟩; have hBrkHi := hWf1.brk_bounds.2.2.2.2
            rw [hBrk1] at hBrkEq hBrkGe hBrkHi
            have hBrkAdd1 : (s.brk + 1#64 == 0#64) = false := beq_false_of_ne fun h => by have := congrArg BitVec.toNat h; rw [BitVec.toNat_add] at this; simp at this; omega
            have hBrkNe0 : (s.brk == 0#64) = false := beq_false_of_ne fun h => by rw [h] at hBrkGe; simp at hBrkGe
            refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 0 - 84#64)
              (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
                s2.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 0 - 84#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
                s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x21 = s2.brk ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s.brk) P_slow) hcl1 ?_) ?_)
            · dsimp only [P_slow, CtxCells]; rw [hAreaCnt0] at hx2_1; rw [hAreaCnt0, hBrkEq]
              simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hBrkAdd1, hBrkNe0] at *
              obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
            · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx21_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
              exact SepWP.weaken_pre hEnt2 (sepWP_slowPathB2_118_fine hWordsSvc hRange hcl2 hInflight hCount hFine hMaStep
                hPc2 hRun2 hSp2 hSp0 hTp0 hBs0 hx20_2 hx21_2 hx24_2 hCs2 hProc2 (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2))
                (hBrk2.symm ▸ hWf) h1 hFm hNoBump hAreaCnt0 hBrkNeg1)
        · obtain ⟨⟨_, hApMod, hApFit⟩, hmProps, hWf', hGrpPost, hPnEx, hTailBm, hApBm, hMpEq⟩ := slowPathA_trans hWf1 hInflight h1 hFm hNoBump hAreaCnt0
          let ap := st.ctx.availMetaAreas; let cnt' := st.ctx.availMetaAreaCount - 1#64; let rest := (List.range cnt'.toNat).map (fun i => (ap + 4096#64) + BitVec.ofNat 64 (4096 * i))
          let bv1 := if hne : st.metaAreas ≠ [] then writeBytesToMap st.byteVal (st.metaAreas.getLast hne).base (metaHdrBytes st.ctx.secret ap) else st.byteVal
          let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := ap + 64#64, availMetaCount := 100#64, availMetaAreaCount := cnt', metaAreaHead := (match st.metaAreas with | [] => ap | hd :: _ => hd.base), metaAreaTail := ap, availMetaAreas := ap + 4096#64 }, metaAreas := appendMetaArea st.metaAreas ap, mmapMetaAreas := ((appendMetaArea st.metaAreas ap).map (·.base)).filter (fun mb => !decide (InRegion brkStart (s1.brk.toNat - brkStart.toNat) mb)), availMetaPages := rest, freeMetas := [], bumpMetas := (List.range 100).map (fun j => ({ base := ap, next := 0#64 } : MetaAreaDesc).slotAddr (1 + j)), reservedMetas := (ap + 24#64) :: st.reservedMetas, byteVal := writeBytesToMap bv1 ap (metaHdrBytes st.ctx.secret 0#64) }
          have hApAlign : 4096 ∣ ap.toNat := Nat.dvd_of_mod_eq_zero hApMod
          have hApMask : (ap &&& 4095#64 == 0#64) = true := beq_iff_eq.mpr (and_4095_eq_zero_of_dvd hApAlign)
          have hAreaBne : (st.ctx.availMetaAreaCount != 0#64) = true := bne_iff_ne.mpr hAreaCnt0
          have hAreaBeq : (st.ctx.availMetaAreaCount == 0#64) = false := beq_false_of_ne hAreaCnt0
          have hCtxEqM : { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } = st.ctx := by
            dsimp only [st', cnt']; rw [BitVec.sub_add_cancel]
          let P_mprot := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
            (ap ↦ₙ List.replicate 4096 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := st.ctx.availMeta, availMetaCount := st.ctx.availMetaCount, availMetaAreaCount := st'.ctx.availMetaAreaCount + 1#64, metaAreaHead := st.ctx.metaAreaHead, metaAreaTail := st.ctx.metaAreaTail, availMetaAreas := st.ctx.availMetaAreas } ∗
            MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗ ByteMap st'.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st')))
          have hPnEx' : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal = ((ap ↦ₙ List.replicate 4096 0#8) ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal) := hPnEx
          have hMpEq' : MappedSet st'.masterDom (OwnedMappedByte st') = MappedSet st.masterDom (OwnedMappedByte st) := hMpEq
          refine SepWP.weaken_pre (P' := P_mprot) (Entails.of_eq (by
            dsimp only [P_slow, P_mprot]
            rw [hCtxEqM, show st'.liveMap = st.liveMap from rfl, show st'.auxvPtr = st.auxvPtr from rfl, show st'.auxvSnap = st.auxvSnap from rfl,
              show ByteMap st'.masterDom (OwnedRwByte st) st.byteVal = ByteMap st.masterDom (OwnedRwByte st) st.byteVal from rfl, hPnEx', ← hMpEq']
            ac_rfl)) ?_
          refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "mprotect" - 12#64)
            (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s2 =>
              s2.pc = mbase 7 + (reloc_call_off% amfRelocs "mprotect" - 12#64) ∧ s2.status = .Running ∧ s2.sp = s0.sp - 80#64 ∧
              s2.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s2.readReg64 .x21 = ap ∧ s2.readReg64 .x24 = 4096#64 ∧ Cs25Preserved s0 s2 ∧ MallocngProcPreserved s0 s2 ∧ s2.brk = s1.brk) P_mprot) hcl1 ?_) ?_)
          · dsimp only [ap, P_mprot]; rw [hCtxEqM]; dsimp only [CtxCells]
            simp only [BitVec.reduceSub] at hPc1; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hAreaBne, hAreaBeq, hApMask] at *
            obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc1; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs1; wp_done
          · intro s2 P2 hPc2 hRun2 ⟨_, hD2, hcl2, ⟨_, _, hSp2, hx20_2, hx21_2, hx24_2, hCs2, hProc2, hBrk2⟩, hEnt2⟩
            have hD02 : MallocngMappedDelta 0 0 s0.mem s2.mem :=
              MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans (MallocngMappedDelta.trans hDelta0 hD1) hD2)
            have hMaLen : st'.metaAreas.length = st.metaAreas.length + 1 := appendMetaArea_length st.metaAreas ap
            have hMaFine : st'.metaAreas.length ≤ fineMaxMetaAreas bP :=
              hMaLen ▸ FineSplitInv.metaAreas_succ_le hFine hWf1 hInflight hFm hNoBump
            exact SepWP.weaken_pre hEnt2 (sepWP_mprotect_224_fine hWords hRange hcl2 hPc2 hRun2 hSp2 hSp0 hTp0 hx20_2 hx21_2 hx24_2 hApAlign hApFit hCs2 hProc2
              hFine (Nat.le_of_eq hMaLen) hMaFine
              (appendMetaArea_len_le_max ap hWf1 hInflight hFm hNoBump hCount)
              (noOrphanMappings_slowPathA_fine hWf1 hAreaCnt0 rfl rfl rfl rfl hD02)
              (MallocngMappedDelta.mono (by decide) (by omega) hD02)
              (metaAreas_ctx_eqs hWf1 rfl rfl rfl rfl rfl) hTailBm (fun hNil => dite_eq_right_iff.mpr fun h => False.elim (h hNil)) hApBm hmProps
              (hBrk2.symm ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hGrpPost)
    · obtain ⟨hmProps, hWf', hRwEx, hPnEq, hMpEq⟩ := fastPath2_bump_trans hWf hFm hAvCnt0
      let m := st.ctx.availMeta
      let st' : MallocngSt := { st with ctx := { st.ctx with availMeta := m + 40#64, availMetaCount := st.ctx.availMetaCount - 1#64 }, bumpMetas := st.bumpMetas.tail, reservedMetas := m :: st.reservedMetas }
      have hBumpBeq : (st.ctx.availMetaCount == 0#64) = false := beq_false_of_ne hAvCnt0
      refine SepWP.cut_at_off (mbase 7) (words_ret_off% amfWords - 28#64)
        (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
          s1.pc = mbase 7 + (words_ret_off% amfWords - 28#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
          s1.readReg64 .x19 = m ∧ s1.readReg64 .x0 = st'.ctx.availMetaCount ∧ s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧
          Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s.brk)
          (StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st'.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
            (m ↦ₛ List.replicate 40 0#8) ∗ CtxCells maddrs.ctx { st'.ctx with availMeta := m, availMetaCount := st.ctx.availMetaCount } ∗
            MallocngAuxvPtrCell ro maddrs.libc st'.auxvPtr ∗ MallocngAuxvStateRo ro γ st'.auxvPtr st'.auxvSnap ∗
            ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∗ ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∗ MappedSet st'.masterDom (OwnedMappedByte st'))))) hcl ?_) ?_)
      · have hMidEq : ctxMiddleBytes { st'.ctx with availMeta := m, availMetaCount := st.ctx.availMetaCount } = ctxMiddleBytes st.ctx := rfl
        rw [hRwEx, ← hPnEq, ← hMpEq]; dsimp only [m, CtxCells]; rw [hMidEq]; dsimp only [st']; rw [hHd0]
        conv => arg 2; simp only [BitVec.reduceSub]
        wp_sym_steps; simp only [hBumpBeq] at *
        obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc; obtain ⟨hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hcv⟩ := hCs21; wp_done
      · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx19_1, hx0_1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
        have hD01 : MallocngMappedDelta 0 0 s0.mem s1.mem :=
          MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hDelta0 hD1)
        exact SepWP.weaken_pre hEnt1 (sepWP_epilogue_26c_fine hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0 hx19_1 hx0_1 hx20_1 rfl hCs1 hProc1
          hFine (Nat.le_succ _) hFine.meta_le
          (Nat.le_max_left _ _) (noOrphanMappings_of_same_ivs_delta_zero rfl hD01)
          (MallocngMappedDelta.mono (by decide) (by omega) hD01)
          hmProps (hBrk1 ▸ hWf') ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ _ _ _ => rfl))


/-! ## 9. Lazy Init Continuation and Entry Theorem -/

set_option maxHeartbeats 400000 in
private theorem sepWP_lazyInit_to_b1_fine [MallocngMultiPlacement] {ro : Bool}
    {inflight : Nat} {γ : GhostName} {tp brkStart : BitVec 64}
    {liveCost peakCost peakCount : Nat} {bL bP : FineBudget} {maxMeta : Nat}
    {st : MallocngSt} {sec : BitVec 64} {errnoVal : BitVec 32} {s0 s2 : State}
    (_hWords0 : AmfHasWords0 mallocngFaultSvcAmf) (hWordsSvc : AmfHasWords116 msvc) (hRange : AmfRange116)
    (hcl2 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem)
    (hInflight : inflight ≤ 7) (hCount : totalLiveCount st ≤ peakCount)
    (hFine : FineSplitInv bL bP st) (hMaStep : st.metaAreas.length ≤ maxMeta + 5)
    (hPc2 : s2.pc = mbase 7 + (words_insn_off% amfWords "cbz" 0 + 4#64)) (hRun2 : s2.status = .Running)
    (hSp2 : s2.sp = s0.sp - 80#64) (hSp0 : s0.spAligned = true) (hTp0 : s0.tpidrEl0 = tp) (hBs0 : s0.brkStart = brkStart)
    (hx20_2 : s2.readReg64 .x20 = Obj.pageOf maddrs.ctx) (hCs2 : Cs21Preserved s0 s2) (hProc2 : MallocngProcPreserved s0 s2)
    (hD02 : MallocngMappedDelta 0 0 s0.mem s2.mem)
    (hWf : MallocngWFInflight inflight maddrs.base brkStart s2.brk liveCost peakCost st) (h0 : st.ctx.initDone = 0#32) :
    SepWP (mallocngBlockProg mmpl 7 msvc) (s0.readReg64 Reg.lr) s2
      (StackFrameOpen s0 ∗ CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗
        MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MappedSet st.masterDom (OwnedMappedByte st)))
      (AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s0 sf⌝) := by
  have _hWords : AmfHasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  have _hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  obtain ⟨hc21, hc22, hc23, hc24, hCs25_2⟩ := hCs2
  unfold StackFrameOpen
  rw [cells_split_sub s0.sp 48 16 4 2, cells_sub_succ s0.sp 48 4 (by decide) (by decide),
    cells_sub_succ s0.sp 40 3 (by decide) (by decide), cells_sub_succ s0.sp 32 2 (by decide) (by decide),
    cells_sub_succ s0.sp 24 1 (by decide) (by decide)]
  simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v48; apply SepWP.exists_elim; intro v40; apply SepWP.exists_elim; intro v32; apply SepWP.exists_elim; intro v24
  let P_b1 := StackFrameSlow s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx { st.ctx with secret := sec, initDone := 1#32 } ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
  refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "__mmap" 1 - 80#64)
    (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s3 =>
      s3.pc = mbase 7 + (reloc_call_off% amfRelocs "__mmap" 1 - 80#64) ∧ s3.status = .Running ∧ s3.sp = s0.sp - 80#64 ∧
      s3.readReg64 .x1 = maddrs.ctx ∧ s3.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ s3.readReg64 .x24 = 4096#64 ∧
      Cs25Preserved s0 s3 ∧ MallocngProcPreserved s0 s3 ∧ s3.brk = s2.brk) P_b1) hcl2 ?_) ?_)
  · have hCtxSec : { st.ctx with secret := sec, initDone := 1#32 } = { emptyCtxFields with secret := sec, initDone := 1#32, seq := st.ctx.seq } := by
      rw [(hWf.initZero_wf h0).1]
    have hMidSec : ctxMiddleBytes { emptyCtxFields with secret := sec, initDone := 1#32, seq := st.ctx.seq } = ctxMiddleBytes st.ctx := by
      rw [← hCtxSec]; rfl
    simp only [BitVec.reduceAdd] at hPc2; dsimp only [P_b1, StackFrameSlow, SavedRegs0, SavedRegs21] at hCtxSec ⊢
    rw [hCtxSec]; dsimp only [CtxCells]; rw [hMidSec]; dsimp only [emptyCtxFields]; clear hCtxSec hMidSec
    (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; simp only [hc21, hc22, hc23, hc24] at *
    obtain ⟨hFs, hTr, hTp, hBs, hOr, hSy, hSig⟩ := hProc2; obtain ⟨hc25, hc26, hc27, hc28, hcv⟩ := hCs25_2; wp_done
  · intro s3 P3 hPc3 hRun3 ⟨_, hD3, hcl3, ⟨_, _, hSp3, hx1_3, hx20_3, hx24_3, hCs3, hProc3, hBrk3⟩, hEnt3⟩
    exact SepWP.weaken_pre hEnt3 (sepWP_slowPathB1_1a8_fine hWordsSvc hRange hcl3 hInflight hCount hFine hMaStep
      hPc3 hRun3 hSp3 hSp0 hTp0 hBs0 hx1_3 hx20_3 hx24_3 hCs3 hProc3
      (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hD02 hD3)) (hBrk3 ▸ hWf) h0)

theorem placed_allocMeta_fine_ok {ro : Bool} : AllocMetaFineStmt ro := by
  intro _ inflight hInflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st hCount hFine hMaStep
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  have ⟨hWords0Svc, _⟩ := hasWords_blk_seg0 (i := 7) (by decide)
    (ws := AllocMetaFullH.blk07Words0) (R := AllocMetaFullH.blk07Relocs0) (by decide +kernel)
  have ⟨hWordsSvc, hRange⟩ := hasWords_blk_seg (i := 7) (by decide) 116
    (ws := AllocMetaFullH.blk07Words116) (R := AllocMetaFullH.blk07Relocs116) (by decide +kernel)
  have hWords0 : AmfHasWords0 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWords0Svc
  have hWords : AmfHasWords116 mallocngFaultSvcAmf := Program.hasWords_withSvc_amf hWordsSvc
  apply subroutine_ok_of_sepWP_init; intro _ R s0 hPc0 hRun0 hPre0 hSp0; refine ⟨_, hPre0, ?_⟩; dsimp only
  refine SepWP.mono ?_ (fun sf P_f _ _ (hPost : AllocMetaFinePost (ro := ro) inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st s0 sf P_f) =>
    ⟨fun hmf => Satisfies.mono (sepConj_mono_left hPost.1) hmf, hPost.2.1, hPost.2.2⟩)
  apply SepWP.pure_elim; rintro rfl; apply SepWP.pure_elim; rintro ⟨hTp0, hBs0⟩
  unfold MallocngCoreStInflightModeA MallocngRuntime
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]; apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hWf
  have hSt224 : stackFrame s0 224 = (memRegion (s0.sp - 224#64) 80 ∗ (stackAt (s0.sp - 80#64) 64 ∗ cells (s0.sp - 80#64) 10)) := by
    unfold stackFrame; rw [← stackFrameAt_eq_memRegion s0.sp 224, ← stackAt_eq_stackFrameAt s0.sp 224]
    exact wrapperFrame_split s0.sp (wrapperStack := 224) (hookStack := 64) 10 (by decide)
  rw [hSt224, cells_split_sub s0.sp 80 48 4 6, cells_sub_succ s0.sp 80 4 (by decide) (by decide),
    cells_sub_succ s0.sp 72 3 (by decide) (by decide), cells_sub_succ s0.sp 64 2 (by decide) (by decide),
    cells_sub_succ s0.sp 56 1 (by decide) (by decide)]
  simp only [Nat.reduceSub, cells_zero, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro v80; apply SepWP.exists_elim; intro v72; apply SepWP.exists_elim; intro v64; apply SepWP.exists_elim; intro v56
  obtain ⟨l1, l2, l3, l4, l5, _⟩ := hWf.ctx_lens
  have hCtxCells := ctx_toBytes_eq_cells maddrs.ctx st.ctx l1 l2 l3 l4 (by rw [l5]; rfl)
  have _hSpSub : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 80#64 (by simpa [State.spAligned] using hSp0)
  let P_open (c : CtxFields) := StackFrameOpen s0 ∗ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
    CtxCells maddrs.ctx c ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
  refine SepWP.weaken_pre (P' := ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗ ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗ CtxCells maddrs.ctx st.ctx ∗
    (memRegion (s0.sp - 224#64) 80 ∗ stackAt (s0.sp - 80#64) 64 ∗ cells (s0.sp - 48#64) 6 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st)))
    (by unfold StaticFrameA; rw [hCtxCells]; sep_frame) ?_
  clear l1 l2 l3 l4 l5 hCtxCells hSt224
  rcases hWf.initDone_wf with h0 | h1
  · refine SepWP.cut_at_off (mbase 7) (reloc_call_off% amfRelocs "memcpy" - 68#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (reloc_call_off% amfRelocs "memcpy" - 68#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s0.brk) (P_open st.ctx)) hcl0 ?_) ?_)
    · dsimp only [P_open, StackFrameOpen, SavedRegs0, CtxCells]; rw [h0]; (conv => arg 2; simp only [BitVec.reduceSub]); wp_sym_steps; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre (Entails.trans hEnt1 (by dsimp only [P_open]; sep_frame)) (sepWP_lazyInit_05c
        (R_frame := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ StaticFrameA γ maddrs st.liveMap ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗
          ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ MappedSet st.masterDom (OwnedMappedByte st))
        hWords0 hWords hRange hcl1 hPc1 hRun1 hSp1 hSp0 hx20_1 hCs1 hProc1
        fun s2 sec hcl2 hPc2 hRun2 hSp2 hx20_2 hCs2 hProc2 hBrk2 hD2 =>
          sepWP_lazyInit_to_b1_fine hWords0 hWordsSvc hRange hcl2 hInflight hCount hFine hMaStep hPc2 hRun2 hSp2 hSp0 hTp0 hBs0 hx20_2 hCs2 hProc2
            (MallocngMappedDelta.mono (by decide) (by decide) (MallocngMappedDelta.trans hD1 hD2)) ((hBrk2.trans hBrk1) ▸ hWf) h0)
  · refine SepWP.cut_at_off (mbase 7) (words_insn_off% amfWords "cbz" 0 + 4#64)
      (SepWP.mono (sepWP_lift_faultSvcAmf_cl (sepPost (fun s1 =>
        s1.pc = mbase 7 + (words_insn_off% amfWords "cbz" 0 + 4#64) ∧ s1.status = .Running ∧ s1.sp = s0.sp - 80#64 ∧
        s1.readReg64 .x20 = Obj.pageOf maddrs.ctx ∧ Cs21Preserved s0 s1 ∧ MallocngProcPreserved s0 s1 ∧ s1.brk = s0.brk) (P_open st.ctx)) hcl0 ?_) ?_)
    · dsimp only [P_open, StackFrameOpen, SavedRegs0, CtxCells]; rw [h1]; (conv => arg 2; simp only [BitVec.reduceAdd]); wp_sym_steps; wp_done
    · intro s1 P1 hPc1 hRun1 ⟨_, hD1, hcl1, ⟨_, _, hSp1, hx20_1, hCs1, hProc1, hBrk1⟩, hEnt1⟩
      exact SepWP.weaken_pre hEnt1 (sepWP_postInit_01c_fine hWords0 hWordsSvc hRange hcl1 hInflight hCount hFine hMaStep
        hPc1 hRun1 hSp1 hSp0 hTp0 hBs0 hx20_1 hCs1 hProc1 (MallocngMappedDelta.mono (by decide) (by decide) hD1) (hBrk1 ▸ hWf) h1)

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
