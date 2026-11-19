/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Specs
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof

/-!
# Placed `__libc_realloc` (`blk14`) & Exported `"realloc"` (`blk13`) for the Fine Cost Model

- **Role**: `Role::Proof` (untrusted).
- **Key Exports**:
  1. `placed_libcRealloc_fine_ok`: verifies `__libc_realloc` (`blk14`, `800` B stack) over
     `mallocngFineCostModel` / `mallocngFineIface`, parameterized over `LibcMallocImplFineStmt`
     and `LibcFreeFineStmt`.
  2. `fine_realloc_entry_ok`: verifies exported `"realloc"` (`blk13`, `b __libc_realloc`,
     `1024` B stack) against `mallocngModelReallocSpec mallocngFineCostModel mallocngFineIface`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost

/-! ## 1. Budget, Reserve, OOM, and Environment Bridge Helpers -/

private theorem fine_evReqBytes_realloc16_eq (n : Nat) :
    evReqBytes (.realloc 16 0 n) = n := by
  simp [evReqBytes, mallocngAlignedEffSize]

private theorem fine_le_alignedEffSize (al n : Nat) :
    n ≤ mallocngAlignedEffSize al n := by
  unfold mallocngAlignedEffSize
  split <;> omega

private theorem FineStepBound_mono_req {maxMeta r1 r2 : Nat} (h : r1 ≤ r2) :
    FineStepBound maxMeta r1 ≤ FineStepBound maxMeta r2 := by
  unfold FineStepBound
  omega

private theorem fine_stepOom_congr {svc : State → State} {b1 b2 : Nat}
    {s0 sPre sf : State}
    (hb : b1 ≤ b2)
    (hfs : sPre.fs = s0.fs) (htr : sPre.trace = s0.trace)
    (hsig : sPre.sigActions = s0.sigActions) (hperm : sPre.mem.perm = s0.mem.perm)
    (hoom : MallocngStepOomCond svc b1 sPre sf) :
    MallocngStepOomCond svc b2 s0 sf := by
  obtain ⟨hfs1, htr1, hsig1, ivs, hlen, hsum, hcov, hgap⟩ := stepOomCond_mono hb hoom
  refine ⟨hfs1.trans hfs, htr1.trans htr, hsig1.trans hsig, ivs, hlen, hsum, fun a ha => ?_, hgap⟩
  exact (hcov a ha).imp (fun hm => by rwa [← hperm]) id

private theorem fine_pack_postEnv [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt' : FineBudget) (bCoarse' : MallocngBudget)
    (ivs0 ivsf : List (BitVec 64 × Nat)) (st' : MallocngSt) (s0 sf : State)
    (hNoOrph : MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem)
    (hCount : MallocngCountIvsWF bCoarse' ivsf st')
    (hFine : MallocngFineInv bgt' ivsf st')
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart) :
    (MallocngRoTablesA maddrs ∗
     MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
     MallocngRuntime maddrs tp) ⊢
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
        γ maddrs tp brkStart bgt' ivs0 s0 sf := by
  unfold MallocngModelPostEnv MallocngModelEnv
  refine Entails.sepExists_right ivsf (Entails.pure_right hNoOrph ?_)
  refine Entails.pure_right ⟨htp, hbrks⟩ ?_
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  dsimp only [FineCoreModeImpl]
  refine Entails.trans (Entails.of_eq (sepConj_assoc (MallocngRoTablesA maddrs) _ _).symm)
    (sepConj_mono_left ?_)
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right st'
    (Entails.sepExists_right bCoarse' (Entails.pure_right ⟨hCount, hFine⟩ (Entails.refl _)))

private theorem fine_postEnv_congr_state {ro : Bool} {γ : GhostName} {A : MallocngAddrs}
    {tp brkStart : BitVec 64} {bf : FineBudget} {ivs0 : List (BitVec 64 × Nat)}
    {s0 s1 s2 : State}
    (hmem : s2.mem = s1.mem) (hbrk : s2.brk = s1.brk)
    (htp : s2.tpidrEl0 = s1.tpidrEl0) (hbrks : s2.brkStart = s1.brkStart) :
    MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bf ivs0 s0 s1 =
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bf ivs0 s0 s2 := by
  unfold MallocngModelPostEnv MallocngModelEnv
  rw [hmem, hbrk, htp, hbrks]

private theorem fine_tightInit_to_modelInit {ro : Bool} (γ : GhostName) (al : Nat) (q : BitVec 64)
    (sz : Nat) (bs : List (BitVec 8)) :
    ⌜(MallocngTightInitBlock γ (max al 16)).pureWf q (sz, bs)⌝ ∗
    (MallocngTightInitBlock γ (max al 16)).interp q (sz, bs) ⊢
      ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (sz, max al 16, bs)⌝ ∗
      (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (sz, max al 16, bs) := by
  dsimp only [MallocngTightInitBlock, MallocngModelInitBlock]
  rw [mallocngFineModeIface_block_eq]
  rw [Nat.max_eq_left (Nat.le_max_right al 16)]
  exact Entails.refl _

private theorem fineHeap_read_liveUser_unpackTight {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (bgt : FineBudget) (ivs : List (BitVec 64 × Nat))
    (p : BitVec 64) (n a : Nat) :
    FineHeapModeImpl ro γ A tp brkStart brk bgt ivs ∗ MallocngTightBlock γ p n a ⊢
      ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
      ∃∗ g : GroupDesc, ∃∗ idx : Nat, ∃∗ effCost : Nat,
        ⌜MallocngFineInv bgt ivs st ∧
          g ∈ st.groups ∧
          (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p n effCost) ∧
          LiveUserBlockFacts st g idx p n effCost ∧ st.liveMap.ov p ≤ a - 16⌝ ∗
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRestMode ro γ A tp brkStart brk bCoarse ivs st ∗
        MallocngTightBlock γ p n a := by
  unfold FineHeapModeImpl FineCoreModeImpl
  rw [sepConj_assoc, sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_mono fun st => ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_left]
  refine Entails.sepExists_mono fun bCoarse => ?_
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngCountIvsWF bCoarse ivs st ∧ MallocngFineInv bgt ivs st⌝ ∗
      ((MallocngRoTablesA A ∗
        MallocngCoreStModeA ro γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st) ∗
       MallocngRuntime A tp) ∗
      MallocngTightBlock γ p n a by
    generalize (MallocngRoTablesA A) = PRo
    generalize (MallocngCoreStModeA ro γ A brkStart brk bCoarse.liveCost bCoarse.peakCost st) = PSt
    generalize (MallocngRuntime A tp) = PRt
    ac_rfl)) ?_
  refine Entails.pure_left fun ⟨hCount, hFine⟩ => ?_
  unfold MallocngRoTablesA MallocngCoreStModeA MallocngCoreStInflightModeA
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngWF A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      ((MallocngLiveAuth γ st.liveMap ∗ MallocngTightBlock γ p n a) ∗
       (MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
        MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)) by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl)) ?_
  refine Entails.pure_left fun hWf => ?_
  refine Entails.trans (sepConj_mono_left (mallocngTightBlock_lookup γ st.liveMap p n a)) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨_, hLive, hOv⟩ => ?_
  obtain ⟨g, hg, idx, hIdx, effCost, hSlot⟩ := (hWf.liveMap_wf p n).mp hLive
  have hFacts := liveUserBlockFacts_of hWf hg hIdx hSlot
  refine Entails.sepExists_right g (Entails.sepExists_right idx (Entails.sepExists_right effCost ?_))
  refine Entails.pure_right ⟨hFine, hg, ⟨hIdx, hSlot⟩, hFacts, hOv⟩ ?_
  unfold MallocngReadRestMode
  refine Entails.trans ?_
    (Entails.of_eq (show
      ⌜MallocngCountIvsWF bCoarse ivs st ∧
        MallocngWF A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      (MallocngRoTablesAt A ∗
       (MallocngLiveAuth γ st.liveMap ∗
        (A.ctx ↦ₛ st.ctx.toBytes) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
        MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st)) ∗
       MallocngRuntime A tp ∗
       MallocngTightBlock γ p n a) = _ by
      generalize (MallocngRoTablesAt A) = PRo
      generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl))
  exact Entails.pure_right ⟨hCount, hWf⟩ (Entails.of_eq (by ac_rfl))

private theorem fineHeap_read_liveUser_repack {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (bgt : FineBudget) (bCoarse : MallocngBudget)
    (ivs : List (BitVec 64 × Nat)) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs st) :
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
    MallocngReadRestMode ro γ A tp brkStart brk bCoarse ivs st ⊢
      FineHeapModeImpl ro γ A tp brkStart brk bgt ivs := by
  unfold FineHeapModeImpl FineCoreModeImpl MallocngReadRestMode MallocngRoTablesA
    MallocngCoreStModeA MallocngCoreStInflightModeA
  refine Entails.trans (Entails.of_eq (show _ =
      ⌜MallocngCountIvsWF bCoarse ivs st ∧
        MallocngWF A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      MallocngRoTablesAt A ∗
      (MallocngLiveAuth γ st.liveMap ∗
       (A.ctx ↦ₛ st.ctx.toBytes) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
       MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
       MappedSet st.masterDom (OwnedMappedByte st)) ∗
      MallocngRuntime A tp by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl)) ?_
  refine Entails.pure_left fun ⟨hCount, hWf⟩ => ?_
  refine Entails.trans (Entails.of_eq (sepConj_assoc (MallocngRoTablesAt A) _ _).symm)
    (sepConj_mono_left ?_)
  refine sepConj_mono_right ?_
  exact Entails.sepExists_right st (Entails.sepExists_right bCoarse
    (Entails.pure_right ⟨hCount, hFine⟩ (Entails.pure_right hWf (Entails.refl _))))

private theorem fine_repack_read_to_stage4 [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    {p : BitVec 64} {oldSz al : Nat} (origBs tailBs : List (BitVec 8))
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
     MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  have hHeap := fineHeap_read_liveUser_repack (ro := ro) γ maddrs tp brkStart s0.brk bgt bCoarse ivs0 st hFine
  have hEnv : FineHeapModeImpl ro γ maddrs tp brkStart s0.brk bgt ivs0 ⊢
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s := by
    unfold MallocngModelEnv
    rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq, hbrk]
    exact Entails.pure_right ⟨htp, hbrks⟩ (Entails.refl _)
  have hUser := unsplit_user_bytes p origBs tailBs oldSz hTailLen
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) ∗
      MallocngTightBlock γ p oldSz al ∗
      (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
    (Entails.of_eq (by
      show _ = (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) ∗
        MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
      ac_rfl)) ?_
  refine sepConj_mono (Entails.trans hHeap hEnv) (sepConj_mono_right ?_)
  exact Entails.trans (sepConj_mono_left hUser) (Entails.of_eq (by ac_rfl))

/-! ## 2. Internal Placed `__libc_realloc` (`blk14`) Contract & `ENOMEM` / Null Paths -/

/-- Internal `800`-byte stack contract for placed `__libc_realloc(p, newSize)` (`blk14`) on
    `mallocngFineCostModel` / `mallocngFineIface`. -/
def libcReallocFineSpec [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)) (ro : Bool := false) : Spec Unit :=
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map fun (_, _, bs) => bs).getD []).take newSize.toNat
  let ev : AllocEvent := match oldBlk with
    | none => .alloc newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let evRes : AllocEvent := match oldBlk with
    | none => .realloc 16 0 newSize.toNat
    | some (oldSize, align, _) => .realloc align oldSize newSize.toNat
  let outAlign : Nat := match oldBlk with
    | none => 16
    | some (_, align, _) => max align 16
  let bgt' := if ok then mallocngFineCostModel.step ev bgt else bgt
  let stepB := if ok then mallocngFineCostModel.stepReserve evRes bgt
    else mallocngFineCostModel.stepReserve (.alloc 0) bgt
  withCL mmpl {
    pre := fun (_ : Unit) s0 =>
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk⌝ ∗
      stackFrame s0 800 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
      (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk
    post := fun _ s0 sf =>
      ⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
      stackFrame s0 800 ∗
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf ∗
      if ok then
        ∃∗ q : BitVec 64,
          ⌜sf.readReg64 .x0 = q ∧
           (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, outAlign, keptBs)⌝ ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, outAlign, keptBs)
      else
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk
    onOom := fun _ s0 sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝
  }

def LibcReallocFineStmt (ro : Bool := false) : Prop :=
  ∀ [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat)),
    subroutine_ok (mallocngBlockProg mmpl 14 msvc) (mbase 14)
      (libcReallocFineSpec γ tp brkStart p newSize oldBlk bgt ivs0 ro)

private theorem fineEnv_focus_errno {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs : List (BitVec 64 × Nat)) (s : State) :
    MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt ivs s ⊢
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (FineCoreModeImpl ro γ A brkStart s.brk bgt ivs ∗
         ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) := by
  unfold MallocngModelEnv
  refine sepConj_mono_right ?_
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  unfold MallocngRuntime
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun ev => Entails.of_eq ?_
  generalize (FineCoreModeImpl ro γ A brkStart s.brk bgt ivs) = PCore
  ac_rfl

private theorem fineEnv_unfocus_errno {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs : List (BitVec 64 × Nat))
    {s0 sf : State} (errnoVal' : BitVec 32)
    (hPerm : sf.mem.perm = s0.mem.perm) (hBrk : sf.brk = s0.brk)
    (hTp : sf.tpidrEl0 = tp) (hBrkS : sf.brkStart = brkStart) :
    ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
    (FineCoreModeImpl ro γ A brkStart s0.brk bgt ivs ∗
     ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ⊢
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ A tp brkStart bgt ivs s0 sf := by
  have hNoOrph : MallocngNoOrphanMappings ivs ivs s0.mem sf.mem := by
    intro a hm hor
    rw [hPerm] at hm
    exact hor.elim (fun hn => Bool.noConfusion (hn.symm.trans hm)) id
  unfold MallocngModelPostEnv MallocngModelEnv
  refine Entails.sepExists_right ivs (Entails.pure_right hNoOrph (Entails.pure_right ⟨hTp, hBrkS⟩ ?_))
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq, hBrk]
  unfold MallocngRuntime
  refine Entails.trans (Entails.of_eq (show _ =
      FineCoreModeImpl ro γ A brkStart s0.brk bgt ivs ∗
      ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
      ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64) by
    generalize (FineCoreModeImpl ro γ A brkStart s0.brk bgt ivs) = PCore
    ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro errnoVal'))

/-- At `+0x2b8`, calls `___errno_location`, stores `12#32` (`ENOMEM`), sets `x20 := 0#64`,
    and jumps to `+0x294` (`realloc_epilogue_ok`) while preserving `FineCoreImpl` intact. -/
private theorem fine_realloc_enomem_ok [MallocngMultiPlacement] {ro : Bool} {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {Rest : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2b8#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk)
    (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx23 : s.readReg64 .x23 = s0.readReg64 .x23) (hx24 : s.readReg64 .x24 = s0.readReg64 .x24)
    (hx25 : s.readReg64 .x25 = s0.readReg64 .x25) (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hcs : ReallocUntouchedCS s0 s)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s ∗
       Rest)
      (fun sf Pf =>
        sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = 0#64 ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt ivs0 s0 sf ∗ Rest)) oom := by
  intro sp1; have _ := hb
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (fineEnv_focus_errno γ maddrs tp brkStart bgt ivs0 s))))) ?_
  refine SepWP.weaken_pre (P' :=
      ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (ReallocSavedLo s0 sp1 ∗
         (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
          memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
         stackFrameAt sp1 720 ∗
         (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0 ∗
          ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
         Rest))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun ev => Entails.of_eq ?_
      generalize (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0) = PCore
      generalize (s.tpidrEl0 = tp ∧ s.brkStart = brkStart) = PureE
      ac_rfl) ?_
  apply SepWP.pure_elim; rintro ⟨htp, hbrks⟩
  apply SepWP.exists_left; intro errnoVal
  wp_step -- +0x2b8: bl ___errno_location
  have hErr := placed_errnoLocation_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
    (by intro pc; simp) rfl
  refine SepWP.call_subroutine_frame hErr (x := ())
    (F := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
      (ReallocSavedLo s0 sp1 ∗
       (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
        memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
       stackFrameAt sp1 720 ∗
       (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0 ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
       Rest))
    (ret_pc := b + 0x2bc#64)
    (by simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by simp [hrun])
    (by simpa [State.spAligned] using hal)
    (by simp)
    (fun R' hm => by dsimp only [withCL]; rw [emp_sepConj, satisfies_pure_sepConj]; exact ⟨hcl, hm⟩)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s1 hpc1 hrun1 hsp1 hcs1
  dsimp only [withCL]
  refine SepWP.weaken_pre (P' :=
      ⌜(MallocngProcPreserved s s1 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
        s1.readReg64 .x0 = tp - 0xa4#64) ∧
       VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem⌝ ∗
      (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
       (ReallocSavedLo s0 sp1 ∗
        (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
         memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
        stackFrameAt sp1 720 ∗
        (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
        Rest)))
    (by
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hp1, hb1, hm1, hx0_1⟩ => Entails.pure_left fun hcl1 => ?_
      exact Entails.pure_right ⟨⟨⟨hp1.1, hp1.2.1, hp1.2.2.1, hp1.2.2.2.1, hp1.2.2.2.2.1,
        hp1.2.2.2.2.2.1, hp1.2.2.2.2.2.2⟩, hb1, hm1,
        by simpa [htp] using hx0_1⟩, hcl1⟩ (Entails.refl _)) ?_
  apply SepWP.pure_elim; rintro ⟨⟨hproc1, hbrk1, hperm1, hx0_1⟩, hcl1⟩
  have hsp1Eq : s1.sp = s0.sp - 80#64 := by simpa [hsp] using hsp1
  have hal1 : s1.spAligned = true := spAligned_of_sub80 hsp1Eq hsp0
  have _ := hpc1; have _ := hx0_1
  wp_step; wp_step -- +0x2bc: mov x20, #0; +0x2c0: mov w1, #12
  wp_str32_cl m2 hm2Perm hcl1 _hcl2 -- +0x2c4: str w1, [x0]
  wp_step -- +0x2c8: b +0x294
  apply sepWP_bind_state; intro sFin hsFin
  have hpcF : sFin.pc = b + 0x294#64 := by rw [hsFin]; simp
  have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun1]
  have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp1Eq]
  have halF : sFin.spAligned = true := by rw [hsFin]; simpa [State.spAligned] using hal1
  have hPermF : sFin.mem.perm = s0.mem.perm := by
    rw [hsFin]; exact hm2Perm.trans (hperm1.trans hPerm)
  have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; exact hbrk1.trans hbrk
  have hprocF : MallocngProcPreserved s0 sFin := by
    have h01 := mallocngProcPreserved_trans hproc hproc1
    rw [hsFin]
    exact ⟨by simp [h01.1], by simp [h01.2.1], by simp [h01.2.2.1], by simp [h01.2.2.2.1],
           by simp [h01.2.2.2.2.1], by simp [h01.2.2.2.2.2.1], by simp [h01.2.2.2.2.2.2]⟩
  obtain ⟨_, _, _, _, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _hfp1, hv_1⟩ := hcs1
  have hx20F : sFin.readReg64 .x20 = 0#64 := by rw [hsFin]; simp
  have hx23F : sFin.readReg64 .x23 = s0.readReg64 .x23 := by
    rw [hsFin]; simp [Reg.x23] at hx23_1 hx23 ⊢; exact hx23_1.trans hx23
  have hx24F : sFin.readReg64 .x24 = s0.readReg64 .x24 := by
    rw [hsFin]; simp [Reg.x24] at hx24_1 hx24 ⊢; exact hx24_1.trans hx24
  have hx25F : sFin.readReg64 .x25 = s0.readReg64 .x25 := by
    rw [hsFin]; simp [Reg.x25] at hx25_1 hx25 ⊢; exact hx25_1.trans hx25
  have hx26F : sFin.readReg64 .x26 = s0.readReg64 .x26 := by
    rw [hsFin]; simp [Reg.x26] at hx26_1 hx26 ⊢; exact hx26_1.trans hx26
  have hcsF : ReallocUntouchedCS s0 sFin := by
    rw [hsFin]
    exact ⟨by simp [Reg.x27] at hx27_1 ⊢; exact hx27_1.trans hcs.1,
           by simp [Reg.x28] at hx28_1 ⊢; exact hx28_1.trans hcs.2.1,
           by simpa [calleeSavedVRegs] using hv_1.trans hcs.2.2⟩
  clear hsFin
  refine SepWP.weaken_pre (P' :=
      ReallocSavedLo s0 sp1 ∗
      (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
       memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
      stackFrameAt sp1 720 ∗
      (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
        γ maddrs tp brkStart bgt ivs0 s0 sFin ∗ Rest))
    (by
      have htp0 : s0.tpidrEl0 = tp := hproc.2.2.1.symm.trans htp
      have hbrks0 : s0.brkStart = brkStart := hproc.2.2.2.1.symm.trans hbrks
      have hUnf := fineEnv_unfocus_errno (ro := ro) γ maddrs tp brkStart bgt ivs0 (s0 := s0) (sf := sFin)
        12#32 hPermF hbrkF (hprocF.2.2.1.trans htp0) (hprocF.2.2.2.1.trans hbrks0)
      rw [← hbrk] at hUnf
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          ((((tp - 0xa4#64) ↦₃₂ 12#32) ∗
            (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0 ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) ∗ Rest))
        (Entails.of_eq (by
          generalize (FineCoreModeImpl ro γ maddrs brkStart s.brk bgt ivs0) = PCore
          ac_rfl)) ?_
      exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hUnf)))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  refine ⟨by rw [hmemEq]; exact hPermF, hbrkEq.trans hbrkF,
    mallocngProcPreserved_trans hprocF hprocE, hspE, hcsE, hx0E, ?_⟩
  rw [fine_postEnv_congr_state (γ := γ) (A := maddrs) (tp := tp) (brkStart := brkStart)
    (bf := bgt) (ivs0 := ivs0) (s0 := s0) hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1] at hPf
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

set_option maxHeartbeats 400000 in
private theorem fine_realloc_null_path_ok [MallocngMultiPlacement] {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart newSize : BitVec 64)
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 0#64) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let bf := if ok then fineStepAlloc newSize.toNat bgt else bgt
    let stepB := FineStepBound (fineMaxMetaAreas bgt) (if ok then newSize.toNat else 0)
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0)
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
              stackFrame s0 800 ∗
              MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, 16, [])⌝ ∗
                  (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, 16, [])
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗ emp) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf =>
        ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro ok bf stepB; have _ := hb; have _ := hx0; have _ := hx1
  have hspMask0 : s0.sp &&& 15#64 = 0#64 := of_decide_eq_true hsp0
  have hspAlign80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hspMask0; bv_robdd
  refine SepWP.weaken_pre (sepConj_mono_left (stackFrame800_entails_exists_cells s0)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2; apply SepWP.exists_left; intro v3
  apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7
  apply SepWP.exists_left; intro v8; apply SepWP.exists_left; intro v9
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply sepWP_bind_state; intro sTail hsTail
  have hPermTail : sTail.mem.perm = s0.mem.perm := by
    have hmEq : sTail.mem = m2 := by rw [hsTail]; rfl
    rw [hmEq, hm2, hm1]
  have hclTail : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sTail.mem := by
    have hmEq : sTail.mem = m2 := by rw [hsTail]; rfl
    rwa [hmEq]
  have hspTail : sTail.sp = s0.sp := by rw [hsTail]; simp
  have hspAlignTail : sTail.spAligned = true := by
    unfold State.spAligned at hsp0 ⊢; rwa [hspTail]
  have hEnvTail :
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 =
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 sTail := by
    unfold MallocngModelEnv
    have htpT : sTail.tpidrEl0 = s0.tpidrEl0 := by rw [hsTail]; rfl
    have hbrksT : sTail.brkStart = s0.brkStart := by rw [hsTail]; rfl
    have hbrkT : sTail.brk = s0.brk := by rw [hsTail]; rfl
    rw [htpT, hbrksT, hbrkT]
  refine SepWP.weaken_pre (sepConj_mono_left
    (stack80_cells_to_stackFrame800 s0 (s0.readReg64 .x29) (s0.readReg64 .x30)
      v2 v3 (s0.readReg64 .x21) (s0.readReg64 .x22) v6 v7 v8 v9)) ?_
  have hSplit704 : stackFrame s0 800 = (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) := by
    unfold stackFrame
    rw [hspTail, ← stackFrameAt_eq_memRegion s0.sp 800, ← stackFrameAt_eq_memRegion s0.sp 704,
        show (800 : Nat) = 704 + 96 from rfl, stackFrameAt_split s0.sp 704 96]
  rw [hSplit704, hEnvTail]
  have hMalloc := call_placed_libcMallocImpl_fine hImpl (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart bgt ivs0 newSize.toNat (by intro pc; simp) rfl
  have hlrTail : sTail.readReg64 Reg.lr = s0.readReg64 Reg.lr := by rw [hsTail]; simp
  refine SepWP.call_subroutine_frame hMalloc (x := ())
    (F := stackFrameAt (s0.sp - 704#64) 96)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hsTail]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hsTail]; simp [hrun])
    hspAlignTail
    hlrTail
    (fun R' hm => by
      have hx0T : (sTail.readReg64 .x0).toNat = newSize.toNat := by
        rw [hsTail]; simp
      refine Satisfies.mono ?_ hm
      dsimp only [libcMallocImplFineSpec, withCL]
      refine Entails.trans (Q :=
          (stackFrame sTail 704 ∗
           MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 sTail) ∗
          stackFrameAt (s0.sp - 704#64) 96 ∗ R')
        (Entails.of_eq (by
          generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt ivs0 sTail) = PEnv
          ac_rfl)) ?_
      refine sepConj_mono_left ?_
      rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sTail.mem⌝]
      exact Entails.pure_right hclTail (Entails.pure_right hx0T (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  · have hspSf0 : sf.sp = s0.sp := hspSf.trans hspTail
    have hcsSf0 : CalleeSavedPreserved s0 sf := by
      have hcsT : CalleeSavedPreserved s0 sTail := by
        rw [hsTail]
        refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩
      exact CalleeSavedPreserved.trans hcsT hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    dsimp only [libcMallocImplFineSpec, withCL] at hm
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
    obtain ⟨⟨hProcTSf, hDeltaTSf⟩, hm⟩ := hm
    have hProc0T : MallocngProcPreserved s0 sTail := by
      rw [hsTail]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hProc0Sf : MallocngProcPreserved s0 sf := mallocngProcPreserved_trans hProc0T hProcTSf
    have hDelta0Sf : MallocngMappedDelta 16 stepB s0.mem sf.mem := by
      obtain ⟨ivs, hlen, hsum, hcov⟩ := hDeltaTSf
      refine ⟨ivs, hlen, hsum, fun a ha => ?_⟩
      rcases hcov a ha with hmT | hin
      · exact Or.inl (by rwa [← hPermTail])
      · exact Or.inr hin
    have hAcc0Sf : MallocngCallAccounting 16 stepB s0 sf := ⟨hProc0Sf, hDelta0Sf⟩
    by_cases hLeMax : newSize.toNat ≤ MallocngMaxAllocSize
    · have hOkTrue : ok = true := decide_eq_true hLeMax
      simp only [hLeMax, decide_true, hOkTrue, ↓reduceIte] at hAcc0Sf hm ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
      obtain ⟨q, bs, st', bCoarse', hm⟩ := hm
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨⟨hx0Q, htpSf, hbrksSf, hWfQ, hBsLen, hNoOrphT, hCountSt', hFineSt', _⟩, hm⟩ := hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          (MallocngRoTablesA maddrs ∗
           MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
           MallocngRuntime maddrs tp) ∗
          ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q newSize.toNat 0) ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (MallocngRoTablesA maddrs) = PRo
        generalize (MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st') = PCore
        generalize (MallocngRuntime maddrs tp) = PRt
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hNoOrph0 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem := by
        intro a hmA hor0
        rcases hor0 with hnot0 | hin0
        · exact hNoOrphT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoOrphT a hmA (Or.inr hin0)
      have ⟨hPureInit, hEntInit⟩ := mallocBlock_to_initBlock_nil γ q bs newSize.toNat 16 hWfQ hBsLen
      have hPostEnvEnt :
          MallocngRoTablesA maddrs ∗
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
          MallocngRuntime maddrs tp ⊢
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf := by
        dsimp only [bf]; rw [hOkTrue]; simp only [↓reduceIte]
        exact fine_pack_postEnv γ tp brkStart (fineStepAlloc newSize.toNat bgt) bCoarse' ivs0
          (dynamicRootRegions st') st' s0 sf hNoOrph0 hCountSt' hFineSt' htpSf hbrksSf
      have hBlkEnt :
          ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q newSize.toNat 0) ⊢
          ∃∗ q' : BitVec 64,
            ⌜sf.readReg64 .x0 = q' ∧
             (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q' (newSize.toNat, 16, [])⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q' (newSize.toNat, 16, []) := by
        have hModel := fine_tightInit_to_modelInit (ro := ro) γ 16 q newSize.toNat []
        have hMax16 : max 16 16 = 16 := rfl
        rw [hMax16] at hModel
        have h1 : ((q ↦ₛ bs) ∗ MallocngBlockTokenK γ q newSize.toNat 0) ⊢
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, 16, [])⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, 16, []) :=
          Entails.trans (Entails.pure_right hPureInit hEntInit) hModel
        refine Entails.trans h1 (Entails.sepExists_right q ?_)
        exact Entails.pure_left fun hPM => Entails.pure_right ⟨hx0Q, hPM⟩ (Entails.refl _)
      rw [← hSplit704,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 _ s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right (sepConj_mono hPostEnvEnt (sepConj_mono_left hBlkEnt))
    · have hOkFalse : ok = false := decide_eq_false hLeMax
      simp only [hLeMax, decide_false, hOkFalse, Bool.false_eq_true, ↓reduceIte] at hAcc0Sf hm ⊢
      rw [← sepConj_assoc (stackFrame sTail 704) ⌜_⌝,
          sepConj_comm (stackFrame sTail 704) ⌜_⌝,
          sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      obtain ⟨hx0_0, hm⟩ := hm
      have hm' : sf.mem ⊨
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
          (stackFrame sTail 704 ∗ stackFrameAt (s0.sp - 704#64) 96) ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt ivs0 sTail sf ∗ R := by
        refine Satisfies.mono (Entails.of_eq ?_) hm
        generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
          γ maddrs tp brkStart bgt ivs0 sTail sf) = PPost
        ac_rfl
      rw [← hSplit704, satisfies_pure_sepConj] at hm'
      obtain ⟨hclSf, hm'⟩ := hm'
      have hPostCongr :
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt ivs0 sTail sf ⊢
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf ivs0 s0 sf := by
        dsimp only [bf]; rw [hOkFalse]; simp only [Bool.false_eq_true, ↓reduceIte]
        unfold MallocngModelPostEnv
        refine Entails.sepExists_mono fun ivsf => Entails.pure_left fun hNoT => ?_
        refine Entails.pure_right (fun a hmA hor0 => ?_) (Entails.refl _)
        rcases hor0 with hnot0 | hin0
        · exact hNoT a hmA (Or.inl (by rwa [hPermTail]))
        · exact hNoT a hmA (Or.inr hin0)
      rw [← hSplit704, sepConj_emp,
          sepConj_comm (_ : SepProp) ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝,
          sepConj_assoc ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ _ R,
          sepConj_assoc ⌜MallocngCallAccounting 16 _ s0 sf⌝ _ R,
          sepConj_assoc (stackFrame s0 800) _ R,
          sepConj_assoc (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf ivs0 s0 sf) _ R]
      refine Satisfies.mono ?_ hm'
      refine Entails.pure_right hclSf (Entails.pure_right hAcc0Sf ?_)
      exact sepConj_mono_right
        (sepConj_mono hPostCongr (Entails.pure_right hx0_0 (Entails.refl R)))
  · have hOom' := Satisfies.drop_mid hOom
    dsimp only [libcMallocImplFineSpec, withCL] at hOom' ⊢
    rw [satisfies_pure_sepConj] at hOom' ⊢
    obtain ⟨hOomT, hR'⟩ := hOom'
    refine ⟨?_, hR'⟩
    exact fine_stepOom_congr
      (Nat.le_refl _)
      (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) (by rw [hsTail]; rfl) hPermTail hOomT

/-! ## 3. Stage 4 Out-of-Place `malloc + memcpy + free` (`+0x260` → `ret`) -/

private theorem fineInv_b1_to_realloc {inAlign oldSz newSz : Nat} {bgt : FineBudget}
    {ivs : List (BitVec 64 × Nat)} {st : MallocngSt}
    (h : MallocngFineInv (fineStepFree oldSz (fineStepAlloc newSz bgt)) ivs st) :
    MallocngFineInv (fineStepRealloc inAlign oldSz newSz bgt) ivs st := by
  unfold fineStepRealloc
  split
  · refine h.mono ?_ ?_ (fun _ _ => Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    · refine ⟨h.budget_inv.live_len, h.budget_inv.peak_len, vec48Of_length _, h.budget_inv.exc_len,
        h.budget_inv.live_le_peak, fun sc hsc => ?_, h.budget_inv.live63Bytes_le,
        h.budget_inv.live63Count_le⟩
      rw [vec48Of_getD]; simp only [hsc, ↓reduceIte]
      split
      · exact Nat.max_le.mpr ⟨h.budget_inv.realloc_le_peak sc hsc, h.budget_inv.live_le_peak sc hsc⟩
      · exact h.budget_inv.realloc_le_peak sc hsc
    · refine ⟨fun _ _ => Nat.le_refl _, fun sc hsc => ?_, fun _ _ => Nat.le_refl _,
        Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
      rw [vec48Of_getD]; simp only [hsc, ↓reduceIte]
      split
      · exact Nat.le_max_left _ _
      · exact Nat.le_refl _
  · exact h

private theorem fineHeap_b1_to_realloc {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64) (inAlign oldSz newSz : Nat) (bgt : FineBudget)
    (ivs : List (BitVec 64 × Nat)) :
    FineHeapModeImpl ro γ A tp brkStart brk (fineStepFree oldSz (fineStepAlloc newSz bgt)) ivs ⊢
      FineHeapModeImpl ro γ A tp brkStart brk (fineStepRealloc inAlign oldSz newSz bgt) ivs := by
  unfold FineHeapModeImpl FineCoreModeImpl
  refine sepConj_mono_left (sepConj_mono_right ?_)
  refine Entails.sepExists_mono fun st => Entails.sepExists_mono fun bCoarse => ?_
  exact sepConj_mono_left (Entails.pure_mono fun ⟨hC, hF⟩ => ⟨hC, fineInv_b1_to_realloc hF⟩)

private theorem fine_s4_free_ok [MallocngMultiPlacement] {ro : Bool}
    (hFree : LibcFreeFineStmt ro) {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 ivs1 : List (BitVec 64 × Nat))
    (s0 s3 : State) {p q : BitVec 64} {oldSz newSz inAlign : Nat} (origBs : List (BitVec 8))
    {Frame : SepProp}
    (hpNe : p ≠ 0#64) (hqNe : q ≠ 0#64) (hq16 : 16 ∣ q.toNat) (hq48 : q.toNat + newSz ≤ 2 ^ 48)
    (hpc3 : s3.pc = b + 0x284#64) (hrun3 : s3.status = .Running)
    (hsp3Eq : s3.sp = s0.sp - 80#64) (hal3 : s3.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19_s3 : s3.readReg64 .x19 = p) (hx20_s3 : s3.readReg64 .x20 = q)
    (hcs3 : ReallocUntouchedCS s0 s3) (hcl3 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem)
    (hProc03 : MallocngProcPreserved s0 s3)
    (hDelta03 : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bgt) newSz) s0.mem s3.mem)
    (hNoOrph03 : MallocngNoOrphanMappings ivs0 ivs1 s0.mem s3.mem) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf1 := fineStepAlloc newSz bgt
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let stepB := FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s3
      (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf1 ivs1 s3 ∗
       MallocngTightBlock γ p oldSz al ∗ memRegion p oldSz ∗
       stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
       MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
      (fun sf Pf =>
        ∃ q' : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q' ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q' (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q' (newSz, al, keptBs) ∗ Frame))
      (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro sp1 al bf1 bf stepB keptBs; have _ := hb; have _ := hpc3; have _ := hx19_s3
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  wp_step; wp_step
  apply sepWP_bind_state; intro s4 hs4
  have hsp4Eq : s4.sp = sp1 := by rw [hs4]; simpa using hsp3Eq
  have hmem4Eq : s4.mem = s3.mem := by rw [hs4]; rfl
  have hFreeCall := call_placed_libcFree_fine hFree (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart p inAlign oldSz bf1 ivs1 (by intro pc; simp) rfl
  have hEnvS4 :
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf1 ivs1 s3 =
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf1 ivs1 s4 := by
    rw [hs4]; rfl
  have hSf272 : stackFrameAt sp1 720 = (stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) := by
    rw [stackFrameAt_720_split sp1 272 448 (by decide),
        ← stackFrame_eq_stackFrameAt_720 272 (by decide) hsp4Eq]
  refine SepWP.call_subroutine_frame hFreeCall (x := ())
    (F := stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x28c#64)
    (by rw [hs4]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs4]; simp [hrun3]) (by rw [hs4]; simpa [State.spAligned] using hal3)
    (by rw [hs4]; simp)
    (fun R' hm => by
      dsimp only [libcFreeFineSpec, withCL, al]; simp only [hpNe, ↓reduceIte]
      have hx0_s4 : s4.readReg64 .x0 = p := by rw [hs4]; simp
      have hcl_s4 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem := by rwa [hmem4Eq]
      refine Satisfies.mono ?_ hm; rw [hSf272, hEnvS4]
      refine Entails.trans (Q :=
          (stackFrame s4 272 ∗
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf1 ivs1 s4 ∗
            (MallocngTightBlock γ p oldSz (max inAlign 16) ∗ memRegion p oldSz)) ∗
          (stackFrameAt (sp1 - 272#64) 448 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           MallocngTightBlock γ q newSz (max inAlign 16) ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          dsimp only [al]
          generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf1 ivs1 s4) = PEnv4
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s4.mem⌝]
      exact Entails.pure_right hcl_s4 (Entails.pure_right hx0_s4 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s5 hpc5 hrun5 hsp5 hcs45
  dsimp only [libcFreeFineSpec, withCL]
  have hpBeqF : (p == 0#64) = false := beq_false_of_ne hpNe
  rw [hpBeqF]; simp only [Bool.false_eq_true, ↓reduceIte]
  let b1 := fineStepFree oldSz bf1
  have hsp5Eq : s5.sp = sp1 := by simpa [hsp4Eq] using hsp5
  have hal5 : s5.spAligned = true := spAligned_of_sub80 hsp5Eq hsp0
  refine SepWP.weaken_pre (P' :=
      ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
      ((((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) ∗
       ReallocSavedLo s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart b1 ivs1 s4 s5 ∗
       MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
       memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
    (by
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s5.mem⌝ ∗
          ((stackFrame s4 272 ∗ stackFrameAt (sp1 - 272#64) 448) ∗
           ReallocSavedHi s0 sp1 ∗ ReallocSavedLo s0 sp1 ∗
           MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart b1 ivs1 s4 s5 ∗
           MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
           memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
        (Entails.of_eq (by
          dsimp only [b1]
          generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart (fineStepFree oldSz bf1) ivs1 s4 s5) = PPost5
          generalize (MallocngProcPreserved s4 s5 ∧ MallocngMappedDelta 0 0 s4.mem s5.mem) = Pure5
          ac_rfl)) ?_
      refine Entails.pure_left fun hP5 => Entails.pure_left fun _hcl5 => Entails.pure_right hP5 ?_
      rw [hSf272.symm, ← reallocSavedHi_eq s0]
      exact Entails.of_eq (by
        generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
          γ maddrs tp brkStart b1 ivs1 s4 s5) = PPost5
        ac_rfl)) ?_
  apply SepWP.pure_elim; rintro ⟨hProc45, hDelta45⟩
  have _ := hpc5; wp_step; wp_step
  obtain ⟨_, hx20_5, _, _, _, _, _, _, hx27_5, hx28_5, _hfp5, hv_5⟩ := hcs45
  have hx20_s5 : s5.readReg64 .x20 = q := by
    rw [hs4] at hx20_5; simp [Reg.x20] at hx20_5 ⊢; exact hx20_5.trans hx20_s3
  apply sepWP_bind_state; intro sFin hsFin
  have hpcF : sFin.pc = b + 0x294#64 := by rw [hsFin]; simp
  have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun5]
  have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp5Eq, sp1]
  have halF : sFin.spAligned = true := by rw [hsFin]; simpa [State.spAligned] using hal5
  have hx20F : sFin.readReg64 .x20 = q := by rw [hsFin]; simp [hx20_s5]
  have hx23F : sFin.readReg64 .x23 = s0.readReg64 .x23 := by rw [hsFin]; simp
  have hx24F : sFin.readReg64 .x24 = s0.readReg64 .x24 := by rw [hsFin]; simp
  have hx25F : sFin.readReg64 .x25 = s0.readReg64 .x25 := by rw [hsFin]; simp
  have hx26F : sFin.readReg64 .x26 = s0.readReg64 .x26 := by rw [hsFin]; simp
  have hcsF : ReallocUntouchedCS s0 sFin := by
    rw [hs4] at hx27_5 hx28_5 hv_5; rw [hsFin]
    exact ⟨by simp [Reg.x27] at hx27_5 ⊢; exact hx27_5.trans hcs3.1,
           by simp [Reg.x28] at hx28_5 ⊢; exact hx28_5.trans hcs3.2.1,
           by simpa [calleeSavedVRegs] using hv_5.trans hcs3.2.2⟩
  have hmemF : sFin.mem = s5.mem := by rw [hsFin]; rfl
  have hbrkF : sFin.brk = s5.brk := by rw [hsFin]; rfl
  have hProc35 : MallocngProcPreserved s3 s5 := by rw [hs4] at hProc45; exact hProc45
  have hProc05 : MallocngProcPreserved s0 s5 := mallocngProcPreserved_trans hProc03 hProc35
  have hProc0F : MallocngProcPreserved s0 sFin := by
    rw [hsFin]
    exact ⟨by simp [hProc05.1], by simp [hProc05.2.1], by simp [hProc05.2.2.1],
           by simp [hProc05.2.2.2.1], by simp [hProc05.2.2.2.2.1],
           by simp [hProc05.2.2.2.2.2.1], by simp [hProc05.2.2.2.2.2.2]⟩
  clear hsFin; rw [hmem4Eq] at hDelta45
  have hPostTrans :
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart b1 ivs1 s4 s5 ⊢
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf ivs0 s0 sFin := by
    unfold MallocngModelPostEnv
    refine Entails.sepExists_elim fun ivsf => Entails.pure_left fun hNoOrph45 => ?_
    rw [hmem4Eq] at hNoOrph45
    have hNoOrph05 : MallocngNoOrphanMappings ivs0 ivsf s0.mem sFin.mem := by
      rw [hmemF]; exact noOrphanMappings_chain_alloc_free hNoOrph03 rfl hDelta45 hNoOrph45
    refine Entails.sepExists_right ivsf (Entails.pure_right hNoOrph05 ?_)
    unfold MallocngModelEnv
    rw [hbrkF, show sFin.tpidrEl0 = s5.tpidrEl0 from hProc0F.2.2.1.trans hProc05.2.2.1.symm,
        show sFin.brkStart = s5.brkStart from hProc0F.2.2.2.1.trans hProc05.2.2.2.1.symm]
    simp only [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
    exact sepConj_mono_right (fineHeap_b1_to_realloc (ro := ro) γ maddrs tp brkStart s5.brk inAlign oldSz newSz bgt ivsf)
  have hInitInterp : (MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
      memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ⊢
      ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
      (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) :=
    Entails.trans
      (Entails.pure_right ⟨hqNe, hq16, by omega, by simp [keptBs]; omega⟩ (Entails.refl _))
      (fine_tightInit_to_modelInit γ inAlign q newSz keptBs)
  refine SepWP.weaken_pre (P' :=
      ReallocSavedLo s0 sp1 ∗
      (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
       memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
      stackFrameAt sp1 720 ∗
      (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf ivs0 s0 sFin ∗
       ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
       (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) ∗ Frame))
    (by
      rw [← reallocSavedHi_eq s0]
      refine Entails.trans (sepConj_mono_left (reallocSavedHi_entails_memRegions s0 sp1)) ?_
      refine Entails.trans (Q := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart b1 ivs1 s4 s5 ∗
           ((MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
             memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length)) ∗ Frame)))
        (Entails.of_eq (by
          generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart b1 ivs1 s4 s5) = PPost5
          ac_rfl)) ?_
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hPostTrans ?_)))
      exact Entails.trans (sepConj_mono_left hInitInterp) (Entails.of_eq (by ac_rfl))) ?_
  refine SepWP.mono (realloc_epilogue_ok hb hpcF hrunF hspF halF hsp0 hx20F
    hx23F hx24F hx25F hx26F hcsF) ?_
  intro sf Pf _ _ ⟨hmemEq, hbrkEq, hprocE, hspE, hcsE, hx0E, hPf⟩
  have hDelta0Sf : MallocngMappedDelta 16 stepB s0.mem sf.mem := by
    rw [hmemEq, hmemF]
    exact mappedDelta_mono_bounds (Nat.le_refl 16)
      (FineStepBound_mono_req (fine_le_alignedEffSize inAlign newSz))
      (mappedDelta_trans_zero_right hDelta03 hDelta45)
  refine ⟨q, ⟨mallocngProcPreserved_trans hProc0F hprocE, hDelta0Sf⟩, hspE, hcsE, hx0E, ?_⟩
  rw [fine_postEnv_congr_state (γ := γ) (A := maddrs)
    (tp := tp) (brkStart := brkStart) (bf := bf) (ivs0 := ivs0) (s0 := s0)
    hmemEq hbrkEq hprocE.2.2.1 hprocE.2.2.2.1] at hPf
  dsimp only [MallocngModelInitBlock] at hPf ⊢
  exact Entails.trans hPf (Entails.of_eq (by ac_rfl))

private theorem fine_pack_env [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt' : FineBudget) (bCoarse' : MallocngBudget) (st' : MallocngSt) (sf : State)
    (htp : sf.tpidrEl0 = tp) (hbrks : sf.brkStart = brkStart)
    (hCount : MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st')
    (hFine : MallocngFineInv bgt' (dynamicRootRegions st') st') :
    (MallocngRoTablesA maddrs ∗
     MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
     MallocngRuntime maddrs tp) ⊢
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
        γ maddrs tp brkStart bgt' (dynamicRootRegions st') sf := by
  unfold MallocngModelEnv
  refine Entails.pure_right ⟨htp, hbrks⟩ ?_
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  dsimp only [FineCoreModeImpl]
  refine Entails.trans (Entails.of_eq (sepConj_assoc (MallocngRoTablesA maddrs) _ _).symm)
    (sepConj_mono_left (sepConj_mono_right ?_))
  exact Entails.sepExists_right st'
    (Entails.sepExists_right bCoarse' (Entails.pure_right ⟨hCount, hFine⟩ (Entails.refl _)))

set_option maxHeartbeats 400000 in
/-- Out-of-place `malloc(newSz) + memcpy(q, p, min oldSz newSz) + free(p)` (`+0x260` → `ret`). -/
private theorem fine_stage4_oop_ok [MallocngMultiPlacement] {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {p : BitVec 64} {oldSz newSz inAlign : Nat} (origBs : List (BitVec 8))
    {Frame : SepProp}
    (hpNe : p ≠ 0#64) (hpOld48 : p.toNat + oldSz ≤ 2 ^ 48)
    (hOrigLe : origBs.length ≤ oldSz) (hNewMax : newSz ≤ MallocngMaxAllocSize)
    (hpc : s.pc = b + 0x260#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hproc : MallocngProcPreserved s0 s)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = p) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx23 : s.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hcs : ReallocUntouchedCS s0 s) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let stepB := FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) ∗
            Frame))
      (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro sp1 al bf stepB keptBs; have _ := hb
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxLt64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
  have hNewBvNat : (BitVec.ofNat 64 newSz).toNat = newSz := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (by
      rw [← sepConj_assoc]
      exact sepConj_mono_left (shrink_init_prefix p origBs oldSz newSz hOrigLe hpOld48))))))) ?_
  have _ := hx21
  wp_step; wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hsp1Eq : s1.sp = sp1 := by rw [hs1]; simpa using hsp
  have hmem1Eq : s1.mem = s.mem := by rw [hs1]; rfl
  have hMalloc := call_placed_libcMallocImpl_fine hImpl (P := blkPC_b14.rebase b (fun _ => none))
    γ tp brkStart bgt ivs0 newSz (by intro pc; simp) rfl
  have hEnvS1 :
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s =
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s1 := by
    rw [hs1]; rfl
  have hSf704 : stackFrameAt sp1 720 = (stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) := by
    rw [stackFrameAt_720_split sp1 704 16 (by decide),
        ← stackFrame_eq_stackFrameAt_720 704 (by decide) hsp1Eq]
  refine SepWP.call_subroutine_frame hMalloc (x := ())
    (F := stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ keptBs) ∗
      memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame)
    (ret_pc := b + 0x268#64)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun]) (by rw [hs1]; simpa [State.spAligned] using hal)
    (by rw [hs1]; simp)
    (fun R' hm => by
      dsimp only [libcMallocImplFineSpec, withCL]
      have hx0_s1 : (s1.readReg64 .x0).toNat = newSz := by
        rw [hs1]; simp only [wp_norm, arm64_norm, hNewBvNat]
      have hcl_s1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rwa [hmem1Eq]
      refine Satisfies.mono ?_ hm; rw [hSf704, hEnvS1]
      refine Entails.trans (Q :=
          (stackFrame s1 704 ∗
           MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s1) ∗
          (stackFrameAt (sp1 - 704#64) 16 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ keptBs) ∗
           memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame) ∗ R')
        (Entails.of_eq (by
          dsimp only [keptBs]
          generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bgt ivs0 s1) = PEnv
          ac_rfl)) ?_
      refine sepConj_mono_left ?_; rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem⌝]
      exact Entails.pure_right hcl_s1 (Entails.pure_right hx0_s1 (Entails.refl _)))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    ?_
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho
      dsimp only [libcMallocImplFineSpec, withCL] at ho'; rw [satisfies_pure_sepConj] at ho' ⊢
      obtain ⟨ho1, hR'⟩ := ho'; simp only [hNewMax, decide_true, ↓reduceIte] at ho1
      have hfs1 : s1.fs = s0.fs := by rw [hs1]; exact hproc.1
      have htr1 : s1.trace = s0.trace := by rw [hs1]; exact hproc.2.1
      have hsig1 : s1.sigActions = s0.sigActions := by rw [hs1]; exact hproc.2.2.2.2.2.2
      have hp1 : s1.mem.perm = s0.mem.perm := by rw [hmem1Eq]; exact hPerm
      exact ⟨fine_stepOom_congr
        (FineStepBound_mono_req (fine_le_alignedEffSize inAlign newSz))
        hfs1 htr1 hsig1 hp1 ho1, hR'⟩)
  intro s2 hpc2 hrun2 hsp2 hcs12
  let bf1 := fineStepAlloc newSz bgt
  dsimp only [libcMallocImplFineSpec, withCL]; simp only [hNewMax, decide_true, ↓reduceIte]
  refine SepWP.weaken_pre (P' :=
      ∃∗ q : BitVec 64, ∃∗ bsNew : List (BitVec 8), ∃∗ st' : MallocngSt,
        ⌜MallocngProcPreserved s1 s2 ∧
         MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bgt) newSz) s1.mem s2.mem ∧
         VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem ∧
         s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
         MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
         MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem⌝ ∗
        (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
           γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
         memRegion q newSz ∗ MallocngTightBlock γ q newSz al ∗
         stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
         MallocngTightBlock γ p oldSz al ∗
         (p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
         Frame))
    (by
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine Entails.sepExists_mono fun q => Entails.sepExists_mono fun bsNew =>
        Entails.sepExists_mono fun st' => Entails.sepExists_elim fun bCoarse' => ?_
      have hPackEnv := fine_pack_env (ro := ro) γ tp brkStart bf1 bCoarse' st' s2
      refine Entails.trans (Q :=
          ⌜MallocngProcPreserved s1 s2 ∧
            MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bgt) newSz) s1.mem s2.mem⌝ ∗
          ⌜s2.readReg64 .x0 = q ∧ s2.tpidrEl0 = tp ∧ s2.brkStart = brkStart ∧
            MallocngBlockWf q newSz ∧ bsNew.length = newSz ∧
            MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s1.mem s2.mem ∧
            MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
            MallocngFineInv bf1 (dynamicRootRegions st') st' ∧
            ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
              g'.slots[idx]'hIdx = .liveUser q newSz (max newSz MallocngMinBlockCost) ∧
              q.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
              (g'.isMmapped = true → bsNew = List.replicate newSz 0#8)⌝ ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2.mem⌝ ∗
          ((MallocngRoTablesA maddrs ∗
            MallocngCoreStModeA ro γ maddrs brkStart s2.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
            MallocngRuntime maddrs tp) ∗ (q ↦ₛ bsNew) ∗ MallocngBlockTokenK γ q newSz 0 ∗
           (stackFrame s1 704 ∗ stackFrameAt (sp1 - 704#64) 16) ∗
           ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
           MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ keptBs) ∗
           memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗ Frame))
        (Entails.of_eq (by
          dsimp only [bf1, keptBs]
          generalize (MallocngRoTablesA maddrs) = PRo
          generalize (MallocngCoreStModeA ro γ maddrs brkStart s2.brk bCoarse'.liveCost bCoarse'.peakCost st') = PSt
          generalize (MallocngRuntime maddrs tp) = PRt
          ac_rfl)) ?_
      refine Entails.pure_left fun ⟨hProc2, hDelta2⟩ =>
        Entails.pure_left fun ⟨hx0_2, htp2, hbrks2, hWfQ, hbsLen, hNoOrph2, hCnt2, hFine2, _⟩ =>
        Entails.pure_left fun hcl2 => ?_
      refine Entails.pure_right ⟨hProc2, hDelta2, hcl2, hx0_2,
        htp2, hbrks2, hWfQ, hbsLen, hNoOrph2⟩ ?_
      rw [hSf704.symm]
      have hRegQ' : (q ↦ₛ bsNew) ⊢ memRegion q newSz := by
        rw [← hbsLen]; exact (IsBlock.pointsToBytes q bsNew).entails_memRegion
      exact sepConj_mono (hPackEnv htp2 hbrks2 hCnt2 hFine2)
        (sepConj_mono hRegQ'
          (sepConj_mono_left (mallocngBlockTokenK_to_tight γ q newSz 0 al (Nat.zero_le _))))) ?_
  apply SepWP.exists_left; intro q; apply SepWP.exists_left; intro _bsNew
  apply SepWP.exists_left; intro st'; apply SepWP.pure_elim
  rintro ⟨hProc12, hDelta12, hcl2, hx0_2, _htp2, _hbrks2, ⟨hqNe, hq16, hq48, _⟩, _hbsLen, hNoOrph12⟩
  have hsp2Eq : s2.sp = sp1 := by simpa [hsp1Eq] using hsp2
  have hal2 : s2.spAligned = true := spAligned_of_sub80 hsp2Eq hsp0
  obtain ⟨hx19_2, _, hx21_2, _, hx23_2, _, _, _, hx27_2, hx28_2, _hfp2, hv_2⟩ := hcs12
  have hx19_s2 : s2.readReg64 .x19 = p := by
    rw [hs1] at hx19_2; simp [Reg.x19] at hx19_2 ⊢; exact hx19_2.trans hx19
  have hx21_s2 : s2.readReg64 .x21 = BitVec.ofNat 64 newSz := by
    rw [hs1] at hx21_2; simp [Reg.x21] at hx21_2 ⊢; exact hx21_2.trans hx21
  have hx23_s2 : s2.readReg64 .x23 = p + BitVec.ofNat 64 oldSz := by
    rw [hs1] at hx23_2; simp [Reg.x23] at hx23_2 ⊢; exact hx23_2.trans hx23
  have _ := hpc2; have _ := hx19_s2; have _ := hx21_s2; have _ := hx23_s2
  wp_step; wp_step
  wp_if hzQ
  · exact absurd hzQ hqNe
  · wp_step; wp_step; wp_step; wp_step; wp_step
    let copyLen := min oldSz newSz
    have hKeptLenLe : keptBs.length ≤ copyLen := by
      dsimp only [keptBs, copyLen]; rw [List.length_take]; omega
    refine SepWP.weaken_pre (P' :=
        ∃∗ dstBs : List (BitVec 8), ∃∗ midBs : List (BitVec 8),
          ⌜dstBs.length = copyLen ∧ (keptBs ++ midBs).length = copyLen⌝ ∗
          (((q ↦ₛ dstBs) ∗ (p ↦ₛ (keptBs ++ midBs))) ∗
           (memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
            memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen) ∗
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            MallocngTightBlock γ q newSz al ∗
            stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            MallocngTightBlock γ p oldSz al ∗ Frame)))
      (by
        have hPrep := copyPrep_entails p q keptBs oldSz newSz copyLen
          hKeptLenLe (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega) (by omega)
        refine Entails.trans (Q :=
            ((p ↦ₛ keptBs) ∗ memRegion (p + BitVec.ofNat 64 keptBs.length) (oldSz - keptBs.length) ∗
              memRegion q newSz) ∗
            (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
               γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
             MallocngTightBlock γ p oldSz al ∗ Frame))
          (Entails.of_eq (by
            generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hPrep) ?_
        simp only [sepExists_sepConj_left]
        refine Entails.sepExists_mono fun dstBs => Entails.sepExists_mono fun midBs => Entails.of_eq ?_
        generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
          γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
        generalize (dstBs.length = copyLen ∧ (keptBs ++ midBs).length = copyLen) = PurePrep
        ac_rfl) ?_
    apply SepWP.exists_left; intro dstBs; apply SepWP.exists_left; intro midBs
    apply SepWP.pure_elim; rintro ⟨hDstLen, hMidLen⟩
    have hMemcpy := placed_memcpy_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
      q p dstBs (keptBs ++ midBs) copyLen hDstLen hMidLen (by dsimp only [copyLen]; omega)
      (by intro pc; simp) rfl
    have hSubOld : (p + BitVec.ofNat 64 oldSz) - p = BitVec.ofNat 64 oldSz := by bv_lin
    have hOldBvNat : (BitVec.ofNat 64 oldSz).toNat = oldSz := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    apply sepWP_bind_state; intro s2c hs2c
    refine SepWP.call_subroutine_frame hMemcpy (x := ())
      (F := memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
            memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen) ∗
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
            MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            MallocngTightBlock γ p oldSz al ∗ Frame)
      (ret_pc := b + 0x284#64)
      (by rw [hs2c]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
      (by rw [hs2c]; simp [hrun2]) (by rw [hs2c]; simpa [State.spAligned] using hal2)
      (by rw [hs2c]; simp)
      (fun R' hm => by
        dsimp only [withCL]
        have hcl_2c : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2c.mem := by rw [hs2c]; exact hcl2
        have hArgs : s2c.readReg64 .x0 = q ∧ s2c.readReg64 .x1 = p ∧ (s2c.readReg64 .x2).toNat = copyLen := by
          rw [hs2c]; refine ⟨by simp [hx0_2], by simp, ?_⟩
          simp only [wp_norm, arm64_norm, hSubOld]; rw [ule_ite_toNat_eq_min, hOldBvNat, hNewBvNat]
        rw [sepConj_assoc] at hm
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s2c.mem⌝]
        exact Entails.pure_right hcl_2c (Entails.pure_right hArgs (Entails.of_eq (by ac_rfl))))
      (fun _ _ _ hp => not_satisfies_false_sepConj hp)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      ?_
      (fun _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
    intro s3 hpc3 hrun3 hsp3 hcs23
    dsimp only [withCL]
    refine SepWP.weaken_pre (P' :=
        ⌜(MallocngProcPreserved s2 s3 ∧ s3.brk = s2.brk ∧ s3.mem.perm = s2.mem.perm) ∧
         VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem⌝ ∗
        (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
           γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 ∗
         MallocngTightBlock γ p oldSz al ∗ memRegion p oldSz ∗
         stackFrameAt sp1 720 ∗ ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
         MallocngTightBlock γ q newSz al ∗ (q ↦ₛ keptBs) ∗
         memRegion (q + BitVec.ofNat 64 keptBs.length) (newSz - keptBs.length) ∗ Frame))
      (by
        have hFin := copyFinish_entails p q keptBs midBs oldSz newSz copyLen
          hMidLen (Nat.min_le_left _ _) (Nat.min_le_right _ _) (by omega) (by omega)
        refine Entails.trans (Q :=
            ⌜MallocngProcPreserved s2c s3 ∧ s3.brk = s2c.brk ∧
              s3.mem.perm = s2c.mem.perm ∧ s3.readReg64 .x0 = q⌝ ∗
            ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s3.mem⌝ ∗
            (((q ↦ₛ (keptBs ++ midBs)) ∗ (p ↦ₛ (keptBs ++ midBs)) ∗
              memRegion (p + BitVec.ofNat 64 copyLen) (oldSz - copyLen) ∗
              memRegion (q + BitVec.ofNat 64 copyLen) (newSz - copyLen)) ∗
             MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
               γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 ∗
             MallocngTightBlock γ q newSz al ∗ stackFrameAt sp1 720 ∗
             ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
             MallocngTightBlock γ p oldSz al ∗ Frame))
          (Entails.of_eq (by
            generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2) = PEnv2
            generalize (MallocngProcPreserved s2c s3 ∧ s3.brk = s2c.brk ∧
              s3.mem.perm = s2c.mem.perm ∧ s3.readReg64 .x0 = q) = Pure3
            ac_rfl)) ?_
        refine Entails.pure_left fun ⟨hp3, hbrk3, hperm3, _⟩ => Entails.pure_left fun hcl3 => ?_
        have hp3' : MallocngProcPreserved s2 s3 := by rw [hs2c] at hp3; exact hp3
        have hbrk3' : s3.brk = s2.brk := by rw [hs2c] at hbrk3; exact hbrk3
        have hperm3' : s3.mem.perm = s2.mem.perm := by rw [hs2c] at hperm3; exact hperm3
        have hEnv23 :
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s2 =
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3 := by
          unfold MallocngModelEnv; rw [hbrk3', hp3'.2.2.1, hp3'.2.2.2.1]
        rw [hEnv23]
        refine Entails.pure_right ⟨⟨hp3', hbrk3', hperm3'⟩, hcl3⟩ ?_
        refine Entails.trans (sepConj_mono_left hFin) ?_
        exact Entails.of_eq (by
          generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf1 (dynamicRootRegions st') s3) = PEnv3
          ac_rfl)) ?_
    apply SepWP.pure_elim; rintro ⟨⟨hProc23, _hbrk23, hperm23⟩, hcl3⟩
    have hsp3Eq : s3.sp = sp1 := by rw [hs2c] at hsp3; simpa [hsp2Eq] using hsp3
    have hal3 : s3.spAligned = true := spAligned_of_sub80 hsp3Eq hsp0
    obtain ⟨hx19_3, hx20_3, _, _, _, _, _, _, hx27_3, hx28_3, _hfp3, hv_3⟩ := hcs23
    have hx19_s3 : s3.readReg64 .x19 = p := by
      rw [hs2c] at hx19_3; simp [Reg.x19] at hx19_3 ⊢; exact hx19_3.trans hx19_s2
    have hx20_s3 : s3.readReg64 .x20 = q := by
      rw [hs2c] at hx20_3; simpa [Reg.x20] using hx20_3
    have hcs3 : ReallocUntouchedCS s0 s3 := by
      rw [hs2c] at hx27_3 hx28_3 hv_3; rw [hs1] at hx27_2 hx28_2 hv_2
      exact ⟨by simp [Reg.x27] at hx27_3 hx27_2 ⊢; exact hx27_3.trans (hx27_2.trans hcs.1),
             by simp [Reg.x28] at hx28_3 hx28_2 ⊢; exact hx28_3.trans (hx28_2.trans hcs.2.1),
             by simpa [calleeSavedVRegs] using hv_3.trans (hv_2.trans hcs.2.2)⟩
    have hProcS2 : MallocngProcPreserved s s2 := by rw [hs1] at hProc12; exact hProc12
    have hProc03 : MallocngProcPreserved s0 s3 :=
      mallocngProcPreserved_trans hproc (mallocngProcPreserved_trans hProcS2 hProc23)
    have hDelta03 : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bgt) newSz) s0.mem s3.mem := by
      rw [hmem1Eq] at hDelta12
      have h0s : MallocngMappedDelta 0 0 s0.mem s.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hPerm] at hm)⟩
      have h23 : MallocngMappedDelta 0 0 s2.mem s3.mem :=
        ⟨[], by decide, by decide, fun _ hm => Or.inl (by rwa [hperm23] at hm)⟩
      exact mappedDelta_trans_zero_right (mappedDelta_zero_trans_left h0s hDelta12) h23
    have hNoOrph03 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem s3.mem := by
      intro a hm3 hor0
      exact hNoOrph12 a (by rwa [← hperm23]) (hor0.imp (fun h0 => by rwa [hmem1Eq, hPerm]) id)
    exact fine_s4_free_ok (inAlign := inAlign) hFree hb γ tp brkStart bgt ivs0
      (dynamicRootRegions st') s0 s3 origBs
      hpNe hqNe hq16 hq48 hpc3 hrun3 hsp3Eq hal3 hsp0 hx19_s3 hx20_s3
      hcs3 hcl3 hProc03 hDelta03 hNoOrph03

/-! ## 4. Stage 2 In-Place `set_size` (`+0x2cc` → `ret`) -/

set_option maxHeartbeats 400000 in
private theorem fine_s2_finish_ok [MallocngMultiPlacement] {ro : Bool} {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz inAlign : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {bsCur : List (BitVec 8)} {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2fc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx19 : s.readReg64 .x19 = p)
    (hw4 : (s.readReg32 .x4).truncate 8 =
      BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (hcs : ReallocUntouchedCS s0 s)
    (hBs0Len : (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs)).length = g.stride)
    (hCurLen : bsCur.length = g.stride)
    (hLo : (g.slotStart idx).toNat ≤ p.toNat) (hSt4 : 4 ≤ (g.slotStart idx).toNat)
    (hEn : (g.slotEnd idx).toNat = (g.slotStart idx - 4#64).toNat + g.stride)
    (h48 : (g.slotStart idx - 4#64).toNat + g.stride ≤ 2 ^ 48)
    (hPost : SetSizeSlicePost (mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (p.toNat - (g.slotStart idx).toNat + 1) g.stride newSz
      (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
      (ByteSlice.write8 bsCur (p.toNat - (g.slotStart idx).toNat + 1)
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx)))) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let base := g.slotStart idx - 4#64
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((base ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
        MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf ivs0 s0 sf ∗
          ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (newSz, al, keptBs)⌝ ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (newSz, al, keptBs) ∗
          Frame)) oom := by
  intro sp1 al base bf keptBs
  have _ := hb; have _ := hpc
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  obtain ⟨hAddrP3Sub, _, _, _⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := sp_sub80_align16 hsp0
  let bsFinal := ByteSlice.write8 bsCur hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
  have hTail : ∀ {m1 : Memory} {s2 : State},
      m1.perm = s.mem.perm →
      s2.pc = b + 0x294#64 → s2.status = .Running → s2.mem = m1 → s2.brk = s0.brk →
      MallocngProcPreserved s0 s2 → s2.sp = s0.sp - 80#64 → s2.spAligned = true →
      s2.readReg64 .x20 = p →
      s2.readReg64 .x23 = s0.readReg64 .x23 → s2.readReg64 .x24 = s0.readReg64 .x24 →
      s2.readReg64 .x25 = s0.readReg64 .x25 → s2.readReg64 .x26 = s0.readReg64 .x26 →
      ReallocUntouchedCS s0 s2 →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s2
        ((base ↦ₛ bsFinal) ∗
         (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗
          (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
           MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
           MallocngTightBlock γ p oldSz al ∗ Frame)))
        (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (newSz, al, keptBs) ∗ Frame)) oom := by
    intro m1 s2 hm1Perm hpc2 hrun2 hmem2 hbrk2 hproc2 hsp2 hal2 hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    have hm1Perm0 : m1.perm = s0.mem.perm := hm1Perm.trans hPerm
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
         (base ↦ₛ bsFinal) ∗ MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
         MallocngTightBlock γ p oldSz al) ∗ Frame)
      (Entails.of_eq (by
        dsimp only [base]
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
        ac_rfl)) ?_
    apply VerifiedLibraries.Mallocng.Proofs.sepWP_bupd_pre (Q :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗
        (memRegion (s0.sp - 80#64 + 48#64) 8 ∗ memRegion (s0.sp - 80#64 + 56#64) 8 ∗
         memRegion (s0.sp - 80#64 + 64#64) 8 ∗ memRegion (s0.sp - 80#64 + 72#64) 8) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
           γ maddrs tp brkStart bf ivs0 s0 s2 ∗
         ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (newSz, al, keptBs)⌝ ∗
         (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (newSz, al, keptBs) ∗ Frame))
    · have hSub4 : (g.slotStart idx - 4#64).toNat = (g.slotStart idx).toNat - 4 :=
        bv64_sub_toNat hSt4
      have hSc48 : g.sc < 48 := by
        have hScCases := (hwf.groups_wf g hg).1
        have hUnitsLt48 : sizeToClassUnits ((newSz + 3) / 16) < 48 := nomSc_lt_48 hNewMax
        omega
      have hStrideFit : newSz + 4 ≤ g.stride := by omega
      have hAbsSt := reallocInPlace_absorb_st (ro := ro) (al := al) γ maddrs tp brkStart bCoarse ivs0 s0 s2
        st hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe
        (mallocngMappedDelta_of_perm_eq (hmem2 ▸ hm1Perm0))
        bsFinal (hPost.1.trans hBs0Len)
        (fun i hi hiNe => hPost.2.1 i (by omega) hiNe)
        hPost.2.2.1
        (fun h1 => by
          have h1' : bsFinal.getD (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) 0#8 = 0#8 :=
            hPost.2.2.2.1 (by omega)
          rwa [show p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz =
            p.toNat - (g.slotStart idx).toNat + 4 + newSz by omega] at h1')
        (fun h5 => by
          obtain ⟨h5a, h5b⟩ := hPost.2.2.2.2.1 (by omega)
          refine ⟨h5a, fun j hj => ?_⟩
          have h5bj : bsFinal.getD (g.stride - 4 + j) 0#8 = _ := h5b j hj
          rwa [show g.stride - (p.toNat - (g.slotStart idx).toNat + 1 + 3 + newSz) =
            (g.slotEnd idx).toNat - (p.toNat + newSz) by omega] at h5bj)
      rw [hbrk2] at hAbsSt
      have hAbsFine :
          MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
          (base ↦ₛ bsFinal) ∗ MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
          MallocngTightBlock γ p oldSz al ⊢
            |==> (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                    γ maddrs tp brkStart bf ivs0 s0 s2 ∗
                  ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (newSz, al, keptBs)⌝ ∗
                  (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (newSz, al, keptBs)) := by
        dsimp only [base]
        refine Entails.trans hAbsSt (bupd_mono ?_)
        refine Entails.pure_left fun ⟨_hCnt0, hNoOrph, hCnt', hPureTight⟩ => ?_
        let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
        let g' : GroupDesc := { g with slots := g.slots.set idx (.liveUser p newSz newEff) }
        let st' : MallocngSt :=
          { st with groups := VerifiedLibraries.Mallocng.Proofs.replaceGroup st.groups g.metaPtr g',
                    byteVal := writeBytesToMap st.byteVal (g.slotStart idx - 4#64) bsFinal,
                    liveMap := (st.liveMap.erase p).insert p newSz (st.liveMap.ov p) }
        have hFine' : MallocngFineInv bf ivs0 st' :=
          (fineGroupsInv_realloc_inplace (al := inAlign) (st' := st') (g' := g')
            hFine.toGroupsInv hwf.groups_nodup.1
            hg hIdx hSlot hSc48 hNewMax hScLe hStrideFit rfl rfl rfl rfl rfl rfl rfl rfl).toFineInv
            hCnt'.2.2.1
        let bfC := mallocngReallocBudget true (some (oldSz, origBs)) newSz bCoarse
        have hPack := fine_pack_postEnv (ro := ro) γ tp brkStart bf bfC ivs0 ivs0 st' s0 s2
          hNoOrph hCnt' hFine' (hproc2.2.2.1.trans htp0) (hproc2.2.2.2.1.trans hbrks0)
        rw [hbrk2] at hPack
        have hInit := Entails.trans (Entails.pure_right hPureTight (Entails.refl _))
          (fine_tightInit_to_modelInit (ro := ro) γ inAlign p newSz keptBs)
        exact Entails.trans
          (Entails.of_eq (show
            MallocngRoTablesA maddrs ∗
            (MallocngCoreStModeA ro γ maddrs brkStart s0.brk bfC.liveCost bfC.peakCost st' ∗
             (MallocngRuntime maddrs tp ∗
              (MallocngTightInitBlock γ al).interp p (newSz, keptBs))) =
            (MallocngRoTablesA maddrs ∗
             MallocngCoreStModeA ro γ maddrs brkStart s0.brk bfC.liveCost bfC.peakCost st' ∗
             MallocngRuntime maddrs tp) ∗
            (MallocngTightInitBlock γ al).interp p (newSz, keptBs) by
            simp only [sepConj_assoc]))
          (sepConj_mono hPack hInit)
      refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbsFine)))) ?_
      exact Entails.trans bupd_frame_mid (bupd_mono (Entails.of_eq (by ac_rfl)))
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hMemM1 : sf.mem = m1 := hsfMem.trans hmem2
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := mallocngProcPreserved_trans hproc2 hsfProc
      refine ⟨hMemM1 ▸ hm1Perm0, hBrk0, hProc0, hsfSp, hsfCS, hsfX0, Entails.trans hPf ?_⟩
      rw [fine_postEnv_congr_state (γ := γ) (A := maddrs) (tp := tp) (brkStart := brkStart)
        (bf := bf) (ivs0 := ivs0) (s0 := s0) hsfMem hsfBrk hsfProc.2.2.1 hsfProc.2.2.2.1]
      dsimp only [MallocngModelInitBlock]
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv : (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
    ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
    MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
    MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post' = post →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  wp_str8_slice m1 hm1Perm hdrOff
    (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
    (by have hw4' := hw4; try dsimp only [Reg.x4] at hw4'; try simp only [wp_norm, arm64_norm] at hw4' ⊢; first | rfl | exact hw4')
    (by first | rfl | (try simp only [wp_norm, arm64_norm, hx19]; exact (by bv_lin : p + (-3#64) = p - 3#64).trans hAddrP3Sub))
    (by have := bv64_sub_toNat hSt4; rw [hCurLen]; dsimp only [hdrOff]; omega)
  conv => arg 4; rw [reallocSavedHi_eq s0]
  wp_step; wp_step; wp_step; wp_step
  conv => arg 4; rw [← reallocSavedHi_eq s0]
  subst hPostGoal; rw [← hRestEnv]
  exact hTail hm1Perm (by simp) (by simp [hrun]) (by simp) (by simp [hbrk])
    ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
     by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    (by simp [hsp]) (by simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩

set_option maxHeartbeats 400000 in
/-- Complete Stage 2 (`+0x2cc` → `ret`) for `mallocngFineCostModel`. -/
private theorem fine_stage2_inplace_ok [MallocngMultiPlacement] {ro : Bool} {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff newSz inAlign : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLen : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hNewMax : newSz ≤ 131051) (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1)
    {Frame : SepProp} {oom : State → SepProp}
    (hpc : s.pc = b + 0x2cc#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4 : s.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5 : s.readReg64 .x5 = g.slotEnd idx)
    (hx19 : s.readReg64 .x19 = p)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf => sf.mem.perm = s0.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = p ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart bf ivs0 s0 sf ∗
          ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (newSz, al, keptBs)⌝ ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (newSz, al, keptBs) ∗
          Frame)) oom := by
  intro sp1 al bf keptBs
  have _ := hb; have _ := hpc
  apply sepWP_pure_of_sat (fun R hm =>
    satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
      stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
      ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
      MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame ∗ R)
      (Satisfies.mono (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
        ac_rfl)) hm))
  rintro ⟨_, hwf⟩
  obtain ⟨hLo, _, hSt4, _hSub4, hEn, h48, _hCapMax, hIdx31, hBs0Hdr⟩ :=
    inPlace_oldCap_bounds hwf hg hIdx hSlot hNewMax hScLe (origBs ++ tailBs)
  obtain ⟨hBs0Len, hSliceEq⟩ := liveUser_slotSlice_split hwf hg hIdx hSlot (origBs ++ tailBs)
    (by rw [List.length_append, hTailLen]; omega)
  let base := g.slotStart idx - 4#64
  let hdrOff := p.toNat - (g.slotStart idx).toNat + 1
  generalize hbs0 : mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs) = bs0 at hBs0Hdr hBs0Len hSliceEq
  let oldCap := (g.slotEnd idx).toNat - p.toNat
  let res := (g.slotEnd idx).toNat - (p.toNat + newSz)
  have hResEq : oldCap - newSz = res := by dsimp only [oldCap, res]; omega
  obtain ⟨hSub32, hEq32⟩ := subs32_cap_newSz (cap := oldCap) (newSz := newSz)
    (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega) (by dsimp only [oldCap]; omega)
  rw [hResEq] at hSub32 hEq32
  obtain ⟨hAddrP3Sub, _, hAddrZeroOf, hAddrEndOf⟩ := slot_set_size_addrs hLo hSt4 hEn h48 hFit
  refine SepWP.weaken_pre (P' :=
      (base ↦ₛ bs0) ∗
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion base g.stride a) st.byteVal ∗
       MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ Frame))
    (Entails.of_eq (by
      have hAssoc : (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
          (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
           MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)) =
        ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
          MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
          MallocngTightBlock γ p oldSz al ∗ Frame) := by
        generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
        ac_rfl
      rw [hAssoc, hSliceEq]
      dsimp only [base]
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
      ac_rfl)) ?_
  have hCapFold : (g.slotStart idx).toNat - 4 + g.stride - p.toNat = oldCap := by
    dsimp only [oldCap]; omega
  have halOf : ∀ s' : State, s'.sp = s.sp → s'.spAligned = true := fun s' hsp' => by
    simp only [State.spAligned, hsp'] at hal ⊢; exact hal
  apply sepWP_abstract_env; intro RestS2 postGoal hRestS2 hPostGoal
  wp_step; wp_step
  wp_if heq
  · have hRes0 : res = 0 := by
      try rw [hx3] at heq
      try rw [hx21] at heq
      try rw [hCapFold] at heq
      exact hEq32.mp heq
    subst hPostGoal hRestS2 hbs0
    exact fine_s2_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 _ st hFine hwf
      hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe
      (bsCur := mkLiveUserSlotBs st.byteVal g idx oldSz p (origBs ++ tailBs))
      (by simp) (by simp [hrun]) (by simpa using hPerm) (by simpa using hbrk)
      ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
       by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      htp0 hbrks0 (by simp [hsp]) (halOf _ (by simp)) hsp0 (by simp [hx19])
      (by try simp only [wp_norm, arm64_norm]; try rw [hx4]; exact idx_trunc8_eq_hdr0 hRes0 hIdx31)
      ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      hBs0Len hBs0Len hLo hSt4 hEn h48
      (setSize_case0 _ hdrOff g.stride newSz _ (by dsimp only [hdrOff, res] at hRes0 ⊢; omega)
        (by omega))
  · have hResPos : 1 ≤ res := by
      have hNe0 : res ≠ 0 := fun h0 => heq (by
        try rw [hx3]
        try rw [hx21]
        try rw [hCapFold]
        exact hEq32.mpr h0)
      omega
    wp_step; wp_step
    have hSub32z : BitVec.zeroExtend 32 (BitVec.ofNat 64 oldCap) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 res := hSub32
    have hAddrZero := hAddrZeroOf hResPos (by omega)
    wp_str8_slice m1 hm1Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by try simp only [wp_norm, arm64_norm]
          try rw [hx5]
          try rw [hx3]
          try rw [hx21]
          try rw [hCapFold]
          try rw [hSub32]
          try rw [hSub32z]
          try rw [BitVec.zero_sub]
          try rw [BitVec.shiftLeft_zero]
          first | rfl | exact hAddrZero)
      (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)
    let bs1 := ByteSlice.write8 bs0 (hdrOff + 3 + newSz) 0#8
    have hBs1Len : bs1.length = g.stride :=
      (ByteSlice.write8_length _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)).trans hBs0Len
    wp_step
    wp_if hle4
    · have hRes4 : res ≤ 4 := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        exact hle4
      have hBs1Hdr : bs1.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs1]
        rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hResPos ⊢; omega)]
        simp only [show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs1 hdrOff (by rw [hBs1Len]; dsimp only [hdrOff]; omega)]
      have hPost1 := setSize_case1to4 bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (by dsimp only [hdrOff, res] at hResPos ⊢; omega)
        (by dsimp only [hdrOff, res] at hRes4 ⊢; omega) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by subst hsFin; exact hm1Perm.trans hPerm
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hx3]; try rw [hx21]; try rw [hCapFold]; try rw [hSub32]; try rw [hSub32z]
        try rw [hBs1Hdr]
        exact hdrByte_res1to4 hBs0Hdr hIdx31 hRes4
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact fine_s2_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sFin st hFine hwf
        hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe (bsCur := bs1)
        hpcF hrunF hPermF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs1Len hLo hSt4 hEn h48 hPost1
    · have hRes5 : 5 ≤ res := by
        try rw [hx3] at hle4
        try rw [hx21] at hle4
        try rw [hCapFold] at hle4
        try rw [hSub32] at hle4
        try rw [hSub32z] at hle4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 (by dsimp only [res]; omega) (by decide),
            decide_eq_true_eq] at hle4
        omega
      obtain ⟨hAddrEnd5, hAddrEnd4⟩ := hAddrEndOf hRes5
      wp_str8_slice m2 hm2Perm (g.stride - 5) 0#8 rfl
        (by rw [← hAddrEnd5]; try simp only [wp_norm, arm64_norm, hx5]; bv_lin)
        (by rw [hBs1Len]; omega)
      let bs2 := ByteSlice.write8 bs1 (g.stride - 5) 0#8
      have hBs2Len : bs2.length = g.stride :=
        (ByteSlice.write8_length _ _ _ (by rw [hBs1Len]; omega)).trans hBs1Len
      wp_str32_slice m3 hm3Perm (g.stride - 4) (BitVec.ofNat 32 res)
        (by first | exact hSub32 | (first | exact hSub32z | (try simp only [wp_norm, arm64_norm]; try rw [hx3]; try rw [hx21]; try rw [hCapFold]; first | exact hSub32 | (first | exact hSub32z | rfl))))
        (by rw [← hAddrEnd4]; try simp only [wp_norm, arm64_norm, hx5]; bv_lin)
        (by rw [hBs2Len]; omega)
      let bs3 := ByteSlice.write32 bs2 (g.stride - 4) (BitVec.ofNat 32 res)
      have hBs3Len : bs3.length = g.stride :=
        (ByteSlice.write32_length _ _ _ (by rw [hBs2Len]; omega)).trans hBs2Len
      have hBs3Hdr : bs3.getD hdrOff 0#8 = bs0.getD hdrOff 0#8 := by
        dsimp only [bs3, bs2, bs1]
        rw [ByteSlice.getD_write32 _ _ _ _ _ (by rw [hBs2Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs1Len]; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hBs0Len]; dsimp only [hdrOff, res] at hRes5 ⊢; omega)]
        simp only [show ¬ (g.stride - 4 ≤ hdrOff ∧ hdrOff < g.stride - 4 + 4) by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ g.stride - 5 by dsimp only [hdrOff, res] at hRes5 ⊢; omega,
          show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte]
      conv => arg 4; arg 1; rw [pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      wp_step; wp_step; wp_step; wp_step
      conv => arg 4; arg 1; rw [← pointsToBytes_focus8 base bs3 hdrOff (by rw [hBs3Len]; dsimp only [hdrOff]; omega)]
      have hResStride : g.stride - (hdrOff + 3 + newSz) = res := by
        dsimp only [hdrOff, res]; omega
      have hPost5 := setSize_case5up bs0 hdrOff g.stride newSz
        (BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx))
        (BitVec.ofNat 32 res) (by rw [hResStride]; exact hRes5) (by rw [hResStride]) (by omega)
      refine (fun {sFin P post} (h : ∀ s', s' = sFin →
          SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s' P post oom) => h sFin rfl) ?_
      intro sFin hsFin
      have hpcF : sFin.pc = b + 0x2fc#64 := by subst hsFin; simp
      have hrunF : sFin.status = .Running := by subst hsFin; simp [hrun]
      have hPermF : sFin.mem.perm = s0.mem.perm := by
        subst hsFin; exact hm3Perm.trans (hm2Perm.trans (hm1Perm.trans hPerm))
      have hbrkF : sFin.brk = s0.brk := by subst hsFin; simpa using hbrk
      have hprocF : MallocngProcPreserved s0 sFin := by
        subst hsFin
        exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
               by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by subst hsFin; simp [hsp]
      have halF : sFin.spAligned = true := halOf _ (by subst hsFin; simp)
      have hx19F : sFin.readReg64 .x19 = p := by subst hsFin; simp [hx19]
      have hw4F : (sFin.readReg32 .x4).truncate 8 =
          BitVec.ofNat 8 (((min ((g.slotEnd idx).toNat - (p.toNat + newSz)) 5) <<< 5) ||| idx) := by
        subst hsFin
        try simp only [wp_norm, arm64_norm]
        try rw [hBs3Hdr]
        exact hdrByte_res5up hBs0Hdr hIdx31 hRes5
      have hcsF : ReallocUntouchedCS s0 sFin := by
        subst hsFin
        exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin
      subst hPostGoal hRestS2 hbs0
      exact fine_s2_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sFin st hFine hwf
        hg hIdx origBs tailBs hOrigLen hTailLen hSlot hNewMax hFit hScLe (bsCur := bs3)
        hpcF hrunF hPermF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx19F hw4F hcsF
        hBs0Len hBs3Len hLo hSt4 hEn h48 hPost5

/-! ## 5. Stage 3 Individual-`mmap` `sc = 63` `mremap` (`+0x324` → `ret`) -/

set_option maxRecDepth 20000 in
private theorem mremap_fine_oom_bounds {newSz extra oldSz maplen phys maxMeta inAlign : Nat}
    (hNewLo : 131051 < newSz)
    (hOldFit : 16 + extra + oldSz + 4 ≤ maplen * 4096)
    (hPhys : phys + maplen * 4096 < (newSz + extra + 4115) / 4096 * 4096) :
    PAGE_SIZE ≤ pageAlignUp newSz ∧
    pageAlignUp newSz % PAGE_SIZE = 0 ∧
    ([].map (@Prod.snd (BitVec 64) Nat)).sum + pageAlignUp newSz ≤
      FineStepBound maxMeta (mallocngAlignedEffSize inAlign newSz) ∧
    phys < pageAlignUp newSz := by
  have h1 : newSz + extra + 4115 ≤ (newSz + 4095) + maplen * 4096 := by omega
  have h2 : (newSz + extra + 4115) / 4096 ≤ (newSz + 4095) / 4096 + maplen := by
    have hd := Nat.div_le_div_right (c := 4096) h1
    rwa [Nat.add_mul_div_right _ _ (by decide : 0 < 4096)] at hd
  have hNeedLe : (newSz + extra + 4115) / 4096 * 4096 ≤ pageAlignUp newSz + maplen * 4096 := by
    unfold pageAlignUp PAGE_SIZE
    simpa [Nat.add_mul] using Nat.mul_le_mul_right 4096 h2
  have hPgGe : PAGE_SIZE ≤ pageAlignUp newSz := by unfold pageAlignUp PAGE_SIZE; omega
  have hPgMod : pageAlignUp newSz % PAGE_SIZE = 0 := Nat.mul_mod_left _ 4096
  rw [List.map_nil, List.sum_nil, Nat.zero_add]
  have hPA : pageAlignUp newSz ≤ newSz + 4095 := by unfold pageAlignUp PAGE_SIZE; omega
  have hPhysLt : phys < pageAlignUp newSz := by omega
  have hLeEff := fine_le_alignedEffSize inAlign newSz
  have hStep := Nat.le_trans (Nat.le_add_left _ (FineMetaStep maxMeta))
    (fineStepBound_large_le maxMeta (pageAlignUp newSz) (mallocngAlignedEffSize inAlign newSz)
      (by omega))
  exact ⟨hPgGe, hPgMod, hStep, hPhysLt⟩

private theorem mremap_needed_le_fine {newSz extra over ov inAlign maxMeta : Nat}
    (hOffLe : extra ≤ over + 255 * 16) (hOverLe : over ≤ MaxAlignedAllocAlign - 16)
    (hOverOv : over ≤ ov) (hOvAl : ov ≤ max inAlign 16 - 16) :
    (newSz + extra + 4115) / 4096 * 4096 ≤
      FineStepBound maxMeta (mallocngAlignedEffSize inAlign newSz) := by
  have hDiv : (newSz + extra + 4115) / 4096 * 4096 ≤ newSz + extra + 4115 :=
    Nat.div_mul_le_self _ _
  have hResLe : (newSz + extra + 4115) / 4096 * 4096 ≤
      mallocngReallocRes (max inAlign 16) newSz + 8195 := by
    unfold mallocngReallocRes
    have hMaxVal : MaxAlignedAllocAlign = 2 ^ 31 := rfl
    omega
  have hEff := fine_reallocRes_le newSz (Nat.le_refl (max inAlign 16))
  exact Nat.le_trans (Nat.le_add_left _ (FineMetaStep maxMeta))
    (fineStepBound_large_le maxMeta _ _ (by omega))

private theorem cap0_sub_extra_fine {needed extra : Nat}
    (h1 : 20 + extra ≤ needed) (h2 : needed < 2 ^ 64) :
    (BitVec.ofNat 64 needed - 20#64) - BitVec.ofNat 64 extra =
      BitVec.ofNat 64 ((needed - 4) - (16 + extra)) := by
  bv_omega

private theorem entails_pure_of_pair_fine {A B C Q : SepProp} {φ : Prop}
    (hAB : A ∗ B ⊢ ⌜φ⌝ ∗ A ∗ B) (h : φ → (A ∗ B ∗ C ⊢ Q)) : A ∗ B ∗ C ⊢ Q := by
  refine Entails.trans (Entails.of_eq (sepConj_assoc A B C).symm) ?_
  refine Entails.trans (sepConj_mono_left hAB) ?_
  refine Entails.trans (Entails.of_eq (sepConj_assoc _ _ C)) ?_
  refine Entails.pure_left fun hφ => ?_
  exact Entails.trans (Entails.of_eq (sepConj_assoc A B C)) (h hφ)

private theorem packedWord_sc63_mask_trunc_fine (g : GroupDesc) (hLast : g.lastIdx ≤ 31)
    (hSc63 : g.sc = 63) (hMap : g.maplen < 2 ^ 52) :
    BitVec.truncate 32 ((g.packedWord.extractLsb' 0 16).zeroExtend 64 &&& 17317308141504#64) =
      0xfc0#32 := by
  have hTr : ∀ x : BitVec 16,
      BitVec.truncate 32 (x.zeroExtend 64 &&& 17317308141504#64) = x.zeroExtend 32 &&& 0xfc0#32 :=
    fun _ => by bv_robdd
  rw [hTr]; exact VerifiedLibraries.Mallocng.Proofs.packedWord_sc63_mask g hLast hSc63 hMap

private theorem not_add_one_eq_zero_of_le_48_fine {x : BitVec 64}
    (h : x.toNat ≤ 2 ^ 48) (heq : x + 1#64 = 0#64) : False := by
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem fine_extract_to_mremap [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) {st : MallocngSt}
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
     MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
     MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame) ⊢
      ⌜st.liveMap.ov p ≤ al - 16⌝ ∗
      ∃∗ errnoVal : BitVec 32,
        (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         memMapped g.mem (g.maplen * 4096) ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
         MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngTightBlock γ p oldSz al ∗ Frame) := by
  unfold MallocngReadRestMode
  have hExt := reallocMremap_extract maddrs tp hwf hg hIdx0 (origBs ++ tailBs)
    hUserLen hSlot0 hSc63
  refine Entails.trans (Q :=
      ⌜MallocngCountIvsWF bCoarse ivs0 st ∧
        MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st⌝ ∗
      ((ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ Frame)))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.pure_left fun _ => ?_
  refine Entails.trans (Q := MallocngLiveAuth γ st.liveMap ∗ MallocngTightBlock γ p oldSz al ∗
      (ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ (origBs ++ tailBs))) ∗
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗ Frame))
    (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (MallocngRuntime maddrs tp) = PRt
      generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine entails_pure_of_pair_fine (mallocngTightBlock_lookup γ st.liveMap p oldSz al)
    fun ⟨_, _, hOv⟩ => Entails.pure_right hOv ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hExt))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_mono fun errnoVal => Entails.of_eq ?_
  generalize (MallocngRoTablesAt maddrs) = PRo
  generalize (ReallocMremapFrame maddrs tp st g) = PFr
  generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
  ac_rfl

private theorem fine_reallocMremap_unextract {ro : Bool} (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart brk : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    {st : MallocngSt}
    (hFine : MallocngFineInv bgt ivs0 st)
    (hCount : MallocngCountIvsWF bCoarse ivs0 st)
    (hwf : MallocngWF A.base brkStart brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (userBs : List (BitVec 8))
    (hUserLen : userBs.length = oldSz)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63) (errnoVal' : BitVec 32) :
    (MallocngRoTablesAt A ∗
     (A.ctx ↦ₛ st.ctx.toBytes) ∗
     (g.metaPtr ↦ₛ g.metaBytes) ∗
     (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
     memMapped g.mem (g.maplen * 4096) ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
     ReallocMremapFrame A tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32) ∗
     MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
     MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ⊢
      FineHeapModeImpl ro γ A tp brkStart brk bgt ivs0 ∗ (p ↦ₛ userBs) := by
  have hgw := hwf.groups_wf g hg
  have hMpPos := (hgw.2.2.2.1 hSc63).2.1
  have hTotEq : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
  have hMemFit : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 := by
    have h := hgw.2.2.2.2.2.2.1; rwa [hTotEq] at h
  obtain ⟨_, _, hMemOwn⟩ := sc63_metaPtr_and_mem_owned hwf hg hIdx hSlot hSc63
  have hExtMp := MappedSet_extract_slice hwf.masterDom_wf.1 (keep := OwnedMappedByte st)
    g.mem (n := g.maplen * 4096) (by omega)
    (fun a ha => (hMemOwn a ha).1) (fun a ha => (hMemOwn a ha).2.1)
  have hSplitRw := sc63_rw_split_eq hwf hg hIdx userBs hUserLen hSlot hSc63
  have hRepack := fineHeap_read_liveUser_repack (ro := ro) γ A tp brkStart brk bgt bCoarse ivs0 st hFine
  unfold MallocngReadRestMode at hRepack
  unfold ReallocMremapFrame
  have hErrno : ((tp - 0xa4#64) ↦₃₂ errnoVal') ⊢
      ∃∗ ev : BitVec 32, (tp - 0xa4#64) ↦₃₂ ev := Entails.sepExists_intro errnoVal'
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      (((tp - 0xa4#64) ↦₃₂ errnoVal') ∗
       ((A.libc + 3#64) ↦₈ 0#8) ∗ ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
      (((g.metaPtr ↦ₛ g.metaBytes) ∗
        (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz userBs) ∗
        ByteMap st.masterDom
          (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a ∧
            ¬ InRegion g.mem (g.maplen * 4096) a) st.byteVal) ∗
       (memMapped g.mem (g.maplen * 4096) ∗
        MappedSet st.masterDom
          (fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem (g.maplen * 4096) a)) ∗
       MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st.ctx.toBytes) ∗
       MallocngLiveAuth γ st.liveMap ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
       MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal))) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono_left hErrno)) ?_
  change (MallocngRuntime A tp ∗ _) ⊢ _
  rw [← hSplitRw, ← hExtMp]
  refine Entails.trans (Entails.of_eq (by
    generalize (MallocngRoTablesAt A) = PRo
    generalize (MallocngRuntime A tp) = PRt
    generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
    ac_rfl : _ =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       (MallocngLiveAuth γ st.liveMap ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro A.libc st.auxvPtr ∗
        MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MappedSet st.masterDom (OwnedMappedByte st) ∗
        MallocngRuntime A tp)) ∗
      (p ↦ₛ userBs))) ?_
  exact sepConj_mono_left
    (Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right ⟨hCount, hwf⟩ (Entails.refl _))))) hRepack)

private theorem fine_unextract_to_stage4 [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) {st : MallocngSt}
    (hFine : MallocngFineInv bgt ivs0 st)
    (hCount : MallocngCountIvsWF bCoarse ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff al : Nat} (origBs tailBs : List (BitVec 8))
    (hUserLen : (origBs ++ tailBs).length = oldSz)
    (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    (hbrk : s.brk = s0.brk) (htp : s.tpidrEl0 = tp) (hbrks : s.brkStart = brkStart)
    (err32 : BitVec 32) (sp1 : BitVec 64) (Frame : SepProp) :
    (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
     ((tp - 0xa4#64) ↦₃₂ err32) ∗
     (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
     memMapped g.mem (g.maplen * 4096) ∗
     (g.metaPtr ↦ₛ g.metaBytes) ∗
     MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) ⊢
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s ∗
       MallocngTightBlock γ p oldSz al ∗
       (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
       Frame) := by
  have hUn := fine_reallocMremap_unextract (ro := ro) γ maddrs tp brkStart s0.brk bgt bCoarse ivs0
    hFine hCount hwf hg hIdx0 (origBs ++ tailBs) hUserLen hSlot0 hSc63 err32
  have hEnv : FineHeapModeImpl ro γ maddrs tp brkStart s0.brk bgt ivs0 ⊢
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s := by
    unfold MallocngModelEnv
    rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq, hbrk]
    exact Entails.pure_right ⟨htp, hbrks⟩ (Entails.refl _)
  have hUser := unsplit_user_bytes p origBs tailBs oldSz hTailLen
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  refine Entails.trans (Q :=
      (MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       (g.metaPtr ↦ₛ g.metaBytes) ∗
       (g.mem ↦ₛ mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)) ∗
       memMapped g.mem (g.maplen * 4096) ∗
       ((tp - 0xa4#64) ↦₃₂ err32) ∗
       ReallocMremapFrame maddrs tp st g ∗
       MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
       ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) ∗
      MallocngTightBlock γ p oldSz al ∗ Frame)
    (Entails.of_eq (by
      show _ = _ ∗ MallocngTightBlock γ p oldSz al ∗ Frame
      generalize (MallocngRoTablesAt maddrs) = PRo
      generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
      ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hUn) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono hEnv hUser)) ?_
  exact Entails.of_eq (by
    generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s) = PEnv
    ac_rfl)

set_option maxHeartbeats 400000 in
private theorem fine_s3_finish_ok [MallocngMultiPlacement] {ro : Bool} {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    (hCount : MallocngCountIvsWF bCoarse ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff inAlign : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32) {bsCur : List (BitVec 8)}
    {Frame : SepProp} {oom : State → SepProp}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hpc : s.pc = b + 0x3b8#64) (hrun : s.status = .Running)
    (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx20 : s.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (hw24 : s.readReg32 .x24 =
      BitVec.ofNat 32 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
    (hcs : ReallocUntouchedCS s0 s)
    (hCurLen : bsCur.length = needed)
    (hCurHdr : bsCur.getD (13 + (p.toNat - (g.slotStart 0).toNat)) 0#8 = st.byteVal (p - 3#64))
    (hSetSize :
      SetSizeSlicePost
        (ByteSlice.write8
          ((mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
            List.replicate (needed - g.maplen * 4096) 0#8)
          (needed - 4) 0#8)
        (13 + (p.toNat - (g.slotStart 0).toNat))
        (needed - 4)
        newSz
        (BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
        (ByteSlice.write8 bsCur (13 + (p.toNat - (g.slotStart 0).toNat))
          (BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5)))) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((newBase ↦ₛ bsCur) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗
        (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
        memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗
        (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗
        (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗
        MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf =>
        (∃ newQ : BitVec 64,
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf newQ (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp newQ (newSz, al, keptBs) ∗
            Frame))) oom := by
  intro sp1 al bf keptBs
  let newP := (newBase + 16#64) + BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat)
  have _ := hb
  obtain ⟨_, hLast0, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, hNewSlotFit0, _, _, hNeedLo0, hNeedDvd0, _, _, _⟩ :=
    sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
  have hSlotsLen1 : g.slots.length = 1 := by
    have hLenCnt := (hwf.groups_wf g hg).2.2.1
    unfold GroupDesc.cnt at hLenCnt
    omega
  have hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed := by
    rw [hNeedEq]; exact hNewSlotFit0
  have hNeedLo : 4096 ≤ needed := by rw [hNeedEq]; exact hNeedLo0
  have hNeedDvd : 4096 ∣ needed := by rw [hNeedEq]; exact hNeedDvd0
  have hNeedAl : needed % 4096 = 0 := Nat.mod_eq_zero_of_dvd hNeedDvd
  let extra := p.toNat - (g.slotStart 0).toNat
  let hdrOff := 13 + extra
  let hdr8 := BitVec.ofNat 8 (min ((needed - 4) - (16 + extra + newSz)) 5 <<< 5)
  obtain ⟨_, hNewPNat, _, hAddrP3Neg, _, _⟩ := sc63_post_mremap_addrs hNewBaseFit hNewSlotFit
  have hHdrAnd31 := sc63_oldHdr_and31 hwf hg hIdx0 hSlot0
  have hspAlign1 : (s0.sp - 80#64) &&& 15#64 = 0#64 := sp_sub80_align16 hsp0
  let bsFinal := ByteSlice.write8 bsCur hdrOff hdr8
  have hFinalLen : bsFinal.length = needed :=
    (ByteSlice.write8_length bsCur hdrOff hdr8 (by rw [hCurLen]; dsimp only [hdrOff, extra]; omega)).trans hCurLen
  have hTail : ∀ {m1 : Memory} {s2 : State},
      m1.perm = s.mem.perm →
      s2.pc = b + 0x294#64 → s2.status = .Running → s2.mem = m1 → s2.brk = s0.brk →
      MallocngProcPreserved s0 s2 → s2.sp = s0.sp - 80#64 → s2.spAligned = true →
      s2.readReg64 .x20 = newP →
      s2.readReg64 .x23 = s0.readReg64 .x23 → s2.readReg64 .x24 = s0.readReg64 .x24 →
      s2.readReg64 .x25 = s0.readReg64 .x25 → s2.readReg64 .x26 = s0.readReg64 .x26 →
      ReallocUntouchedCS s0 s2 →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s2
        ((newBase ↦ₛ bsFinal) ∗
         (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗
          (MallocngRoTablesAt maddrs ∗
           (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
           (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
           memMapped newBase needed ∗
           ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
           ReallocMremapFrame maddrs tp st g ∗
           MallocngLiveAuth γ st.liveMap ∗
           (maddrs.lock ↦₃₂ 0#32) ∗
           (maddrs.replaced ↦₃₂ 0#32) ∗
           (maddrs.aaReplaced ↦₃₂ 0#32) ∗
           MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗
           MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
           ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
           MallocngTightBlock γ p oldSz al ∗ Frame)))
        (fun sf Pf =>
          (∃ newQ : BitVec 64,
            sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
            (Pf ⊢ stackFrame s0 800 ∗
              MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                γ maddrs tp brkStart bf ivs0 s0 sf ∗
              ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf newQ (newSz, al, keptBs)⌝ ∗
              (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp newQ (newSz, al, keptBs) ∗
              Frame))) oom := by
    intro m1 s2 hm1Perm hpc2 hrun2 hmem2 hbrk2 hproc2 hsp2 hal2 hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2
    apply sepWP_pure_of_sat (fun R hm =>
      reallocMremap_disjoint hwf hg hSc63 hFinalLen hNewBaseAl hNeedAl hNeedLo hNewBaseFit
        (Q := ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ MallocngLiveAuth γ st.liveMap ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          MallocngTightBlock γ p oldSz al ∗ Frame ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (ReallocMremapFrame maddrs tp st g) = PFr
          generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
          generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
          ac_rfl)) hm))
    rintro ⟨hDisjMa, hDisjGp, hDisjAp, hDisjRg⟩
    have hPermRel2 :
        (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s2.mem.perm = s0.mem.perm) ∨
        (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧
          s2.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
      rw [hmem2, hm1Perm]
      exact hPermRel
    refine SepWP.weaken_pre (P' :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngRoTablesAt maddrs ∗
         (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
         (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
         (newBase ↦ₛ bsFinal) ∗
         memMapped newBase needed ∗
         ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
         ReallocMremapFrame maddrs tp st g ∗
         MallocngLiveAuth γ st.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗
         (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗
         MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
         ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
         MallocngTightBlock γ p oldSz al) ∗ Frame)
      (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo
        generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
        ac_rfl)) ?_
    apply VerifiedLibraries.Mallocng.Proofs.sepWP_bupd_pre (Q :=
        ReallocSavedLo s0 (s0.sp - 80#64) ∗
        (memRegion (s0.sp - 80#64 + 48#64) 8 ∗ memRegion (s0.sp - 80#64 + 56#64) 8 ∗
         memRegion (s0.sp - 80#64 + 64#64) 8 ∗ memRegion (s0.sp - 80#64 + 72#64) 8) ∗
        stackFrameAt (s0.sp - 80#64) 720 ∗
        (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
           γ maddrs tp brkStart bf ivs0 s0 s2 ∗
         ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf newP (newSz, al, keptBs)⌝ ∗
         (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp newP (newSz, al, keptBs) ∗ Frame))
    · have hwf2 : MallocngWF maddrs.base brkStart s2.brk bCoarse.liveCost bCoarse.peakCost st := by
        rwa [hbrk2]
      have hAbsSt := reallocMremap_absorb_st (ro := ro) (newP := newP) (al := al) γ maddrs tp brkStart bCoarse
        ivs0 s0 s2 st hCount hwf2 hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63
        errnoVal bsFinal hNewLo hNewHi hNeedEq hNewBaseGe hNewBaseAl hNewBaseFit hNewPNat
        hOldRw hPermRel2 hDisjMa hDisjGp hDisjAp hDisjRg hSetSize
      have hAbsFine :
          MallocngRoTablesAt maddrs ∗
          (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
          (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
          (newBase ↦ₛ bsFinal) ∗
          memMapped newBase needed ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
          ReallocMremapFrame maddrs tp st g ∗
          MallocngLiveAuth γ st.liveMap ∗
          (maddrs.lock ↦₃₂ 0#32) ∗
          (maddrs.replaced ↦₃₂ 0#32) ∗
          (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗
          MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
          ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
          MallocngTightBlock γ p oldSz al ⊢
            |==> (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                    γ maddrs tp brkStart bf ivs0 s0 s2 ∗
                  ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf newP (newSz, al, keptBs)⌝ ∗
                  (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp newP (newSz, al, keptBs)) := by
        refine Entails.trans hAbsSt (bupd_mono ?_)
        refine Entails.pure_left fun ⟨hNoOrph, hCnt', hPureTight⟩ => ?_
        let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
        let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
        let st' := mkReallocMremapSt st g p newBase newP needed newSz newEff bsFinal
        have hFine' : MallocngFineInv bf (dynamicRootRegions st') st' :=
          (fineGroupsInv_realloc_mremap63 (al := inAlign) (st' := st') (g' := g')
            hFine.toGroupsInv hwf.groups_nodup.1
            hg hSlotsLen1 hSlot0 hSc63 hNewLo
            rfl rfl rfl rfl rfl rfl rfl).toFineInv rfl
        let bfC := mallocngReallocBudget true (some (oldSz, origBs)) newSz bCoarse
        have hPack := fine_pack_postEnv (ro := ro) γ tp brkStart bf bfC ivs0 (dynamicRootRegions st') st' s0 s2
          hNoOrph hCnt' hFine' (hproc2.2.2.1.trans htp0) (hproc2.2.2.2.1.trans hbrks0)
        have hInit := Entails.trans (Entails.pure_right hPureTight (Entails.refl _))
          (fine_tightInit_to_modelInit (ro := ro) γ inAlign newP newSz keptBs)
        exact Entails.trans
          (Entails.of_eq (show
            MallocngRoTablesA maddrs ∗
            (MallocngCoreStModeA ro γ maddrs brkStart s2.brk bfC.liveCost bfC.peakCost st' ∗
             (MallocngRuntime maddrs tp ∗
              (MallocngTightInitBlock γ al).interp newP (newSz, keptBs))) =
            (MallocngRoTablesA maddrs ∗
             MallocngCoreStModeA ro γ maddrs brkStart s2.brk bfC.liveCost bfC.peakCost st' ∗
             MallocngRuntime maddrs tp) ∗
            (MallocngTightInitBlock γ al).interp newP (newSz, keptBs) by
            simp only [sepConj_assoc]))
          (sepConj_mono hPack hInit)
      refine Entails.trans (sepConj_mono_right (sepConj_mono (reallocSavedHi_entails_memRegions s0 _)
        (sepConj_mono_right (sepConj_mono_left hAbsFine)))) ?_
      exact Entails.trans bupd_frame_mid (bupd_mono (Entails.of_eq (by
        dsimp only [MallocngModelInitBlock]
        ac_rfl)))
    · refine SepWP.mono (realloc_epilogue_ok hb hpc2 hrun2 hsp2 hal2 hsp0
        hx20_2 hx23_2 hx24_2 hx25_2 hx26_2 hcs2) ?_
      intro sf Pf _ _ ⟨hsfMem, hsfBrk, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
      have hBrk0 : sf.brk = s0.brk := hsfBrk.trans hbrk2
      have hProc0 : MallocngProcPreserved s0 sf := mallocngProcPreserved_trans hproc2 hsfProc
      refine ⟨newP, by rw [hsfMem, hmem2, hm1Perm], hBrk0, hProc0, hsfSp, hsfCS, hsfX0, Entails.trans hPf ?_⟩
      rw [fine_postEnv_congr_state (γ := γ) (A := maddrs) (tp := tp) (brkStart := brkStart)
        (bf := bf) (ivs0 := ivs0) (s0 := s0) hsfMem hsfBrk hsfProc.2.2.1 hsfProc.2.2.2.1]
      dsimp only [MallocngModelInitBlock]
      exact Entails.of_eq (by ac_rfl)
  conv => arg 4; dsimp only [sp1]
  generalize hRestEnv :
    (MallocngRoTablesAt maddrs ∗
     (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
     (g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗
     memMapped newBase needed ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
     ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗
     (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗
     (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗
     MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post' = post →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  have hFocusHdr : hdrOff < bsCur.length := by rw [hCurLen]; dsimp only [hdrOff, extra]; omega
  conv => arg 4; arg 1; rw [pointsToBytes_focus8 newBase bsCur hdrOff hFocusHdr]
  have hLdAddr : (newBase + 16#64) + BitVec.ofNat 64 extra + (-3#64) = newBase + BitVec.ofNat 64 hdrOff :=
    hAddrP3Neg
  wp_step; wp_step; wp_step
  conv => arg 4; arg 1; rw [← pointsToBytes_focus8 newBase bsCur hdrOff hFocusHdr]
  wp_str8_slice m1 hm1Perm hdrOff hdr8
    (by have hw24' := hw24
        try dsimp only [Reg.x24] at hw24'
        try simp only [wp_norm, arm64_norm] at hw24' ⊢
        try rw [hw24']
        try rw [hCurHdr]
        try rw [hHdrAnd31]
        try rw [BitVec.add_zero]
        dsimp only [hdr8, extra]
        bv_omega)
    (by rw [← hAddrP3Neg]; try simp only [wp_norm, arm64_norm, hx20]; bv_lin)
    (by rw [hCurLen]; dsimp only [hdrOff, extra]; omega)
  conv => arg 4; rw [reallocSavedHi_eq s0]
  wp_step; wp_step; wp_step
  conv => arg 4; rw [← reallocSavedHi_eq s0]
  subst hPostGoal; rw [← hRestEnv]
  exact hTail hm1Perm (by simp) (by simp [hrun]) (by simp) (by simp [hbrk])
    ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1], by simp [hproc.2.2.2.1],
     by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    (by simp [hsp]) (by simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
    (by simp [hx20, newP]) (by simp) (by simp) (by simp) (by simp)
    ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩

set_option maxHeartbeats 400000 in
private theorem fine_s3_post_mremap_ok [MallocngMultiPlacement] {ro : Bool} {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    (hCount : MallocngCountIvsWF bCoarse ivs0 st)
    (hwf : MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff inAlign : Nat} (origBs tailBs : List (BitVec 8))
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase : BitVec 64} {needed newSz : Nat}
    (errnoVal : BitVec 32)
    {Frame : SepProp} {oom : State → SepProp}
    (hNewLo : 131051 < newSz) (hNewHi : newSz ≤ MallocngMaxAllocSize)
    (hNeedEq : needed = ((newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) / 4096) * 4096)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hOldRw : ∀ x, InRegion g.mem (g.maplen * 4096) x → s0.mem.perm x = some Perm.rw)
    (hPermRel :
      (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ s.mem.perm = s0.mem.perm) ∨
      (∃ m1 : Memory, m1.perm = s0.mem.perm ∧
        s.mem.perm = (m1.remapRw g.mem (g.maplen * 4096) newBase needed).perm))
    (hpc : s.pc = b + 0x364#64) (hrun : s.status = .Running)
    (hbrk : s.brk = s0.brk) (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = newBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (p.toNat - (g.slotStart 0).toNat))
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx22 : s.readReg64 .x22 = g.metaPtr)
    (hx24 : s.readReg64 .x24 = 0#64)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115))
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 needed)
    (hcs : ReallocUntouchedCS s0 s) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let keptBs := origBs.take newSz
    let bsRemap0 := (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).take needed ++
      List.replicate (needed - g.maplen * 4096) 0#8
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ (newBase ↦ₛ bsRemap0) ∗
       (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
        MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
        MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
        (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ Frame))
      (fun sf Pf =>
        (∃ newQ : BitVec 64,
          sf.mem.perm = s.mem.perm ∧ sf.brk = s0.brk ∧ MallocngProcPreserved s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = newQ ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf newQ (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp newQ (newSz, al, keptBs) ∗ Frame))) oom := by
  intro sp1 al bf keptBs bsRemap0
  have _ := hb
  dsimp only [Reg.x0, Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26] at hx0 hx20 hx21 hx22 hx24 hx25 hx26
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let extra := p.toNat - (g.slotStart 0).toNat
  let hdrOff := 13 + extra
  let newRes := (needed - 4) - (16 + extra + newSz)
  let hdr8 := BitVec.ofNat 8 (min newRes 5 <<< 5)
  have ⟨hLast0, hOldMemFit, hSt0Nat, hLoP, hOldSlotFit, hNewSlotFit, hNeedLo, hNeedDvd⟩ :
      g.lastIdx = 0 ∧ g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 ∧
      (g.slotStart 0).toNat = g.mem.toNat + 16 ∧ (g.slotStart 0).toNat ≤ p.toNat ∧
      16 + extra + oldSz + 4 ≤ g.maplen * 4096 ∧ 16 + extra + newSz + 4 ≤ needed ∧
      4096 ≤ needed ∧ 4096 ∣ needed := by
    obtain ⟨_, h1, _, _, _, _, _, _, _, _, h2, _, h3, _, h4, _, _, h5, h6, _, _, h7, h8, _, _, _⟩ :=
      sc63_liveUser_bounds hCount hwf hg hIdx0 hSlot0 hSc63 hNewLo hNewHi
    rw [← hNeedEq] at h6 h7 h8; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hResBound : newRes ≤ 4095 := by dsimp only [newRes, extra] at hNeedEq ⊢; omega
  have hUserLen : (origBs ++ tailBs).length = oldSz := by simp [hTailLen]; omega
  have hOldMapLen : (mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)).length = g.maplen * 4096 :=
    mkSc63OldMapBs_length st.byteVal g p oldSz (origBs ++ tailBs) hUserLen (by omega) (by omega)
  have hRemapLen0 : bsRemap0.length = needed := by
    simp only [bsRemap0, List.length_append, List.length_take, List.length_replicate, hOldMapLen]; omega
  have hRemapHdr0 : bsRemap0.getD hdrOff 0#8 = st.byteVal (p - 3#64) :=
    sc63_bsRemap_getD_hdr st.byteVal g (origBs ++ tailBs) hUserLen hOldMemFit hSt0Nat hLoP hOldSlotFit
      (by dsimp only [extra] at hNewSlotFit; omega)
  clear hSt0Nat
  have hAddrRes1 := (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).2.2.2.2.1
  have hAddrRes5 := (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).2.2.2.2.2
  have hDivEq : (newSz + extra + 4115) / 4096 = needed / 4096 := by
    rw [hNeedEq, Nat.mul_div_cancel _ (by decide)]
  have hNeedSymm := hNeedEq.symm; clear hNeedEq
  have hLsr25 : BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) >>> 12 =
      BitVec.ofNat 64 (needed / 4096) := by
    rw [lsr12_eq_pageDiv (by dsimp only [extra] at hNewSlotFit; omega)]
    exact congrArg (BitVec.ofNat 64) hDivEq
  generalize hv25 : BitVec.ofNat 64 (newSz + (p.toNat - (g.slotStart 0).toNat) + 4115) = v25 at hx25 hLsr25
  clear hv25
  have hBfiPw : g.packedWord &&& 4095#64 ||| ((BitVec.ofNat 64 (needed / 4096) &&& 4503599627370495#64) <<< 12) =
      ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).packedWord :=
    bfi_packedWord_maplen g (by omega) (by omega) (by omega)
  have hCap0Sub : (BitVec.ofNat 64 needed - 20#64) - BitVec.ofNat 64 extra =
      BitVec.ofNat 64 ((needed - 4) - (16 + extra)) := cap0_sub_extra_fine (by omega) (by omega)
  have ⟨hSubsRes, hEqCap32⟩ := subs32_cap_newSz (cap := (needed - 4) - (16 + extra))
    (newSz := newSz) (by omega) (by omega) (by omega)
  have hHdr3Eq : hdrOff + 3 + newSz = 16 + extra + newSz := by dsimp only [hdrOff]; omega
  conv => arg 4; dsimp only [sp1]
  generalize hbsRemap : bsRemap0 = bsRemap
  have hRemapLen : bsRemap.length = needed := hbsRemap ▸ hRemapLen0
  have hRemapHdr : bsRemap.getD hdrOff 0#8 = st.byteVal (p - 3#64) := hbsRemap ▸ hRemapHdr0
  generalize hRestEnv :
    (ReallocSavedLo s0 (s0.sp - 80#64) ∗ ReallocSavedHi s0 (s0.sp - 80#64) ∗
     stackFrameAt (s0.sp - 80#64) 720 ∗ MallocngRoTablesAt maddrs ∗
     (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ memMapped newBase needed ∗
     ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ReallocMremapFrame maddrs tp st g ∗
     MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
     (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
     MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
     ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
     MallocngTightBlock γ p oldSz al ∗ Frame) = RestEnv
  refine (fun {P post} (h : ∀ post', post = post' →
      SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s P post' oom) => h post rfl) ?_
  intro postGoal hPostGoal
  conv => arg 4; arg 1; rw [GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step
  conv => arg 4; arg 1; rw [← GroupDesc.metaBytes_pointsTo g.metaPtr g]
  wp_step; wp_step; wp_step
  wp_str64_slice m1 hm1Perm 16 newBase (by first | rfl | rw [hx0]) (by first | rfl | rw [hx22])
    (by rw [GroupDesc.metaBytes_length]; decide)
  wp_step; wp_step
  wp_str64_slice m2 hm2Perm 32 (({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).packedWord)
    (by rw [hLast0, hSc63])
    (by first | rfl | rw [hx22])
    (by rw [ByteSlice.write64_length _ _ _ (by rw [GroupDesc.metaBytes_length]; decide),
            GroupDesc.metaBytes_length]; decide)
  conv => arg 4; arg 1; rw [metaBytes_write_mem_packedWord g newBase (needed / 4096) _ rfl]
  refine SepWP.weaken_pre (P' := (newBase ↦ₛ bsRemap) ∗
      ((g.metaPtr ↦ₛ ({ g with mem := newBase, maplen := needed / 4096 } : GroupDesc).metaBytes) ∗ RestEnv))
    (Entails.of_eq (by ac_rfl)) ?_
  wp_str8_slice m3 hm3Perm (needed - 4) 0#8 rfl
    (by try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]
        exact (sc63_post_mremap_addrs hNewBaseFit hNewSlotFit).1)
    (by rw [hRemapLen]; omega)
  have hZeroLen : (ByteSlice.write8 bsRemap (needed - 4) 0#8).length = needed :=
    (ByteSlice.write8_length bsRemap (needed - 4) 0#8 (by rw [hRemapLen]; omega)).trans hRemapLen
  have hZeroHdr : (ByteSlice.write8 bsRemap (needed - 4) 0#8).getD hdrOff 0#8 = st.byteVal (p - 3#64) := by
    rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hRemapLen]; omega)]
    simp only [show hdrOff ≠ needed - 4 by dsimp only [hdrOff]; omega, ↓reduceIte, hRemapHdr]
  wp_step; wp_step; wp_step; wp_step
  wp_if hEq0
  · have hRes0 : newRes = 0 := by
      try rw [hx20] at hEq0; try rw [hx21] at hEq0; try rw [hx26] at hEq0
      dsimp only [extra] at hCap0Sub hEqCap32; rw [hCap0Sub] at hEq0
      have h0 := hEqCap32.mp hEq0; dsimp only [newRes, extra]; omega
    apply sepWP_bind_state; intro sFin hsFin
    have hPermEqF : sFin.mem.perm = s.mem.perm := by
      rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm3Perm, hm2Perm, hm1Perm]
    have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
        (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
      rw [hPermEqF]; exact hPermRel
    have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
    have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
    have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
    have hprocF : MallocngProcPreserved s0 sFin := by
      rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
        by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
    have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
    have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
    have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
      rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
    have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
      rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]; try rw [hx24]; rw [hRes0]; decide
    have hcsF : ReallocUntouchedCS s0 sFin := by
      rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
    clear hsFin; subst hPostGoal; rw [← hRestEnv]
    have hSet0 := setSize_case0 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
      (by dsimp only [hdrOff, newRes] at hRes0 ⊢; omega) (by rw [hZeroLen]; omega)
    subst hbsRemap
    refine SepWP.weaken_pre (Entails.of_eq (by
      generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
      generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
      generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
      (SepWP.mono (fine_s3_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sFin st
        hFine hCount hwf hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal
        hNewLo hNewHi hNeedSymm.symm hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF
        hpcF hrunF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx20F hw24F hcsF hZeroLen hZeroHdr hSet0)
        (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))
  · have hSubsRes' : (BitVec.ofNat 64 ((needed - 4) - (16 + extra))).truncate 32 -
        (BitVec.ofNat 64 newSz).truncate 32 = BitVec.ofNat 32 newRes := by
      rw [show (needed - 4) - (16 + extra) - newSz = newRes by dsimp only [newRes]; omega] at hSubsRes
      exact hSubsRes
    have hSubsResZ : BitVec.zeroExtend 32 (BitVec.ofNat 64 ((needed - 4) - (16 + extra))) -
        BitVec.zeroExtend 32 (BitVec.ofNat 64 newSz) = BitVec.ofNat 32 newRes := hSubsRes'
    have hResPos : 1 ≤ newRes := by
      have hNe0 : (needed - 4) - (16 + extra) - newSz ≠ 0 := fun h0 => by
        have hEqTrue := hEqCap32.mpr h0
        exfalso; revert hEq0
        try rw [hx20]; try rw [hx21]; try rw [hx26]
        dsimp only [extra] at hCap0Sub hEqTrue
        rw [hCap0Sub]; simp [hEqTrue]
      dsimp only [newRes]; omega
    have hAddr1 : (newBase + 16#64) + (BitVec.ofNat 64 needed - 20#64) +
        (0#32 - BitVec.ofNat 32 newRes).signExtend 64 =
        newBase + BitVec.ofNat 64 (hdrOff + 3 + newSz) := by
      rw [BitVec.zero_sub, hHdr3Eq]; exact hAddrRes1 hResPos (by omega)
    wp_step; wp_step; wp_step
    wp_str8_slice m4 hm4Perm (hdrOff + 3 + newSz) 0#8 rfl
      (by rw [← hAddr1]; try simp only [wp_norm, arm64_norm]
          try rw [hx0]; try rw [hx20]; try rw [hx21]; try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ ⊢
          try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]; bv_lin)
      (by rw [hZeroLen]; dsimp only [hdrOff]; omega)
    try conv => arg 4; arg 1; rw [Nat.add_comm newSz (hdrOff + 3)]
    have hLen1 : (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8).length = needed :=
      (ByteSlice.write8_length _ _ _ (by rw [hZeroLen]; dsimp only [hdrOff]; omega)).trans hZeroLen
    have hHdr1 : (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8).getD hdrOff 0#8 =
        st.byteVal (p - 3#64) := by
      rw [ByteSlice.getD_write8 _ _ _ _ _ (by rw [hZeroLen]; dsimp only [hdrOff]; omega)]
      simp only [show hdrOff ≠ hdrOff + 3 + newSz by omega, ↓reduceIte, hZeroHdr]
    wp_step
    wp_if hLe4
    · have hResLe4 : newRes ≤ 4 := by
        try rw [hx20] at hLe4; try rw [hx21] at hLe4; try rw [hx26] at hLe4
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
        try rw [hCap0Sub] at hLe4; try rw [hSubsRes'] at hLe4; try rw [hSubsResZ] at hLe4
        rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
            VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 (by omega) (by decide),
            decide_eq_true_eq] at hLe4
        exact hLe4
      apply sepWP_bind_state; intro sFin hsFin
      have hPermEqF : sFin.mem.perm = s.mem.perm := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm4Perm, hm3Perm, hm2Perm, hm1Perm]
      have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
          (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
        rw [hPermEqF]; exact hPermRel
      have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
      have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
      have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
      have hprocF : MallocngProcPreserved s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
          by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
      have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
      have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
        rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
      have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
        rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
        try rw [hx20]; try rw [hx21]; try rw [hx26]
        dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
        try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]
        rcases (by omega : newRes = 0 ∨ newRes = 1 ∨ newRes = 2 ∨ newRes = 3 ∨ newRes = 4) with hR | hR | hR | hR | hR <;>
          (rw [hR]; decide)
      have hcsF : ReallocUntouchedCS s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin; subst hPostGoal; rw [← hRestEnv]
      have hSet14 := setSize_case1to4 (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (by rw [hHdr3Eq]; exact hResPos) (by rw [hHdr3Eq]; exact hResLe4) (by rw [hZeroLen]; omega)
      subst hbsRemap
      refine SepWP.weaken_pre (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
        (SepWP.mono (fine_s3_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sFin st
          hFine hCount hwf hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal
          hNewLo hNewHi hNeedSymm.symm hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF
          hpcF hrunF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx20F hw24F hcsF hLen1 hHdr1 hSet14)
          (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))
    · have hResGe5 : 5 ≤ newRes := by
        have hNotLe : ¬ (newRes ≤ 4) := fun h4 => by
          have hSle : BitVec.sle (BitVec.ofNat 32 newRes) 4#32 = true := by
            rw [show (4#32 : BitVec 32) = BitVec.ofNat 32 4 from rfl,
                VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 (by omega) (by decide),
                decide_eq_true_eq]
            exact h4
          exfalso; revert hLe4
          try rw [hx20]; try rw [hx21]; try rw [hx26]
          dsimp only [extra] at hCap0Sub hSubsRes' hSubsResZ
          try rw [hCap0Sub]; try rw [hSubsRes']; try rw [hSubsResZ]
          simp [hSle]
        omega
      wp_step
      wp_str8_slice m5 hm5Perm ((needed - 4) - 5) 0#8 rfl
        (by rw [← (hAddrRes5 hResGe5).1]; try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]; bv_lin)
        (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)
      have hLen2 : (ByteSlice.write8 (ByteSlice.write8 (ByteSlice.write8 bsRemap (needed - 4) 0#8)
          (hdrOff + 3 + newSz) 0#8) ((needed - 4) - 5) 0#8).length = needed :=
        (ByteSlice.write8_length _ _ _ (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)).trans hLen1
      wp_str32_slice m6 hm6Perm ((needed - 4) - 4) (BitVec.ofNat 32 newRes)
        (by try simp only [wp_norm, arm64_norm]; try rw [hx20]; try rw [hx21]; try rw [hx26]
            dsimp only [extra] at hCap0Sub hSubsRes'; rw [hCap0Sub, hSubsRes'])
        (by rw [← (hAddrRes5 hResGe5).2]; try simp only [wp_norm, arm64_norm]; try rw [hx0]; try rw [hx26]; bv_lin)
        (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega)
      have hLen3 : (ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8
          (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8)
          ((needed - 4) - 5) 0#8) ((needed - 4) - 4) (BitVec.ofNat 32 newRes)).length = needed :=
        (ByteSlice.write32_length _ _ _ (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega)).trans hLen2
      have hHdr3 : (ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8
          (ByteSlice.write8 bsRemap (needed - 4) 0#8) (hdrOff + 3 + newSz) 0#8)
          ((needed - 4) - 5) 0#8) ((needed - 4) - 4) (BitVec.ofNat 32 newRes)).getD hdrOff 0#8 = st.byteVal (p - 3#64) := by
        rw [ByteSlice.getD_write32 _ _ _ _ _ (by rw [hLen2]; dsimp only [newRes] at hResGe5; omega),
            ByteSlice.getD_write8 _ _ _ _ _ (by rw [hLen1]; dsimp only [newRes] at hResGe5; omega)]
        simp only [show ¬ ((needed - 4) - 4 ≤ hdrOff ∧ hdrOff < (needed - 4) - 4 + 4) by dsimp only [hdrOff, newRes] at hResGe5 ⊢; omega,
          show hdrOff ≠ (needed - 4) - 5 by dsimp only [hdrOff, newRes] at hResGe5 ⊢; omega, ↓reduceIte, hHdr1]
      apply sepWP_bind_state; intro sFin hsFin
      have hPermF : (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sFin.mem.perm = s0.mem.perm) ∨
          (∃ m0' : Memory, m0'.perm = s0.mem.perm ∧ sFin.mem.perm = (m0'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm6Perm, hm5Perm, hm4Perm, hm3Perm, hm2Perm, hm1Perm]; exact hPermRel
      have hPermEqF : sFin.mem.perm = s.mem.perm := by
        rw [hsFin]; simp only [wp_norm, arm64_norm]; rw [hm6Perm, hm5Perm, hm4Perm, hm3Perm, hm2Perm, hm1Perm]
      have hpcF : sFin.pc = b + 0x3b8#64 := by rw [hsFin]; simp
      have hrunF : sFin.status = .Running := by rw [hsFin]; simp [hrun]
      have hbrkF : sFin.brk = s0.brk := by rw [hsFin]; simp [hbrk]
      have hprocF : MallocngProcPreserved s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hproc.1], by simp [hproc.2.1], by simp [hproc.2.2.1],
          by simp [hproc.2.2.2.1], by simp [hproc.2.2.2.2.1], by simp [hproc.2.2.2.2.2.1], by simp [hproc.2.2.2.2.2.2]⟩
      have hspF : sFin.sp = s0.sp - 80#64 := by rw [hsFin]; simp [hsp]
      have halF : sFin.spAligned = true := by rw [hsFin]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal
      have hx20F : sFin.readReg64 .x20 = (newBase + 16#64) + BitVec.ofNat 64 extra := by
        rw [hsFin]; dsimp only [Reg.x20]; simp only [wp_norm, arm64_norm]; rfl
      have hw24F : sFin.readReg32 .x24 = BitVec.ofNat 32 (min newRes 5 <<< 5) := by
        rw [hsFin]; dsimp only [State.readReg32, Reg.x24]; simp only [wp_norm, arm64_norm]
        exact mov_0xa0_res5up hResGe5
      have hcsF : ReallocUntouchedCS s0 sFin := by
        rw [hsFin]; exact ⟨by simp [hcs.1], by simp [hcs.2.1], by simpa [calleeSavedVRegs] using hcs.2.2⟩
      clear hsFin; subst hPostGoal; rw [← hRestEnv]
      have hSet5 := setSize_case5up (ByteSlice.write8 bsRemap (needed - 4) 0#8) hdrOff (needed - 4) newSz hdr8
        (BitVec.ofNat 32 newRes) (by rw [hHdr3Eq]; exact hResGe5) (by rw [hHdr3Eq]) (by rw [hZeroLen]; omega)
      subst hbsRemap
      refine SepWP.weaken_pre (Entails.of_eq (by
        generalize (MallocngRoTablesAt maddrs) = PRo; generalize (ReallocMremapFrame maddrs tp st g) = PFr
        generalize (ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal) = PPn
        generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu; ac_rfl))
        (SepWP.mono (fine_s3_finish_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sFin st
          hFine hCount hwf hg hIdx0 origBs tailBs hOrigLe hTailLen hSlot0 hSc63 errnoVal
          hNewLo hNewHi hNeedSymm.symm hNewBaseGe hNewBaseAl hNewBaseFit hOldRw hPermF
          hpcF hrunF hbrkF hprocF htp0 hbrks0 hspF halF hsp0 hx20F hw24F hcsF hLen3 hHdr3 hSet5)
          (fun _ _ _ _ ⟨newQ, hpEq, rest⟩ => ⟨newQ, hpEq.trans hPermEqF, rest⟩))

set_option maxHeartbeats 400000 in
private theorem fine_stage3_mremap_ok [MallocngMultiPlacement] {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 s : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    {p : BitVec 64} {oldSz oldEff newSz inAlign : Nat}
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (origBs tailBs : List (BitVec 8))
    (hpNe : p ≠ 0#64)
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ MallocngMaxAllocSize)
    {Frame : SepProp}
    (hpc : s.pc = b + 0x324#64) (hrun : s.status = .Running)
    (hPerm : s.mem.perm = s0.mem.perm) (hbrk : s.brk = s0.brk)
    (hproc : MallocngProcPreserved s0 s)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hsp : s.sp = s0.sp - 80#64) (hal : s.spAligned = true) (hsp0 : s0.sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = g.mem)
    (hx1 : s.readReg64 .x1 = g.packedWord)
    (hx2 : s.readReg64 .x2 = 131051#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx7 : s.readReg64 .x7 = (g.packedWord.extractLsb' 0 16).zeroExtend 64)
    (hx19 : s.readReg64 .x19 = p)
    (hx20 : s.readReg64 .x20 = g.slotStart idx)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx22 : s.readReg64 .x22 = g.metaPtr)
    (hx23 : s.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hx24 : s.readReg64 .x24 = 0#64)
    (hcs : ReallocUntouchedCS s0 s)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let bf := fineStepRealloc inAlign oldSz newSz bgt
    let stepB := FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)
    let keptBs := origBs.take newSz
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) s
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame)
      (fun sf Pf =>
        ∃ q : BitVec 64,
          MallocngCallAccounting 16 stepB s0 sf ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
          (Pf ⊢ stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) ∗
            Frame))
      (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro sp1 al bf stepB keptBs; have _ := hb
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxLt64 : MallocngMaxAllocSize < 2 ^ 64 := maxAllocSize_lt_pow64
  have hpOld48 : p.toNat + oldSz ≤ 2 ^ 48 :=
    Nat.le_trans hF.p_add_n_le_end hF.stride_bounds.2.2.2.2.2
  have hUserLen : (origBs ++ tailBs).length = oldSz := by simp [hTailLen]; omega
  apply sepWP_abstract_all; intro PGoal1 postGoal1 oomGoal1 hPG1 hPostG1 hOomG1
  wp_step; wp_step; wp_step
  wp_if hls
  · subst hPG1 hPostG1 hOomG1
    apply sepWP_bind_state; intro sA hsA
    have hbrkA : sA.brk = s0.brk := by rw [hsA]; simpa using hbrk
    have htpA : sA.tpidrEl0 = tp := by rw [hsA]; simpa [htp0] using hproc.2.2.1
    have hbrksA : sA.brkStart = brkStart := by rw [hsA]; simpa [hbrks0] using hproc.2.2.2.1
    refine SepWP.weaken_pre
      (fine_repack_read_to_stage4 (al := al) γ tp brkStart bgt bCoarse ivs0 s0 sA st hFine
        origBs tailBs hTailLen hbrkA htpA hbrksA sp1 Frame) ?_
    exact fine_stage4_oop_ok (inAlign := inAlign) hImpl hFree hb γ tp brkStart bgt ivs0 s0 sA origBs
      hpNe hpOld48 hOrigLe hNewMax
      (by rw [hsA]; simp only [wp_norm, arm64_norm, hb])
      (by rw [hsA]; simp [hrun])
      (by rw [hsA]; simpa using hPerm)
      ⟨by rw [hsA]; simpa using hproc.1, by rw [hsA]; simpa using hproc.2.1,
       by rw [hsA]; simpa using hproc.2.2.1, by rw [hsA]; simpa using hproc.2.2.2.1,
       by rw [hsA]; simpa using hproc.2.2.2.2.1, by rw [hsA]; simpa using hproc.2.2.2.2.2.1,
       by rw [hsA]; simpa using hproc.2.2.2.2.2.2⟩
      (by rw [hsA]; simpa using hsp)
      (by rw [hsA]; simp only [wp_norm, arm64_norm, State.spAligned] at hal ⊢; exact hal)
      hsp0
      (by rw [hsA]; simpa using hx19)
      (by rw [hsA]; simpa using hx21)
      (by rw [hsA]; simpa using hx23)
      ⟨by rw [hsA]; simpa using hcs.1, by rw [hsA]; simpa using hcs.2.1,
       by rw [hsA]; simpa [calleeSavedVRegs] using hcs.2.2⟩
      (by rw [hsA]; simpa using hcl)
  · have ⟨hSc63, hNewLo⟩ : g.sc = 63 ∧ 131051 < newSz := by
      have hw6 : BitVec.truncate 32 (BitVec.ofNat 64 g.sc) = BitVec.ofNat 32 g.sc := by bv_omega
      rw [hw6] at hls
      rcases hF.sc_cases with h48 | h63
      · exfalso; apply hls
        have hUltF : (47#32).ult (BitVec.ofNat 32 g.sc) = false := by
          rw [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          change ¬ 47 < g.sc % 4294967296; omega
        rw [hUltF]; simp only [Bool.false_eq_true, ↓reduceIte]; decide
      · refine ⟨h63, Classical.byContradiction fun hLe => hls ?_⟩
        have hUltT : (47#32).ult (BitVec.ofNat 32 63) = true := by decide
        rw [h63, hUltT]; simp only [↓reduceIte, BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat]
        omega
    subst hPG1 hPostG1 hOomG1
    apply sepWP_pure_of_sat (fun R hm =>
      satisfies_readRest_wf (Rest := ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
        stackFrameAt sp1 720 ∗ MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
        MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ Frame ∗ R)
        (Satisfies.mono (Entails.of_eq (by
          generalize (MallocngRoTablesAt maddrs) = PRo
          generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
          ac_rfl)) hm))
    rintro ⟨hCount, hwf⟩
    obtain ⟨hIdxEq0, _hLast0, _, hMpPos, _, _, _, _,
            hMemGe, hMemDvd, hMemFit, _, _, _, hLoP, _, hExtraBound,
            hOldSlotFit, _hNewSlotFit, _, hPageIdem, _hNeedLo, _hNeedDvd,
            _hNeedMax, _hStep, _⟩ :=
      sc63_liveUser_bounds hCount hwf hg hIdx hSlot hSc63 hNewLo hNewMax
    subst hIdxEq0
    let extra := p.toNat - (g.slotStart 0).toNat
    let oldLen := g.maplen * 4096
    let needed := ((newSz + extra + 4115) / 4096) * 4096
    let oldMapBs := mkSc63OldMapBs st.byteVal g p oldSz (origBs ++ tailBs)
    have hOldMapLen : oldMapBs.length = oldLen :=
      mkSc63OldMapBs_length st.byteVal g p oldSz (origBs ++ tailBs) hUserLen
        (Nat.le_trans (by have ⟨_, _, hSt, _, _, _, _, _, _⟩ :=
          VerifiedLibraries.Mallocng.Proofs.group_slot_bounds (hwf.groups_wf g hg) hIdx; omega) hLoP)
        (by omega)
    refine SepWP.weaken_pre
      (fine_extract_to_mremap (al := al) γ tp brkStart bCoarse ivs0 s0 hwf hg hIdx origBs tailBs
        hUserLen hSlot hSc63 sp1 Frame) ?_
    apply SepWP.pure_elim; intro hOvAl
    have hStepT : needed ≤ stepB := by
      have hsw := (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx
      rw [hSlot] at hsw
      obtain ⟨_, _, _, _, _, _, _, _, ⟨hOffLe, hOverLe, hOverOv⟩, _⟩ := hsw
      exact mremap_needed_le_fine hOffLe hOverLe hOverOv hOvAl
    apply SepWP.exists_left; intro errnoVal
    apply sepWP_pure_of_sat (φ := ∀ x, InRegion g.mem oldLen x → s0.mem.perm x = some Perm.rw)
      (fun R hm => by
        intro x hx
        rw [sepConj_assoc] at hm
        have hRw := (IsBlock.pointsToBytes g.mem oldMapBs).perm_rw hm
          (by simpa [hOldMapLen] using hx)
        simpa [hPerm] using hRw)
    intro hOldRw
    have hMapLt52 : g.maplen < 2 ^ 52 := by
      have hgw := hwf.groups_wf g hg
      have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpPos]
      have hFit := hgw.2.2.2.2.2.2.1
      omega
    have hSubExtra : p - g.slotStart 0 = BitVec.ofNat 64 extra := by
      dsimp only [extra]; bv_omega
    have hAdd25a : BitVec.ofNat 64 newSz + 4115#64 = BitVec.ofNat 64 (newSz + 4115) := by bv_omega
    have hAdd25b : BitVec.ofNat 64 (newSz + 4115) + BitVec.ofNat 64 extra =
        BitVec.ofNat 64 (newSz + extra + 4115) := by
      dsimp only [extra] at hExtraBound ⊢; bv_omega
    have hMapMask : g.packedWord &&& -4096#64 = BitVec.ofNat 64 oldLen :=
      VerifiedLibraries.Mallocng.Proofs.packedWord_maplen_mask g hF.last_le_31 (hSc63 ▸ by decide)
        (Nat.le_trans (Nat.le_add_left _ _) hMemFit)
    have hNeedMask : BitVec.ofNat 64 (newSz + extra + 4115) &&& -4096#64 = BitVec.ofNat 64 needed :=
      and_neg4096_eq_pageMul (by dsimp only [extra] at hExtraBound ⊢; omega)
    apply sepWP_abstract_all; intro PGoal2 postGoal2 oomGoal2 hPG2 hPostG2 hOomG2
    wp_step; wp_step; wp_step
    wp_if hne7
    · exfalso
      exact hne7 (packedWord_sc63_mask_trunc_fine g hF.last_le_31 hSc63 hMapLt52)
    · wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
      wp_if hneLen
      · wp_step; wp_step; wp_step
        subst hPG2 hPostG2 hOomG2
        apply sepWP_bind_state; intro sCall hsCall
        have hspCall : sCall.sp = sp1 := by rw [hsCall]; simpa using hsp
        have hmemCall : sCall.mem = s.mem := by rw [hsCall]; simp
        have htpCall : sCall.tpidrEl0 = tp := by rw [hsCall]; simpa [htp0] using hproc.2.2.1
        have hx0Call : sCall.readReg64 .x0 = g.mem := by
          rw [hsCall]; dsimp only [Reg.x0] at hx0 ⊢; simpa using hx0
        have hx1Call : (sCall.readReg64 .x1).toNat = oldLen := by
          have hx1v : sCall.readReg64 .x1 = BitVec.ofNat 64 oldLen := by
            rw [hsCall]; simp only [wp_norm, arm64_norm]
          rw [hx1v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hx2Call : (sCall.readReg64 .x2).toNat = needed := by
          have hx2v : sCall.readReg64 .x2 = BitVec.ofNat 64 needed := by
            rw [hsCall]; simp only [wp_norm, arm64_norm]
          rw [hx2v, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have hx3Call : sCall.readReg32 .x3 = 1#32 := by rw [hsCall]; simp [wp_norm, arm64_norm]
        have hclCall : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem := by rwa [hmemCall]
        have hSf144 : stackFrameAt sp1 720 = (stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) := by
          rw [stackFrameAt_720_split sp1 144 576 (by decide),
              ← stackFrame_eq_stackFrameAt_720 144 (by decide) hspCall]
        have hMrSpec := placed_mremapWrapper_perm_ok (P := blkPC_b14.rebase b (fun _ => none))
          tp g.mem errnoVal oldMapBs oldLen needed hOldMapLen
          (by dsimp only [oldLen]; omega) (Nat.dvd_mul_left 4096 g.maplen)
          hMemDvd hMemFit (by omega) (by intro pc; simp) rfl
        refine SepWP.call_subroutine_frame hMrSpec (x := ())
          (F := stackFrameAt (sp1 - 144#64) 576 ∗
            (g.metaPtr ↦ₛ g.metaBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
            MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
            MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
            (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
            ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
            MallocngTightBlock γ p oldSz al ∗ Frame)
          (ret_pc := b + 0x3e0#64)
          (by rw [hsCall]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
          (by rw [hsCall]; simp [hrun])
          (by rw [hsCall]; simpa [State.spAligned] using hal)
          (by rw [hsCall]; simp)
          (fun R' hm => by
            dsimp only [withCL]
            refine Satisfies.mono ?_ hm
            rw [hSf144]
            refine Entails.trans (Q :=
                (stackFrame sCall 144 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                 (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen) ∗
                (stackFrameAt (sp1 - 144#64) 576 ∗
                 (g.metaPtr ↦ₛ g.metaBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
                 ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                 MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                 MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                 (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                 MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
                 ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                 MallocngTightBlock γ p oldSz al ∗ Frame) ∗ R')
              (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl)) ?_
            refine sepConj_mono_left ?_
            rw [sepConj_comm _ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sCall.mem⌝]
            exact Entails.pure_right hclCall
              (Entails.pure_right ⟨htpCall, hx0Call, hx1Call, hx2Call, hx3Call⟩ (Entails.refl _)))
          (fun _ _ _ hp => not_satisfies_false_sepConj hp)
          (fun _ _ _ _ he => not_satisfies_false_sepConj he)
          ?_
          (fun R' sf _ ho => by
            dsimp only [withCL] at ho
            rw [sepConj_assoc, satisfies_pure_sepConj] at ho
            obtain ⟨⟨hfsO, htrO, hsigO, hpermO, _, hphysO⟩, hmO⟩ := ho
            have hpermCall : sCall.mem.perm = s0.mem.perm := by rwa [hmemCall]
            have hfsCall : sCall.fs = s0.fs := by rw [hsCall]; simpa using hproc.1
            have htrCall : sCall.trace = s0.trace := by rw [hsCall]; simpa using hproc.2.1
            have hsigCall : sCall.sigActions = s0.sigActions := by rw [hsCall]; simpa using hproc.2.2.2.2.2.2
            rw [hPageIdem] at hphysO
            obtain ⟨hPgGe, hPgMod, hPgStep, hPhysNew⟩ :=
              mremap_fine_oom_bounds (maxMeta := fineMaxMetaAreas bgt) (inAlign := inAlign)
                hNewLo hOldSlotFit hphysO
            have hpermSf : sf.mem.perm = s0.mem.perm := hpermO.trans hpermCall
            exact Satisfies.pure_intro
              ⟨hfsO.trans hfsCall, htrO.trans htrCall, hsigO.trans hsigCall,
               [], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hpermSf ▸ ha),
               fun _ => ⟨pageAlignUp newSz, hPgGe, hPgMod, hPgStep, Or.inr hPhysNew⟩⟩
              (Satisfies.drop_left (Satisfies.drop_left hmO)))
        intro sMr hpcMr hrunMr hspMr hcsMr
        obtain ⟨h19Mr, h20Mr, h21Mr, h22Mr, h23Mr, h24Mr, h25Mr, h26Mr, h27Mr, h28Mr, _, hVrMr⟩ := hcsMr
        have hx19Mr : sMr.readReg64 .x19 = p := by
          rw [h19Mr, hsCall]; dsimp only [Reg.x19] at hx19 ⊢; simpa using hx19
        have hx20Mr : sMr.readReg64 .x20 = BitVec.ofNat 64 extra := by
          rw [h20Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hx21Mr : sMr.readReg64 .x21 = BitVec.ofNat 64 newSz := by
          rw [h21Mr, hsCall]; dsimp only [Reg.x21] at hx21 ⊢; simpa using hx21
        have hx22Mr : sMr.readReg64 .x22 = g.metaPtr := by
          rw [h22Mr, hsCall]; dsimp only [Reg.x22] at hx22 ⊢; simpa using hx22
        have hx23Mr : sMr.readReg64 .x23 = p + BitVec.ofNat 64 oldSz := by
          rw [h23Mr, hsCall]; dsimp only [Reg.x23] at hx23 ⊢; simpa using hx23
        have hx24Mr : sMr.readReg64 .x24 = 0#64 := by
          rw [h24Mr, hsCall]; dsimp only [Reg.x24] at hx24 ⊢; simpa using hx24
        have hx25Mr : sMr.readReg64 .x25 = BitVec.ofNat 64 (newSz + extra + 4115) := by
          rw [h25Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hx26Mr : sMr.readReg64 .x26 = BitVec.ofNat 64 needed := by
          rw [h26Mr, hsCall]; simp only [wp_norm, arm64_norm]
        have hcs0Mr : ReallocUntouchedCS s0 sMr :=
          ⟨by rw [h27Mr, hsCall]; dsimp only [Reg.x27]; simpa using hcs.1,
           by rw [h28Mr, hsCall]; dsimp only [Reg.x28]; simpa using hcs.2.1,
           by rw [hVrMr, hsCall]; simpa [calleeSavedVRegs] using hcs.2.2⟩
        have hProc0Call : MallocngProcPreserved s0 sCall :=
          ⟨by rw [hsCall]; simpa using hproc.1, by rw [hsCall]; simpa using hproc.2.1,
           by rw [hsCall]; simpa using hproc.2.2.1, by rw [hsCall]; simpa using hproc.2.2.2.1,
           by rw [hsCall]; simpa using hproc.2.2.2.2.1, by rw [hsCall]; simpa using hproc.2.2.2.2.2.1,
           by rw [hsCall]; simpa using hproc.2.2.2.2.2.2⟩
        have hbrkCall : sCall.brk = s0.brk := by rw [hsCall]; simpa using hbrk
        dsimp only [withCL]
        by_cases hFail : sMr.readReg64 .x0 = BitVec.allOnes 64
        · simp only [hFail, ↓reduceIte]
          refine SepWP.weaken_pre (P' :=
              ∃∗ err32 : BitVec 32,
                ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem ∧
                 MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk ∧
                 sMr.mem.perm = sCall.mem.perm⌝ ∗
                (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                 ((tp - 0xa4#64) ↦₃₂ err32) ∗ (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen ∗
                 (g.metaPtr ↦ₛ g.metaBytes) ∗ MallocngRoTablesAt maddrs ∗
                 (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
                 MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                 (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                 MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
                 ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                 MallocngTightBlock γ p oldSz al ∗ Frame))
            (by
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              refine Entails.sepExists_mono fun err32 => ?_
              refine Entails.trans (Q :=
                  ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem⌝ ∗
                  ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk⌝ ∗
                  ⌜sMr.mem.perm = sCall.mem.perm ∧ MallocngMappedDelta 0 0 sCall.mem sMr.mem⌝ ∗
                  ((stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) ∗
                   ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                   ((tp - 0xa4#64) ↦₃₂ err32) ∗ (g.mem ↦ₛ oldMapBs) ∗ memMapped g.mem oldLen ∗
                   (g.metaPtr ↦ₛ g.metaBytes) ∗ MallocngRoTablesAt maddrs ∗
                   (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗ ReallocMremapFrame maddrs tp st g ∗
                   MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                   (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                   MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
                   ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                   MallocngTightBlock γ p oldSz al ∗ Frame))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun hclM => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun ⟨hpmM, _⟩ => ?_
              exact Entails.pure_right ⟨hclM, hpM, hbM, hpmM⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.exists_left; intro err32
          apply SepWP.pure_elim; rintro ⟨hclMr, hProcMr, hBrkMr, hPermMr⟩
          clear hsCall
          apply sepWP_abstract_all; intro PGoal4 postGoal4 oomGoal4 hPG4 hPostG4 hOomG4
          wp_step; wp_step; wp_step
          subst hPG4 hPostG4 hOomG4
          apply sepWP_bind_state; intro sF hsF
          have hProcMrF : MallocngProcPreserved sMr sF :=
            ⟨by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp,
             by rw [hsF]; simp, by rw [hsF]; simp, by rw [hsF]; simp⟩
          have hProc0F : MallocngProcPreserved s0 sF :=
            mallocngProcPreserved_trans (mallocngProcPreserved_trans hProc0Call hProcMr) hProcMrF
          have hBrkF : sF.brk = sMr.brk := by rw [hsF]; simp
          have hMemF : sF.mem = sMr.mem := by rw [hsF]; simp
          have hBrk0F : sF.brk = s0.brk := hBrkF.trans (hBrkMr.trans hbrkCall)
          have hPerm0F : sF.mem.perm = s0.mem.perm :=
            (congrArg Memory.perm hMemF).trans (hPermMr.trans (by rw [hmemCall]; exact hPerm))
          refine SepWP.weaken_pre
            (fine_unextract_to_stage4 (al := al) γ tp brkStart bgt bCoarse ivs0 s0 sF
              hFine hCount hwf hg hIdx origBs tailBs hUserLen hTailLen hSlot hSc63
              hBrk0F (hProc0F.2.2.1.trans htp0) (hProc0F.2.2.2.1.trans hbrks0) err32 sp1 Frame) ?_
          exact fine_stage4_oop_ok (inAlign := inAlign) hImpl hFree hb γ tp brkStart bgt ivs0 s0 sF origBs
            hpNe hpOld48 hOrigLe hNewMax
            (by rw [hsF]; simp only [wp_norm, arm64_norm, hb])
            (by rw [hsF]; simp [hrunMr])
            hPerm0F hProc0F
            (by rw [hsF]; simpa [hspCall] using hspMr)
            (spAligned_of_sub80 (by rw [hsF]; simpa [hspCall] using hspMr) hsp0)
            hsp0
            (by rw [hsF]; simpa using hx19Mr)
            (by rw [hsF]; simpa using hx21Mr)
            (by rw [hsF]; simpa using hx23Mr)
            ⟨by rw [hsF]; simpa using hcs0Mr.1, by rw [hsF]; simpa using hcs0Mr.2.1,
             by rw [hsF]; simpa [calleeSavedVRegs] using hcs0Mr.2.2⟩
            (by rw [hMemF]; exact hclMr)
        · have hPageIdem' : pageAlignUp needed = needed := hPageIdem
          simp only [hFail, ↓reduceIte, hPageIdem']
          refine SepWP.weaken_pre (P' :=
              ∃∗ newBase : BitVec 64,
                ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk ∧
                 sMr.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
                 4096 ∣ newBase.toNat ∧ newBase.toNat + needed ≤ 2 ^ 48 ∧
                 MallocngMappedDelta 1 needed sCall.mem sMr.mem ∧
                 (∃ m1 : Memory, m1.perm = sCall.mem.perm ∧
                   sMr.mem.perm = (m1.remapRw g.mem oldLen newBase needed).perm)⌝ ∗
                ((g.metaPtr ↦ₛ g.metaBytes) ∗
                 (newBase ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - oldLen) 0#8)) ∗
                 (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                  MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                  memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                  ReallocMremapFrame maddrs tp st g ∗
                  MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                  (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                  MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
                  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                  MallocngTightBlock γ p oldSz al ∗ Frame)))
            (by
              simp only [sepExists_sepConj_left, sepExists_sepConj_right]
              refine Entails.sepExists_mono fun newBase => ?_
              refine Entails.trans (Q :=
                  ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sMr.mem⌝ ∗
                  ⌜MallocngProcPreserved sCall sMr ∧ sMr.brk = sCall.brk⌝ ∗
                  ⌜sMr.readReg64 .x0 = newBase ∧ newBase ≠ 0#64 ∧ newBase ≠ BitVec.allOnes 64 ∧
                   4096 ∣ newBase.toNat ∧ newBase.toNat + needed ≤ 2 ^ 48 ∧
                   MallocngMappedDelta 1 needed sCall.mem sMr.mem ∧
                   (∃ m1 : Memory, m1.perm = sCall.mem.perm ∧
                     sMr.mem.perm = (m1.remapRw g.mem oldLen newBase needed).perm)⌝ ∗
                  ((stackFrame sCall 144 ∗ stackFrameAt (sp1 - 144#64) 576) ∗
                   (g.metaPtr ↦ₛ g.metaBytes) ∗
                   (newBase ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - oldLen) 0#8)) ∗
                   (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗
                    MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
                    memMapped newBase needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
                    ReallocMremapFrame maddrs tp st g ∗
                    MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
                    (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
                    MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
                    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
                    MallocngTightBlock γ p oldSz al ∗ Frame)))
                (Entails.of_eq (by
                  generalize (MallocngRoTablesAt maddrs) = PRo
                  generalize (ReallocMremapFrame maddrs tp st g) = PFr
                  generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
                  ac_rfl)) ?_
              rw [← hSf144]
              refine Entails.pure_left fun _ => Entails.pure_left fun ⟨hpM, hbM⟩ =>
                Entails.pure_left fun hRest => ?_
              exact Entails.pure_right ⟨hpM, hbM, hRest⟩ (Entails.of_eq (by
                generalize (MallocngRoTablesAt maddrs) = PRo
                generalize (ReallocMremapFrame maddrs tp st g) = PFr
                generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
                ac_rfl))) ?_
          apply SepWP.exists_left; intro newBase
          apply SepWP.pure_elim
          rintro ⟨hProcMr, hBrkMr, hx0Mr, hNbNe0, _hNbNe1, hNbDvd, hNbFit, hDeltaMr, m1, hm1P, hMrP⟩
          clear hsCall
          have hNbGe : 4096 ≤ newBase.toNat := by
            obtain ⟨k, hk⟩ := hNbDvd
            have hk0 : k ≠ 0 := fun h0 => hNbNe0 (BitVec.eq_of_toNat_eq (by simp [hk, h0]))
            omega
          apply sepWP_abstract_all; intro PGoal5 postGoal5 oomGoal5 hPG5 hPostG5 hOomG5
          wp_step; wp_step; wp_step
          wp_if heqNeg1
          · exfalso
            try rw [show sMr.readReg64 (Reg.gpr 0#5) = newBase from hx0Mr] at heqNeg1
            try rw [hx0Mr] at heqNeg1
            exact not_add_one_eq_zero_of_le_48_fine (Nat.le_trans (Nat.le_add_right _ _) hNbFit) heqNeg1
          · subst hPG5 hPostG5 hOomG5
            apply sepWP_bind_state; intro sPost hsPost
            have hProcMrP : MallocngProcPreserved sMr sPost :=
              ⟨by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp,
               by rw [hsPost]; simp, by rw [hsPost]; simp, by rw [hsPost]; simp⟩
            have hProc0P : MallocngProcPreserved s0 sPost :=
              mallocngProcPreserved_trans (mallocngProcPreserved_trans hProc0Call hProcMr) hProcMrP
            have hMemPost : sPost.mem = sMr.mem := by rw [hsPost]; simp
            have hBrkPost : sPost.brk = sMr.brk := by rw [hsPost]; simp
            have hPermCall0 : sCall.mem.perm = s0.mem.perm := by rw [hmemCall]; exact hPerm
            have hPermRelP :
                (newBase = g.mem ∧ needed = g.maplen * 4096 ∧ sPost.mem.perm = s0.mem.perm) ∨
                (∃ m1' : Memory, m1'.perm = s0.mem.perm ∧
                  sPost.mem.perm = (m1'.remapRw g.mem (g.maplen * 4096) newBase needed).perm) :=
              Or.inr ⟨m1, hm1P.trans hPermCall0, (congrArg Memory.perm hMemPost).trans hMrP⟩
            refine SepWP.mono
              (fine_s3_post_mremap_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sPost st
                hFine hCount hwf hg hIdx origBs tailBs hOrigLe hTailLen hSlot hSc63
                (newBase := newBase) (needed := needed) (newSz := newSz) errnoVal
                hNewLo hNewMax rfl hNbGe (Nat.mod_eq_zero_of_dvd hNbDvd) hNbFit hOldRw hPermRelP
                (by rw [hsPost]; simp only [wp_norm, arm64_norm, hb])
                (by rw [hsPost]; simp [hrunMr])
                (hBrkPost.trans (hBrkMr.trans hbrkCall))
                hProc0P htp0 hbrks0
                (by rw [hsPost]; simpa [hspCall] using hspMr)
                (spAligned_of_sub80 (by rw [hsPost]; simpa [hspCall] using hspMr) hsp0)
                hsp0
                (by rw [hsPost]; simpa using hx0Mr)
                (by rw [hsPost]; simpa using hx20Mr)
                (by rw [hsPost]; simpa using hx21Mr)
                (by rw [hsPost]; simpa using hx22Mr)
                (by rw [hsPost]; simpa using hx24Mr)
                (by rw [hsPost]; simpa using hx25Mr)
                (by rw [hsPost]; simpa using hx26Mr)
                ⟨by rw [hsPost]; simpa using hcs0Mr.1, by rw [hsPost]; simpa using hcs0Mr.2.1,
                 by rw [hsPost]; simpa [calleeSavedVRegs] using hcs0Mr.2.2⟩) ?_
            intro sf Pf _ _ ⟨newQ, hsfPerm, _, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
            have hsfPermMr : sf.mem.perm = sMr.mem.perm :=
              hsfPerm.trans (congrArg Memory.perm hMemPost)
            have hDelta0Sf : MallocngMappedDelta 16 stepB s0.mem sf.mem :=
              mappedDelta_mono_bounds (by decide : 1 ≤ 16) hStepT
                (mappedDelta_trans_zero_right
                  (mappedDelta_zero_trans_left
                    (mallocngMappedDelta_of_perm_eq hPermCall0) hDeltaMr)
                  (mallocngMappedDelta_of_perm_eq hsfPermMr))
            exact ⟨newQ, ⟨hsfProc, hDelta0Sf⟩, hsfSp, hsfCS, hsfX0, hPf⟩
      · have hNeedEqOld : needed = oldLen := by
          have h := congrArg BitVec.toNat hneLen
          rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
          exact h.symm
        wp_step; wp_step
        wp_if heqNeg1
        · exfalso
          try rw [show s.readReg64 (Reg.gpr 0#5) = g.mem from hx0] at heqNeg1
          try rw [hx0] at heqNeg1
          exact not_add_one_eq_zero_of_le_48_fine (Nat.le_trans (Nat.le_add_right _ _) hMemFit) heqNeg1
        · subst hPG2 hPostG2 hOomG2
          apply sepWP_bind_state; intro sPost hsPost
          have hProc0P : MallocngProcPreserved s0 sPost :=
            ⟨by rw [hsPost]; simpa using hproc.1, by rw [hsPost]; simpa using hproc.2.1,
             by rw [hsPost]; simpa using hproc.2.2.1, by rw [hsPost]; simpa using hproc.2.2.2.1,
             by rw [hsPost]; simpa using hproc.2.2.2.2.1, by rw [hsPost]; simpa using hproc.2.2.2.2.2.1,
             by rw [hsPost]; simpa using hproc.2.2.2.2.2.2⟩
          have hPerm0P : sPost.mem.perm = s0.mem.perm := by rw [hsPost]; simpa using hPerm
          have hBsEq : oldMapBs =
              oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8 := by
            rw [hNeedEqOld]; dsimp only [oldLen]
            rw [List.take_of_length_le (Nat.le_of_eq hOldMapLen), Nat.sub_self,
                List.replicate_zero, List.append_nil]
          refine SepWP.weaken_pre (P' :=
              (g.metaPtr ↦ₛ g.metaBytes) ∗
              (g.mem ↦ₛ (oldMapBs.take needed ++ List.replicate (needed - g.maplen * 4096) 0#8)) ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
               memMapped g.mem needed ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
               ReallocMremapFrame maddrs tp st g ∗
               MallocngLiveAuth γ st.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗
               (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
               MallocngAuxvPtrCell ro maddrs.libc st.auxvPtr ∗ MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap ∗
               ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
               MallocngTightBlock γ p oldSz al ∗ Frame))
            (Entails.of_eq (by
              rw [← hBsEq, hNeedEqOld]
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocMremapFrame maddrs tp st g) = PFr
              generalize (MallocngAuxvStateRo ro γ st.auxvPtr st.auxvSnap) = PAu
              ac_rfl)) ?_
          refine SepWP.mono
            (fine_s3_post_mremap_ok (inAlign := inAlign) hb γ tp brkStart bgt bCoarse ivs0 s0 sPost st
              hFine hCount hwf hg hIdx origBs tailBs hOrigLe hTailLen hSlot hSc63
              (newBase := g.mem) (needed := needed) (newSz := newSz) errnoVal
              hNewLo hNewMax rfl hMemGe (Nat.mod_eq_zero_of_dvd hMemDvd)
              (by rw [hNeedEqOld]; exact hMemFit) hOldRw
              (Or.inl ⟨rfl, hNeedEqOld, hPerm0P⟩)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm, hb])
              (by rw [hsPost]; simp [hrun])
              (by rw [hsPost]; simpa using hbrk)
              hProc0P htp0 hbrks0
              (by rw [hsPost]; simpa using hsp)
              (spAligned_of_sub80 (by rw [hsPost]; simp [hsp]) hsp0)
              hsp0
              (by rw [hsPost]; dsimp only [Reg.x0] at hx0 ⊢; simpa using hx0)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm]; rfl)
              (by rw [hsPost]; dsimp only [Reg.x21] at hx21 ⊢; simpa using hx21)
              (by rw [hsPost]; dsimp only [Reg.x22] at hx22 ⊢; simpa using hx22)
              (by rw [hsPost]; dsimp only [Reg.x24] at hx24 ⊢; simpa using hx24)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm]; rfl)
              (by rw [hsPost]; simp only [wp_norm, arm64_norm])
              ⟨by rw [hsPost]; simpa using hcs.1, by rw [hsPost]; simpa using hcs.2.1,
               by rw [hsPost]; simpa [calleeSavedVRegs] using hcs.2.2⟩) ?_
          intro sf Pf _ _ ⟨newQ, hsfPerm, _, hsfProc, hsfSp, hsfCS, hsfX0, hPf⟩
          exact ⟨newQ, ⟨hsfProc, mappedDelta_mono_bounds (Nat.zero_le _) (Nat.zero_le _)
            (mallocngMappedDelta_of_perm_eq (hsfPerm.trans hPerm0P))⟩,
            hsfSp, hsfCS, hsfX0, hPf⟩

/-! ## 6. Non-Null Dispatcher, Placed `__libc_realloc` (`blk14`), & Exported `"realloc"` (`blk13`) -/

private theorem procPreserved_setPState_setPC_fine {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : MallocngProcPreserved s0 s) :
    MallocngProcPreserved s0 ((s.setPState ps).setPC pc) := h

private theorem untouchedCS_setPState_setPC_fine {s0 s : State} (ps : PState) (pc : BitVec 64)
    (h : ReallocUntouchedCS s0 s) :
    ReallocUntouchedCS s0 ((s.setPState ps).setPC pc) :=
  ⟨h.1, h.2.1, h.2.2⟩

private theorem fine_post_sc_ok [MallocngMultiPlacement] {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p : BitVec 64) (inAlign : Nat)
    (oldSz oldEff newSz : Nat) (origBs tailBs : List (BitVec 8))
    (bgt : FineBudget) (bCoarse : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sSc : State) (st : MallocngSt)
    (hFine : MallocngFineInv bgt ivs0 st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hpNe : p ≠ 0#64)
    (hOrigLe : origBs.length ≤ oldSz) (hTailLen : tailBs.length = oldSz - origBs.length)
    (hSlot : g.slots[idx]'hIdx = .liveUser p oldSz oldEff)
    (hF : LiveUserBlockFacts st g idx p oldSz oldEff)
    (hNewMax : newSz ≤ MallocngMaxAllocSize) (hNew131 : newSz ≤ 131051)
    (hFit : p.toNat + newSz ≤ (g.slotEnd idx).toNat)
    (hpcSc : sSc.pc = b + 0x258#64) (hrunSc : sSc.status = .Running)
    (hPermSc : sSc.mem.perm = s0.mem.perm) (hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem)
    (hbrkSc0 : sSc.brk = s0.brk) (hprocSc0 : MallocngProcPreserved s0 sSc)
    (htp0 : s0.tpidrEl0 = tp) (hbrks0 : s0.brkStart = brkStart)
    (hspSc0 : sSc.sp = s0.sp - 80#64) (hspMask0 : s0.sp &&& 15#64 = 0#64)
    (hw2_sc : sSc.readReg32 .x2 = BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1))
    (hx3Sc0 : sSc.readReg64 .x3 = BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat))
    (hx4Sc0 : sSc.readReg64 .x4 = (BitVec.ofNat 32 idx).zeroExtend 64)
    (hx5Sc0 : sSc.readReg64 .x5 = g.slotEnd idx)
    (hx6Sc0 : sSc.readReg64 .x6 = BitVec.ofNat 64 g.sc)
    (hx19Sc0 : sSc.readReg64 .x19 = p)
    (hx21_sc : sSc.readReg64 .x21 = BitVec.ofNat 64 newSz)
    (hx23Sc0 : sSc.readReg64 .x23 = p + BitVec.ofNat 64 oldSz)
    (hcsSc0 : ReallocUntouchedCS s0 sSc)
    {post : State → SepProp → Prop}
    (hFinishPost : ∀ sf Pf,
      (∃ q : BitVec 64,
        MallocngCallAccounting 16
          (FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)) s0 sf ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
        (Pf ⊢ stackFrame s0 800 ∗
          MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
            γ maddrs tp brkStart (fineStepRealloc inAlign oldSz newSz bgt) ivs0 s0 sf ∗
          ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q
            (newSz, max inAlign 16, origBs.take newSz)⌝ ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q
            (newSz, max inAlign 16, origBs.take newSz) ∗ emp)) →
      post sf Pf) :
    let sp1 := s0.sp - 80#64
    let al := max inAlign 16
    let stepB := FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 .x30) sSc
      (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
       MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
       ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
       MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
       MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
      post
      (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro sp1 al stepB; have _ := hb
  apply sepWP_abstract_all; intro PG postG oomG hPG hPostG hOomG
  generalize hw2Val : BitVec.ofNat 32 (sizeToClassUnits ((newSz + 3) / 16) + 1) = w2v at hw2_sc
  wp_step; wp_step
  wp_if hleSc
  · subst hPG hPostG hOomG
    have hScLt31 : g.sc < 2 ^ 31 := by rcases hF.sc_cases with h | h <;> omega
    have hUnitsLt48 : sizeToClassUnits ((newSz + 3) / 16) < 48 := nomSc_lt_48 hNew131
    have hScLe : g.sc ≤ sizeToClassUnits ((newSz + 3) / 16) + 1 := by
      have hTrunc6 : BitVec.truncate 32 (BitVec.ofNat 64 g.sc) = BitVec.ofNat 32 g.sc := by bv_omega
      dsimp only [State.readReg32] at hw2_sc
      try rw [hx6Sc0] at hleSc
      try rw [hw2_sc] at hleSc
      rw [hTrunc6, ← hw2Val,
          VerifiedLibraries.Mallocng.Proofs.bv32_sle_iff_of_lt31 hScLt31 (by omega),
          decide_eq_true_eq] at hleSc
      exact hleSc
    apply sepWP_bind_state; intro sS2 hsS2
    refine SepWP.mono (fine_stage2_inplace_ok (inAlign := inAlign) hb
      γ tp brkStart bgt bCoarse ivs0 s0 sS2 st hFine hg hIdx origBs tailBs
      hOrigLe hTailLen hSlot hNew131 hFit hScLe (Frame := emp)
      (by rw [hsS2, State.pc_setPC])
      (by rw [hsS2, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hsS2, State.mem_setPC, State.mem_setPState]; exact hPermSc)
      (by rw [hsS2, State.brk_setPC, State.brk_setPState]; exact hbrkSc0)
      (by rw [hsS2]; exact procPreserved_setPState_setPC_fine _ _ hprocSc0) htp0 hbrks0
      (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS2, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx3Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx4Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx5Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS2, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS2]; exact untouchedCS_setPState_setPC_fine _ _ hcsSc0)) ?_
    intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf, hPf⟩
    exact hFinishPost sf Pf
      ⟨p, ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩, hspSf, hcsSf, hx0Sf, hPf⟩
  · subst hPG hPostG hOomG
    apply sepWP_bind_state; intro sS4 hsS4
    have hmS4 : sS4.mem = sSc.mem := by rw [hsS4, State.mem_setPC, State.mem_setPState]
    have hbrkS4 : sS4.brk = s0.brk := by rw [hsS4, State.brk_setPC, State.brk_setPState]; exact hbrkSc0
    have hprocS4 : MallocngProcPreserved s0 sS4 := by
      rw [hsS4]; exact procPreserved_setPState_setPC_fine _ _ hprocSc0
    refine SepWP.weaken_pre (fine_repack_read_to_stage4 (al := al) γ tp brkStart bgt bCoarse ivs0
      s0 sS4 st hFine origBs tailBs hTailLen hbrkS4 (hprocS4.2.2.1.trans htp0)
      (hprocS4.2.2.2.1.trans hbrks0) sp1 emp) ?_
    refine SepWP.mono (fine_stage4_oop_ok (inAlign := inAlign) hImpl hFree hb
      γ tp brkStart bgt ivs0 s0 sS4 origBs (Frame := emp)
      hpNe (Nat.le_trans hF.p_add_n_le_end hF.stride_bounds.2.2.2.2.2) hOrigLe hNewMax
      (by rw [hsS4, State.pc_setPC])
      (by rw [hsS4, State.status_setPC, State.status_setPState]; exact hrunSc)
      (by rw [hmS4]; exact hPermSc) hprocS4
      (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0)
      (spAligned_of_sub80 (by rw [hsS4, State.sp_setPC, State.sp_setPState]; exact hspSc0) hspMask0)
      hspMask0
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx19Sc0)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx21_sc)
      (by rw [hsS4, State.readReg64_setPC, State.readReg64_setPState]; exact hx23Sc0)
      (by rw [hsS4]; exact untouchedCS_setPState_setPC_fine _ _ hcsSc0)
      (by rw [hmS4]; exact hclSc))
      (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)

set_option maxHeartbeats 400000 in
private theorem fine_realloc_nonnull_path_ok [MallocngMultiPlacement] {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 14 b)
    (γ : GhostName) (tp brkStart p newSize : BitVec 64) (inAlign : Nat)
    (oldSz : Nat) (origBs : List (BitVec 8))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 : State) (R : SepProp)
    (hpWf : (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf p (oldSz, inAlign, origBs))
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hsp0 : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = p) (hx1 : s0.readReg64 .x1 = newSize)
    (hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let keptBs := origBs.take newSize.toNat
    let ev := AllocEvent.realloc inAlign oldSz newSize.toNat
    let al := max inAlign 16
    let bf := if ok then mallocngFineCostModel.step ev bgt else bgt
    let stepB := if ok then mallocngFineCostModel.stepReserve ev bgt
      else mallocngFineCostModel.stepReserve (.alloc 0) bgt
    SepWP (blkPC_b14.rebase b (fun _ => none)) (s0.readReg64 Reg.lr) s0
      (stackFrame s0 800 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
       (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs))
      (fun sf Pf =>
        (sf.mem ⊨ Pf ∗ R →
          sf.mem ⊨
            ((⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
              stackFrame s0 800 ∗
              MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                γ maddrs tp brkStart bf ivs0 s0 sf ∗
              if ok then
                ∃∗ q : BitVec 64,
                  ⌜sf.readReg64 .x0 = q ∧
                   (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, al, keptBs)⌝ ∗
                  (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, al, keptBs)
              else
                ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs)) ∗
             ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗ R) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) := by
  intro ok keptBs ev al bf stepB; have _ := hb
  obtain ⟨hpNe, hpAlign, _hpOld64, hOrigLe⟩ := hpWf
  have hspMask0 : s0.sp &&& 15#64 = 0#64 := of_decide_eq_true hsp0
  have hspAlign80 : (s0.sp - 80#64) &&& 15#64 = 0#64 := by revert hspMask0; bv_robdd
  let sp1 := s0.sp - 80#64
  refine sepWP_mono_cl (post := fun sf Pf =>
      (sf.mem ⊨ Pf ∗ R →
        sf.mem ⊨
          (⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
            stackFrame s0 800 ∗
            MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
              γ maddrs tp brkStart bf ivs0 s0 sf ∗
            if ok then
              ∃∗ q : BitVec 64,
                ⌜sf.readReg64 .x0 = q ∧
                 (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, al, keptBs)⌝ ∗
                (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, al, keptBs)
            else
              ⌜sf.readReg64 .x0 = 0#64⌝ ∗
              (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs)) ∗ R) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
    hcl0 ?_ (fun sf Pf _ _ hclSf ⟨hq, hspF, hcsF⟩ =>
      ⟨fun hm => Satisfies.mono (sepConj_mono_left
        (Entails.trans (Entails.pure_right hclSf (Entails.refl _))
          (Entails.of_eq (sepConj_comm _ _)))) (hq hm), hspF, hcsF⟩)
  refine SepWP.weaken_pre (sepConj_mono_left (stackFrame800_entails_exists_cells s0)) ?_
  simp only [sepExists_sepConj_left]
  apply SepWP.exists_left; intro v0; apply SepWP.exists_left; intro v1
  apply SepWP.exists_left; intro v2; apply SepWP.exists_left; intro v3
  apply SepWP.exists_left; intro v4; apply SepWP.exists_left; intro v5
  apply SepWP.exists_left; intro v6; apply SepWP.exists_left; intro v7
  apply SepWP.exists_left; intro v8; apply SepWP.exists_left; intro v9
  wp_stp64_cl m1 hm1 hcl0 hcl1
  wp_step
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_step; wp_step
  wp_if hzP
  · exact absurd hzP hpNe
  · wp_stp64_cl m3 hm3 hcl2 hcl3
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_if hhiMax
    · have hNotLe : ¬ (newSize.toNat ≤ MallocngMaxAllocSize) :=
        (ult_maxAllocBv_iff newSize).mp hhiMax
      have hOkFalse : ok = false := decide_eq_false hNotLe
      have hBfEq : bf = bgt := by dsimp only [bf]; simp [hOkFalse]; rfl
      apply sepWP_bind_state; intro sEn hsEn
      have hPermEn : sEn.mem.perm = s0.mem.perm := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rw [hmEq, hm3, hm2, hm1]
      have hclEn : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sEn.mem := by
        have hmEq : sEn.mem = m3 := by rw [hsEn]; rfl
        rwa [hmEq]
      have hEnvEn :
          MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 =
          MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 sEn := by
        unfold MallocngModelEnv; rw [hsEn]; rfl
      have hLoPack :
          (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
           ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
           ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
           ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
           ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) ⊢
          ReallocSavedLo s0 sp1 ∗ (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
            memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) := by
        dsimp only [ReallocSavedLo, sp1]
        rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
            show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
            show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
            show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
            show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
        have hGrp :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
             ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9)) =
            ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
              ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
              ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22)) ∗
             (((s0.sp - 32#64) ↦₆₄ v6) ∗ ((s0.sp - 24#64) ↦₆₄ v7) ∗
              ((s0.sp - 16#64) ↦₆₄ v8) ∗ ((s0.sp - 8#64) ↦₆₄ v9))) := by ac_rfl
        rw [hGrp]
        exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))))
      rw [hEnvEn]
      refine SepWP.weaken_pre (P' := ReallocSavedLo s0 sp1 ∗
          (memRegion (sp1 + 48#64) 8 ∗ memRegion (sp1 + 56#64) 8 ∗
           memRegion (sp1 + 64#64) 8 ∗ memRegion (sp1 + 72#64) 8) ∗
          stackFrameAt sp1 720 ∗
          MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 sEn ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs))
        (Entails.trans (sepConj_mono_left (sepConj_mono_left hLoPack))
          (Entails.of_eq (by
            dsimp only [MallocngModelInitBlock, sp1]
            generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 sEn) = PEnv
            ac_rfl))) ?_
      refine SepWP.mono (fine_realloc_enomem_ok hb γ tp brkStart bgt ivs0 s0 sEn
        (Rest := (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs))
        (by rw [hsEn]; simp) (by rw [hsEn]; simp [hrun]) hPermEn (by rw [hsEn]; rfl)
        (by rw [hsEn]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by rw [hsEn]; simp)
        (spAligned_of_sub80 (by rw [hsEn]; simp) hspMask0) hspMask0
        (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp) (by rw [hsEn]; simp)
        (by rw [hsEn]; exact ⟨by simp, by simp, by simp [calleeSavedVRegs]⟩) hclEn) ?_
      intro sf Pf _ _ ⟨hPermSf, _, hProcSf, hspSf, hcsSf, hx0Sf, hPf⟩
      refine ⟨fun hm => ?_, hspSf, hcsSf⟩
      have hAcc : MallocngCallAccounting 16 stepB s0 sf :=
        ⟨hProcSf, mallocngMappedDelta_of_perm_eq hPermSf⟩
      simp only [hOkFalse, Bool.false_eq_true, ↓reduceIte, hBfEq] at hAcc ⊢
      refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
      refine Entails.trans (sepConj_mono_left (Entails.pure_right hAcc
        (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hx0Sf (Entails.refl _)))))) ?_
      exact Entails.of_eq (by
        dsimp only [MallocngModelInitBlock]
        try ac_rfl)
    · have hNewMax : newSize.toNat ≤ MallocngMaxAllocSize :=
        Classical.not_not.mp (mt (ult_maxAllocBv_iff newSize).mpr hhiMax)
      have hOkTrue : ok = true := decide_eq_true hNewMax
      let newSz := newSize.toNat
      have hBfTrue : bf = fineStepRealloc inAlign oldSz newSz bgt := by
        dsimp only [bf, ev, newSz]; simp [hOkTrue, mallocngFineCostModel_step, fineStep]; rfl
      have hStepTrue : stepB =
          FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz) := by
        dsimp only [stepB, ev, newSz]; rw [fine_stepB_ite]; simp [hOkTrue, evReqBytes]
      wp_stp64_cl m4 hm4 hcl3 hcl4; wp_step; wp_stp64_cl m5 hm5 hcl4 hcl5; wp_step
      wp_if hneAlign
      · exact absurd (align16_and15_eq_zero hpAlign) hneAlign
      · apply sepWP_bind_state; intro s1 hs1
        have hPerm1 : s1.mem.perm = s0.mem.perm := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rw [hmEq, hm5, hm4, hm3, hm2, hm1]
        have hcl1' : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by
          have hmEq : s1.mem = m5 := by rw [hs1]; rfl
          rwa [hmEq]
        have hSavedEq :
            (((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x26)) =
            (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) := by
          dsimp only [ReallocSavedLo, ReallocSavedHi, sp1]
          rw [show s0.sp - 80#64 + 8#64 = s0.sp - 72#64 by bv_lin, show s0.sp - 80#64 + 16#64 = s0.sp - 64#64 by bv_lin,
              show s0.sp - 80#64 + 24#64 = s0.sp - 56#64 by bv_lin, show s0.sp - 80#64 + 32#64 = s0.sp - 48#64 by bv_lin,
              show s0.sp - 80#64 + 40#64 = s0.sp - 40#64 by bv_lin, show s0.sp - 80#64 + 48#64 = s0.sp - 32#64 by bv_lin,
              show s0.sp - 80#64 + 56#64 = s0.sp - 24#64 by bv_lin, show s0.sp - 80#64 + 64#64 = s0.sp - 16#64 by bv_lin,
              show s0.sp - 80#64 + 72#64 = s0.sp - 8#64 by bv_lin]
          ac_rfl
        have hUnpackPre :
            ((ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1) ∗ stackFrameAt sp1 720) ∗
            MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
            (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs) ⊢
            ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
            ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget, ∃∗ g : GroupDesc,
            ∃∗ idx : Nat, ∃∗ oldEff : Nat, ∃∗ tailBs : List (BitVec 8),
              ⌜(MallocngFineInv bgt ivs0 st ∧
                g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff) ∧
               tailBs.length = oldSz - origBs.length⌝ ∗
              reallocReadPre maddrs st
                (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
                 MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
                 MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs))) := by
          dsimp only [MallocngModelEnv, MallocngModelInitBlock, al]
          rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq, mallocngFineModeIface_block_eq]
          have hUnpackH := fineHeap_read_liveUser_unpackTight (ro := ro) γ maddrs tp brkStart s0.brk bgt ivs0
            p oldSz (max inAlign 16)
          have hTailE := memRegion_entails_exists_pointsToBytes (oldSz - origBs.length)
            (p + BitVec.ofNat 64 origBs.length) (by omega)
          refine Entails.trans (Q :=
              ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
              (FineHeapModeImpl ro γ maddrs tp brkStart s0.brk bgt ivs0 ∗
               MallocngTightBlock γ p oldSz (max inAlign 16)) ∗
              (p ↦ₛ origBs) ∗ memRegion (p + BitVec.ofNat 64 origBs.length) (oldSz - origBs.length) ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720))
            (Entails.of_eq (by
              dsimp only [FineHeapModeImpl]
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          refine sepConj_mono_right ?_
          refine Entails.trans (sepConj_mono hUnpackH (sepConj_mono_right (sepConj_mono_left hTailE))) ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun st => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun bCoarse => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun g => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun idx => ?_
          rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun oldEff => ?_
          rw [sepExists_sepConj_left]; rw [sepExists_sepConj_right]; rw [sepExists_sepConj_right]
          refine Entails.sepExists_mono fun tailBs => ?_
          refine Entails.trans (Q :=
              ⌜MallocngFineInv bgt ivs0 st ∧
                g ∈ st.groups ∧
                (∃ hIdx : idx < g.slots.length, g.slots[idx]'hIdx = .liveUser p oldSz oldEff) ∧
                LiveUserBlockFacts st g idx p oldSz oldEff ∧
                st.liveMap.ov p ≤ max inAlign 16 - 16⌝ ∗
              ⌜tailBs.length = oldSz - origBs.length⌝ ∗
              ((p ↦ₛ origBs) ∗ ((p + BitVec.ofNat 64 origBs.length) ↦ₛ tailBs)) ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
              MallocngTightBlock γ p oldSz (max inAlign 16))
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          refine Entails.pure_left fun ⟨hF0, hF1, hF2, hF3, _⟩ => Entails.pure_left fun hTLen => ?_
          refine Entails.pure_right ⟨⟨hF0, hF1, hF2, hF3⟩, hTLen⟩ ?_
          rw [← pointsToBytes_append p origBs tailBs]
          unfold reallocReadPre
          exact Entails.of_eq (by
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            ac_rfl)
        rw [hSavedEq]
        refine SepWP.weaken_pre hUnpackPre ?_
        apply SepWP.pure_elim; rintro ⟨htp0, hbrks0⟩
        apply SepWP.exists_left; intro st; apply SepWP.exists_left; intro bCoarse
        apply SepWP.exists_left; intro g; apply SepWP.exists_left; intro idx
        apply SepWP.exists_left; intro oldEff; apply SepWP.exists_left; intro tailBs
        apply SepWP.pure_elim; rintro ⟨⟨hFine, hg, ⟨hIdx, hSlot⟩, hF⟩, hTailLen⟩
        apply SepWP.seq (realloc_stage1_read_ok hb hF
          (by rw [hs1]; simp) (by rw [hs1]; simp [hrun])
          (by rw [hs1]; simp) (by rw [hs1]))
        intro s7 P7 hpc7 hrun7
          ⟨⟨hP17, hx0_7, hx1_7, hx3_7, hx4_7, hx5_7, hx6_7, hx7_7, hx19_7, hx20_7, hx21_7, hx22_7, hx23_7, hx24_7⟩, hEnt7⟩
        refine SepWP.weaken_pre hEnt7 ?_
        obtain ⟨hmem17, hbrk17, hproc17, hsp17, _, _, _, hcs17⟩ := hP17
        have hPerm7 : s7.mem.perm = s0.mem.perm := by rw [hmem17, hPerm1]
        have hcl7 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s7.mem := by rwa [hmem17]
        have hbrk7 : s7.brk = s0.brk := hbrk17.trans (by rw [hs1]; rfl)
        have hproc7 : MallocngProcPreserved s0 s7 :=
          mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hproc17
        have hsp7 : s7.sp = s0.sp - 80#64 := hsp17.trans (by rw [hs1]; simp)
        have hcs7 : ReallocUntouchedCS s0 s7 := by
          obtain ⟨h27, h28, hv⟩ := hcs17
          exact ⟨h27.trans (by rw [hs1]; simp), h28.trans (by rw [hs1]; simp),
            hv.trans (by rw [hs1]; simp [calleeSavedVRegs])⟩
        refine SepWP.weaken_pre (P' :=
            ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
            MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
            ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
            MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
            MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
          (Entails.of_eq (by
            unfold reallocReadPre
            generalize (MallocngRoTablesAt maddrs) = PRo
            generalize (MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st) = PRest
            generalize (ReallocSavedLo s0 sp1) = PLo
            generalize (ReallocSavedHi s0 sp1) = PHi
            simp only [sepConj_emp]; ac_rfl)) ?_
        have hFinishPost : ∀ sf Pf,
            (∃ q : BitVec 64,
              MallocngCallAccounting 16
                (FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)) s0 sf ∧
              sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.readReg64 .x0 = q ∧
              (Pf ⊢ stackFrame s0 800 ∗
                MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                  γ maddrs tp brkStart (fineStepRealloc inAlign oldSz newSz bgt) ivs0 s0 sf ∗
                ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
                (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) ∗ emp)) →
            (sf.mem ⊨ Pf ∗ R →
              sf.mem ⊨
                (⌜MallocngCallAccounting 16 stepB s0 sf⌝ ∗
                  stackFrame s0 800 ∗
                  MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro)
                    γ maddrs tp brkStart bf ivs0 s0 sf ∗
                  if ok then
                    ∃∗ q : BitVec 64,
                      ⌜sf.readReg64 .x0 = q ∧
                       (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, al, keptBs)⌝ ∗
                      (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, al, keptBs)
                  else
                    ⌜sf.readReg64 .x0 = 0#64⌝ ∗
                    (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
          rintro sf Pf ⟨q, hAcc, hspSf, hcsSf, hx0Q, hPf⟩
          refine ⟨fun hm => ?_, hspSf, hcsSf⟩
          simp only [hOkTrue, ↓reduceIte, hBfTrue, hStepTrue]
          change sf.mem ⊨ _ at hm
          refine Satisfies.mono ?_ (Satisfies.mono (sepConj_mono_left hPf) hm)
          rw [sepConj_emp]
          have hRetEnt :
              ⌜(MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSz, al, keptBs)⌝ ∗
              (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSz, al, keptBs) ⊢
              ∃∗ q' : BitVec 64,
                ⌜sf.readReg64 .x0 = q' ∧
                 (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q' (newSz, al, keptBs)⌝ ∗
                (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q' (newSz, al, keptBs) :=
            Entails.sepExists_right q
              (Entails.pure_left fun hWfQ => Entails.pure_right ⟨hx0Q, hWfQ⟩ (Entails.refl _))
          exact sepConj_mono_left
            (Entails.pure_right hAcc (sepConj_mono_right (sepConj_mono_right hRetEnt)))
        have hOomEq :
            (fun sf => ⌜MallocngStepOomCond msvc stepB s0 sf⌝) =
            (fun sf => ⌜MallocngStepOomCond msvc
              (FineStepBound (fineMaxMetaAreas bgt) (mallocngAlignedEffSize inAlign newSz)) s0 sf⌝) := by
          funext sf; rw [hStepTrue]
        rw [hOomEq]
        have hlr0 : s0.readReg64 Reg.lr = s0.readReg64 .x30 := rfl
        rw [hlr0]
        have _ := hx3_7; have _ := hx21_7
        wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
        wp_if hhiStage3
        · apply sepWP_bind_state; intro sS3 hsS3
          refine SepWP.mono (fine_stage3_mremap_ok (inAlign := inAlign) hImpl hFree hb
            γ tp brkStart bgt bCoarse ivs0 s0 sS3 st hFine hg hIdx origBs tailBs
            hpNe hOrigLe hTailLen hSlot hF hNewMax
            (Frame := emp)
            (by rw [hsS3]; simp) (by rw [hsS3]; simp [hrun7])
            (by rw [hsS3]; simpa using hPerm7) (by rw [hsS3]; simpa using hbrk7)
            (by rw [hsS3]; exact hproc7) htp0 hbrks0
            (by rw [hsS3]; simpa using hsp7)
            (spAligned_of_sub80 (by rw [hsS3]; simpa using hsp7) hspMask0) hspMask0
            (by rw [hsS3]; simpa using hx0_7) (by rw [hsS3]; simpa using hx1_7)
            (by rw [hsS3]; simp) (by rw [hsS3]; simpa using hx6_7)
            (by rw [hsS3]; simpa using hx7_7) (by rw [hsS3]; simpa using hx19_7)
            (by rw [hsS3]; simpa using hx20_7) (by rw [hsS3]; simpa [newSz] using hx21_7)
            (by rw [hsS3]; simpa using hx22_7) (by rw [hsS3]; simpa using hx23_7)
            (by rw [hsS3]; simpa using hx24_7)
            (by rw [hsS3]; exact ⟨hcs7.1, hcs7.2.1, hcs7.2.2⟩)
            (by rw [hsS3]; exact hcl7))
            (fun sf Pf _ _ hPost => hFinishPost sf Pf hPost)
        · have hP7Cond : ¬ ((if (BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat)).ule 131051#64 then
              BitVec.ofNat 64 ((g.slotEnd idx).toNat - p.toNat) else 131051#64).ult
              (BitVec.ofNat 64 newSz) = true) := by simpa [newSz] using hhiStage3
          have ⟨hNew131, hFit⟩ := not_stage3_hi_bounds
            (Nat.le_trans (Nat.le_add_right _ _) hF.p_add_n_le_end)
            hF.stride_bounds.2.2.2.2.2 hNewMax hP7Cond
          apply sepWP_bind_state; intro sSc0 hsSc0
          refine SepWP.weaken_pre (P' :=
              MallocngRoTablesAt maddrs ∗
              (ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
               (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
               ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
               MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
               MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp))
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          apply SepWP.seq (realloc_sizeToClass_ok hb (newSize := BitVec.ofNat 64 newSz) rfl hNew131
            (by rw [hsSc0]; simp) (by rw [hsSc0]; simp [hrun7])
            (by rw [hsSc0]; simpa [newSz] using hx21_7))
          intro sSc PSc hpcSc hrunSc
            ⟨⟨hPSc, hw2_sc, hx3_sc, hx4_sc, hx5_sc, hx6_sc, hx19_sc, _, hx21_sc, _, hx23_sc, _⟩, hEntSc⟩
          refine SepWP.weaken_pre hEntSc ?_
          refine SepWP.weaken_pre (P' :=
              ReallocSavedLo s0 sp1 ∗ ReallocSavedHi s0 sp1 ∗ stackFrameAt sp1 720 ∗
              MallocngRoTablesAt maddrs ∗ (maddrs.ctx ↦ₛ st.ctx.toBytes) ∗
              ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
              MallocngReadRestMode ro γ maddrs tp brkStart s0.brk bCoarse ivs0 st ∗
              MallocngTightBlock γ p oldSz al ∗ (p ↦ₛ (origBs ++ tailBs)) ∗ emp)
            (Entails.of_eq (by
              generalize (MallocngRoTablesAt maddrs) = PRo
              generalize (ReallocSavedLo s0 sp1) = PLo
              generalize (ReallocSavedHi s0 sp1) = PHi
              ac_rfl)) ?_
          obtain ⟨hmemSc, hbrkSc, hprocSc, hspSc, _, _, _, hcsSc⟩ := hPSc
          have hPermSc : sSc.mem.perm = s0.mem.perm := by rw [hmemSc, hsSc0]; exact hPerm7
          have hclSc : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sSc.mem := by rw [hmemSc, hsSc0]; exact hcl7
          have hbrkSc0 : sSc.brk = s0.brk := hbrkSc.trans (by rw [hsSc0]; exact hbrk7)
          have hprocSc0 : MallocngProcPreserved s0 sSc :=
            mallocngProcPreserved_trans (by rw [hsSc0]; exact hproc7) hprocSc
          have hspSc0 : sSc.sp = s0.sp - 80#64 := hspSc.trans (by rw [hsSc0]; exact hsp7)
          have hcsSc0 : ReallocUntouchedCS s0 sSc :=
            ⟨hcsSc.1.trans (by rw [hsSc0]; exact hcs7.1),
              hcsSc.2.1.trans (by rw [hsSc0]; exact hcs7.2.1),
              hcsSc.2.2.trans (by rw [hsSc0]; exact hcs7.2.2)⟩
          exact fine_post_sc_ok hImpl hFree hb γ tp brkStart p inAlign oldSz oldEff newSz origBs tailBs
            bgt bCoarse ivs0 s0 sSc st hFine hg hIdx hpNe hOrigLe hTailLen hSlot hF hNewMax hNew131 hFit
            hpcSc hrunSc hPermSc hclSc hbrkSc0 hprocSc0 htp0 hbrks0 hspSc0 hspMask0 hw2_sc
            (hx3_sc.trans (by rw [hsSc0]; simpa using hx3_7))
            (hx4_sc.trans (by rw [hsSc0]; simpa using hx4_7))
            (hx5_sc.trans (by rw [hsSc0]; simpa using hx5_7))
            (hx6_sc.trans (by rw [hsSc0]; simpa using hx6_7))
            (hx19_sc.trans (by rw [hsSc0]; simpa using hx19_7))
            hx21_sc
            (hx23_sc.trans (by rw [hsSc0]; simpa using hx23_7))
            hcsSc0 hFinishPost

/-- Placed `__libc_realloc(p, newSize)` (`blk14`, `800` B stack) for the fine cost model. -/
theorem placed_libcRealloc_fine_ok {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro) :
    LibcReallocFineStmt ro := by
  intro _ γ tp brkStart p newSize oldBlk bgt ivs0
  have hfn : ∀ c, (blkPC_b14.rebase c (fun _ => none)).fnAddr "__libc_realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b14.fnOff "__libc_realloc") = c
    rw [blkPC_b14_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b14 (hfn (mbase 14)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk⌝ ∗
      (stackFrame s0 800 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [libcReallocFineSpec, withCL]
    generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  cases oldBlk with
  | none =>
    rw [OptOwn_interp_none] at hpre'
    have hpre'' : s0.mem ⊨ ⌜p = 0#64⌝ ∗
        (stackFrame s0 800 ∗
         MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0) ∗ R :=
      Satisfies.mono (Entails.of_eq (by
        generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0) = PEnv
        ac_rfl)) hpre'
    rw [satisfies_pure_sepConj] at hpre''; obtain ⟨hp0, hpre''⟩ := hpre''; subst hp0
    have hBgtNull :
        (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then
          mallocngFineCostModel.step (.alloc newSize.toNat) bgt else bgt) =
        (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then
          fineStepAlloc newSize.toNat bgt else bgt) := by
      cases decide (newSize.toNat ≤ MallocngMaxAllocSize) <;> rfl
    have hStepNull :
        (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then
          mallocngFineCostModel.stepReserve (.realloc 16 0 newSize.toNat) bgt
        else mallocngFineCostModel.stepReserve (.alloc 0) bgt) =
        FineStepBound (fineMaxMetaAreas bgt)
          (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then newSize.toNat else 0) := by
      rw [fine_stepB_ite, fine_evReqBytes_realloc16_eq]
    refine ⟨stackFrame s0 800 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0,
      hpre'', ?_⟩
    have hOomNull :
        (libcReallocFineSpec γ tp brkStart 0#64 newSize none bgt ivs0 ro).onOom () s0 =
        (fun sf => ⌜MallocngStepOomCond msvc
          (FineStepBound (fineMaxMetaAreas bgt)
            (if decide (newSize.toNat ≤ MallocngMaxAllocSize) then newSize.toNat else 0)) s0 sf⌝) := by
      funext sf
      dsimp only [libcReallocFineSpec, withCL]
      rw [hStepNull]
    rw [hOomNull]
    refine SepWP.mono
      (fine_realloc_null_path_ok hImpl hb γ tp brkStart newSize bgt ivs0 s0 R hpc hrun hsp hx0 hx1 hcl0)
      fun sf Pf _ _ ⟨hq, hspF, hcsF⟩ => ⟨fun hm => Satisfies.mono ?_ (hq hm), hspF, hcsF⟩
    dsimp only [libcReallocFineSpec, withCL, Option.map, Option.getD]
    simp only [List.take_nil, hBgtNull, hStepNull]
    refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))))
    split
    · exact Entails.refl _
    · refine sepConj_mono_right ?_
      rw [OptOwn_interp_none, ← sepConj_emp ⌜(0#64 : BitVec 64) = 0#64⌝]
      exact Entails.pure_right rfl (Entails.refl emp)
  | some blk =>
    rcases blk with ⟨oldSz, inAlign, origBs⟩
    exact ⟨stackFrame s0 800 ∗
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
      (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp p (oldSz, inAlign, origBs), hpre',
      fine_realloc_nonnull_path_ok hImpl hFree hb γ tp brkStart p newSize inAlign oldSz origBs
        bgt ivs0 s0 R hpWf.2 hpc hrun hsp hx0 hx1 hcl0⟩

private theorem call_placed_libcRealloc_fine {ro : Bool} (h : LibcReallocFineStmt ro) [MallocngMultiPlacement]
    {P : Program} (γ : GhostName) (tp brkStart p newSize : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (bgt : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 14) (libcReallocFineSpec γ tp brkStart p newSize oldBlk bgt ivs0 ro) :=
  subroutine_ok_block_to_block (j := 14) (by decide)
    (h γ tp brkStart p newSize oldBlk bgt ivs0) hext hsvc

private theorem fine_realloc_entry_post [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart p newSize sp : BitVec 64)
    (oldBlk : Option (Nat × Nat × List (BitVec 8)))
    (outAlign : Nat) (keptBs : List (BitVec 8))
    (bgt bgtStep : mallocngFineCostModel.σ) (resStep resZero : Nat)
    (ivs0 : List (BitVec 64 × Nat))
    (s0 s1 sf : State) (R : SepProp)
    (hSf1 : stackFrame s0 800 = stackFrame s1 800)
    (hSf1024 : stackFrameAt sp 1024 = (stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224))
    (hAccCongr : ∀ k m, MallocngCallAccounting k m s1 sf → MallocngCallAccounting k m s0 sf)
    (hpWf : (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk)
    (hm :
      let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
      let bgt' := if ok then bgtStep else bgt
      let stepB := if ok then resStep else resZero
      sf.mem ⊨
        (((⌜MallocngCallAccounting 16 stepB s1 sf⌝ ∗
           stackFrame s1 800 ∗
           MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf ∗
           if ok then
             ∃∗ q : BitVec 64,
               ⌜sf.readReg64 .x0 = q ∧
                (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q (newSize.toNat, outAlign, keptBs)⌝ ∗
               (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q (newSize.toNat, outAlign, keptBs)
           else
             ⌜sf.readReg64 .x0 = 0#64⌝ ∗
             (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) ∗
          ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝) ∗
         stackFrameAt (sp - 800#64) 224) ∗ R) :
    let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
    let bgt' := if ok then bgtStep else bgt
    let stepB := if ok then resStep else resZero
    sf.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
      ⌜(CType.CondOwn (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ))).pureWf p
         (if ok then none else some oldBlk) ∧
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf (sf.readReg64 .x0)
         (if ok then some (newSize.toNat, outAlign, keptBs) else none) ∧
       MallocngCallAccounting 16 stepB s0 sf⌝ ∗
      (CType.CondOwn (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ))).interp p
        (if ok then none else some oldBlk) ∗
      (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp (sf.readReg64 .x0)
        (if ok then some (newSize.toNat, outAlign, keptBs) else none) ∗
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf ∗
      stackFrameAt sp 1024 ∗ R := by
  dsimp only at hm ⊢
  have hSfCombine : stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224 = stackFrameAt sp 1024 := by
    rw [← hSf1, ← hSf1024]
  by_cases hLe : newSize.toNat ≤ MallocngMaxAllocSize
  · simp only [decide_eq_true hLe, ↓reduceIte] at hm ⊢
    dsimp only [CType.CondOwn]
    have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
        ⌜MallocngCallAccounting 16 resStep s1 sf⌝ ∗
        (∃∗ q : BitVec 64, ⌜sf.readReg64 .x0 = q ∧
           (MallocngModelInitBlock (mallocngFineModeIface ro) γ).pureWf q
             (newSize.toNat, outAlign, keptBs)⌝ ∗
          (MallocngModelInitBlock (mallocngFineModeIface ro) γ).interp q
            (newSize.toNat, outAlign, keptBs)) ∗
        (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart
          bgtStep ivs0 s0 sf ∗ R := by
      refine Satisfies.mono (Entails.of_eq ?_) hm
      dsimp only [MallocngModelInitBlock]
      generalize (∃∗ q : BitVec 64, _) = PRet
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgtStep ivs0 s0 sf) = PPost
      ac_rfl
    rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
    rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm'; obtain ⟨q, hm'⟩ := hm'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm'; obtain ⟨⟨hx0Q, hWfQ⟩, hm'⟩ := hm'
    have hAcc0 := hAccCongr _ _ hAcc1; rw [← hx0Q] at hWfQ hm'
    have hPurePost : (True : Prop) ∧
        (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf (sf.readReg64 .x0)
          (some (newSize.toNat, outAlign, keptBs)) ∧
        MallocngCallAccounting 16 resStep s0 sf :=
      ⟨trivial, ⟨hWfQ.1, hWfQ⟩, hAcc0⟩
    refine Satisfies.mono (Entails.trans
      (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
    exact Entails.of_eq (by
      dsimp only [OptOwn, MallocngModelInitBlock]
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgtStep ivs0 s0 sf) = PPost
      simp only [emp_sepConj]; ac_rfl)
  · simp only [decide_eq_false hLe, Bool.false_eq_true, ↓reduceIte] at hm ⊢
    dsimp only [CType.CondOwn]
    have hm' : sf.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sf.mem⌝ ∗
        ⌜MallocngCallAccounting 16 resZero s1 sf⌝ ∗
        ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk ∗
        (stackFrame s1 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart
          bgt ivs0 s0 sf ∗ R := by
      refine Satisfies.mono (Entails.of_eq ?_) hm
      generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) = POld
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 sf) = PPost
      ac_rfl
    rw [hSfCombine, satisfies_pure_sepConj] at hm'; obtain ⟨hclSf, hm'⟩ := hm'
    rw [satisfies_pure_sepConj] at hm'; obtain ⟨hAcc1, hm'⟩ := hm'
    have hPurePost :
        (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk ∧
        (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf (sf.readReg64 .x0) none ∧
        MallocngCallAccounting 16 resZero s0 sf :=
      ⟨hpWf, trivial, hAccCongr _ _ hAcc1⟩
    refine Satisfies.mono (Entails.trans
      (Entails.pure_right hclSf (Entails.pure_right hPurePost (Entails.refl _))) ?_) hm'
    exact Entails.of_eq (by
      dsimp only [OptOwn]
      generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) = POld
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 sf) = PPost
      ac_rfl)

set_option maxHeartbeats 400000 in
/-- Exported `"realloc"` (`blk13`, 1-instruction `b __libc_realloc` tail-call, `1024` B stack)
    verified against `mallocngModelReallocSpec mallocngFineCostModel mallocngFineIface`. -/
theorem fine_realloc_entry_ok {ro : Bool}
    (hImpl : LibcMallocImplFineStmt ro) (hFree : LibcFreeFineStmt ro)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngModelReallocSpec mallocngFineCostModel (mallocngFineModeIface ro) svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  refine ⟨by decide, 13, 0, by decide +kernel, ?_⟩
  rw [fnAddr_realloc mpl]
  apply withCL_to_withCodeLoaded
  have hfn : ∀ c, (blkPC_b13.rebase c (fun _ => none)).fnAddr "realloc" = c := fun c => by
    dsimp only [Program.fnAddr, Program.rebase]
    change c + BitVec.ofNat 64 (blkPC_b13.fnOff "realloc") = c
    rw [blkPC_b13_fnOff_0x0]
    exact BitVec.add_zero c
  refine mallocngBlock_subOk mallocngBlockProg_eq_b13 (hfn (mbase 13)) fun b hb => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨p, newSize, sp, oldBlk, tp, brkStart, bgt, ivs0⟩ R s0 hpc hrun hpre hsp
  rw [hfn b] at hpc
  have _ := hb
  have hpre' : s0.mem ⊨
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗
      ⌜s0.sp = sp ∧ s0.readReg64 .x0 = p ∧ s0.readReg64 .x1 = newSize ∧
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk⌝ ∗
      (stackFrameAt sp 1024 ∗
       MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
       (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) ∗ R := by
    refine Satisfies.mono (Entails.of_eq ?_) hpre
    dsimp only [withCL, mallocngModelReallocSpec, ToBaseSpec.toSpec, CType.CondOwn, mallocngStackBytes]
    generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0) = PEnv
    generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) = POld
    ac_rfl
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨hcl0, hpre'⟩ := hpre'
  rw [satisfies_pure_sepConj] at hpre'; obtain ⟨⟨hspEq, hx0, hx1, hpWf⟩, hpre'⟩ := hpre'
  have hSf1024 : stackFrameAt sp 1024 = (stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) := by
    rw [show (1024 : Nat) = 800 + 224 from rfl, stackFrameAt_split sp 800 224]
    congr 1; unfold stackFrame; rw [hspEq, stackFrameAt_eq_memRegion sp 800]
  rw [hSf1024] at hpre'
  have hpWfA := hpWf
  have hpreA := hpre'
  refine ⟨(stackFrame s0 800 ∗ stackFrameAt (sp - 800#64) 224) ∗
    MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 ∗
    (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk, hpreA, ?_⟩
  wp_step
  apply sepWP_bind_state; intro s1 hs1
  have hRealloc := call_placed_libcRealloc_fine (placed_libcRealloc_fine_ok hImpl hFree)
    (P := blkPC_b13.rebase b (fun _ => none))
    γ tp brkStart p newSize oldBlk bgt ivs0 (by intro pc; simp) rfl
  have hEnv1 :
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 =
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s1 := by
    unfold MallocngModelEnv; rw [hs1]; rfl
  have hSf1 : stackFrame s0 800 = stackFrame s1 800 := by unfold stackFrame; rw [hs1]; simp
  rw [hEnv1, hSf1]
  refine SepWP.call_subroutine_frame hRealloc (x := ()) (F := stackFrameAt (sp - 800#64) 224)
    (ret_pc := s0.readReg64 Reg.lr)
    (by rw [hs1]; simp only [wp_norm, arm64_norm, hb]; bv_lin)
    (by rw [hs1]; simp [hrun])
    (by unfold State.spAligned at hsp ⊢; rw [hs1]; simpa using hsp)
    (by rw [hs1]; simp)
    (fun R' hm => by
      have hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem := by rw [hs1]; exact hcl0
      have hPure1 : s1.readReg64 .x0 = p ∧ s1.readReg64 .x1 = newSize ∧
          (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).pureWf p oldBlk :=
        ⟨by rw [hs1]; simpa using hx0, by rw [hs1]; simpa using hx1, hpWfA⟩
      refine Satisfies.mono ?_ hm
      dsimp only [libcReallocFineSpec, withCL]
      refine Entails.trans (Entails.pure_right hcl1 (Entails.pure_right hPure1 (Entails.refl _))) ?_
      exact Entails.of_eq (by
        generalize (MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s1) = PEnv
        generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp p oldBlk) = POld
        ac_rfl))
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcSf hrunSf hspSf hcsSf => ?_)
    (fun R' sf _ hOom => ?_)
  · have hspSf0 : sf.sp = s0.sp := hspSf.trans (by rw [hs1]; simp)
    have hcsSf0 : CalleeSavedPreserved s0 sf := CalleeSavedPreserved.trans (by
      rw [hs1]; exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp [calleeSavedVRegs]⟩) hcsSf
    refine SepWP.done hpcSf hrunSf ⟨fun hm => ?_, hspSf0, hcsSf0⟩
    have hs1Mem : s1.mem = s0.mem := by rw [hs1]; rfl
    have hAccCongr : ∀ k m, MallocngCallAccounting k m s1 sf → MallocngCallAccounting k m s0 sf := by
      intro k m ⟨hPr, hDl⟩
      exact ⟨mallocngProcPreserved_trans (by rw [hs1]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hPr,
        by rwa [hs1Mem] at hDl⟩
    have hPostCongr : ∀ bf',
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf' ivs0 s1 sf =
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bf' ivs0 s0 sf :=
      fun bf' => by unfold MallocngModelPostEnv MallocngNoOrphanMappings; rw [hs1Mem]
    rcases oldBlk with _ | ⟨oldSize, align, bs⟩
    · dsimp only [libcReallocFineSpec, withCL, mallocngModelReallocSpec, ToBaseSpec.toSpec,
        mallocngStackBytes, Option.map, Option.getD] at hm ⊢
      rw [hPostCongr] at hm
      have hRes := fine_realloc_entry_post γ tp brkStart p newSize sp none 16
        (([] : List (BitVec 8)).take newSize.toNat)
        bgt (mallocngFineCostModel.step (.alloc newSize.toNat) bgt)
        (mallocngFineCostModel.stepReserve (.realloc 16 0 newSize.toNat) bgt)
        (mallocngFineCostModel.stepReserve (.alloc 0) bgt)
        ivs0 s0 s1 sf R hSf1 hSf1024 hAccCongr hpWf hm
      dsimp only at hRes
      refine Satisfies.mono (Entails.of_eq ?_) hRes
      generalize ((CType.CondOwn (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ))).interp p _) = PCond
      generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp (sf.readReg64 .x0) _) = PRet
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart _ ivs0 s0 sf) = PPost
      ac_rfl
    · dsimp only [libcReallocFineSpec, withCL, mallocngModelReallocSpec, ToBaseSpec.toSpec,
        mallocngStackBytes, Option.map, Option.getD] at hm ⊢
      rw [hPostCongr] at hm
      have hRes := fine_realloc_entry_post γ tp brkStart p newSize sp (some (oldSize, align, bs))
        (max align 16) (bs.take newSize.toNat)
        bgt (mallocngFineCostModel.step (.realloc align oldSize newSize.toNat) bgt)
        (mallocngFineCostModel.stepReserve (.realloc align oldSize newSize.toNat) bgt)
        (mallocngFineCostModel.stepReserve (.alloc 0) bgt)
        ivs0 s0 s1 sf R hSf1 hSf1024 hAccCongr hpWf hm
      dsimp only at hRes
      refine Satisfies.mono (Entails.of_eq ?_) hRes
      generalize ((CType.CondOwn (OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ))).interp p _) = PCond
      generalize ((OptOwn (MallocngModelInitBlock (mallocngFineModeIface ro) γ)).interp (sf.readReg64 .x0) _) = PRet
      generalize (MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart _ ivs0 s0 sf) = PPost
      ac_rfl
  · have hOom' := Satisfies.drop_mid hOom
    rcases oldBlk with _ | ⟨oldSize, align, bs⟩
    · dsimp only [libcReallocFineSpec, withCL, mallocngModelReallocSpec, ToBaseSpec.toSpec] at hOom' ⊢
      rw [satisfies_pure_sepConj] at hOom' ⊢; obtain ⟨hOom1, hR'⟩ := hOom'
      exact ⟨fine_stepOom_congr (Nat.le_refl _)
        (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) hOom1, hR'⟩
    · dsimp only [libcReallocFineSpec, withCL, mallocngModelReallocSpec, ToBaseSpec.toSpec] at hOom' ⊢
      rw [satisfies_pure_sepConj] at hOom' ⊢; obtain ⟨hOom1, hR'⟩ := hOom'
      exact ⟨fine_stepOom_congr (Nat.le_refl _)
        (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) (by rw [hs1]; rfl) hOom1, hR'⟩

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
