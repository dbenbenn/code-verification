/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Specs

/-!
# Fine Verification of Placed `alloc_group` (`blk08`, `+0x280`)

- **Role**: `Role::Proof` (untrusted).
- **Purpose**: Proves `wp_placed_allocGroup_fine : AllocMetaFineStmt → AllocGroupFineAtOffStmt`,
  threading `FineSplitInv bL bP`, `AllocSlotOccRoom bP`, non-increasing `stClassBound` on strictly
  smaller classes `k < sc`, and the fine mapped-memory bound
  `(allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng
  VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost

arm64_proof_prelude

/-! ## 1. Fine OOM & `MallocngMappedDelta` Composition Helpers -/

private theorem fineMetaStep_le_allocSlot (sc maxMeta : Nat) :
    FineMetaStep maxMeta ≤ (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576 := by
  have h1 : 1 * FineMetaStep maxMeta ≤ (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta := Nat.mul_le_mul_right _ (by omega)
  omega

private theorem fineRecStep_le_allocSlot {sc pSc : Nat} (maxMeta : Nat)
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc) :
    FineMetaStep maxMeta + ((allocSlotDepthBound pSc + 1) * FineMetaStep maxMeta + 1048576) ≤
      (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576 := by
  have h1 : (1 + (allocSlotDepthBound pSc + 1)) * FineMetaStep maxMeta ≤
      (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h1; omega

private theorem oom_from_allocMeta_fine {svc : State → State} {sc maxMeta : Nat} {s0 s_call sf : State}
    (hProc : MallocngProcPreserved s0 s_call) (hperm : s_call.mem.perm = s0.mem.perm)
    (hoom : MallocngPlacedOomCond svc 1 (FineMetaStep maxMeta) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf := by
  obtain ⟨hfs, htr, hsig, ivs, hivsK, hivsB, hmap, hgap⟩ := hoom
  exact MallocngPlacedOomCond.mono (by omega) (fineMetaStep_le_allocSlot sc maxMeta)
    ⟨hfs.trans hProc.1, htr.trans hProc.2.1, hsig.trans hProc.2.2.2.2.2.2, ivs, hivsK, hivsB,
     fun a ha => by rw [← hperm]; exact hmap a ha, hgap⟩

private theorem oom_from_recAllocSlot_fine {svc : State → State} {sc pSc maxMeta : Nat} {s0 s_call sf : State}
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc) (hProc : MallocngProcPreserved s0 s_call)
    (hd0 : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem s_call.mem)
    (hoom : MallocngPlacedOomCond svc (2 * (allocSlotDepthBound pSc + 1)) ((allocSlotDepthBound pSc + 1) * FineMetaStep maxMeta + 1048576) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf :=
  (MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hd0 hoom).mono (by omega) (fineRecStep_le_allocSlot maxMeta hdepth)

private theorem root_mappedDelta_combine_fine {sc maxMeta len : Nat} {m0 m1 m2 m3 mf : Memory}
    (hd1 : MallocngMappedDelta 1 (FineMetaStep maxMeta) m0 m1) (hp12 : m2.perm = m1.perm)
    (hdMmap : MallocngMappedDelta 1 len m2 m3) (hp3f : mf.perm = m3.perm) (hlenHi : len ≤ 1048576) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) m0 mf := by
  have h1 : 1 * FineMetaStep maxMeta ≤ (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta := Nat.mul_le_mul_right _ (by omega)
  exact MallocngMappedDelta.mono (by omega) (by omega) (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hdMmap hp3f))

private theorem nested_mappedDelta_combine_fine {sc pSc maxMeta : Nat} {m0 m1 m2 m3 mf : Memory}
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc) (hd1 : MallocngMappedDelta 1 (FineMetaStep maxMeta) m0 m1) (hp12 : m2.perm = m1.perm)
    (hd2 : MallocngMappedDelta (2 * (allocSlotDepthBound pSc + 1)) ((allocSlotDepthBound pSc + 1) * FineMetaStep maxMeta + 1048576) m2 m3) (hp3f : mf.perm = m3.perm) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) m0 mf :=
  MallocngMappedDelta.mono (by omega) (fineRecStep_le_allocSlot maxMeta hdepth)
    (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hd2 hp3f))

/-! ## 2. Count Dispatch & Root Size Selection with `RootPairSel` -/

private def RootPairSel (sc c cnt_f req len : Nat) : Prop :=
  (cnt_f = c ∧ len = pageAlignUp (c * slotStride sc + 16)) ∨
  (cnt_f = 1 ∧ c ≤ 7 ∧ len = pageAlignUp (req + 20) ∧ (len < slotStride sc + 16 ∨ 16384 ≤ len))

private theorem slotStride_le_3000_of_le_25 {sc : Nat} (hsc : sc ≤ 25) : slotStride sc ≤ 3000 := by
  have hchk : ((List.range 26).all fun s => decide (slotStride s ≤ 3000)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hchk sc (List.mem_range.mpr (by omega)))

private theorem cnt_le_7_of_not_skip {cnt : Nat} (hhi : cnt ≤ 32) {w : BitVec 64}
    (hne : ¬ BitVec.setWidth 32 ((if (7#32).slt (BitVec.setWidth 32 (BitVec.ofNat 64 cnt)) = true then 0#64 else 1#64) &&& w) = 0#32) : cnt ≤ 7 :=
  Classical.byContradiction fun hgt => by
    have hw : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
    have hslt : (7#32).slt (BitVec.ofNat 32 cnt) = true := by
      have hlo8 : (7#64).ult (BitVec.ofNat 64 cnt) = true := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change 7 < cnt % (2 ^ 64); rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hhi32 : (BitVec.ofNat 64 cnt).ule 32#64 = true := by
        rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_ofNat]; change cnt % (2 ^ 64) ≤ 32; rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [← hw]; revert hlo8 hhi32; bv_robdd
    rw [hw, hslt] at hne; simp at hne

private theorem lsl1_32_eq_fine {cnt : Nat} (hhi : cnt ≤ 32) :
    (BitVec.ofNat 32 cnt)[30] = false ∧ BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) &&& 4294967295#64 = BitVec.ofNat 64 (2 * cnt) := by
  refine ⟨?_, ?_⟩
  · rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 32)) 30 = false
    rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
  · have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 1) = BitVec.ofNat 64 (2 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (2 * cnt)).ult 65#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change (2 * cnt) % (2 ^ 64) < 65; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

private theorem wp_cnt_check_mem_fine [MallocngMultiPlacement] (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (_hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 2 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_check) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt) (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx1 : s.readReg64 .x1 = 2048#64)
    (hNested : ∀ sn : State, sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem → sn.sp = s.sp → sn.spAligned = s.spAligned →
      PureStatePres s sn → ValidNestedCnt sc cnt → sn.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt → (∀ r, r ≠ .x0 → r ≠ .x3 → sn.readReg64 r = s.readReg64 r) → SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ sr : State, sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem → sr.sp = s.sp → sr.spAligned = s.spAligned →
      PureStatePres s sr → 2048 < cnt * slotStride sc + 16 → cnt * slotStride sc ≤ 1048575 → (sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) → sr.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sr.readReg64 .x28 = BitVec.ofNat 64 cnt → (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) → SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_check] at hpc
  have ⟨_, hshi⟩ := slotStride_bounds_48 hsc; have hbd : cnt * slotStride sc ≤ 32 * 131056 := Nat.mul_le_mul hhi hshi
  have hmul_eq : BitVec.ofNat 64 (slotStride sc) * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * slotStride sc) := by rw [← BitVec.ofNat_mul, Nat.mul_comm]
  wp_sym_steps; wp_if hls
  · have hle2048 : cnt * slotStride sc + 16 ≤ 2048 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048 at hls; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; exact hls
    have hvnc : ValidNestedCnt sc cnt := ⟨hlo, hhi, hle2048, fun h8 => by obtain ⟨j, hj, rfl⟩ := hsm h8; rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp⟩
    exact hNested _ rfl (by simp [hrun]) rfl (by simp) (by simp [State.spAligned]) psp_rfl hvnc (by simp) (by simpa using hx20) (by simpa using hx28) fun r h0 h3 => by
      simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]
  · have hgt2048 : 2048 < cnt * slotStride sc + 16 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ¬ (((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048) at hls; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; omega
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
      (fun sr => sr.mem = s.mem ∧ sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧ sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) ∧
        sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) ∧ sr.readReg64 .x20 = BitVec.ofNat 64 cnt ∧ sr.readReg64 .x28 = BitVec.ofNat 64 cnt ∧
        ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) ?_
      (fun sr hpcr hrunr ⟨hm, hs, ha, hp, h0, h6, h20, h28, hr⟩ => hRoot sr hpcr hrunr hm hs ha hp hgt2048 hprod h25 h0 h6 h20 h28 hr)
    dsimp only [allocSlotOff_root]; wp_sym_steps
    have hb29 : (BitVec.ofNat 32 cnt)[29] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 32)) 29 = false
      rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl, by simp, ?_, by simpa using hx20, by simpa using hx28, fun r h0 h3 h6 => by
      simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h6,
        State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]⟩, by sep_entail⟩
    simp [hb29]; have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 2) = BitVec.ofNat 64 (4 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (4 * cnt)).ult 133#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change (4 * cnt) % (2 ^ 64) < 133; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

private theorem wp_cnt_dispatch_mem_fine [MallocngMultiPlacement] (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hc1 : cnt = 1 → 9 ≤ sc) (hpc : s.pc = mbase 8 + allocSlotOff_cnt_join) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (_hx4 : s.readReg64 .x4 = 4096#64)
    (hNested : ∀ (cnt' : Nat) (sn : State), sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem → sn.sp = s.sp →
      sn.spAligned = s.spAligned → PureStatePres s sn → cnt' = Cost.cntBump sc cnt → ValidNestedCnt sc cnt' →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt' → sn.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x28 → sn.readReg64 r = s.readReg64 r) → SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ (cnt' : Nat) (sr : State), sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem → sr.sp = s.sp →
      sr.spAligned = s.spAligned → PureStatePres s sr → cnt' = Cost.cntBump sc cnt → 1 ≤ cnt' → cnt' ≤ 32 →
      2048 < cnt' * slotStride sc + 16 → cnt' * slotStride sc ≤ 1048575 → (sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt') →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt' → sr.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 → sr.readReg64 r = s.readReg64 r) → SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_join] at hpc; have ⟨_, hshi⟩ := slotStride_bounds_48 hsc; wp_sym_steps; wp_if heq1
  · have hcnt1 : cnt = 1 := by
      have hw : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
      have ht := congrArg BitVec.toNat (hw ▸ heq1); simp only [BitVec.toNat_ofNat] at ht
      change cnt % (2 ^ 32) = 1 at ht; rw [Nat.mod_eq_of_lt (by omega)] at ht; exact ht
    subst hcnt1; have hsc9 : 9 ≤ sc := hc1 rfl; wp_sym_steps; wp_if hhi1
    · have hgt2048 : 2048 < 1 * slotStride sc + 16 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change 2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64) at hhi1; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
        (fun sr => sr.mem = s.mem ∧ sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
          sr.readReg64 .x0 = BitVec.ofNat 64 (1 * slotStride sc) ∧ sr.readReg64 .x6 = BitVec.ofNat 64 (4 * 1) ∧
          sr.readReg64 .x20 = BitVec.ofNat 64 1 ∧ sr.readReg64 .x28 = BitVec.ofNat 64 1 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 → sr.readReg64 r = s.readReg64 r) ?_
        (fun sr hpcr hrunr ⟨hm, hs, ha, hp, h0, h6, h20, h28, hr⟩ =>
          hRoot 1 sr hpcr hrunr hm hs ha hp (by simp only [Cost.cntBump]; split <;> omega) (by omega) (by omega) hgt2048 hprod h25 h0 h6 h20 h28 hr)
      dsimp only [allocSlotOff_root]; wp_sym_steps
      refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl, by simp, by simp, by simpa using hx20, by simp,
        fun r h0 h1 _ h6 _ h28 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h6,
          State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h1, State.readReg64_writeReg64_ne _ _ _ _ h28]⟩, by sep_entail⟩
    · have hle2048 : slotStride sc + 16 ≤ 2048 := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hhi1
        change ¬ (2048 < (slotStride sc % (2 ^ 64) + 16) % (2 ^ 64)) at hhi1; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hhi1; omega
      refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_cnt_check)
        (fun sj => sj.mem = s.mem ∧ sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.readReg64 .x20 = BitVec.ofNat 64 2 ∧
          sj.readReg64 .x28 = BitVec.ofNat 64 2 ∧ sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sj.readReg64 .x1 = 2048#64 ∧
          ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x20 → r ≠ .x28 → sj.readReg64 r = s.readReg64 r) ?_ ?_
      · dsimp only [allocSlotOff_cnt_check]; wp_sym_steps
        refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl, by simp, by simp, by simpa using hx24, by simp,
          fun r h0 h1 h20 h28 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
            State.readReg64_writeReg64_ne _ _ _ _ h28, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h1]⟩, by sep_entail⟩
      · intro sj hjpc hjrun ⟨hmj, hspj, halj, hpspj, hj20, hj28, hj24, hj1, hjr⟩
        exact wp_cnt_check_mem_fine target_pc sj sc 2 P hw768 hsc (by omega) (by omega) (by omega) (fun _ => by omega) (fun _ => by omega) hjpc hjrun hj20 hj28 hj24 hj1
          (fun sn hp hr hm hs ha hp2 hv h0 h20 h28 hrg => hNested 2 sn hp hr (hm.trans hmj) (hs.trans hspj) (ha.trans halj) (hpspj.trans hp2)
            (by simp only [Cost.cntBump, true_and, hle2048, ↓reduceIte]) hv h0 h20 h28 fun r r0 r1 r3 r20 r28 => (hrg r r0 r3).trans (hjr r r0 r1 r20 r28))
          (fun sr hp hr hm hs ha hp2 hgt hpr h25' h0 h6 h20 h28 hrg => hRoot 2 sr hp hr (hm.trans hmj) (hs.trans hspj) (ha.trans halj) (hpspj.trans hp2)
            (by simp only [Cost.cntBump, true_and, hle2048, ↓reduceIte]) (by omega) (by omega) hgt hpr h25' h0 h6 h20 h28
            fun r r0 r1 r3 r6 r20 r28 => (hrg r r0 r3 r6).trans (hjr r r0 r1 r20 r28))
  · have hge2 : 2 ≤ cnt := Classical.byContradiction fun hlt => heq1 (by obtain rfl : cnt = 1 := (by omega); rfl)
    have hb31 : (BitVec.ofNat 64 cnt)[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat]; change Nat.testBit (cnt % (2 ^ 64)) 31 = false
      rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.testBit_lt_two_pow (by omega)
    have hand32 : BitVec.ofNat 64 cnt &&& 4294967295#64 = BitVec.ofNat 64 cnt := by
      have hlt : (BitVec.ofNat 64 cnt).ult 33#64 = true := by
        rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]; change cnt % (2 ^ 64) < 33; rw [Nat.mod_eq_of_lt (by omega)]; omega
      revert hlt; bv_robdd
    exact wp_cnt_check_mem_fine target_pc _ sc cnt P hw768 hsc hge2 hhi hprod h25 hsm rfl (by simp [hrun])
      (by simpa using hx20) (by simp [hb31]; exact hand32) (by simpa using hx24) (by simp)
      (fun sn hp hr hm hs ha hp2 hv h0 h20 h28 hrg => hNested cnt sn hp hr hm (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
        (by simp only [Cost.cntBump]; split <;> omega) hv h0 h20 h28 fun r r0 r1 r3 _ r28 => (hrg r r0 r3).trans
        (by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))
      (fun sr hp hr hm hs ha hp2 hgt hpr h25' h0 h6 h20 h28 hrg => hRoot cnt sr hp hr hm (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
        (by simp only [Cost.cntBump]; split <;> omega) (by omega) hhi hgt hpr h25' h0 h6 h20 h28 fun r r0 r1 r3 r6 _ r28 => (hrg r r0 r3 r6).trans
        (by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))

private theorem wp_root_req_round_fine [MallocngMultiPlacement]
    (s : State) (sc req cnt_cur len_cur : Nat) (Frame : SepProp) (_hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hc7 : cnt_cur ≤ 7) (hCur : RootMmapParamsOk sc cnt_cur len_cur)
    (hCurReq : cnt_cur = 1 → req + 20 ≤ len_cur) (hCurLen : len_cur = pageAlignUp (cnt_cur * slotStride sc + 16))
    (hpc : s.pc = mbase 8 + allocSlotOff_req_round) (hrun : s.status = .Running) (hx3 : s.readReg64 .x3 = 4095#64) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt_cur) (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc))
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 len_cur) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧ RootPairSel sc cnt_cur cnt_f req len ∧
        (∀ x5, Cost.RootLenOk sc cnt_cur len (s.readReg64 .x2) x5) ∧ sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧ sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame) (fun _ => ⌜False⌝) := by
  dsimp only [allocSlotOff_req_round, allocSlotOff_mmap_go] at hpc ⊢; have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc
  have hreq_hi : req + 20 ≤ slotStride sc + 16 := by unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
  obtain ⟨hbv_req, h4096_req, hdvd_req, hle1M_req, hle64_req⟩ := align4096_bv_eq (m := req + 20) (by omega) (by omega)
  have hge_req := pageAlignUp_le (req + 20); have hlt_req := pageAlignUp_lt (req + 20); have h4_req : 0 < pageAlignUp (req + 20) / 4096 := Nat.div_pos h4096_req (by omega)
  have hcap_req : 12 + 1 * (if (1 : Nat) - 1 == 0 && 0 < pageAlignUp (req + 20) / 4096 then pageAlignUp (req + 20) - 16 else slotStride sc) < pageAlignUp (req + 20) := by
    simp only [Nat.sub_self, beq_self_eq_true, Bool.true_and, decide_eq_true h4_req, ↓reduceIte]; omega
  have h25_req : sc ≤ 25 → pageAlignUp (req + 20) ≤ 65536 := fun hs => hle64_req (by have := slotStride_le_3000_of_le_25 hs; omega)
  have hr20 : BitVec.ofNat 64 req + 20#64 = BitVec.ofNat 64 (req + 20) := (BitVec.ofNat_add req 20).symm
  have hx25_eq : ∀ c_neg : BitVec 64, c_neg + 20#64 = 0#64 → ((c_neg - BitVec.ofNat 64 req) &&& 4095#64) + BitVec.ofNat 64 (req + 20) = BitVec.ofNat 64 (pageAlignUp (req + 20)) :=
    fun c_neg hc => by rw [neg_k_sub 20#64 _ _ hc, hr20, hbv_req]
  have hx0_nat : (BitVec.ofNat 64 (slotStride sc) + 16#64).toNat = slotStride sc + 16 := by rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  wp_sym_steps; wp_if hlo1
  · have hlt_str : pageAlignUp (req + 20) < slotStride sc + 16 := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1; exact hlo1
    have hOk1 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) := ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req, h25_req, fun _ => Or.inl (by omega), hcap_req⟩
    have hLen1 : ∀ x5, Cost.RootLenOk sc cnt_cur (pageAlignUp (req + 20)) (s.readReg64 .x2) x5 := fun _ => Or.inl (by have := pageAlignUp_le (slotStride sc + 16); omega)
    wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk1, fun _ => hge_req, Or.inr ⟨rfl, hc7, rfl, Or.inl hlt_str⟩, hLen1,
      by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp, by simp; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req],
      fun r h0 h20 h25 h26 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
        State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
  · have hge_str : slotStride sc + 16 ≤ pageAlignUp (req + 20) := by
      rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, hx0_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo1; omega
    wp_sym_steps; wp_if hlo2
    · have hlt16k : pageAlignUp (req + 20) < 16384 := by
        rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo2
        change pageAlignUp (req + 20) < 16384 at hlo2; exact hlo2
      refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hCurReq, Or.inl ⟨rfl, hCurLen⟩, fun _ => Or.inr ⟨hCurLen, fun _ _ h => absurd h (by omega)⟩,
        by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20, by simpa using hx26,
        fun r h0 _ h25 _ => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
    · have hge16k : 16384 ≤ pageAlignUp (req + 20) := by
        rw [hx25_eq _ (by decide), BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pageAlignUp (req + 20) < 2 ^ 64)] at hlo2
        change ¬ pageAlignUp (req + 20) < 16384 at hlo2; omega
      have hAlignEq : pageAlignUp (req + 20) = pageAlignUp (slotStride sc + 16) := by
        obtain ⟨qr, hqr⟩ := hdvd_req; obtain ⟨qs, hqs⟩ := pageAlignUp_dvd (slotStride sc + 16)
        have := pageAlignUp_le (slotStride sc + 16); have := pageAlignUp_lt (slotStride sc + 16); omega
      have h24 : 24 ≤ sc := Classical.byContradiction fun hlt24 => by have := slotStride_le_2032_of_le_23 (by omega : sc ≤ 23); omega
      have hOk2 : RootMmapParamsOk sc 1 (pageAlignUp (req + 20)) := ⟨by omega, by omega, h4096_req, hdvd_req, hle1M_req, h25_req, fun _ => Or.inr ⟨h24, hAlignEq⟩, hcap_req⟩
      wp_sym_steps; have hhi_cur : cnt_cur ≤ 32 := hCur.2.1; have hw20 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt_cur) = BitVec.ofNat 64 cnt_cur := by bv_omega
      have ⟨hc30, hlsl1⟩ := lsl1_32_eq_fine hhi_cur
      by_cases hcond : (BitVec.ofNat 64 (2 * cnt_cur)).ule (s.readReg64 (Reg.gpr 2#5)) = true
      · refine SepWP.done rfl (by simp [hrun]) ⟨cnt_cur, len_cur, hCur, hCurReq, Or.inl ⟨rfl, hCurLen⟩, fun _ => Or.inr ⟨hCurLen, fun _ _ _ => hcond⟩,
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp [hc30, hlsl1, hcond, hw20], by simp [hc30, hlsl1, hcond, hCurLen],
          fun r h0 h20 h25 h26 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
            State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩
      · refine SepWP.done rfl (by simp [hrun]) ⟨1, pageAlignUp (req + 20), hOk2, fun _ => hge_req, Or.inr ⟨rfl, hc7, rfl, Or.inr hge16k⟩, fun _ => Or.inl (Nat.le_of_eq hAlignEq),
          by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simp [hc30, hlsl1, hcond],
          by simp [hc30, hlsl1, hcond]; rw [neg_k_sub 20#64 _ _ (by decide), hr20, hbv_req],
          fun r h0 h20 h25 h26 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h20,
            State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h25], rfl⟩

private theorem wp_root_mmap_prep_fine [MallocngMultiPlacement]
    (s : State) (sc req cnt' : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hgt2048 : 2048 < cnt' * slotStride sc + 16) (hprod : cnt' * slotStride sc ≤ 1048575) (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hpc : s.pc = mbase 8 + allocSlotOff_mmap_prep) (hrun : s.status = .Running) (hx4 : s.readReg64 .x4 = 4096#64) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧ RootPairSel sc cnt' cnt_f req len ∧
        Cost.RootLenOk sc cnt' len (s.readReg64 .x2) (s.readReg64 .x5) ∧ sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame) (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc; have h1M := stride_prod_plus16_le hsc hprod
  have hc_25 : sc ≤ 25 → cnt' * slotStride sc + 16 ≤ 65536 := fun hs => by have := h25 hs; omega
  have hc1_24 : cnt' = 1 → 24 ≤ sc := fun hc1 => by subst hc1; exact Classical.byContradiction fun hlt24 => by have := slotStride_le_2032_of_le_23 (by omega : sc ≤ 23); omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := cnt' * slotStride sc + 16) (by omega) h1M
  have hOk_c := rootMmapParams_of_cnt (by omega) hlo hhi h1M hc_25 hc1_24
  have hCurReq : cnt' = 1 → req + 20 ≤ pageAlignUp (cnt' * slotStride sc + 16) := fun hc1 => by
    subst hc1; have : req + 20 ≤ 1 * slotStride sc + 16 := by unfold nominalSlotCap at hReq; unfold slotStride at hslo ⊢; omega
    have := pageAlignUp_le (1 * slotStride sc + 16); omega
  have hadd16 : BitVec.ofNat 64 (cnt' * slotStride sc) + 16#64 = BitVec.ofNat 64 (cnt' * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  dsimp only [allocSlotOff_mmap_prep, allocSlotOff_mmap_go] at hpc ⊢; wp_sym_steps; wp_if hne
  · have hc7 : cnt' ≤ 7 := cnt_le_7_of_not_skip hhi hne
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
      (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
        sj.readReg64 .x20 = BitVec.ofNat 64 cnt' ∧ sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
        sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (cnt' * slotStride sc + 16)) ∧ ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x26 → r ≠ .x27 → sj.readReg64 r = s.readReg64 r) ?_ ?_
    · dsimp only [allocSlotOff_req_round]; refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl, by simp, by simpa using hx4,
        by simpa using hx20, by simpa using hx24, by simpa using hx25, by rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
        fun r r0 r1 r3 r26 r27 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r26,
          State.readReg64_writeReg64_ne _ _ _ _ r27, State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3]⟩, by sep_entail⟩
    · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
      have hr := wp_root_req_round_fine sj sc req cnt' (pageAlignUp (cnt' * slotStride sc + 16)) Frame hw768 hsc hReq hc7 hOk_c hCurReq rfl hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26
      dsimp only [allocSlotOff_mmap_go] at hr; refine SepWP.mono hr fun sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hSel, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩ =>
        ⟨cnt_f, len, hOk, hRq, hSel, (hjr .x2 (by decide) (by decide) (by decide) (by decide) (by decide)) ▸ hLen _, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
          fun r r0 r1 r3 r20 r25 r26 r27 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r1 r3 r26 r27), hPf⟩
  · refine SepWP.done rfl (by simp [hrun]) ⟨cnt', pageAlignUp (cnt' * slotStride sc + 16), hOk_c, hCurReq, Or.inl ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, fun hc hx5 _ => (root_skip_x5_ne hc hx5 hne).elim⟩, by simp [hrun], by simp, by simp [State.spAligned], psp_rfl, by simpa using hx20,
      by rw [smull_stride_cnt' hhi hshi]; simp; rw [neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
      fun r r0 r1 r3 _ _ r26 r27 => by simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ r26,
        State.readReg64_writeReg64_ne _ _ _ _ r27, State.readReg64_writeReg64_ne _ _ _ _ r0, State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r3], rfl⟩

private theorem wp_root_cnt_mul_fine [MallocngMultiPlacement]
    (s : State) (sc req c : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hclo : 2 ≤ c) (hchi : c ≤ 5) (hpc : s.pc = mbase 8 + allocSlotOff_cnt_mul) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 c) (hx4 : s.readReg64 .x4 = 4096#64) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 c)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧ RootPairSel sc c cnt_f req len ∧
        (∀ x5, Cost.RootLenOk sc c len (s.readReg64 .x2) x5) ∧ sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame) (fun _ => ⌜False⌝) := by
  have ⟨hslo, hshi⟩ := slotStride_bounds_48 hsc; have h1M : c * slotStride sc + 16 ≤ 1048576 := by have := Nat.mul_le_mul hchi hshi; omega
  obtain ⟨hbv_c, _⟩ := align4096_bv_eq (m := c * slotStride sc + 16) (by omega) h1M
  have hc_25 : sc ≤ 25 → c * slotStride sc + 16 ≤ 65536 := fun hs => by have := slotStride_le_3000_of_le_25 hs; have := Nat.mul_le_mul hchi this; omega
  have hOk_c := rootMmapParams_of_cnt (by omega) (by omega) (by omega) h1M hc_25 (by omega)
  have hadd16 : BitVec.ofNat 64 (c * slotStride sc) + 16#64 = BitVec.ofNat 64 (c * slotStride sc + 16) := (BitVec.ofNat_add _ 16).symm
  have hmul_eq : BitVec.ofNat 64 (slotStride sc) * BitVec.ofNat 64 c = BitVec.ofNat 64 (c * slotStride sc) := by rw [← BitVec.ofNat_mul, Nat.mul_comm]
  refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_req_round)
    (fun sj => sj.sp = s.sp ∧ sj.spAligned = s.spAligned ∧ PureStatePres s sj ∧ sj.readReg64 .x3 = 4095#64 ∧ sj.readReg64 .x4 = 4096#64 ∧
      sj.readReg64 .x20 = BitVec.ofNat 64 c ∧ sj.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧ sj.readReg64 .x25 = BitVec.ofNat 64 req ∧
      sj.readReg64 .x26 = BitVec.ofNat 64 (pageAlignUp (c * slotStride sc + 16)) ∧ ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x26 → sj.readReg64 r = s.readReg64 r) ?_ ?_
  · dsimp only [allocSlotOff_cnt_mul, allocSlotOff_req_round] at hpc ⊢; wp_sym_steps
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨by simp, by simp [State.spAligned], psp_rfl, by simp, by simpa using hx4, by simpa using hx20, by simpa using hx24, by simpa using hx25,
      by simp; rw [hmul_eq, neg_k_sub 16#64 _ _ (by decide), hadd16, hbv_c],
      fun r h0 h3 h26 => by simp only [State.readReg64_setPC, State.readReg64_writeReg64_ne _ _ _ _ h26, State.readReg64_writeReg64_ne _ _ _ _ h0, State.readReg64_writeReg64_ne _ _ _ _ h3]⟩, by sep_entail⟩
  · intro sj hjpc hjrun ⟨hsp, hal, hpsp, hj3, hj4, hj20, hj24, hj25, hj26, hjr⟩
    refine SepWP.mono (wp_root_req_round_fine sj sc req c (pageAlignUp (c * slotStride sc + 16)) Frame hw768 hsc hReq (by omega) hOk_c (by omega) rfl hjpc hjrun hj3 hj4 hj20 hj24 hj25 hj26)
      fun sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hSel, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩ =>
        ⟨cnt_f, len, hOk, hRq, hSel, (hjr .x2 (by decide) (by decide) (by decide)) ▸ hLen, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
          fun r r0 r3 r20 r25 r26 => (hregs r r0 r20 r25 r26).trans (hjr r r0 r3 r26), hPf⟩

set_option maxHeartbeats 800000 in
private theorem wp_root_size_select_fine [MallocngMultiPlacement]
    (s : State) (sc req cnt' : Nat) (Frame : SepProp) (hw768 : Blk08HasWords768 mallocngFaultSvc)
    (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32)
    (hgt2048 : 2048 < cnt' * slotStride sc + 16) (hprod : cnt' * slotStride sc ≤ 1048575) (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (hpc : s.pc = mbase 8 + allocSlotOff_bounces_cap) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc)) (hx4 : s.readReg64 .x4 = 4096#64)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt')) (hx7 : 38 < sc → s.readReg64 .x7 = 1#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt') (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc)) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        (∃ c, Cost.RootCntRel sc cnt' c (s.readReg64 .x2) ∧ RootPairSel sc c cnt_f req len ∧ Cost.RootLenOk sc c len (s.readReg64 .x2) (s.readReg64 .x5)) ∧
        sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧
        sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame) (fun _ => ⌜False⌝) := by
  let Post : State → SepProp → Prop := fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
    (∃ c, Cost.RootCntRel sc cnt' c (s.readReg64 .x2) ∧ RootPairSel sc c cnt_f req len ∧ Cost.RootLenOk sc c len (s.readReg64 .x2) (s.readReg64 .x5)) ∧
    sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧ PureStatePres s sf ∧ sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧
    sf.readReg64 .x26 = BitVec.ofNat 64 len ∧ (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame
  refine wp_root_size_select_core s sc cnt' Frame Post hw768 hsc hhi hprod hpc hrun hx0 hx4 hx6 hx7 hx21 ?_ ?_
  · intro hrel sm hmp hmrun hsp hal hpsp hmr
    refine SepWP.mono (wp_root_mmap_prep_fine sm sc req cnt' Frame hw768 hsc hReq hlo hhi hgt2048 hprod h25 hmp hmrun
      (by rw [hmr .x4 (by decide), hx4]) (by rw [hmr .x20 (by decide), hx20]) (by rw [hmr .x24 (by decide), hx24]) (by rw [hmr .x25 (by decide), hx25]) (by rw [hmr .x27 (by decide), hx27])) ?_
    rintro sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hSel, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    refine ⟨cnt_f, len, hOk, hRq, ⟨cnt', hrel, hSel, ?_⟩, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
      fun r r0 r1 r3 r20 r25 r26 r27 => (hregs r r0 r1 r3 r20 r25 r26 r27).trans (hmr r r1), hPf⟩
    rw [← hmr .x2 (by decide), ← hmr .x5 (by decide)]; exact hLen
  · intro c sm hclo hchi hrel hmp hmrun hsp hal hpsp hm0 hm20 hmr
    refine SepWP.mono (wp_root_cnt_mul_fine sm sc req c Frame hw768 hsc hReq hclo hchi hmp hmrun hm0
      (by rw [hmr .x4 (by decide) (by decide) (by decide), hx4]) hm20 (by rw [hmr .x24 (by decide) (by decide) (by decide), hx24]) (by rw [hmr .x25 (by decide) (by decide) (by decide), hx25])) ?_
    rintro sf P_f _ _ ⟨cnt_f, len, hOk, hRq, hSel, hLen, h1, h2, h3, hpsp2, h6, h7, hregs, hPf⟩
    refine ⟨cnt_f, len, hOk, hRq, ⟨c, hrel, hSel, ?_⟩, h1, h2.trans hsp, h3.trans hal, hpsp.trans hpsp2, h6, h7,
      fun r r0 r1 r3 r20 r25 r26 _ => (hregs r r0 r3 r20 r25 r26).trans (hmr r r0 r1 r20), hPf⟩
    rw [← hmr .x2 (by decide) (by decide) (by decide)]; exact hLen _

/-! ## 3. `GroupsFreeMono` Entry Lift (Using `Nodup` on `st0`) & Root `mmap` Path -/

private theorem slotUserWeight_le_of_sub_ag {w : SlotState → Nat} (h0 : ∀ s, (∀ p req eff, s ≠ .liveUser p req eff) → w s = 0)
    {ss' ss : List SlotState} (hSub : SlotUserSub ss' ss) : (ss'.map w).sum ≤ (ss.map w).sum := by
  induction ss' generalizing ss with
  | nil => exact Nat.zero_le _
  | cons x tl' ih =>
    obtain ⟨hLen, hImp⟩ := hSub; cases ss with
    | nil => simp at hLen
    | cons y tl =>
      simp only [List.length_cons] at hLen
      have hSubTl : SlotUserSub tl' tl := ⟨by omega, fun i hi' hi p req eff hEq => hImp (i + 1) (Nat.succ_lt_succ hi') (Nat.succ_lt_succ hi) p req eff hEq⟩
      have hHead : w x ≤ w y := by
        cases hx : x with
        | liveUser p req eff =>
          have hy := hImp 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) p req eff (by simp [hx]); simp only [List.getElem_cons_zero] at hy; rw [hy]; exact Nat.le_refl _
        | _ => rw [h0 _ (by intro _ _ _ h; cases h)]; exact Nat.zero_le _
      have hRec := ih hSubTl; simp only [List.map_cons, List.sum_cons]; omega

private theorem nodup_mem_eq_of_metaPtr_ag {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g1 g2 : GroupDesc} (hg1 : g1 ∈ gs) (hg2 : g2 ∈ gs) (hEq : g1.metaPtr = g2.metaPtr) : g1 = g2 := by
  induction gs with
  | nil => cases hg1
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd
    rcases List.mem_cons.mp hg1 with rfl | hg1'
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · rfl
      · exact False.elim (hNd.1 (hEq ▸ List.mem_map_of_mem hg2'))
    · rcases List.mem_cons.mp hg2 with rfl | hg2'
      · exact False.elim (hNd.1 (hEq.symm ▸ List.mem_map_of_mem hg1'))
      · exact ih hNd.2 hg1' hg2'

private theorem sum_le_of_nodup_inj_ag {gs gs' : List GroupDesc} {w w' : GroupDesc → Nat}
    (hNd : (gs.map (·.metaPtr)).Nodup) (hNd' : (gs'.map (·.metaPtr)).Nodup)
    (hMap : ∀ g' ∈ gs', ∃ g ∈ gs, g'.metaPtr = g.metaPtr ∧ w' g' ≤ w g) : (gs'.map w').sum ≤ (gs.map w).sum := by
  induction gs' generalizing gs with
  | nil => exact Nat.zero_le _
  | cons g' tl' ih =>
    simp only [List.map_cons, List.nodup_cons] at hNd'; obtain ⟨g, hg, hMetaEq, hwLe⟩ := hMap g' List.mem_cons_self; obtain ⟨pre, suf, rfl⟩ := List.append_of_mem hg
    have hNdApp : ((pre ++ suf).map (·.metaPtr)).Nodup := by rw [List.map_append] at hNd ⊢; simp only [List.map_cons] at hNd; exact List.Nodup.sublist (by simp) hNd
    have hTlMap : ∀ h' ∈ tl', ∃ h ∈ pre ++ suf, h'.metaPtr = h.metaPtr ∧ w' h' ≤ w h := fun h' hh' => by
      obtain ⟨h, hh, hmEq, hwH⟩ := hMap h' (List.mem_cons_of_mem g' hh'); rw [List.mem_append, List.mem_cons] at hh
      rcases hh with hPre | rfl | hSuf
      · exact ⟨h, List.mem_append_left _ hPre, hmEq, hwH⟩
      · exact False.elim (hNd'.1 (hMetaEq ▸ hmEq.symm ▸ List.mem_map_of_mem hh'))
      · exact ⟨h, List.mem_append_right _ hSuf, hmEq, hwH⟩
    have hRec := ih hNdApp hNd'.2 hTlMap; simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append] at hRec ⊢; omega

private theorem filter_sum_le_of_groupsFreeMono_ag {gs gs' : List GroupDesc} (p : GroupDesc → Bool) (w : GroupDesc → Nat)
    (hpC : ∀ g' g : GroupDesc, g'.sc = g.sc → g'.cnt = g.cnt → g'.maplen = g.maplen → p g' = p g)
    (hwLe : ∀ g' g : GroupDesc, g'.sc = g.sc → g'.cnt = g.cnt → g'.maplen = g.maplen → SlotUserSub g'.slots g.slots → w g' ≤ w g)
    (hNd : (gs.map (·.metaPtr)).Nodup) (hNd' : (gs'.map (·.metaPtr)).Nodup) (hMono : GroupsFreeMono gs gs') :
    ((gs'.filter p).map w).sum ≤ ((gs.filter p).map w).sum := by
  have hSubNd : ∀ xs : List GroupDesc, (xs.map (·.metaPtr)).Nodup → ((xs.filter p).map (·.metaPtr)).Nodup := fun _ h => List.Nodup.sublist (List.filter_sublist.map _) h
  refine sum_le_of_nodup_inj_ag (hSubNd gs hNd) (hSubNd gs' hNd') fun g' hg' => ?_
  have ⟨hg'In, hp'⟩ := List.mem_filter.mp hg'; obtain ⟨g, hgIn, hM, hSc, hCnt, hMl, _, hSl⟩ := hMono g' hg'In
  exact ⟨g, List.mem_filter.mpr ⟨hgIn, (hpC g' g hSc hCnt hMl).symm.trans hp'⟩, hM, hwLe g' g hSc hCnt hMl hSl⟩

private theorem fineSplitInv_of_groupsFreeMono_nd {inflight' : Nat} {base brkStart brk' : BitVec 64} {lc' pc' : Nat}
    {bL bP : FineBudget} {st0 st : MallocngSt} (h : FineSplitInv bL bP st0) (hNd : (st0.groups.map (·.metaPtr)).Nodup)
    (hwf' : MallocngWFInflight inflight' base brkStart brk' lc' pc' st) (hMa : st.metaAreas.length ≤ fineMaxMetaAreas bP)
    (hMono : GroupsFreeMono st0.groups st.groups) : FineSplitInv bL bP st := by
  have hNd' := hwf'.groups_nodup.1
  have hUnf : ∀ w : SlotState → Nat, (∀ s, (∀ p req eff, s ≠ .liveUser p req eff) → w s = 0) →
      (st.groups.map fun g => (g.slots.map w).sum).sum ≤ (st0.groups.map fun g => (g.slots.map w).sum).sum :=
    fun w hw0 => sum_le_of_nodup_inj_ag hNd hNd' fun g' hg' => by
      obtain ⟨g, hg, hM, _, _, _, _, hSl⟩ := hMono g' hg'; exact ⟨g, hg, hM, slotUserWeight_le_of_sub_ag hw0 hSl⟩
  refine {
    live_inv := h.live_inv, peak_inv := h.peak_inv, peaks_le := h.peaks_le, meta_le := hMa, groups_geom := ?_,
    class_bounds := fun sc hsc => ClassFineBound.le_trans (stClassBound_le_of_groupsFreeMono hNd hNd' hMono sc) (h.class_bounds sc hsc),
    liveNom_le := fun k hk => Nat.le_trans (hUnf (slotLiveNom k) fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) (h.liveNom_le k hk),
    reallocCross_le := fun k hk => Nat.le_trans (filter_sum_le_of_groupsFreeMono_ag (·.sc < 48) (fun g => (g.slots.map (slotReallocCross g.sc k)).sum)
      (fun _ _ hSc _ _ => by simp [hSc]) (fun _ _ hSc _ _ hSl => hSc ▸ slotUserWeight_le_of_sub_ag (fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl) hNd hNd' hMono) (h.reallocCross_le k hk),
    exc_le := fun sc hsc => Nat.le_trans (filter_sum_le_of_groupsFreeMono_ag (·.sc == sc) (fun g => (g.slots.map slotHasOverAlign).sum)
      (fun _ _ hSc _ _ => by simp [hSc]) (fun _ _ _ _ _ hSl => slotUserWeight_le_of_sub_ag (fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl) hNd hNd' hMono) (h.exc_le sc hsc),
    live63Count_le := Nat.le_trans (hUnf slotLive63Count fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) h.live63Count_le,
    live63Bytes_le := Nat.le_trans (hUnf slotLive63Bytes fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) h.live63Bytes_le,
    straddle63_le := Nat.le_trans (filter_sum_le_of_groupsFreeMono_ag (·.sc == 63) (fun g => (g.slots.map slotStraddle63).sum)
      (fun _ _ hSc _ _ => by simp [hSc]) (fun _ _ _ _ _ hSl => slotUserWeight_le_of_sub_ag (fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) hSl) hNd hNd' hMono) h.straddle63_le,
    overAlign_le := Nat.le_trans (hUnf slotOverAlign fun s hs => by cases s with | liveUser p r e => exact False.elim (hs p r e rfl) | _ => rfl) h.overAlign_le }
  intro g' hg' hsc'; obtain ⟨g, hg, _, hSc, hCnt, hMl, hPar, hSl⟩ := hMono g' hg'; have hGeomG := h.groups_geom g hg (hSc ▸ hsc')
  refine ⟨fun s hs p req eff hsEq => ?_, fun hMl0' => ?_, fun hPos' => by rw [hCnt, hMl, hSc]; exact hGeomG.2.2 (hMl ▸ hPos')⟩
  · obtain ⟨idx, hIdx', hGet'⟩ := List.getElem_of_mem hs; have hIdx : idx < g.slots.length := hSl.1 ▸ hIdx'
    rw [hSc]; exact hGeomG.1 _ (List.getElem_mem hIdx) p req eff (hSl.2 idx hIdx' hIdx p req eff (hGet'.trans hsEq))
  · obtain ⟨hKind, pg, hpg, hParG, hPgSc⟩ := hGeomG.2.1 (hMl ▸ hMl0')
    obtain ⟨_, pg', hpg', _, _, hPar', _⟩ := (hwf'.groups_wf g' hg').2.2.2.2.2.2.2.2.2.2.2.2.1 hMl0'
    obtain ⟨pg0, hpg0, hPgM, hPg0Sc, _, _, _, _⟩ := hMono pg' hpg'
    have hPg0Eq : pg0 = pg := nodup_mem_eq_of_metaPtr_ag hNd hpg0 hpg (hPgM.symm.trans (Option.some.inj (hPar'.symm.trans (hPar.trans hParG))))
    exact ⟨by rw [hSc, hCnt]; exact hKind, pg', hpg', hPar', by rw [hPg0Sc, hPg0Eq, hPgSc, hCnt, hSc]⟩

set_option maxHeartbeats 800000 in
private theorem wp_allocGroup_root_fine [MallocngMultiPlacement] {ro : Bool}
    (sc req inflight cnt' : Nat) (hsc : sc < 48) (hReqLo : allocSlotReqLo sc ≤ req) (hReqHi : req ≤ nominalSlotCap sc)
    (hlo : 1 ≤ cnt') (hhi : cnt' ≤ 32) (hgt2048 : 2048 < cnt' * slotStride sc + 16) (hprod : cnt' * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) (use : BitVec 64) (hcnt' : cnt' = cntSel sc use.toNat)
    (γ : GhostName) (tp brkStart m : BitVec 64) (liveCost peakCost peakCount : Nat) (bL bP : FineBudget) (maxMeta : Nat)
    (st0 st1 : MallocngSt) (s0 sr : State) (hw564 : Blk08HasWords564 mallocngFaultSvc) (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hClaim1 : totalClaimedSlots st1 = 0) (hFine1 : FineSplitInv bL bP st1) (hRoom1 : AllocSlotOccRoom bP st1 sc)
    (hCB10 : ∀ k, (stClassBound st1 k).le (stClassBound st0 k)) (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length, st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0)
    (hRes1 : st1.reservedMetas = m :: st0.reservedMetas)
    (hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧ totalLiveCount st1 = totalLiveCount st0 ∧
      st1.metaAreas.length ≤ st0.metaAreas.length + 1 ∧ st1.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hOrph1 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sr.mem)
    (hDelta1 : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sr.mem)
    (hGrpCl1 : ∀ U : Nat, peakCount ≤ U → Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st1.groups) (hUse1 : use.toNat ≤ peakCount)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sr.mem) (hpc : sr.pc = mbase 8 + allocSlotOff_root) (hrun : sr.status = .Running)
    (hsp : sr.sp = s0.sp - 96#64) (hsAl : sr.spAligned = true) (htp0 : s0.tpidrEl0 = tp)
    (hProc : MallocngProcPreserved s0 sr) (hvr0 : calleeSavedVRegs sr = calleeSavedVRegs s0)
    (hx4 : sr.readReg64 .x4 = 4096#64) (hx19 : sr.readReg64 .x19 = m) (hx20 : sr.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (hx21 : sr.readReg64 .x21 = BitVec.ofNat 64 sc) (hx22 : sr.readReg64 .x22 = Obj.pageOf maddrs.ctx) (hx23 : sr.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx24 : sr.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx25 : sr.readReg64 .x25 = BitVec.ofNat 64 req) (hx27 : sr.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc))
    (hx0 : sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc)) (hx2 : sr.readReg64 .x2 = use) (hx6 : sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt')) :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) sr
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
        (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ (m ↦ₛ List.replicate 40 0#8) ∗
       MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sr.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp)
      (fun sf P_f => AllocSlotFinePost sc req inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st0 s0 sf P_f ro)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝) := by
  have hsc_pos : 0 < sc := root_sc_pos hhi hgt2048
  unfold MallocngCoreStInflightModeA MallocngRuntime; simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf1; obtain ⟨hActL, hUseL, hUnmL, hBncL, _, hLstL⟩ := hwf1.ctx_lens
  obtain ⟨CtxRest, hCtxSp, hCtxFd⟩ := ctx_split_fields maddrs.ctx st1.ctx hActL hUseL hUnmL hBncL
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21)
    (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  let RestCore : SepProp := (MallocngLiveAuth γ st1.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1) ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))
  let BaseF : SepProp := (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    (m ↦ₛ List.replicate 40 0#8) ∗ ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗ CtxRest ∗ RestCore)
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗
      ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF)
    (Entails.of_eq (by dsimp only [Saved, RestCore, BaseF]; rw [hCtxSp]; ac_rfl)) ?_
  have h_pre : SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 16) sr
      (((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗
       ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF)
      (fun sc0 Pc0 => ∃ cnt_f len bounces' unmapSeq' seq', RootMmapParamsOk sc cnt_f len ∧ (cnt_f = 1 → req + 20 ≤ len) ∧
        (cnt_f, len) ∈ reachableRootPairs sc ∧ len ≤ Cost.rootBytesAt sc use.toNat ∧
        bounces'.length = 32 ∧ (∀ b ∈ bounces', b.toNat ≤ 150) ∧ unmapSeq'.length = 32 ∧ sc0.sp = sr.sp ∧ sc0.spAligned = sr.spAligned ∧ PureStatePres sr sc0 ∧
        sc0.readReg64 .x0 = 0#64 ∧ sc0.readReg64 .x1 = BitVec.ofNat 64 len ∧ sc0.readReg32 .x2 = 3#32 ∧ sc0.readReg32 .x3 = 0x22#32 ∧
        sc0.readReg32 .x4 = BitVec.allOnes 32 ∧ sc0.readReg64 .x5 = 0#64 ∧ sc0.readReg64 .lr = mbase 8 + allocSlotOff_after_mmap ∧
        sc0.readReg64 .x19 = m ∧ sc0.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sc0.readReg64 .x21 = BitVec.ofNat 64 sc ∧
        sc0.readReg64 .x22 = Obj.pageOf maddrs.ctx ∧ sc0.readReg64 .x23 = BitVec.ofNat 64 sc ∧ sc0.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc) ∧
        sc0.readReg64 .x26 = BitVec.ofNat 64 len ∧ Pc0 = (((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗
          ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗ (((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ BaseF))) (fun _ => ⌜False⌝) := by
    refine SepWP.seq (wp_root_bounces sr sc st1.ctx.unmapSeq st1.ctx.bounces st1.ctx.seq _ hw768 hr768 hsc hUnmL hBncL hwf1.bounces_wf hpc hrun hx22 hx21) ?_
    rintro s1 P1 hpc1 hrun1 ⟨bounces', hBncL', hBnc', _, hsp1, hal1, hpsp1, hx1_1, hr1, h39_1, hP1⟩; rw [hP1]
    refine SepWP.weaken_pre (Entails.of_eq (show (((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗
        ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ BaseF) =
        (((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗
         ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ (((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ BaseF)) by ac_rfl)) ?_
    refine SepWP.seq (wp_root_seq_usage s1 sc st1.ctx.usageByClass st1.ctx.unmapSeq st1.ctx.seq _ hw768 hr768 hsc hUseL hUnmL hpc1 hrun1 hx1_1
      (by rw [hr1 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx22])
      (by rw [hr1 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21])) ?_
    rintro s2 P2 hpc2 hrun2 ⟨unmapSeq', seq', hUnmL', _, hsp2, hal2, hpsp2, hr2, hx2_2, hP2⟩; rw [hP2]
    have h2_reg : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s2.readReg64 r = sr.readReg64 r :=
      fun r a1 a2 a3 a5 a7 a8 a9 => (hr2 r a1 a2 a3).trans (hr1 r a1 a3 a5 a7 a8 a9)
    refine SepWP.seq (wp_root_size_select_fine s2 sc req cnt' _ hw768 hsc hReqHi hlo hhi hgt2048 hprod h25 hpc2 hrun2
      (by rw [h2_reg .x0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx0])
      (by rw [h2_reg .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx4])
      (by rw [h2_reg .x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx6])
      (fun h => (hr2 .x7 (by decide) (by decide) (by decide)).trans (h39_1 h).2)
      (by rw [h2_reg .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx20])
      (by rw [h2_reg .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx21])
      (by rw [h2_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx24])
      (by rw [h2_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx25])
      (by rw [h2_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx27])) ?_
    rintro s3 P3 hpc3 hrun3 ⟨cnt_f, len, hOk, hRq, ⟨c, hrel, hSel, hLen⟩, _, hsp3, hal3, hpsp3, hx20_3, hx26_3, hr3, hP3⟩; rw [hP3]
    have hPair : (cnt_f, len) ∈ reachableRootPairs sc := mem_reachableRootPairs_of_rootSelect hsc hcnt' hgt2048 hrel.1 hReqLo hReqHi hSel
    have hRB : len ≤ Cost.rootBytesAt sc use.toNat := Cost.rootLen_le_rootBytesAt' hsc hcnt' hgt2048 hrel
      (fun h => ⟨by rw [hx2_2 (by omega), hr1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx2],
        by rw [hr2 .x5 (by decide) (by decide) (by decide), (h39_1 h).1]⟩) hLen
    refine SepWP.mono (wp_mmap_call_prep s3 len _ hw768 hr768 hpc3 hrun3 hx26_3) ?_
    rintro sc0 Pc0 _ _ ⟨_, hsp4, hal4, hpsp4, h0c, h1c, h2c, h3c, h4c, h5c, hlr_c, hr4, hPc0⟩
    have hkeep : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x4 → r ≠ .x5 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 → sc0.readReg64 r = sr.readReg64 r :=
      fun r a0 a1 a2 a3 a4 a5 a7 a8 a9 a20 a25 a26 a27 a30 => (hr4 r a0 a1 a2 a3 a4 a5 a30).trans ((hr3 r a0 a1 a3 a20 a25 a26 a27).trans (h2_reg r a1 a2 a3 a5 a7 a8 a9))
    exact ⟨cnt_f, len, bounces', unmapSeq', seq', hOk, hRq, hPair, hRB, hBncL', hBnc', hUnmL',
      hsp4.trans (hsp3.trans (hsp2.trans hsp1)), hal4.trans (hal3.trans (hal2.trans hal1)), hpsp1.trans (hpsp2.trans (hpsp3.trans hpsp4)), h0c, h1c, h2c, h3c, h4c, h5c, hlr_c,
      (hkeep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19,
      (hr4 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20_3,
      (hkeep .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21,
      (hkeep .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22,
      (hkeep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23,
      (hkeep .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24,
      (hr4 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26_3, hPc0⟩
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 16) hcl (SepWP.mono h_pre ?_)
  rintro sc0 Pc0 hpcc0 hrc0 ⟨cnt_f, len, bounces', unmapSeq', seq', hOk, hRq, hPair, hRB, hBncL', hBnc', hUnmL', hspc0, halc0, hpspc0,
    h0c, h1c, h2c, h3c, h4c, h5c, hlr_c, h19c, h20c, h21c, h22c, h23c, h24c, h26c, hPc0⟩ hpermc0 hclc0; subst hPc0
  obtain ⟨hcf_lo, hcf_hi, hlen4096, hdvd_len, hlen1M, hlen25, hlen0, hcap_lt⟩ := hOk
  have hAlignEq : pageAlignUp len = len := by obtain ⟨k, rfl⟩ := hdvd_len; unfold pageAlignUp PAGE_SIZE; omega
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  have hsp_c : sc0.sp = s0.sp - 96#64 := hspc0.trans hsp; have hal_c : sc0.spAligned = true := halc0.trans hsAl
  have hProc_c : MallocngProcPreserved s0 sc0 := MallocngProcPreserved.trans hProc hpspc0.1
  have htp_c : sc0.tpidrEl0 = tp := hProc_c.2.2.1.trans htp0; have hlen_mod : len % PAGE_SIZE = 0 := Nat.mod_eq_zero_of_dvd hdvd_len
  have hx1_nat : (sc0.readReg64 .x1).toNat = len := by rw [h1c, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) =
      (stackFrame sc0 64 ∗ stackFrameAt (s0.sp - 96#64 - 64#64) (allocSlotDepthBound sc * 96 + 224 - 64)) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) 64 _ (by omega) (by omega), solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) 64 (by omega)]
    unfold stackFrame; rw [hsp_c]
  refine call_withCL_frame_auto (x := ()) (placed_mmapRw_large_ok (P := mallocngBlockProg mmpl 8 msvc) tp errnoVal len
      (by omega) (by rw [mallocngMaxAllocSize_eq]; omega)) hclc0 hpcc0 hrc0 hal_c hlr_c
    (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    ?_ (by intro R h; dsimp only; dsimp +zeta only [BaseF, RestCore] at h; rw [pure_sepConj_of_true ⟨htp_c, h0c, hx1_nat, h2c, h3c, h4c, h5c⟩]; rw [hStkSp] at h; revert R h; sep_frame)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢
      obtain ⟨⟨hfs, htr, hsig, hpm, _, hgap⟩, hR'⟩ := ho'; rw [hAlignEq] at hgap
      have hbd := fineMetaStep_le_allocSlot sc maxMeta
      have h1 : 1 * FineMetaStep maxMeta ≤ (allocSlotDepthBound sc + 1) * FineMetaStep maxMeta :=
        Nat.mul_le_mul_right _ (by omega)
      exact ⟨MallocngPlacedOomCond.of_delta (k' := 2 * (allocSlotDepthBound sc + 1))
        (hfs.trans hProc_c.1) (htr.trans hProc_c.2.1) (hsig.trans hProc_c.2.2.2.2.2.2)
        (mappedDelta_perm_right hDelta1 (hpm.trans hpermc0)) (by omega) hbd
        fun hsan => ⟨len, by dsimp [PAGE_SIZE]; omega, hlen_mod, by omega, hgap hsan⟩, hR'⟩)
  intro sm hpc_m hrun_m hsp_m hcs_m hcl_m; dsimp only; rw [hAlignEq]; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro mb; apply SepWP.pure_elim; rintro ⟨hProc_m, hbrk_m, hx0_m, hMbNe0, hMbNeg1, hMbDvd, hMbHi, hDMmap, hNewMmap⟩
  let maplen := len / 4096; have hMapEq : maplen * 4096 = len := Nat.div_mul_cancel hdvd_len
  have hMapLo : 1 ≤ maplen := (by omega); have hMapHi : maplen ≤ 256 := by omega
  have hMapPos : 0 < maplen := Nat.lt_of_lt_of_le Nat.zero_lt_one hMapLo
  have hMbAl : mb.toNat % 4096 = 0 := Nat.mod_eq_zero_of_dvd hMbDvd; have hsp_m0 : sm.sp = s0.sp - 96#64 := hsp_m.trans hsp_c
  have hal_m : sm.spAligned = true := by rw [State.spAligned, hsp_m]; simpa [State.spAligned] using hal_c
  apply SepWP.with_sat; rintro ⟨R_sat, hm_sat⟩
  have ⟨R_disj, hm_disj⟩ : ∃ R_disj, sm.mem ⊨ (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ∗ memMapped mb (maplen * 4096) ∗
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗ ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1) ∗ (R_disj ∗ R_sat) := ⟨?_, by revert R_sat hm_sat; rw [hMapEq]; sep_frame⟩
  obtain ⟨hMbLo, hDisjRoot⟩ := fresh_mmap_disjoint_placed hwf1 hMapPos hMbNe0 hMbDvd (hMapEq ▸ hMbHi) hm_disj
  let PostMmapF := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    ((m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32)) ∗
    ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗ ((maddrs.ctx + 464#64) ↦₆₄* st1.ctx.usageByClass) ∗
    ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗
    CtxRest ∗ (mb ↦ₛ List.replicate (maplen * 4096) 0#8) ∗ memMapped mb (maplen * 4096) ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ PostMmapF)
    (Entails.of_eq (by dsimp +zeta only [PostMmapF, RestCore, Saved]; rw [hStkSp, split_rep40_zero m, hMapEq]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_pub_add) hcl_m
    (SepWP.mono (wp_root_after_mmap sm m mb st1.ctx.mmapCounter sc cnt_f maplen PostMmapF hw768 hr768 hsc hcf_lo hcf_hi hMapLo hMapHi hMbNeg1 hpc_m hrun_m hx0_m
      (hcs_m.1.trans h19c) (hcs_m.2.1.trans h20c) (hcs_m.2.2.2.1.trans h22c) (hcs_m.2.2.2.2.2.1.trans h24c) (hcs_m.2.2.2.2.2.2.2.1.trans (hMapEq ▸ h26c)))
      fun spub Ppub hpcpub hrpub ⟨_, hsp_p, hal_p, hpsp_p, hx0_p, hx1_p, hx2_p, hx28_p, hr_p, hPpub⟩ hperm_p _ => ?_)
  subst hPpub; let lastIdx := cnt_f - 1; let activeIdx := min (4080 / slotStride sc - 1) (cnt_f - 1)
  have hscA : sc < st1.ctx.active.length := (by omega); have hscU : sc < st1.ctx.usageByClass.length := (by omega); have hscL : sc < st1.activeLists.length := by omega
  obtain ⟨ActRest, hActSp, hActUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st1.ctx.active sc hscA
  obtain ⟨UseRest, hUseSp, hUseUp⟩ := words64_focus_set (maddrs.ctx + 464#64) st1.ctx.usageByClass sc hscU
  let PubF : SepProp := (((maddrs.ctx + 12#64) ↦₃₂ (st1.ctx.mmapCounter + 1#32)) ∗ ActRest ∗ UseRest ∗ ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗
    ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗ CtxRest ∗ ((mb + 9#64) ↦ₛ List.replicate (maplen * 4096 - 9) 0#8) ∗
    memMapped mb (maplen * 4096) ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ RestCore)
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗ ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU)) ∗
      (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32) ∗ ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 maplen <<< 12)) ∗ (mb ↦₆₄ 0#64) ∗ ((mb + 8#64) ↦₈ 0#8) ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗ ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x27) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x28) ∗ PubF)
    (Entails.of_eq (by dsimp only [PostMmapF, Saved, AllocSlotSaved12, PubF]; rw [hActSp, hAct0 hscA, hUseSp, split_mmap_hdr9 mb (n := maplen * 4096) (by omega)]; ac_rfl)) ?_
  refine SepWP.mono (wp_publish_new_group s0.sp (s0.readReg64 .x30) m mb (st1.ctx.usageByClass[sc]'hscU) 0#64 0#64 0#32 0#32 0#8
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29)
      sc activeIdx lastIdx maplen none 0 true PubF _ hw564 hw768 hr768 hsc (by omega) (Nat.min_le_right _ _) hpcpub hrpub (hsp_p.trans hsp_m0) (hal_p.trans hal_m)
      ((hr_p .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.2.1.trans h22c))
      ((hr_p .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.2.2.1.trans h23c))
      ((hr_p .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.2.2.1.trans h21c))
      ((hr_p .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hcs_m.1.trans h19c)) hx0_p hx1_p hx2_p hx28_p) ?_
  rintro sf P_f _ _ ⟨_, hsp_f, _, hpsp_f, hperm_f, hx0_f, h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, _, actB, hActB, hPf⟩
  have hbrk_f : sf.brk = sr.brk := hpsp_f.2.1.trans (hpsp_p.2.1.trans (hbrk_m.trans hpspc0.2.1))
  have hwf1' : MallocngWFInflight (inflight + 1) maddrs.base brkStart sf.brk liveCost peakCost st1 := hbrk_f.symm ▸ hwf1
  have hcap_lt' : 12 + (lastIdx + 1) * (if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc) < maplen * 4096 := by
    dsimp only [lastIdx, maplen]; rw [Nat.sub_add_cancel hcf_lo, hMapEq]; exact hcap_lt
  obtain ⟨hwf', hCost', hCount', hBmRw, hBmPn, hMpEq, hZeroSl0⟩ :=
    wf_alloc_root_mmap (mmapCtr' := st1.ctx.mmapCounter + 1#32) (unmapSeq' := unmapSeq') (bounces' := bounces') (seq' := seq')
      hwf1' hsc hscA hscL hscU (hAct0 hscA) hRes1 hMapPos hMbLo hMbAl (hMapEq ▸ hMbHi) (hMapEq ▸ hlen25) (hMapEq ▸ hlen1M)
      (fun hl0 => by have : cnt_f - 1 = 0 := hl0; exact hMapEq ▸ hlen0 (by omega)) (by omega : lastIdx ≤ 31) (by rw [hActB]; exact Nat.min_le_right _ _) (fun _ => hsc_pos) hcap_lt' hDisjRoot hUnmL' hBncL' hBnc'
  let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 ((actB &&& 0x1f#8).toNat)) - 1#32
  let cg : GroupDesc := { metaPtr := m, prev := m, next := m, mem := mb, availMask := initAvail - 1#32, freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail, lastIdx := lastIdx, sc := sc, maplen := maplen, activeByte := actB, parentMeta := none, nestedCap := 0, slots := newGroupSlots lastIdx ((actB &&& 0x1f#8).toNat), freshZero := true }
  let ctx' : CtxFields := { st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32, active := st1.ctx.active.set sc m, usageByClass := st1.ctx.usageByClass.set sc (st1.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt), unmapSeq := unmapSeq', bounces := bounces', seq := seq' }
  let grpBs : List (BitVec 8) := unpack64 m ++ [actB] ++ List.replicate (maplen * 4096 - 9) 0#8
  let st' : MallocngSt := { st1 with ctx := ctx', reservedMetas := st0.reservedMetas, groups := cg :: st1.groups, activeLists := st1.activeLists.set sc [m], masterDom := extendDom (extendDom st1.masterDom m 40) mb (maplen * 4096), byteVal := writeBytesToMap (writeBytesToMap st1.byteVal mb grpBs) m cg.metaBytes }
  have hCgPair : (cg.cnt, cg.maplen * 4096) ∈ reachableRootPairs sc := by show (lastIdx + 1, maplen * 4096) ∈ _; rw [Nat.sub_add_cancel hcf_lo, hMapEq]; exact hPair
  obtain ⟨hFine', hCB'_1⟩ := fineGroups_add_root (st' := st') hFine1 hwf1 hClaim1 hsc hscU hAct0 hRoom1 rfl hMapPos hCgPair (fun s hs => newGroupSlots_no_liveUser s hs) hFine1.meta_le rfl
  have hCB'_0 : ∀ k < sc, (stClassBound st' k).le (stClassBound st0 k) := fun k hk => ClassFineBound.le_trans (hCB'_1 k hk) (hCB10 k)
  have hProc_f : MallocngProcPreserved s0 sf := MallocngProcPreserved.trans (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_c hProc_m) hpsp_p.1) hpsp_f.1
  have hvr_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := hpsp_f.2.2.trans (hpsp_p.2.2.trans (hcs_m.2.2.2.2.2.2.2.2.2.2.2.trans (hpspc0.2.2.trans hvr0)))
  refine ⟨?_, hsp_f, calleeSaved_of_epilogue h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvr_f⟩
  refine Entails.trans ?_ (Entails.sepExists_intro st'); refine Entails.trans ?_ (Entails.sepExists_intro 0)
  have hDynEq : dynamicRootRegions st' = st1.metaAreas.map (fun ma => (ma.base, 4096)) ++ st1.guardPages.map (fun gp => (gp, 4096)) ++
      st1.availMetaPages.map (fun ap => (ap, 4096)) ++ ((mb, len) :: (st1.groups.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))) := by
    dsimp +zeta only [dynamicRootRegions, st', cg]; simp [hMapPos, hMapEq]
  have hOrph' : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem := by
    refine mallocngNoOrphanMappings_root_step rfl hOrph1 hpermc0 hNewMmap (hperm_f.trans hperm_p) ?_ ?_
    · intro iv hiv; rw [hDynEq]; unfold dynamicRootRegions at hiv; simp only [List.mem_append, List.mem_cons] at hiv ⊢
      rcases hiv with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · rw [hDynEq]; simp only [List.mem_append, List.mem_cons]; exact Or.inr (Or.inl trivial)
  have hPure : MallocngProcPreserved s0 sf ∧ st'.reservedMetas = st0.reservedMetas ∧ st'.liveMap = st0.liveMap ∧
      totalLiveEffCost st' = totalLiveEffCost st0 ∧ totalLiveCount st' = totalLiveCount st0 ∧
      st'.metaAreas.length ≤ st0.metaAreas.length + allocSlotDepthBound sc + 1 ∧ st'.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
      FineSplitInv bL bP st' ∧ (∀ k < sc, (stClassBound st' k).le (stClassBound st0 k)) ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st'.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length, st'.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
      sf.readReg32 .x0 = BitVec.ofNat 32 0 ∧ 0 ≤ 31 ∧
      (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : 0 < g.slots.length,
        g.sc = sc ∧ req + 4 ≤ g.stride ∧ g.metaPtr = st'.ctx.active[sc]'hAct ∧ g.slots[0]'hIdx = .claimed ∧
        (g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart 0) g.stride a → st'.byteVal a = 0#8)) ∧
      MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
      MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0.mem sf.mem ∧
      (∀ U : Nat, peakCount ≤ U → Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st'.groups) := by
    refine ⟨hProc_f, rfl, hRel1.1, hCost'.trans hRel1.2.1, hCount'.trans hRel1.2.2.1, show st1.metaAreas.length ≤ _ by have := hRel1.2.2.2.1; omega, hRel1.2.2.2.2,
      hFine', hCB'_0, (fun k hk hk1 hk0 => ?_), by simp [State.readReg32, hx0_f], by omega,
      ⟨cg, List.Mem.head _, show sc < (st1.ctx.active.set sc m).length by simp [hscA], show 0 < (newGroupSlots lastIdx _).length by simp [newGroupSlots], rfl,
        root_stride_ge_req hsc hReqHi hMapPos (fun hl0 => by have : cnt_f - 1 = 0 := hl0; exact hMapEq ▸ hRq (by omega)), show m = (st1.ctx.active.set sc m)[sc]'_ by simp, rfl, fun _ => hZeroSl0⟩,
      hOrph', root_mappedDelta_combine_fine hDelta1 hpermc0 hDMmap (hperm_f.trans hperm_p) hlen1M,
      fun U hUle hU => (hGrpCl1 U hUle hU).cons fun _ _ => by show maplen * 4096 ≤ Cost.grpMax sc U; rw [hMapEq]; exact Nat.le_trans hRB (Cost.rootBytesAt_le_grpMax sc (Nat.le_trans hUse1 hUle))⟩
    dsimp +zeta only [st', ctx'] at hk1 ⊢; rw [List.getElem_set_ne (by omega : sc ≠ k)]; exact hActLow1 k hk (by simpa using hk1) hk0
  rw [pure_sepConj_of_true hPure]
  have hcg_meta : cg = { metaPtr := m, prev := m, next := m, mem := mb, availMask := ((2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32) - 1#32, freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~((2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32), lastIdx := lastIdx, sc := sc, maplen := maplen, activeByte := actB, parentMeta := none, nestedCap := 0, slots := newGroupSlots lastIdx activeIdx, freshZero := true } := by
    dsimp +zeta only [cg, initAvail]; rw [hActB]
  dsimp only at hPf; rw [← hcg_meta] at hPf; subst hPf
  have hCtxEq : (((maddrs.ctx + 12#64) ↦₃₂ (st1.ctx.mmapCounter + 1#32)) ∗ (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗ ActRest) ∗
      (((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 (lastIdx + 1))) ∗ UseRest) ∗
      ((maddrs.ctx + 848#64) ↦ₛ unmapSeq') ∗ ((maddrs.ctx + 880#64) ↦ₛ bounces') ∗ ((maddrs.ctx + 912#64) ↦₈ seq') ∗ CtxRest) = (maddrs.ctx ↦ₛ ctx'.toBytes) := by
    rw [hActUp, hUseUp]; exact hCtxFd _ _ _ _ _ _ (by simp [hActL]) (by simp [hUseL]) hUnmL' hBncL'
  unfold MallocngCoreStInflightModeA MallocngRuntime; rw [pure_sepConj_of_true hwf']
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_intro (P := fun v => (tp - 0xa4#64) ↦₃₂ v) errnoVal)))))
  have hJoin := saved12_rejoin_stackFrame s0 sc (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  dsimp only [AllocSlotSaved12] at hJoin; have hHdrEq := fold_mmap_hdr9 mb m actB (maplen * 4096 - 9)
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left hJoin)
  rw [← hCtxEq, ← hBmRw, ← hHdrEq, ← hBmPn, ← hMpEq]; dsimp only [PubF, RestCore, st', cg, initAvail, lastIdx]; ac_rfl

/-! ## 4. Nested `alloc_slot` + `enframe` Path (`wp_allocGroup_nested_fine`) -/

private theorem enframe_slot_bytes_wf_fine (val : BitVec 64 → BitVec 8) (pg : GroupDesc)
    (pIdx off sc cnt' : Nat) (m : BitVec 64) (actB : BitVec 8) (bs2 bs3 bs' : List (BitVec 8))
    (hcnt2 : 2 ≤ cnt') (hFit : 16 * off + 16 + cnt' * slotStride sc ≤ pg.stride) (hStrHi : pg.stride ≤ 65524)
    (hSbEnd : (pg.slotStart pIdx - 4#64) + BitVec.ofNat 64 pg.stride = pg.slotEnd pIdx)
    (hSbMb4 : (pg.slotStart pIdx - 4#64) + BitVec.ofNat 64 (16 * off + 4) = pg.slotStart pIdx + BitVec.ofNat 64 (16 * off))
    (hbs2L : bs2.length = pg.stride + 1) (hbs2_0 : bs2.getD 0 0#8 = 0#8) (hbs2_off : bs2.getD (16 * off) 0#8 = 0#8)
    (hbs2_2 : bs2.getD (16 * off + 2) 0#8 = (unpack16 (BitVec.ofNat 16 (((pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)).toNat - pg.storage.toNat) / 16))).getD 0 0#8)
    (hbs2_3 : bs2.getD (16 * off + 3) 0#8 = (unpack16 (BitVec.ofNat 16 (((pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)).toNat - pg.storage.toNat) / 16))).getD 1 0#8)
    (hbs2_end : bs2.getD pg.stride 0#8 = 0#8) (hbs3L : bs3.length = bs2.length)
    (hbs3_1 : bs3.getD (16 * off + 1) 0#8 = BitVec.ofNat 8 ((6 <<< 5) ||| pIdx))
    (hbs3_out : ∀ idx, idx ≠ 16 * off + 1 → bs3.getD idx 0#8 = bs2.getD idx 0#8) (hbs'L : bs'.length = bs3.length)
    (hbs'Z : ∀ j, 0 ≤ j → j ≤ cnt' → bs'.getD (16 * off + 16 + j * slotStride sc) 0#8 = 0#8)
    (hbs'Out : ∀ idx, (∀ j, 0 ≤ j → j ≤ cnt' → idx ≠ 16 * off + 16 + j * slotStride sc) → bs'.getD idx 0#8 = bs3.getD idx 0#8) :
    let slotBase := pg.slotStart pIdx - 4#64; let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
    let slotBs' := replaceSlice bs' (16 * off + 4) (unpack64 m ++ [actB]); let lastIdx := cnt' - 1
    slotBs'.length = pg.stride + 1 ∧ writeBytesToMap val slotBase slotBs' slotBase = 0#8 ∧
    writeBytesToMap val slotBase slotBs' (pg.slotEnd pIdx) = 0#8 ∧ writeBytesToMap val slotBase slotBs' (mb - 4#64) = 0#8 ∧
    writeBytesToMap val slotBase slotBs' (mb - 3#64) = BitVec.ofNat 8 ((6 <<< 5) ||| pIdx) ∧
    readBytesFromMap (writeBytesToMap val slotBase slotBs') (mb - 2#64) 2 = unpack16 (BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16)) ∧
    readBytesFromMap (writeBytesToMap val slotBase slotBs') mb 8 = unpack64 m ∧ writeBytesToMap val slotBase slotBs' (mb + 8#64) = actB ∧
    writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + (lastIdx + 1) * slotStride sc)) = 0#8 ∧
    (∀ idx : Nat, idx < lastIdx + 1 → writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + idx * slotStride sc)) = 0#8) := by
  intro slotBase mb slotBs' lastIdx
  have hSbMb4' : slotBase + BitVec.ofNat 64 (16 * off + 4) = mb := hSbMb4; have hu64L : (unpack64 m).length = 8 := rfl
  have hSub9L : (unpack64 m ++ [actB]).length = 9 := (by simp [hu64L]); have hLen' : bs'.length = pg.stride + 1 := hbs'L.trans (hbs3L.trans hbs2L)
  have hFit9 : (16 * off + 4) + (unpack64 m ++ [actB]).length ≤ bs'.length := by rw [hSub9L, hLen']; omega
  have hSlotL : slotBs'.length = pg.stride + 1 := (replaceSlice_length hFit9).trans hLen'; have hSlot64 : slotBs'.length ≤ 2 ^ 64 := by rw [hSlotL]; omega
  have hPre : ∀ idx, idx < 16 * off + 4 → slotBs'.getD idx 0#8 = bs3.getD idx 0#8 := fun idx hi =>
    (replaceSlice_getD_out hFit9 (Or.inl hi)).trans (hbs'Out idx (fun _ _ _ => by omega))
  have hEndZ : slotBs'.getD pg.stride 0#8 = 0#8 := by
    rw [replaceSlice_getD_out hFit9 (Or.inr (by rw [hSub9L]; omega))]
    by_cases hHit : ∃ j, 0 ≤ j ∧ j ≤ cnt' ∧ pg.stride = 16 * off + 16 + j * slotStride sc
    · obtain ⟨j, hj0, hj1, hEq⟩ := hHit; rw [hEq]; exact hbs'Z j hj0 hj1
    · rw [hbs'Out _ (fun j hj0 hj1 hEq => hHit ⟨j, hj0, hj1, hEq⟩), hbs3_out _ (by omega), hbs2_end]
  have hZeroAt : ∀ j, j ≤ cnt' → writeBytesToMap val slotBase slotBs' (mb + BitVec.ofNat 64 (12 + j * slotStride sc)) = 0#8 := fun j hj => by
    have hjLe : j * slotStride sc ≤ cnt' * slotStride sc := Nat.mul_le_mul_right _ hj
    have hAd : mb + BitVec.ofNat 64 (12 + j * slotStride sc) = slotBase + BitVec.ofNat 64 (16 * off + 16 + j * slotStride sc) := by
      rw [← hSbMb4', BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [hAd, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64,
        replaceSlice_getD_out hFit9 (Or.inr (by rw [hSub9L]; omega)), hbs'Z j (Nat.zero_le _) hj]
  refine ⟨hSlotL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 := writeBytesToMap_getD val slotBase slotBs' (i := 0) (by rw [hSlotL]; omega) hSlot64
    rw [BitVec.add_zero, hPre 0 (by omega), hbs3_out 0 (by omega), hbs2_0] at h0; exact h0
  · rw [← hSbEnd, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64, hEndZ]
  · have ha : mb - 4#64 = slotBase + BitVec.ofNat 64 (16 * off) := by rw [← hSbMb4', BitVec.ofNat_add, ← BitVec.add_assoc]; exact BitVec.add_sub_cancel _ _
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64, hPre _ (by omega), hbs3_out _ (by omega), hbs2_off]
  · have ha : mb - 3#64 = slotBase + BitVec.ofNat 64 (16 * off + 1) := by
      rw [← hSbMb4', show 16 * off + 4 = (16 * off + 1) + 3 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]; exact BitVec.add_sub_cancel _ _
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64, hPre _ (by omega), hbs3_1]
  · have ha : mb - 2#64 = slotBase + BitVec.ofNat 64 (16 * off + 2) := by
      rw [← hSbMb4', show 16 * off + 4 = (16 * off + 2) + 2 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]; exact BitVec.add_sub_cancel _ _
    let u16 := BitVec.ofNat 16 ((mb.toNat - pg.storage.toNat) / 16); have hu16L : (unpack16 u16).length = 2 := rfl
    rw [ha]; change readBytesFromMap _ _ (unpack16 u16).length = unpack16 u16
    refine readBytesFromMap_sub_writeBytesToMap val slotBase slotBs' (unpack16 u16) (by rw [hu16L, hSlotL]; omega) hSlot64 fun j hj => ?_
    rw [hu16L] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [Nat.add_zero, hPre _ (by omega), hbs3_out _ (by omega)]; exact hbs2_2
    · rw [show 16 * off + 2 + 1 = 16 * off + 3 by omega, hPre _ (by omega), hbs3_out _ (by omega)]; exact hbs2_3
  · rw [← hSbMb4']; change readBytesFromMap _ _ (unpack64 m).length = unpack64 m
    refine readBytesFromMap_sub_writeBytesToMap val slotBase slotBs' (unpack64 m) (by rw [hu64L, hSlotL]; omega) hSlot64 fun j hj => ?_
    rw [hu64L] at hj
    rw [show slotBs'.getD (16 * off + 4 + j) 0#8 = (unpack64 m ++ [actB]).getD j 0#8 from replaceSlice_getD_in hFit9 (by rw [hSub9L]; omega),
        List.getD, List.getD, List.getElem?_append_left (by rw [hu64L]; exact hj)]
  · have ha : mb + 8#64 = slotBase + BitVec.ofNat 64 (16 * off + 4 + 8) := by rw [← hSbMb4', BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [ha, writeBytesToMap_getD val slotBase slotBs' (by rw [hSlotL]; omega) hSlot64,
        show slotBs'.getD (16 * off + 4 + 8) 0#8 = (unpack64 m ++ [actB]).getD 8 0#8 from replaceSlice_getD_in hFit9 (by rw [hSub9L]; omega)]; rfl
  · rw [show lastIdx + 1 = cnt' by omega]; exact hZeroAt cnt' (Nat.le_refl _)
  · exact fun idx hidx => hZeroAt idx (by omega)

set_option maxHeartbeats 800000 in
private theorem wp_allocGroup_nested_fine [MallocngMultiPlacement] {ro : Bool}
    (sc req inflight cnt' : Nat) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc) (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc → AllocSlotFineAtDepthStmt pSc ro)
    (hv : ValidNestedCnt sc cnt') (γ : GhostName) (tp brkStart m : BitVec 64)
    (liveCost peakCost peakCount : Nat) (bL bP : FineBudget) (maxMeta : Nat)
    (st0 st1 : MallocngSt) (s0 sn : State)
    (hw564 : Blk08HasWords564 mallocngFaultSvc) (hw768 : Blk08HasWords768 mallocngFaultSvc) (hr768 : Blk08Range768)
    (hwf1 : MallocngWFInflight (inflight + 1) maddrs.base brkStart sn.brk liveCost peakCost st1)
    (hscU1 : sc < st1.ctx.usageByClass.length) (hcnt' : cnt' = cntSel sc (st1.ctx.usageByClass[sc]'hscU1).toNat)
    (hCount1 : totalLiveCount st1 ≤ peakCount) (hClaim1 : totalClaimedSlots st1 = 0)
    (hFine1 : FineSplitInv bL bP st1) (hRoom1 : AllocSlotOccRoom bP st1 sc)
    (hCB10 : ∀ k, (stClassBound st1 k).le (stClassBound st0 k))
    (hMaStep1 : st1.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc) + 1)
    (_hActL1 : st1.ctx.active.length = 48)
    (hAct0 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64)
    (hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length, st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0)
    (hRes1 : st1.reservedMetas = m :: st0.reservedMetas)
    (hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧ totalLiveCount st1 = totalLiveCount st0 ∧
      st1.metaAreas.length ≤ st0.metaAreas.length + 1 ∧
      st1.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101))
    (hOrph1 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sn.mem)
    (hDelta1 : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sn.mem)
    (hGrpCl1 : ∀ U : Nat, peakCount ≤ U → Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st1.groups)
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sn.mem) (hpc : sn.pc = mbase 8 + allocSlotOff_nested) (hrun : sn.status = .Running)
    (hsp : sn.sp = s0.sp - 96#64) (hsAl : sn.spAligned = true) (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hProc : MallocngProcPreserved s0 sn) (hvr0 : calleeSavedVRegs sn = calleeSavedVRegs s0)
    (hx0 : sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc)) (hx19 : sn.readReg64 .x19 = m)
    (hx20 : sn.readReg64 .x20 = BitVec.ofNat 64 cnt') (hx21 : sn.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx22 : sn.readReg64 .x22 = Obj.pageOf maddrs.ctx) (hx23 : sn.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx24 : sn.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx26 : sn.readReg64 .x26 = Obj.pageOf maddrs.sizeClasses)
    (hx28 : sn.readReg64 .x28 = BitVec.ofNat 64 cnt') :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) sn
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25)
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ (m ↦ₛ List.replicate 40 0#8) ∗
       MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp)
      (fun sf P_f => AllocSlotFinePost sc req inflight γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st0 s0 sf P_f ro)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
                   ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0 sf⌝) := by
  let u := cnt' * sizeClass sc; let pSc := sizeToClassUnits u; let needed := cnt' * slotStride sc + 12
  have hNps : sc ≤ 19 ∧ (needed + 3) / 16 = u ∧ sc < pSc ∧ pSc ≤ 24 ∧
      needed ≤ nominalSlotCap pSc ∧ allocSlotDepthBound pSc < allocSlotDepthBound sc := nestedParentSc_spec hsc hv
  obtain ⟨_, hNeedDiv, hscLtP, hpSc24, hNeedNom, hDepthLt⟩ := hNps
  have hpSc48 : pSc < 48 := by omega
  have hNeedLo : allocSlotReqLo pSc ≤ needed :=
    (allocSlotReqLo_le_of_allowedPhysClass (by unfold MmapThresholdReq; have := hv.2.2.1; omega) hpSc48
      (by unfold nomSc allowedPhysClass; rw [hNeedDiv]; exact decide_eq_true ⟨hpSc48, Or.inl rfl⟩)).1
  have hPrepPair : AllocSlotOccRoom bP st1 pSc ∧ NestedFinePrep bP st1 sc cnt' :=
    fineGroups_nested_parent_prep hFine1 hwf1 hClaim1 hsc hscU1 hAct0 hRoom1 hcnt' hv.2.2.1
  obtain ⟨hRoomP, hPrep⟩ := hPrepPair
  have hcnt2 : 2 ≤ cnt' := hv.1; have hcnt32 : cnt' ≤ 32 := hv.2.1; have ⟨hStrScLo, _⟩ := slotStride_bounds_48 hsc
  have hStrSc2032 : slotStride sc ≤ 2032 := by have := Nat.mul_le_mul_right (slotStride sc) hcnt2; have := hv.2.2.1; omega
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  let RoRest := (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗ (maddrs.debruijnAlloc ↦ᵣ debruijn32Table)
  have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ RoRest) := by
    unfold MallocngRoTablesA MallocngRoTablesAt; dsimp only [RoRest]
  let PrepF := RoRest ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ (m ↦ₛ List.replicate 40 0#8) ∗
    MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ PrepF)
    (Entails.of_eq (by rw [hRoSplit]; dsimp only [PrepF, Saved]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8) hcl (SepWP.mono (wp_nested_call_prep sn sc cnt' PrepF hw768 hr768 hsc hv hpc hrun hx0 hx26) ?_)
  rintro sc0 Pc0 hpcc0 hrc0 ⟨_, hspc0, halc0, hpspc0, hw0_c0, hx1_c0, hw25_c0, hlr_c0, hregs_c0, hPc0⟩ hpermc0 hclc0
  refine SepWP.weaken_pre hPc0 ?_
  let subFr := (allocSlotDepthBound pSc + 1) * 96 + 224; let remFr := allocSlotDepthBound sc * 96 + 224 - subFr
  have hsp_c0 : sc0.sp = s0.sp - 96#64 := hspc0.trans hsp; have hal_c0 : sc0.spAligned = true := halc0.trans hsAl
  have hProc_c0 : MallocngProcPreserved s0 sc0 := MallocngProcPreserved.trans hProc hpspc0.1; have htp_c0 : sc0.tpidrEl0 = tp := hProc_c0.2.2.1.trans htp0
  have hbrkS_c0 : sc0.brkStart = brkStart := by obtain ⟨_, _, _, _, _, _, _⟩ := hProc_c0; simp_all
  have hw0_nat : (sc0.readReg32 .x0).toNat = pSc := by rw [hw0_c0, BitVec.toNat_ofNat]; dsimp only [pSc, u] at hpSc24 ⊢; exact Nat.mod_eq_of_lt (by omega)
  have hx1_nat : (sc0.readReg64 .x1).toNat = needed := by rw [hx1_c0, BitVec.toNat_ofNat]; dsimp only [needed]; exact Nat.mod_eq_of_lt (by have := hv.2.2.1; omega)
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) =
      (stackFrame sc0 subFr ∗ stackFrameAt (s0.sp - 96#64 - BitVec.ofNat 64 subFr) remFr) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) subFr _ (by dsimp only [subFr]; omega) (by omega),
        solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) subFr (by dsimp only [subFr]; omega)]
    unfold stackFrame; rw [hsp_c0]
  have h19c := (hregs_c0 .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19; have h20c := (hregs_c0 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20; have h21c := (hregs_c0 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21; have h22c := (hregs_c0 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22
  have h23c := (hregs_c0 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23; have h24c := (hregs_c0 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24; have h26c := (hregs_c0 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26; have h28c := (hregs_c0 .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx28
  have hPreFold : ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ PrepF) =
      (stackFrame sc0 subFr ∗ MallocngRoTablesA maddrs ∗ MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sc0.brk liveCost peakCost st1 ∗
       MallocngRuntime maddrs tp ∗ Saved ∗ stackFrameAt (s0.sp - 96#64 - BitVec.ofNat 64 subFr) remFr ∗ (m ↦ₛ List.replicate 40 0#8)) := by
    dsimp only [PrepF]; rw [hStkSp, ← hpspc0.2.1, hRoSplit]; ac_rfl
  refine call_withCL_frame_auto (x := ())
    (hRec pSc hpSc48 hDepthLt needed (inflight + 1) hpSc48 hNeedLo hNeedNom (by omega)
      γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st1 hCount1 hClaim1 hFine1 hRoomP (by omega))
    hclc0 hpcc0 hrc0 hal_c0 hlr_c0 (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    ?_ (by intro R h; dsimp only; rw [hPreFold] at h; rw [pure_sepConj_of_true ⟨htp_c0, hbrkS_c0, hw0_nat, hx1_nat⟩]; revert R h; sep_frame)
    (fun R' sf _ ho => by
      have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢
      exact ⟨oom_from_recAllocSlot_fine (by omega) hProc_c0 (mappedDelta_perm_right hDelta1 hpermc0) ho'.1, ho'.2⟩)
  intro s_ret hpc_r hrun_r hsp_r hcs_r hcl_r; dsimp only; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st2; apply SepWP.exists_elim; intro pIdx; apply SepWP.pure_elim
  rintro ⟨hProc_r, hRes2_1, hLive2_1, hCost2_1, hCnt2_1, _hMa2_step, _hMa2_max, hFine2, hCB2_1, hActLow2, hw0_r, _,
    ⟨pg, hpg, hpScA, hpIdx, hpSc, _, hPgMetaEq, hClaimed, _⟩, hOrph2, hDelta2, hGrp2⟩
  have hsp_r0 : s_ret.sp = s0.sp - 96#64 := hsp_r.trans hsp_c0
  have hal_r : s_ret.spAligned = true := by rw [State.spAligned, hsp_r]; simpa [State.spAligned] using hal_c0
  have hw25_r : s_ret.readReg32 .x25 = BitVec.ofNat 32 pSc := by simp only [State.readReg32, hcs_r.2.2.2.2.2.2.1]; exact hw25_c0
  have h19r := hcs_r.1.trans h19c; have h20r := hcs_r.2.1.trans h20c; have h21r := hcs_r.2.2.1.trans h21c; have h22r := hcs_r.2.2.2.1.trans h22c
  have h23r := hcs_r.2.2.2.2.1.trans h23c; have h24r := hcs_r.2.2.2.2.2.1.trans h24c; have h26r := hcs_r.2.2.2.2.2.2.2.1.trans h26c; have h28r := hcs_r.2.2.2.2.2.2.2.2.2.1.trans h28c
  unfold MallocngCoreStInflightModeA MallocngRuntime
  simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]; apply SepWP.exists_elim; intro errnoVal
  simp only [show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf2
  obtain ⟨hActL2, hUseL2, hUnmL2, hBncL2, _, _⟩ := hwf2.ctx_lens
  obtain ⟨CtxRest, hCtxSp, hCtxFd⟩ := ctx_split_fields maddrs.ctx st2.ctx hActL2 hUseL2 hUnmL2 hBncL2
  obtain ⟨hpIdx31, hpLast31, hMap52, hpgNested, hMapHi, hpStrLo, hpStrDiv, hStrLe, hStrHi, hStrDiv,
    hEndStor, hpStNat, hpEnNat, hpSbNat, hpStorNat, hMemHi, hSbEnd, hbsLen, hbs0, hbsEnd, PgRest, hBmSplit, hPgResid⟩ :=
    claimed_parent_extract hwf2 hpg hpIdx hClaimed hpSc hpSc24
  let slotBase := pg.slotStart pIdx - 4#64; let bs := readBytesFromMap st2.byteVal slotBase (pg.stride + 1)
  obtain ⟨ActPRest, hActPSp, hActPUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st2.ctx.active pSc hpScA
  let RestCore := MallocngLiveAuth γ st2.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st2.auxvPtr ∗ MallocngAuxvStateRo ro γ st2.auxvPtr st2.auxvSnap ∗
    ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗ MappedSet st2.masterDom (OwnedMappedByte st2) ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  let MHead := (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32)
  let CtxTail := ((maddrs.ctx + 464#64) ↦₆₄* st2.ctx.usageByClass) ∗ ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗
    ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗ ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest
  let InvTail := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MHead ∗ CtxTail ∗ RestCore
  let PostLoadTail := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64) ↦₆₄* st2.ctx.active) ∗ MallocngRoTablesA maddrs ∗ InvTail
  let Resid := ByteMap st2.masterDom (fun a => OwnedRwByte st2 a ∧ ¬ InRegion slotBase (pg.stride + 1) a) st2.byteVal
  let LoadF := ActPRest ∗ ((maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ RoRest) ∗ (slotBase ↦ₛ bs) ∗ PgRest ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ InvTail
  have hActPFold : (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * pSc)) ↦₆₄ pg.metaPtr) ∗ ActPRest) = ((maddrs.ctx + 80#64) ↦₆₄* st2.ctx.active) := by
    rw [hActPUp pg.metaPtr, hPgMetaEq, List.set_getElem_self]
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * pSc)) ↦₆₄ pg.metaPtr) ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (pg.metaPtr ↦ₛ pg.metaBytes) ∗ LoadF)
    (Entails.of_eq (by
      dsimp only [subFr, remFr, pSc, u] at hStkSp
      dsimp only [LoadF, InvTail, CtxTail, MHead, RestCore, Saved, bs, slotBase, subFr, remFr, pSc, u]
      rw [hStkSp, hRoSplit, hCtxSp, hActPSp, ← hPgMetaEq, hBmSplit, split_rep40_zero m]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_pub_add) hcl_r ?_
  refine SepWP.seq (wp_nested_enframe_load s_ret st2.ctx.mmapCounter pSc pIdx pg LoadF
      hw768 hr768 hpSc24 hpIdx31 hpSc hpLast31 hMap52 hpgNested hMapHi hpc_r hrun_r hw0_r hw25_r h22r h26r) ?_
  rintro sA PA hpcA hrunA ⟨_, hspA, halA, hpspA, hx1A, _, hx3A, hw5A, hx6A, hx7A, hrA, hPA⟩; rw [hPA]
  have h19A := (hrA .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19r; have h20A := (hrA .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20r; have h21A := (hrA .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21r; have h22A := (hrA .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22r
  have h23A := (hrA .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23r; have h24A := (hrA .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24r; have h28A := (hrA .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28r
  let OffF := PgRest ∗ ((m + 32#64) ↦₆₄ 0#64) ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := (pg.metaPtr ↦ₛ pg.metaBytes) ∗ (slotBase ↦ₛ bs) ∗ OffF)
    (Entails.of_eq (by dsimp only [LoadF, OffF, PostLoadTail]; rw [← hActPFold, hRoSplit]; ac_rfl)) ?_
  refine SepWP.seq (wp_nested_enframe_off sA pSc pIdx pg bs OffF hw768 hr768 hpIdx31 hpStrLo hStrLe hStrHi hbsLen hbs0 hpcA hrunA hx1A hx3A hw5A hx6A hx7A) ?_
  rintro sB PB hpcB hrunB ⟨off, hoffLe, _, hspB, halB, hpspB, hx0B, hx1B, hx2B, hx4B, hw5B, hx6B, hx7B, hx8B, hrB, hPB⟩; rw [hPB]
  obtain ⟨hNoWrap, hFit, hSbMb16, hSbMb4, hMbLo, hMbAl, hMbEnd, hOffUnits, hCapLe⟩ :=
    enframe_geom_bounds pg pSc pIdx off sc cnt' hpStNat hpEnNat hpSbNat hpStorNat hMemHi hpStrLo hStrLe hStrHi hEndStor hoffLe hNeedNom
  let mb := pg.slotStart pIdx + BitVec.ofNat 64 (16 * off)
  have h19B := (hrB .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19A; have h20B := (hrB .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20A; have h21B := (hrB .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21A; have h22B := (hrB .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22A
  have h23B := (hrB .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23A; have h24B := (hrB .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24A; have h28B := (hrB .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28A
  refine SepWP.seq (wp_enframe_step_off sB pSc pIdx off pg bs OffF hw768 hr768 hpStrLo hStrLe hStrHi hoffLe hbsLen hbs0 hbsEnd hpcB hrunB hx0B hx1B hx2B hx4B hw5B hx6B hx7B hx8B) ?_
  rintro sC PC hpcC hrunC ⟨_, hspC, halC, hpspC, hx0C, hx1C, hx4C, hw5C, hx6C, hx8C, hrC, bs1, hbs1L, hbs1_0, hbs1_off, hbs1_end, hPC⟩; rw [hPC]
  have h19C := (hrC .x19 (by decide) (by decide) (by decide)).trans h19B; have h20C := (hrC .x20 (by decide) (by decide) (by decide)).trans h20B; have h21C := (hrC .x21 (by decide) (by decide) (by decide)).trans h21B; have h22C := (hrC .x22 (by decide) (by decide) (by decide)).trans h22B
  have h23C := (hrC .x23 (by decide) (by decide) (by decide)).trans h23B; have h24C := (hrC .x24 (by decide) (by decide) (by decide)).trans h24B; have h28C := (hrC .x28 (by decide) (by decide) (by decide)).trans h28B
  let RsvF := ((m + 32#64) ↦₆₄ 0#64) ∗ Resid ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := (slotBase ↦ₛ bs1) ∗ RsvF) (Entails.of_eq (by dsimp only [OffF, RsvF, Resid, slotBase]; rw [← hPgResid]; ac_rfl)) ?_
  refine SepWP.seq (wp_enframe_step_rsv sC pSc pIdx off pg bs1 RsvF hw768 hr768 hpIdx31 hpStrLo hpStrDiv hStrHi hStrDiv hoffLe hStrLe hNoWrap hbs1L hbs1_0 hbs1_off hbs1_end hpcC hrunC hx0C hx1C hx4C hw5C hx6C hx8C) ?_
  rintro sD PD hpcD hrunD ⟨_, hspD, halD, hpspD, hx0D, hw1D, hw6D, hrD, bs2, hbs2L, hbs2_0, hbs2_off, _, hbs2_2, hbs2_3, hbs2_end, hPD⟩; rw [hPD]
  have h19D := (hrD .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h19C; have h20D := (hrD .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20C; have h21D := (hrD .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h21C; have h22D := (hrD .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22C
  have h23D := (hrD .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23C; have h24D := (hrD .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24C; have h28D := (hrD .x28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h28C
  let FinF := Resid ∗ PostLoadTail
  refine SepWP.weaken_pre (P' := ((m + 32#64) ↦₆₄ 0#64) ∗ (slotBase ↦ₛ bs2) ∗ FinF) (Entails.of_eq (by dsimp only [RsvF, FinF]; ac_rfl)) ?_
  refine SepWP.seq (wp_enframe_step_fin sD pIdx off cnt' m pg bs2 FinF hw768 hr768 hpIdx31 hcnt32 (by rw [hbs2L]; omega) hpcD hrunD hx0D hw1D hw6D h19D h20D) ?_
  rintro sE PE hpcE hrunE ⟨_, hspE, halE, hpspE, hx0E, hx1E, hw2E, hw3E, hrE, hbs3L, hbs3_1, hbs3_out, hPE⟩; rw [hPE]
  let bTag := BitVec.ofNat 8 ((6 <<< 5) ||| pIdx); let bs3 := replaceSlice bs2 (16 * off + 1) [bTag]
  have h19E := (hrE .x19 (by decide) (by decide) (by decide) (by decide)).trans h19D; have h20E := (hrE .x20 (by decide) (by decide) (by decide) (by decide)).trans h20D; have h21E := (hrE .x21 (by decide) (by decide) (by decide) (by decide)).trans h21D; have h22E := (hrE .x22 (by decide) (by decide) (by decide) (by decide)).trans h22D
  have h23E := (hrE .x23 (by decide) (by decide) (by decide) (by decide)).trans h23D; have h24E := (hrE .x24 (by decide) (by decide) (by decide) (by decide)).trans h24D; have h28E := (hrE .x28 (by decide) (by decide) (by decide) (by decide)).trans h28D
  refine SepWP.weaken_pre (P' := (slotBase ↦ₛ bs3) ∗ RsvF) (Entails.of_eq (by dsimp only [FinF, RsvF, slotBase, bs3, bTag]; ac_rfl)) ?_
  refine SepWP.mono (wp_nested_zero_loop (cnt' + 1) 0 cnt' (slotStride sc) (16 * off + 16) sE slotBase mb bs3 RsvF
      hw768 (by omega) (by omega) hcnt2 hcnt32 hStrScLo hStrSc2032 hSbMb16 (by rw [hbs3L, hbs2L]; omega) (by rw [hbs3L, hbs2L]; omega)
      hpcE hrunE (by simpa using hx1E) hw2E hw3E h20E h24E) ?_
  rintro spub Ppub hpcpub hrpub ⟨_, hspF, halF, hpspF, hx1_p, hx2_p, hrF, bs', hbs'L, hbs'Z, hbs'Out, hPpub⟩ hperm_p _; refine SepWP.weaken_pre hPpub ?_
  have hsp_pub : spub.sp = s0.sp - 96#64 := hspF.trans (hspE.trans (hspD.trans (hspC.trans (hspB.trans (hspA.trans hsp_r0)))))
  have hal_pub : spub.spAligned = true := halF.trans (halE.trans (halD.trans (halC.trans (halB.trans (halA.trans hal_r)))))
  have hpsp_pub : PureStatePres s_ret spub := hpspA.trans (hpspB.trans (hpspC.trans (hpspD.trans (hpspE.trans hpspF))))
  have hx0_p : spub.readReg64 .x0 = mb := (hrF .x0 (by decide) (by decide)).trans hx0E
  have h19_p := (hrF .x19 (by decide) (by decide)).trans h19E; have h21_p := (hrF .x21 (by decide) (by decide)).trans h21E; have h22_p := (hrF .x22 (by decide) (by decide)).trans h22E
  have h23_p := (hrF .x23 (by decide) (by decide)).trans h23E; have h28_p := (hrF .x28 (by decide) (by decide)).trans h28E
  let lastIdx := cnt' - 1; have hscA2 : sc < st2.ctx.active.length := (by omega); have hscU2 : sc < st2.ctx.usageByClass.length := (by omega); have hscL2 : sc < st2.activeLists.length := by omega
  have hAct2_sc0 : st2.ctx.active[sc]'hscA2 = 0#64 := (hActLow2 sc hscLtP hscA2 (by omega)).trans (hAct0 (by omega)); have hbs'LenEq : bs'.length = pg.stride + 1 := hbs'L.trans (hbs3L.trans hbs2L)
  obtain ⟨ActRest, hActSp, hActUp⟩ := words64_focus_set (maddrs.ctx + 80#64) st2.ctx.active sc hscA2; obtain ⟨UseRest, hUseSp, hUseUp⟩ := words64_focus_set (maddrs.ctx + 464#64) st2.ctx.usageByClass sc hscU2
  have hHdrFit : (16 * off + 4) + 9 ≤ bs'.length := (by rw [hbs'LenEq]; omega); obtain ⟨mb0, b8Old, hSlotHdrSp⟩ := split_slot_hdr9 slotBase bs' hHdrFit; rw [hSbMb4] at hSlotHdrSp
  let PubF := ((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ ActRest ∗ UseRest ∗ ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗
    ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest ∗ (slotBase ↦ₛ bs'.take (16 * off + 4)) ∗ ((slotBase + BitVec.ofNat 64 (16 * off + 4 + 9)) ↦ₛ bs'.drop (16 * off + 4 + 9)) ∗
    Resid ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗ RestCore
  refine SepWP.weaken_pre (P' := ((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ 0#64) ∗ ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st2.ctx.usageByClass[sc]'hscU2)) ∗
      (m ↦₆₄ 0#64) ∗ ((m + 8#64) ↦₆₄ 0#64) ∗ ((m + 16#64) ↦₆₄ 0#64) ∗ ((m + 24#64) ↦₃₂ 0#32) ∗ ((m + 28#64) ↦₃₂ 0#32) ∗ ((m + 32#64) ↦₆₄ (BitVec.ofNat 64 0 <<< 12)) ∗ (mb ↦₆₄ mb0) ∗ ((mb + 8#64) ↦₈ b8Old) ∗
      ((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗ ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x20) ∗
      ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x23) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x24) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x25) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x26) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x27) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x28) ∗ PubF)
    (Entails.of_eq (by have hz0 : (BitVec.ofNat 64 0 <<< 12) = 0#64 := (by decide); rw [hz0]; dsimp only [RsvF, PostLoadTail, InvTail, CtxTail, MHead, Saved, AllocSlotSaved12, PubF, mb]; rw [hActSp, hAct2_sc0, hUseSp, hSlotHdrSp]; ac_rfl)) ?_
  refine SepWP.mono (wp_publish_new_group s0.sp (s0.readReg64 .x30) m mb (st2.ctx.usageByClass[sc]'hscU2) 0#64 mb0 0#32 0#32 b8Old
      (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29)
      sc lastIdx lastIdx 0 (some pg.metaPtr) (slotStride pg.sc - 4) false PubF _ hw564 hw768 hr768 hsc (by omega) (Nat.le_refl _) hpcpub hrpub hsp_pub hal_pub h22_p h23_p h21_p h19_p hx0_p hx1_p hx2_p
      (by dsimp only [lastIdx]; rw [Nat.sub_add_cancel (by omega)]; exact h28_p)) ?_
  rintro sf P_f _ _ ⟨_, hsp_f, _, hpsp_f, hperm_f, hx0_f, h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f, h29f, _, actB, hActB, hPf⟩
  have hbrk_f : sf.brk = s_ret.brk := hpsp_f.2.1.trans hpsp_pub.2.1; have hwf2' : MallocngWFInflight ((inflight + 1) + 1) maddrs.base brkStart sf.brk liveCost peakCost st2 := hbrk_f.symm ▸ hwf2
  let slotBs' := replaceSlice bs' (16 * off + 4) (unpack64 m ++ [actB])
  obtain ⟨hSlotL, hVStart, hVEnd, hVMb4, hVMb3, hVMb2, hVMb0, hVMb8, hVCgEnd, hVCgHdr⟩ :=
    enframe_slot_bytes_wf_fine st2.byteVal pg pIdx off sc cnt' m actB bs2 bs3 bs' hcnt2 hFit hStrHi hSbEnd hSbMb4 hbs2L hbs2_0 hbs2_off hbs2_2 hbs2_3 hbs2_end hbs3L hbs3_1 hbs3_out hbs'L hbs'Z hbs'Out
  obtain ⟨hwf', hCost', hCount', hNotMmap, hBmRw, hBmPn, hMpEq⟩ := wf_alloc_nested hwf2' hsc hscA2 hscL2 hscU2 hAct2_sc0 (hRes2_1.trans hRes1) hpg hpIdx hClaimed
    (hpSc ▸ hpSc24) (hpSc ▸ hscLtP) (by omega : 1 ≤ lastIdx) (by omega : lastIdx ≤ 31) (by rw [hActB]; exact Nat.le_refl _) (by rw [hActB]; omega) hMbLo hMbAl (hpSc ▸ hMbEnd) hOffUnits
    (by dsimp only [lastIdx]; rw [Nat.sub_add_cancel (by omega), hpSc]; exact hCapLe) hSlotL hVStart hVEnd hVMb4 hVMb3 hVMb2 hVMb0 hVMb8 hVCgEnd hVCgHdr
  let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 ((actB &&& 0x1f#8).toNat)) - 1#32
  let cg : GroupDesc := { metaPtr := m, prev := m, next := m, mem := mb, availMask := initAvail - 1#32, freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail, lastIdx := lastIdx, sc := sc, maplen := 0, activeByte := actB, parentMeta := some pg.metaPtr, nestedCap := slotStride pg.sc - 4, slots := newGroupSlots lastIdx ((actB &&& 0x1f#8).toNat), freshZero := false }
  let pg' : GroupDesc := { pg with slots := pg.slots.set pIdx (.liveNested m) }
  let f : GroupDesc → GroupDesc := fun g => if g.metaPtr == pg.metaPtr then pg' else g
  let ctx' : CtxFields := { st2.ctx with active := st2.ctx.active.set sc m, usageByClass := st2.ctx.usageByClass.set sc (st2.ctx.usageByClass[sc]'hscU2 + BitVec.ofNat 64 cg.cnt) }
  let st' : MallocngSt := { st2 with ctx := ctx', reservedMetas := st0.reservedMetas, groups := cg :: st2.groups.map f, activeLists := st2.activeLists.set sc [m], masterDom := extendDom st2.masterDom m 40, byteVal := writeBytesToMap (writeBytesToMap st2.byteVal slotBase slotBs') m cg.metaBytes }
  obtain ⟨hFine', hCB'_1⟩ := fineGroups_add_nested (st1 := st1) (st2 := st2) (st' := st') (pg := pg) (pg' := pg') (cg := cg)
    hFine2 hwf2.groups_nodup.1 hsc hPrep (fun k hk => hCB2_1 k (by omega)) hpg hpIdx hpSc (hpSc ▸ hscLtP)
    rfl rfl rfl rfl rfl rfl rfl (show lastIdx + 1 = cnt' by omega) rfl rfl (fun s hs => newGroupSlots_no_liveUser s hs) hFine2.meta_le rfl
  have hCB'_0 : ∀ k < sc, (stClassBound st' k).le (stClassBound st0 k) := fun k hk => ClassFineBound.le_trans (hCB'_1 k hk) (hCB10 k)
  have hProc_f : MallocngProcPreserved s0 sf := MallocngProcPreserved.trans (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_c0 hProc_r) hpsp_pub.1) hpsp_f.1
  have hvr_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := hpsp_f.2.2.trans (hpsp_pub.2.2.trans (hcs_r.2.2.2.2.2.2.2.2.2.2.2.trans (hpspc0.2.2.trans hvr0)))
  refine ⟨?_, hsp_f, calleeSaved_of_epilogue h19f h20f h21f h22f h23f h24f h25f h26f h27f h28f h29f hvr_f⟩
  refine Entails.trans ?_ (Entails.sepExists_intro st'); refine Entails.trans ?_ (Entails.sepExists_intro 0)
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st2 := by
    dsimp +zeta only [dynamicRootRegions, st', cg, f, pg']; rw [List.filter_cons_of_neg (by simp), groups_set_claimed_roots st2.groups hwf2.groups_nodup.1 hpg pIdx m]
  have hOrph1' : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sc0.mem := fun a ha hsrc => hOrph1 a (hpermc0 ▸ ha) hsrc
  have hOrph2' : MallocngNoOrphanMappings (dynamicRootRegions st1) (dynamicRootRegions st') sc0.mem sf.mem := fun a ha hsrc => hDynEq ▸ hOrph2 a ((hperm_f.trans hperm_p) ▸ ha) hsrc
  have hPure : MallocngProcPreserved s0 sf ∧ st'.reservedMetas = st0.reservedMetas ∧ st'.liveMap = st0.liveMap ∧
      totalLiveEffCost st' = totalLiveEffCost st0 ∧ totalLiveCount st' = totalLiveCount st0 ∧
      st'.metaAreas.length ≤ st0.metaAreas.length + allocSlotDepthBound sc + 1 ∧
      st'.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
      FineSplitInv bL bP st' ∧ (∀ k < sc, (stClassBound st' k).le (stClassBound st0 k)) ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st'.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length, st'.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
      sf.readReg32 .x0 = BitVec.ofNat 32 0 ∧ 0 ≤ 31 ∧
      (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : 0 < g.slots.length,
        g.sc = sc ∧ req + 4 ≤ g.stride ∧ g.metaPtr = st'.ctx.active[sc]'hAct ∧ g.slots[0]'hIdx = .claimed ∧
        (g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart 0) g.stride a → st'.byteVal a = 0#8)) ∧
      MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
      MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s0.mem sf.mem ∧
      (∀ U : Nat, peakCount ≤ U → Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st'.groups) := by
    refine ⟨hProc_f, rfl, hLive2_1.trans hRel1.1, hCost'.trans (hCost2_1.trans hRel1.2.1), hCount'.trans (hCnt2_1.trans hRel1.2.2.1),
      show st2.metaAreas.length ≤ _ by have := hRel1.2.2.2.1; omega,
      show st2.metaAreas.length ≤ _ by have := hRel1.2.2.2.2; omega,
      hFine', hCB'_0, (fun k hk hk1 hk0 => ?_), by simp [State.readReg32, hx0_f], by omega,
      ⟨cg, List.Mem.head _, show sc < (st2.ctx.active.set sc m).length by simp [hscA2], show 0 < (newGroupSlots lastIdx _).length by simp [newGroupSlots], rfl,
        by simp [GroupDesc.stride, cg]; rw [show nominalSlotCap sc = slotStride sc - 4 from rfl] at hReq; omega,
        show m = (st2.ctx.active.set sc m)[sc]'_ by simp, rfl, fun hm => by rw [hNotMmap] at hm; cases hm⟩,
      mallocngNoOrphanMappings_trans hOrph1' hOrph2', nested_mappedDelta_combine_fine (by omega) hDelta1 hpermc0 hDelta2 (hperm_f.trans hperm_p),
      fun U hUle hU => by
        have h2 := hGrp2 U hUle (hGrpCl1 U hUle hU)
        exact (h2.map_ite pg.metaPtr (g1 := pg') (h2 pg hpg)).cons fun h0 _ => absurd h0 (Nat.lt_irrefl 0)⟩
    dsimp +zeta only [st', ctx'] at hk1 ⊢; rw [List.getElem_set_ne (by omega : sc ≠ k)]
    exact (hActLow2 k (by omega) (by simpa using hk1) (by omega)).trans (hActLow1 k hk (by omega) hk0)
  rw [pure_sepConj_of_true hPure]
  have hcg_meta : cg = { metaPtr := m, prev := m, next := m, mem := mb, availMask := ((2#32 <<< BitVec.ofNat 32 lastIdx) - 1#32) - 1#32, freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~((2#32 <<< BitVec.ofNat 32 lastIdx) - 1#32), lastIdx := lastIdx, sc := sc, maplen := 0, activeByte := actB, parentMeta := some pg.metaPtr, nestedCap := slotStride pg.sc - 4, slots := newGroupSlots lastIdx lastIdx, freshZero := false } := by
    dsimp +zeta only [cg, initAvail]; rw [hActB]
  dsimp only at hPf; rw [← hcg_meta] at hPf; subst hPf
  have hCtxEq : (((maddrs.ctx + 12#64) ↦₃₂ st2.ctx.mmapCounter) ∗ (((maddrs.ctx + 80#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ m) ∗ ActRest) ∗
      (((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st2.ctx.usageByClass[sc]'hscU2 + BitVec.ofNat 64 (lastIdx + 1))) ∗ UseRest) ∗
      ((maddrs.ctx + 848#64) ↦ₛ st2.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st2.ctx.bounces) ∗ ((maddrs.ctx + 912#64) ↦₈ st2.ctx.seq) ∗ CtxRest) = (maddrs.ctx ↦ₛ ctx'.toBytes) := by
    rw [hActUp, hUseUp]; exact hCtxFd _ _ _ _ _ _ (by simp [hActL2]) (by simp [hUseL2]) hUnmL2 hBncL2
  have hHdrEq : ((mb ↦₆₄ m) ∗ ((mb + 8#64) ↦₈ actB) ∗ (slotBase ↦ₛ bs'.take (16 * off + 4)) ∗ ((slotBase + BitVec.ofNat 64 (16 * off + 4 + 9)) ↦ₛ bs'.drop (16 * off + 4 + 9))) = (slotBase ↦ₛ slotBs') := by
    have h := fold_slot_hdr9 slotBase bs' hHdrFit m actB; rwa [hSbMb4] at h
  unfold MallocngCoreStInflightModeA MallocngRuntime; rw [pure_sepConj_of_true hwf']
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_intro (P := fun v => (tp - 0xa4#64) ↦₃₂ v) errnoVal)))))
  have hJoin := saved12_rejoin_stackFrame s0 sc (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  dsimp only [AllocSlotSaved12] at hJoin; refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left hJoin)
  dsimp only [PubF, RestCore, Resid, slotBase, slotBs', mb, st', ctx', cg, pg', initAvail, lastIdx] at hCtxEq hHdrEq ⊢
  rw [← hCtxEq, ← hBmRw, ← hHdrEq, ← hBmPn, ← hMpEq]; ac_rfl

/-! ## 5. Top-Level Placed `alloc_group` Fine Theorem (`wp_placed_allocGroup_fine`) -/

set_option maxHeartbeats 800000 in
/-- Fine-cost verification of placed `alloc_group` (`blk08`, `+ allocSlotOff_ag`), composing
`__malloc_alloc_meta` (`blk07`), count selection (`Stage2`), and root/nested group initialization. -/
theorem wp_placed_allocGroup_fine {ro : Bool} (hMeta : AllocMetaFineStmt ro) : AllocGroupFineAtOffStmt ro := by
  intro _ sc req inflight hsc hReqLo hReqHi hInflight hRec γ tp brkStart liveCost peakCost peakCount
    bL bP maxMeta st0 st hCount _hClaim0 hFine0 hRoom0 hMaStep0 hNd0 hAct0 hStRel
    s0 s hcl hpc hrun hsp hsAl htp hbrkS hpsp hperm hx22 hx23 hx21 hx25
  obtain ⟨hRes0, hLive0, hCost0, hCnt0, hMa0, hDyn0, hActLow0, hGM0, hFM0, hClaimSt⟩ := hStRel
  obtain ⟨_, _, ⟨hw564, hr564⟩, ⟨hw712, _⟩, ⟨hw768, hr768⟩⟩ := blk08_segments_noSyscalls
  have hw768_msvc : Blk08HasWords768Msvc := blk08_seg768_msvc.1
  have hd_sz : allocSlotDepthBound sc ≤ 3 := by unfold allocSlotDepthBound; repeat (first | split | omega)
  apply SepWP.with_sat; rintro ⟨R_wf, h_wf_sat⟩
  have hwf : MallocngWFInflight inflight maddrs.base brkStart s.brk liveCost peakCost st := by
    have ⟨R', h'⟩ : ∃ R', s.mem ⊨ MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ (R' ∗ R_wf) :=
      ⟨?_, by revert R_wf h_wf_sat; sep_frame⟩
    unfold MallocngCoreStInflightModeA at h'; rw [sepConj_assoc, satisfies_pure_sepConj] at h'; exact h'.1
  have hFineSt : FineSplitInv bL bP st := fineSplitInv_of_groupsFreeMono_nd hFine0 hNd0 hwf (hMa0 ▸ hFine0.meta_le) hFM0
  have hRoomSt : AllocSlotOccRoom bP st sc := AllocSlotOccRoom.of_groupsFreeMono hRoom0 hNd0 hwf.groups_nodup.1 hFM0
  have hCB_st0 : ∀ k, (stClassBound st k).le (stClassBound st0 k) := stClassBound_le_of_groupsFreeMono hNd0 hwf.groups_nodup.1 hFM0
  have hMa5 : st.metaAreas.length ≤ maxMeta + 5 := by rw [hMa0]; omega
  let Saved := AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28)
  let RoTail := (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗
    (maddrs.debruijnAlloc ↦ᵣ debruijn32Table) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table)
  have hRoEq : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ RoTail) := by
    unfold MallocngRoTablesA MallocngRoTablesAt; dsimp only [RoTail]; ac_rfl
  let EntryF := RoTail ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
    MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ EntryF)
    (Entails.of_eq (by rw [hRoEq]; dsimp only [EntryF, Saved]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 7) hcl (SepWP.mono (wp_ag_entry s sc EntryF hw564 hr564 hsc hpc hrun hx23) ?_)
  rintro scm Pcm hpccm hrcm ⟨_, hspcm, halcm, hpspcm, hx24cm, hx26cm, hx27cm, hlrcm, hregcm, hPcm⟩ hpermcm hclcm
  refine SepWP.weaken_pre (Entails.of_eq hPcm) ?_
  have hsp_cm : scm.sp = s0.sp - 96#64 := hspcm.trans hsp; have hal_cm : scm.spAligned = true := halcm.trans hsAl
  have hpsp_cm : PureStatePres s0 scm := hpsp.trans hpspcm; have hProc_cm : MallocngProcPreserved s0 scm := hpsp_cm.1
  have htp_cm : scm.tpidrEl0 = tp := hProc_cm.2.2.1.trans htp; have hperm_cm0 : scm.mem.perm = s0.mem.perm := hpermcm.trans hperm
  have hbrkS_cm : scm.brkStart = brkStart := by obtain ⟨_, _, _, _, _, _, _⟩ := hProc_cm; simp_all
  have hx21cm := (hregcm .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21; have hx22cm := (hregcm .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22
  have hx23cm := (hregcm .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23; have hx25cm := (hregcm .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25
  have hStkSp : stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = (stackFrame scm 224 ∗ stackFrameAt (s0.sp - 96#64 - 224#64) (allocSlotDepthBound sc * 96)) := by
    rw [stackFrameAt_split_top (s0.sp - 96#64) 224 _ (by omega) (by omega), solver_stackFrameAt_eq_memRegion (s0.sp - 96#64) 224 (by omega)]
    unfold stackFrame; rw [hsp_cm, show allocSlotDepthBound sc * 96 + 224 - 224 = allocSlotDepthBound sc * 96 by omega]
  have hMeta8 := call_placed_allocMeta_fine hMeta (P := mallocngBlockProg mmpl 8 msvc)
    inflight (by omega) γ tp brkStart liveCost peakCost peakCount bL bP maxMeta st hCount hFineSt hMa5 (by intro pc; simp) rfl
  have hPreMeta : ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ EntryF) = (stackFrame scm 224 ∗ MallocngCoreStInflightModeA ro inflight γ maddrs brkStart scm.brk liveCost peakCost st ∗
      MallocngRuntime maddrs tp ∗ MallocngRoTablesA maddrs ∗ Saved ∗ stackFrameAt (s0.sp - 96#64 - 224#64) (allocSlotDepthBound sc * 96)) := by
    dsimp only [EntryF]; rw [hStkSp, ← hpspcm.2.1, hRoEq]; ac_rfl
  refine call_withCL_frame_auto (x := ()) hMeta8 hclcm hpccm hrcm hal_cm hlrcm (fun _ _ _ h => not_satisfies_false_sepConj h) (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    ?_ (by intro R h; dsimp only; rw [hPreMeta] at h; rw [pure_sepConj_of_true ⟨htp_cm, hbrkS_cm⟩]; revert R h; sep_frame)
    (fun R' sf _ ho => by have ho' := Satisfies.drop_mid ho; rw [satisfies_pure_sepConj] at ho' ⊢; exact ⟨oom_from_allocMeta_fine hProc_cm hperm_cm0 ho'.1, ho'.2⟩)
  intro sam hpc_am hrun_am hsp_am hcs_am hcl_am; dsimp only; simp only [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1; apply SepWP.exists_elim; intro m; apply SepWP.pure_elim
  rintro ⟨hProc_am, hx0_am, hmNe0, _, _, _, _, hRes1_st, hGrp1_st, _, hLive1_st, hCnt1_st, hMa1_step, hMa1_max, hFine1, hAct1_st, _, _, _, _, _, hOrph_am, hDelta_am⟩
  have hsp_am0 : sam.sp = s0.sp - 96#64 := hsp_am.trans hsp_cm; have hProc_am0 : MallocngProcPreserved s0 sam := MallocngProcPreserved.trans hProc_cm hProc_am
  have hvr_am : calleeSavedVRegs sam = calleeSavedVRegs s0 := hcs_am.2.2.2.2.2.2.2.2.2.2.2.trans hpsp_cm.2.2
  have hal_am : sam.spAligned = true := by rw [State.spAligned, hsp_am]; simpa [State.spAligned] using hal_cm
  have hx21_am := hcs_am.2.2.1.trans hx21cm; have hx22_am := hcs_am.2.2.2.1.trans hx22cm; have hx23_am := hcs_am.2.2.2.2.1.trans hx23cm
  have hx24_am := hcs_am.2.2.2.2.2.1.trans hx24cm; have hx25_am := hcs_am.2.2.2.2.2.2.1.trans hx25cm; have hx26_am := hcs_am.2.2.2.2.2.2.2.1.trans hx26cm; have hx27_am := hcs_am.2.2.2.2.2.2.2.2.1.trans hx27cm
  have hRes1 : st1.reservedMetas = m :: st0.reservedMetas := hRes1_st.trans (congrArg (m :: ·) hRes0); have hCount1 : totalLiveCount st1 ≤ peakCount := hCnt1_st ▸ hCount
  have hCost1_st : totalLiveEffCost st1 = totalLiveEffCost st := by unfold totalLiveEffCost; rw [hGrp1_st]
  have hMa1_0 : st1.metaAreas.length ≤ st0.metaAreas.length + 1 := by rw [← hMa0]; exact hMa1_step
  have hMaStep1 : st1.metaAreas.length ≤ maxMeta + (3 - allocSlotDepthBound sc) + 1 := by omega
  have hRel1 : st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧ totalLiveCount st1 = totalLiveCount st0 ∧
      st1.metaAreas.length ≤ st0.metaAreas.length + 1 ∧ st1.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) :=
    ⟨hLive1_st.trans hLive0, hCost1_st.trans hCost0, hCnt1_st.trans hCnt0, hMa1_0, by rw [← hMa0]; exact hMa1_max⟩
  have hRoom1 : AllocSlotOccRoom bP st1 sc := AllocSlotOccRoom.of_groups_eq hRoomSt hGrp1_st
  have hCB10 : ∀ k, (stClassBound st1 k).le (stClassBound st0 k) := fun k => by
    have : stClassBound st1 k = stClassBound st k := by unfold stClassBound; rw [hGrp1_st]
    rw [this]; exact hCB_st0 k
  have hAct0_1 : ∀ h : sc < st1.ctx.active.length, st1.ctx.active[sc]'h = 0#64 := fun h => by have h' : sc < st.ctx.active.length := hAct1_st ▸ h; simpa [hAct1_st] using hAct0 h'
  have hActLow1 : ∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length, st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0 :=
    fun k hk hk1 hk0 => by have hk' : k < st.ctx.active.length := hAct1_st ▸ hk1; simpa [hAct1_st] using hActLow0 k hk hk' hk0
  have hOrph_am0 : MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sam.mem := fun a ha hsrc => hOrph_am a ha (by rw [hDyn0, hperm_cm0]; exact hsrc)
  have hDelta_am0 : MallocngMappedDelta 1 (FineMetaStep maxMeta) s0.mem sam.mem := mappedDelta_perm_left hperm_cm0 hDelta_am
  unfold MallocngCoreStInflightModeA
  simp only [sepConj_assoc, show ∀ (P : SepProp) (φ : Prop) (Q : SepProp), P ∗ (⌜φ⌝ ∗ Q) = ⌜φ⌝ ∗ (P ∗ Q) from fun P _ _ => by rw [← sepConj_assoc, sepConj_comm P, sepConj_assoc]]
  apply SepWP.pure_elim; intro hwf1; obtain ⟨hActL1, hUseL1, hUnmL1, hBncL1, _, _⟩ := hwf1.ctx_lens; have hscU1 : sc < st1.ctx.usageByClass.length := by omega
  have hClaim1 : totalClaimedSlots st1 = 0 := by unfold totalClaimedSlots; rw [hGrp1_st]; exact hClaimSt
  have hGrpCl1 : ∀ U : Nat, peakCount ≤ U → Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st1.groups := fun U _ hU => by rw [hGrp1_st]; exact hGM0 U hU
  have hUse1 : (st1.ctx.usageByClass[sc]'hscU1).toNat ≤ peakCount := by
    have h1 := Cost.usage_le_live_add_claimed_of_active_zero hwf1 hscU1 hAct0_1; rw [hClaim1] at h1; omega
  obtain ⟨CtxRest1, hCtxSp1, _⟩ := ctx_split_fields maddrs.ctx st1.ctx hActL1 hUseL1 hUnmL1 hBncL1
  obtain ⟨UseRest1, hUseSp1, _⟩ := words64_focus_set (maddrs.ctx + 464#64) st1.ctx.usageByClass sc hscU1
  let CoreRest1 := MallocngLiveAuth γ st1.liveMap ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗ ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1)
  let CntF := (∃∗ v : BitVec 32, (tp - 0xa4#64) ↦₃₂ v) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.ctx + 12#64) ↦₃₂ st1.ctx.mmapCounter) ∗
    ((maddrs.ctx + 80#64) ↦₆₄* st1.ctx.active) ∗ UseRest1 ∗ ((maddrs.ctx + 848#64) ↦ₛ st1.ctx.unmapSeq) ∗ ((maddrs.ctx + 880#64) ↦ₛ st1.ctx.bounces) ∗
    ((maddrs.ctx + 912#64) ↦₈ st1.ctx.seq) ∗ CtxRest1 ∗ CoreRest1 ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
    (maddrs.debruijnAlloc ↦ᵣ debruijn32Table) ∗ (maddrs.debruijnFree ↦ᵣ debruijn32Table) ∗ (m ↦ₛ List.replicate 40 0#8) ∗ Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)
  refine SepWP.weaken_pre (P' := ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ∗ ((maddrs.ctx + 464#64 + BitVec.ofNat 64 (8 * sc)) ↦₆₄ (st1.ctx.usageByClass[sc]'hscU1)) ∗
      (maddrs.medCntTab ↦ᵣ medCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ smallCntTabBytes) ∗ CntF)
    (Entails.of_eq (by unfold MallocngRuntime MallocngRoTablesA MallocngRoTablesAt; dsimp only [CntF, CoreRest1, Saved, AllocSlotSaved12]; rw [hStkSp, hCtxSp1, hUseSp1]; ac_rfl)) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_cnt_join) hcl_am
    (SepWP.mono (wp_alloc_group_cnt_join sam m (st1.ctx.usageByClass[sc]'hscU1) sc CntF hw564 hr564 hw712 hw768 hsc hmNe0 hpc_am hrun_am hx0_am hx22_am hx21_am hx23_am hx24_am hx27_am) ?_)
  rintro scj Pcj hpccj hrcj ⟨cnt, hlo, hhi, hprod, h25, hsm, hc1, hcntRaw, _, hspcj, halcj, hpspcj, hx19cj, hx2cj, hx4cj, hx20cj, hx21cj, hx23cj, hx22cj, hx24cj, hx27cj, hregcj, hPcj⟩ hpermcj hclcj; rw [hPcj]
  have hx25cj := (hregcj .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25_am
  have hx26cj := (hregcj .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26_am
  have hwf1_cj : MallocngWFInflight (inflight + 1) maddrs.base brkStart scj.brk liveCost peakCost st1 := hpspcj.2.1.symm ▸ hwf1
  let JoinP := Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
    (m ↦ₛ List.replicate 40 0#8) ∗ MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart scj.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp
  refine SepWP.weaken_pre (P' := JoinP) (Entails.of_eq (by
      dsimp only [JoinP, CntF, CoreRest1, Saved]; unfold MallocngCoreStInflightModeA MallocngRuntime MallocngRoTablesA MallocngRoTablesAt; rw [pure_sepConj_of_true hwf1_cj, hCtxSp1, hUseSp1]; ac_rfl)) ?_
  refine wp_cnt_dispatch_mem_fine (s0.readReg64 .x30) scj sc cnt JoinP hw768_msvc hsc hlo hhi hprod h25 hsm hc1 hpccj hrcj hx20cj hx24cj hx4cj ?_ ?_
  · intro cnt' sn hp_n hr_n hm_n hsp_n hal_n hpsp_n hbump hv hx0_n hx20_n hx28_n hrg_n; have hperm_n : sn.mem.perm = sam.mem.perm := (congrArg Memory.perm hm_n).trans hpermcj
    have hP_eq : JoinP = (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
        (m ↦ₛ List.replicate 40 0#8) ∗ MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sn.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp) := by dsimp only [JoinP]; rw [hpsp_n.2.1]
    rw [hP_eq]; exact wp_allocGroup_nested_fine sc req inflight cnt' hsc hReqHi hInflight hRec hv γ tp brkStart m liveCost peakCost peakCount bL bP maxMeta st0 st1 s0 sn
      hw564 hw768 hr768 (hpsp_n.2.1.symm ▸ hwf1_cj) hscU1 (by rw [hbump, hcntRaw]; rfl) hCount1 hClaim1 hFine1 hRoom1 hCB10 hMaStep1 hActL1 hAct0_1 hActLow1 hRes1 hRel1
      (fun a ha hsrc => hOrph_am0 a (hperm_n ▸ ha) hsrc) (mappedDelta_perm_right hDelta_am0 hperm_n) hGrpCl1
      (hm_n ▸ hclcj) hp_n hr_n (hsp_n.trans (hspcj.trans hsp_am0)) (hal_n.trans (halcj.trans hal_am)) htp hbrkS
      (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_am0 hpspcj.1) hpsp_n.1) (hpsp_n.2.2.trans (hpspcj.2.2.trans hvr_am)) hx0_n
      ((hrg_n .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19cj) hx20_n
      ((hrg_n .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21cj) ((hrg_n .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22cj)
      ((hrg_n .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23cj) ((hrg_n .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24cj)
      ((hrg_n .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26cj) hx28_n
  · intro cnt' sr hp_r hr_r hm_r hsp_r hal_r hpsp_r hbump hlo_r hhi_r hgt_r hpr_r h25_r hx0_r hx6_r hx20_r _ hrg_r; have hperm_r : sr.mem.perm = sam.mem.perm := (congrArg Memory.perm hm_r).trans hpermcj
    have hP_eq : JoinP = (Saved ∗ stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
        (m ↦ₛ List.replicate 40 0#8) ∗ MallocngCoreStInflightModeA ro (inflight + 1) γ maddrs brkStart sr.brk liveCost peakCost st1 ∗ MallocngRuntime maddrs tp) := by dsimp only [JoinP]; rw [hpsp_r.2.1]
    rw [hP_eq]; exact wp_allocGroup_root_fine sc req inflight cnt' hsc hReqLo hReqHi hlo_r hhi_r hgt_r hpr_r h25_r
      (st1.ctx.usageByClass[sc]'hscU1) (by rw [hbump, hcntRaw]; rfl) γ tp brkStart m liveCost peakCost peakCount bL bP maxMeta st0 st1 s0 sr
      hw564 hw768 hr768 hClaim1 hFine1 hRoom1 hCB10 hAct0_1 hActLow1 hRes1 hRel1
      (fun a ha hsrc => hOrph_am0 a (hperm_r ▸ ha) hsrc) (mappedDelta_perm_right hDelta_am0 hperm_r) hGrpCl1 hUse1
      (hm_r ▸ hclcj) hp_r hr_r (hsp_r.trans (hspcj.trans hsp_am0)) (hal_r.trans (halcj.trans hal_am)) htp
      (MallocngProcPreserved.trans (MallocngProcPreserved.trans hProc_am0 hpspcj.1) hpsp_r.1) (hpsp_r.2.2.trans (hpspcj.2.2.trans hvr_am))
      ((hrg_r .x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx4cj) ((hrg_r .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19cj) hx20_r
      ((hrg_r .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx21cj) ((hrg_r .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22cj)
      ((hrg_r .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23cj) ((hrg_r .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24cj)
      ((hrg_r .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25cj) ((hrg_r .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27cj)
      hx0_r ((hrg_r .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2cj) hx6_r

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
