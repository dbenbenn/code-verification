/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Cost.Fine.Specs
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocLargeProof
import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage2b
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch0
import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Placed `__libc_malloc_impl`, `default_malloc`, and `malloc` Fine-Cost Proofs (`…Cost.Fine.MallocImpl`)

- **Role**: `Role::Proof` (untrusted).
- **Exports**:
  - `placed_libcMallocImpl_fine_raw_ok` (`LibcMallocImplFineRawStmt`)
  - `placed_libcMallocImpl_fine_ok` (`LibcMallocImplFineStmt`)
  - `placed_defaultMalloc_fine_ok` (`DefaultMallocFineStmt`)
  - `fine_malloc_entry_ok` (`mallocngMultiEntryOk` for `"malloc"` under `mallocngFineCostModel`)
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs.Cost.Fine

open Arm64 Arm64.Obj Arm64.CType ProofLib ProofLib.SepLogic ProofLib.ProgramReflection
  VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs VerifiedLibraries.Mallocng.Proofs.Cost

private theorem allowedPhysClass_of_coarseChoice {req sc : Nat} (hScLt : sc < 48)
    (hChoice :
      let sc0 := sizeToClassUnits ((req + 3) / 16)
      sc = sc0 ∨ (4 ≤ sc0 ∧ sc0 ≤ 31 ∧ sc0 ≠ 6 ∧ sc0 % 2 = 0 ∧ sc = sc0 + 1)) :
    allowedPhysClass (nomSc req) sc = true := by
  dsimp only [allowedPhysClass, nomSc, coarseBumpable] at hChoice ⊢
  refine decide_eq_true ⟨hScLt, ?_⟩
  rcases hChoice with rfl | ⟨h1, h2, h3, h4, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨decide_eq_true ⟨h1, h2, h3, h4⟩, rfl⟩

private theorem sc24_props_of_coarse {req sc : Nat}
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req) :
    (24 ≤ sc ∧ sc ≤ 26 → nominalSlotCap 23 < req) ∧
    (sc = 24 → nominalSlotCap 22 < req) := by
  have h16 : 16 ≤ nominalSlotCap 23 := by decide
  have h22_23 : nominalSlotCap 22 ≤ nominalSlotCap 23 := by decide
  have h23_24 : nominalSlotCap 23 ≤ nominalSlotCap 24 := by decide
  refine ⟨fun ⟨hLo, hHi⟩ => ?_, fun hEq => by have := hSc24 hEq; omega⟩
  have hCases : sc = 24 ∨ sc = 25 ∨ sc = 26 := by omega
  rcases hCases with rfl | rfl | rfl
  · exact hSc24 rfl
  · have h : nominalSlotCap 23 < max req 16 := hSc2 ⟨by decide, by decide⟩; omega
  · have h : nominalSlotCap 24 < max req 16 := hSc2 ⟨by decide, by decide⟩; omega

private theorem at_bl_target_b09 [MallocngMultiPlacement] {b : BitVec 64}
    (_hb : BlkBase 9 b) (j : Nat) (off : BitVec 64) :
    mbase j = b + off + (mbase j - b - off) := by bv_arith

private theorem stackFrame_eq_stackFrameAt {s : State} {sp1 : BitVec 64} (k : Nat)
    (_hk : k < 2 ^ 64) (hsp : s.sp = sp1) :
    stackFrame s k = stackFrameAt sp1 k := by
  unfold stackFrame
  rw [hsp, ← stackFrameAt_eq_memRegion sp1 k]

private theorem stackFrameAt_624_eq (sp1 : BitVec 64) (k : Nat) (hk : k ≤ 624) :
    stackFrameAt sp1 624 = (stackFrameAt sp1 k ∗ stackFrameAt (sp1 - BitVec.ofNat 64 k) (624 - k)) := by
  have hEq : (624 : Nat) = k + (624 - k) := by omega
  conv => lhs; rw [hEq]
  exact stackFrameAt_split sp1 k (624 - k)

private theorem untouchedCS_of_calleeSaved {s0 s1 s2 : State}
    (h1 : MallocImplUntouchedCS s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    MallocImplUntouchedCS s0 s2 := by
  rcases h1 with ⟨h26, h27, h28, hv⟩
  rcases h2 with ⟨_, _, _, _, _, _, _, h26', h27', h28', _, hv'⟩
  exact ⟨h26'.trans h26, h27'.trans h27, h28'.trans h28, hv'.trans hv⟩

private theorem getStride_bv_helpers :
    (∀ b : BitVec 8, BitVec.zeroExtend 64 (BitVec.zeroExtend 32 b) = BitVec.zeroExtend 64 b) ∧
    (∀ h : BitVec 16, BitVec.zeroExtend 64 (BitVec.zeroExtend 32 h) = BitVec.zeroExtend 64 h) ∧
    (∀ b : BitVec 8, BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 b)) = BitVec.zeroExtend 64 b) ∧
    (∀ h : BitVec 16, BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 h)) = BitVec.zeroExtend 64 h) ∧
    (∀ u : BitVec 64, (u == 0#64) = true → (u != 0#64) = false) ∧
    (∀ u : BitVec 64, (u == 0#64) = false → (u != 0#64) = true) :=
  ⟨fun _ => by bv_bits, fun _ => by bv_bits, fun _ => by bv_bits, fun _ => by bv_bits,
   fun _ h => by revert h; bv_bits, fun _ h => by revert h; bv_bits⟩

private theorem getStride_ldr8_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s : State} {G : SepProp} {metaPtr packedWord cycVal : BitVec 64}
    {metaBytes : List (BitVec 8)} {req idx : Nat} (hMetaLen : metaBytes.length = 40)
    (hPk : pack64 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8) (metaBytes.getD 34 0#8) (metaBytes.getD 35 0#8)
      (metaBytes.getD 36 0#8) (metaBytes.getD 37 0#8) (metaBytes.getD 38 0#8) (metaBytes.getD 39 0#8) = packedWord)
    (hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true)
    (_hB0N : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 != 0#64) = false)
    (hpc : s.pc = b + miOff_after_unlock) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx) (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_tst_mask) s ((metaPtr ↦ₛ metaBytes) ∗ G)
      (fun s1 P1 =>
        (s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧ s1.readReg64 (.gpr 4#5) = packedWord ∧
         s1.readReg64 (.gpr 19#5) = cycVal ∧ s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
         s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧ (P1 ⊢ (metaPtr ↦ₛ metaBytes) ∗ G))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  dsimp only [miOff_after_unlock, miOff_tst_mask] at hpc ⊢
  have hReadPk : ByteSlice.readLE metaBytes 32 8 = packedWord := by
    rw [← ByteSlice.pack64_eq_readLE_8]; dsimp only [Nat.reduceAdd]; exact hPk
  have hHide : Nonempty (PLift ((BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true ∧
    ByteSlice.readLE metaBytes 32 8 = packedWord)) := ⟨⟨⟨hB0, hReadPk⟩⟩⟩
  clear hPk hB0 hReadPk; wp_step; wp_step; obtain ⟨⟨hB0, hReadPk⟩⟩ := hHide
  conv => arg 3; rw [hB0]
  clear hB0
  have hHide2 : Nonempty (PLift (ByteSlice.readLE metaBytes 32 8 = packedWord)) := ⟨⟨hReadPk⟩⟩
  clear hReadPk; wp_steps 2; obtain ⟨⟨hReadPk⟩⟩ := hHide2
  exact SepWP.done rfl hrun ⟨⟨rfl, rfl, rfl, hProc, untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
    by simp [hReadPk], by simpa using hx19, by simpa using hx20, by simpa using hx21,
    by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩

private theorem getStride_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s : State} {F : SepProp} {metaPtr packedWord cycVal : BitVec 64}
    {metaBytes : List (BitVec 8)} {stride lastIdx sc req idx : Nat} (hMetaLen : metaBytes.length = 40)
    (hPk : pack64 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8) (metaBytes.getD 34 0#8) (metaBytes.getD 35 0#8)
      (metaBytes.getD 36 0#8) (metaBytes.getD 37 0#8) (metaBytes.getD 38 0#8) (metaBytes.getD 39 0#8) = packedWord)
    (hTst0 : (((metaBytes.getD 32 0#8).zeroExtend 32).zeroExtend 64 &&& 0x1f#64 == 0#64) = decide (lastIdx = 0))
    (hZ : lastIdx = 0 → ((packedWord &&& 0xfffffffffffff000#64) == 0#64) = false ∧
      (packedWord &&& 0xfffffffffffff000#64) - 0x10#64 = BitVec.ofNat 64 stride)
    (hNZ : lastIdx ≠ 0 → sc < 48 ∧
      (((pack16 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8)).zeroExtend 32).zeroExtend 64 >>> 6) &&& 0x3f#64 =
        BitVec.ofNat 64 sc ∧ (BitVec.ofNat 64 sc <<< 1) = BitVec.ofNat 64 (2 * sc) ∧
      (((BitVec.ofNat 16 (sizeClass sc)).zeroExtend 32).zeroExtend 64 &&& 0xffff#64) <<< 4 = BitVec.ofNat 64 stride)
    (hpc : s.pc = b + miOff_after_unlock) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx) (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_44) s
      ((metaPtr ↦ₛ metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 4#5) = BitVec.ofNat 64 stride ∧ s1.readReg64 (.gpr 19#5) = cycVal ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
         s1.readReg64 (.gpr 22#5) = metaPtr ∧ s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ (metaPtr ↦ₛ metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ F))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hScLen : sizeClassBytes.length = 96 := sizeClassBytes_length
  by_cases hL0 : lastIdx = 0
  · obtain ⟨hMNe0, hStrEq⟩ := hZ hL0; clear hZ hNZ
    have hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = true := by
      rw [← getStride_bv_helpers.1]; simpa only [hL0, decide_true] using hTst0
    have hB0N := getStride_bv_helpers.2.2.2.2.1 _ hB0; clear hTst0
    refine SepWP.seq_entails_emp
      (getStride_ldr8_step hb hMetaLen hPk hB0 hB0N hpc hrun hProc hcsHi hx19 hx20 hx21 hx22 hx23) ?_
    rintro sm hpcm hrunm ⟨hspm, hbrkm, hpermm, hProcm, hcsm, hx4pk, hx19m, hx20m, hx21m, hx22m, hx23m⟩
    clear hPk hB0 hB0N; dsimp only [miOff_tst_mask, miOff_enframe_44] at hpcm ⊢
    have hHide0 : Nonempty (PLift (((packedWord &&& 0xfffffffffffff000#64) == 0#64) = false ∧
      (packedWord &&& 0xfffffffffffff000#64) - 0x10#64 = BitVec.ofNat 64 stride)) := ⟨⟨⟨hMNe0, hStrEq⟩⟩⟩
    clear hMNe0 hStrEq; wp_steps 2
    wp_if hBr2
    · obtain ⟨⟨hMNe0, _⟩⟩ := hHide0
      have hEq0 : packedWord &&& 0xfffffffffffff000#64 = 0#64 := hBr2
      rw [hEq0] at hMNe0; cases hMNe0
    · wp_steps 3; obtain ⟨⟨_, hStrEq⟩⟩ := hHide0
      exact SepWP.done (by simp) (by simp [hrunm]) ⟨⟨by simp [hspm, hsp], by simp [hbrkm],
        by simp [arm64_norm, hpermm],
        by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProcm,
        untouchedCS_step hcsm (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [hStrEq], by simp [hx19m], by simp [hx20m], by simp [hx21m],
        by simp [hx22m], by simp [hx23m]⟩, Entails.refl _⟩
  · dsimp only [miOff_after_unlock, miOff_enframe_44] at hpc ⊢
    obtain ⟨hSc48, hUbfx, hShl1, hStrEq⟩ := hNZ hL0
    have hB0 : (BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = false := by
      rw [← getStride_bv_helpers.1]; simpa only [hL0, decide_false] using hTst0
    clear hZ hNZ hPk hTst0
    have hUbfx1 : ((BitVec.zeroExtend 64 (pack16 (metaBytes.getD 32 0#8) (metaBytes.getD 33 0#8))) >>> 6) &&& 0x3f#64 =
        BitVec.ofNat 64 sc := by rw [← getStride_bv_helpers.2.1]; exact hUbfx
    have hRead2 : (ByteSlice.readLE metaBytes 32 2 >>> 6) &&& 0x3f#64 = BitVec.ofNat 64 sc := by
      rw [ByteSlice.readLE_two]; dsimp only [Nat.reduceAdd]; exact hUbfx1
    have hPackSc : pack16 (sizeClassBytes.getD (2 * sc) 0#8) (sizeClassBytes.getD (2 * sc + 1) 0#8) =
        BitVec.ofNat 16 (sizeClass sc) := pack16_sizeClassBytes hSc48
    generalize hScV : sizeClass sc = scVal at hPackSc hStrEq; clear hScV
    have hReadSc : ByteSlice.readLE sizeClassBytes (2 * sc) 2 = BitVec.zeroExtend 64 (BitVec.ofNat 16 scVal) := by
      rw [ByteSlice.readLE_two, hPackSc]
    have hStrEq1 : ((BitVec.zeroExtend 64 (BitVec.ofNat 16 scVal)) &&& 0xffff#64) <<< 4 =
        BitVec.ofNat 64 stride := by rw [← getStride_bv_helpers.2.1]; exact hStrEq
    generalize hScB : sizeClassBytes = scBytes at hScLen hPackSc hReadSc ⊢; clear hScB
    have hHideNZ : Nonempty (PLift ((BitVec.zeroExtend 64 (metaBytes.getD 32 0#8) &&& 0x1f#64 == 0#64) = false)) := ⟨⟨hB0⟩⟩
    clear hB0 hUbfx hStrEq; wp_step; wp_step; obtain ⟨⟨hB0⟩⟩ := hHideNZ
    conv => arg 3; rw [hB0]
    clear hB0; wp_steps
    exact SepWP.done (by simp) (by simp [hrun]) ⟨⟨by simp [hsp], by simp, by simp [arm64_norm],
      by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
      untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
      by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩

private theorem enframe_mask_bv_aux (x3 : BitVec 64) (w1 : BitVec 32) (hw1 : w1 &&& 255#32 = w1) :
    let x5 := x3 >>> 4
    let m32 := BitVec.truncate 32 (((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) |||
      (((x5 ||| (x3 >>> 5)) ||| ((x5 ||| (x3 >>> 5)) >>> 2)) >>> 4))
    let w1_raw : BitVec 32 :=
      if x5.ult (BitVec.zeroExtend 64 (w1 &&& m32)) = true then
        (w1 &&& m32) + ~~~(BitVec.truncate 32 x5)
      else w1 &&& m32
    BitVec.truncate 32 (BitVec.zeroExtend 64 w1) = w1 ∧
    ((w1.signExtend 64).ule x5 = true → x5.ult (w1.signExtend 64) = false) ∧
    (w1 = BitVec.ofNat 32 w1.toNat → BitVec.zeroExtend 64 w1 = BitVec.ofNat 64 w1.toNat) ∧
    (¬ (w1.signExtend 64).ule x5 = true →
      w1_raw &&& 255#32 = w1_raw ∧ x5.ult (w1_raw.signExtend 64) = false ∧
      (w1_raw = BitVec.ofNat 32 w1_raw.toNat → BitVec.zeroExtend 64 w1_raw = BitVec.ofNat 64 w1_raw.toNat)) := by
  dsimp only
  refine ⟨by bv_omega, by bv_bits, fun h => by rw [h]; bv_omega, fun hNotUle => ?_⟩
  have hGt : (x3 >>> 4).ult (w1.signExtend 64) = true := by revert hNotUle; bv_bits
  obtain ⟨hUltF, hAnd, _⟩ := enframeMaskReduce_spec x3 w1 hw1 hGt
  exact ⟨hAnd, hUltF, fun h => by rw [h]; bv_omega⟩

private theorem enframe_step_bv_simps :
    (∀ x1v : BitVec 64, x1v &&& 255#64 = x1v →
      BitVec.truncate 32 x1v &&& 255#32 = BitVec.truncate 32 x1v ∧
      x1v = BitVec.zeroExtend 64 (BitVec.truncate 32 x1v)) ∧
    (∀ u : BitVec 64, (u &&& 255#64) &&& 255#64 = u &&& 255#64) :=
  ⟨fun _ h => ⟨by revert h; bv_bits, by revert h; bv_bits⟩, fun _ => by bv_bits⟩

private theorem enframe_mask_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s : State} {P : SepProp}
    {start storage metaPtr : BitVec 64} {stride req idx : Nat}
    (hShr4 : BitVec.ofNat 64 (stride - 4 - req) >>> 4 = BitVec.ofNat 64 ((stride - 4 - req) / 16))
    (hW1Fit : ∀ w : BitVec 32, w &&& 255#32 = w →
      (BitVec.ofNat 64 ((stride - 4 - req) / 16)).ult (w.signExtend 64) = false →
      w.toNat ≤ 255 ∧ 16 * w.toNat + req ≤ stride - 4 ∧ w = BitVec.ofNat 32 w.toNat)
    (hpc : s.pc = b + miOff_enframe_90) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = start) (hx1_and : s.readReg64 (.gpr 1#5) &&& 255#64 = s.readReg64 (.gpr 1#5))
    (hx2 : s.readReg64 (.gpr 2#5) = storage) (hx3 : s.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (stride - 4 - req))
    (hx4 : s.readReg64 (.gpr 4#5) = 0#64) (hx5 : s.readReg64 (.gpr 5#5) = BitVec.ofNat 64 (stride - 4 - req) >>> 4)
    (hx6 : s.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_c4) s P
      (fun s1 P1 =>
        (∃ off : Nat, off ≤ 255 ∧ 16 * off + req ≤ stride - 4 ∧
          s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
          s1.readReg64 (.gpr 0#5) = start ∧ s1.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off ∧
          s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 4#5) = 0#64 ∧
          s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
          s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
          s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧ (P1 ⊢ P))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  have hShrF : Unit → _ := fun _ => hShr4; clear hShr4
  obtain ⟨hw1, hx1⟩ := enframe_step_bv_simps.1 _ hx1_and
  generalize hw1_def : BitVec.truncate 32 (s.readReg64 (.gpr 1#5)) = w1 at hw1 hx1
  clear hw1_def hx1_and
  have hAux : Unit → _ ∧ _ ∧ _ := fun _ => ⟨enframe_mask_bv_aux (BitVec.ofNat 64 (stride - 4 - req)) w1 hw1, hW1Fit, hw1⟩
  clear hW1Fit hw1; wp_steps
  wp_if hHs
  · obtain ⟨⟨hTrW1, hUleImp, hZXNat, _⟩, hW1Fit, hw1⟩ := hAux ()
    have hUltF : (BitVec.ofNat 64 ((stride - 4 - req) / 16)).ult (w1.signExtend 64) = false := by
      rw [← hShrF ()]; exact hUleImp (by simpa only [hTrW1] using hHs)
    obtain ⟨h255, hFit, hW1Eq⟩ := hW1Fit w1 hw1 hUltF
    have hX1Eq := hx1.trans (hZXNat hW1Eq); clear hW1Eq
    exact SepWP.done (by simp) (by simp [hrun]) ⟨⟨w1.toNat, h255, hFit, by simp [hsp], rfl, rfl,
      procPres_setPC (procPres_setPState hProc),
      untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
      by simp [hx0], by simp [hX1Eq], by simp [hx2], by simp [hx4],
      by simp [hx6], by simp [hx20], by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩
  · wp_steps
    wp_if hLoop
    · obtain ⟨⟨hTrW1, _, _, hMaskImp⟩, _, _⟩ := hAux ()
      obtain ⟨_, hUltF', _⟩ := hMaskImp (by simpa only [hTrW1] using hHs)
      exact False.elim (Bool.false_ne_true (hUltF'.symm.trans (by simpa only [hTrW1] using hLoop)))
    · obtain ⟨⟨hTrW1, _, _, hMaskImp⟩, hW1Fit, _⟩ := hAux ()
      obtain ⟨hw1', hUltF', hZXNat'⟩ := hMaskImp (by simpa only [hTrW1] using hHs)
      obtain ⟨h255, hFit, _⟩ := hW1Fit _ hw1' (by rw [← hShrF ()]; exact hUltF')
      clear hZXNat' hMaskImp hAux hW1Fit hTrW1
      exact SepWP.done (State.pc_setPC ..)
        ((State.status_setPC ..).trans ((State.status_setPState ..).trans (by simp [hrun])))
        ⟨⟨_, h255, hFit, by simp [hsp], by simp, by simp [arm64_norm],
          by repeat (first | apply procPres_setPC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
          untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
          by simp [hx0], by simp, by simp [hx2], by simp [hx4], by simp [hx6],
          by simp [hx20], by simp [hx22], by simp [hx23]⟩, Entails.refl _⟩

private theorem enframe_head_step [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s : State} {F : SepProp} {start storage metaPtr cycVal : BitVec 64}
    {slotBs metaBytes : List (BitVec 8)} {stride req idx : Nat}
    (hFit0 : req + 4 ≤ stride) (hSlotLen : slotBs.length = stride) (hMetaLen : metaBytes.length = 40)
    (hMemPk : pack64 (metaBytes.getD 16 0#8) (metaBytes.getD 17 0#8) (metaBytes.getD 18 0#8) (metaBytes.getD 19 0#8)
      (metaBytes.getD 20 0#8) (metaBytes.getD 21 0#8) (metaBytes.getD 22 0#8) (metaBytes.getD 23 0#8) + 16#64 = storage)
    (hSlot0 : (slotBs[0]?).getD 0#8 = 0#8)
    (hStrSubReq : (BitVec.ofNat 64 stride - BitVec.ofNat 64 req) - 4#64 = BitVec.ofNat 64 (stride - 4 - req))
    (hStrSub4 : BitVec.ofNat 64 stride - 4#64 = BitVec.ofNat 64 (stride - 4))
    (hMadd : storage + BitVec.ofNat 64 stride * BitVec.ofNat 64 idx = start)
    (hpc : s.pc = b + miOff_enframe_44) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx4 : s.readReg64 (.gpr 4#5) = BitVec.ofNat 64 stride) (hx19 : s.readReg64 (.gpr 19#5) = cycVal)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_90) s
      (((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
          MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧ s1.readReg64 (.gpr 0#5) = start ∧
          s1.readReg64 (.gpr 1#5) &&& 255#64 = s1.readReg64 (.gpr 1#5) ∧
          s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 3#5) = BitVec.ofNat 64 (stride - 4 - req) ∧
          s1.readReg64 (.gpr 4#5) = 0#64 ∧ s1.readReg64 (.gpr 5#5) = BitVec.ofNat 64 (stride - 4 - req) >>> 4 ∧
          s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
          s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 22#5) = metaPtr ∧
          s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ ((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F))
      (fun _ => ⌜False⌝) := by
  have _ := hb
  obtain ⟨_, hAnd64⟩ := enframe_step_bv_simps
  have hReadMem : ByteSlice.readLE metaBytes 16 8 + 16#64 = storage := by
    rw [← ByteSlice.pack64_eq_readLE_8]; exact hMemPk
  have hSlot0D : slotBs.getD 0 0#8 = 0#8 := by rw [List.getD_eq_getElem?_getD, hSlot0]
  have hSlot1 : ByteSlice.readLE slotBs 0 1 = 0#64 := by rw [ByteSlice.readLE_one, hSlot0D]; rfl
  wp_steps
  wp_if hCbz4
  · wp_steps
    exact SepWP.done rfl hrun ⟨⟨by simpa using hsp, rfl, rfl, hProc,
      untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
      by simp, by simp [hAnd64], by simp, by simp, by simp, by simp, by simp,
      by simpa using hx20, by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩
  · wp_steps
    exact SepWP.done rfl hrun ⟨⟨by simpa using hsp, rfl, rfl, hProc,
      untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
      by simp, by simp [hAnd64], by simp, by simp, by simp, by simp, by simp,
      by simpa using hx20, by simpa using hx22, by simpa using hx23⟩, Entails.refl _⟩

private theorem enframe_bv_aux (n idx totOff16 res : Nat) (hn : n ≤ 255) (hi : idx ≤ 31) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = 0#64 → n = 0) ∧
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) <<< 4) = BitVec.ofNat 32 n <<< 4 ∧
    BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 16 n ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 255#64 = BitVec.ofNat 64 idx ∧
    BitVec.zeroExtend 8 (BitVec.ofNat 64 idx) = BitVec.ofNat 8 idx ∧
    BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 totOff16)) = BitVec.ofNat 16 totOff16 ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) &&& 31#64 = BitVec.ofNat 64 idx ∧
    BitVec.zeroExtend 8 (BitVec.ofNat 64 (min res 5 <<< 5)) + BitVec.zeroExtend 8 (BitVec.ofNat 64 idx) =
      BitVec.truncate 8 (BitVec.ofNat 32 (min res 5 <<< 5) + BitVec.ofNat 32 idx) ∧
    BitVec.zeroExtend 64 (BitVec.ofNat 8 idx) = BitVec.ofNat 64 idx ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 idx) = BitVec.ofNat 64 idx ∧
    (res ≤ 4 → BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (BitVec.ofNat 32 res) &&& 7#64) <<< 5)) =
      BitVec.ofNat 64 (min res 5 <<< 5)) ∧
    (∀ a b : BitVec 32, a - b = BitVec.ofNat 32 res → res < 1048576 → ((a = b) ↔ res = 0)) := by
  have hI : (List.range 32).all (fun k =>
    decide (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) &&& 255#64 = BitVec.ofNat 64 k ∧
      BitVec.zeroExtend 8 (BitVec.ofNat 64 k) = BitVec.ofNat 8 k ∧
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) &&& 31#64 = BitVec.ofNat 64 k ∧
      BitVec.zeroExtend 64 (BitVec.ofNat 8 k) = BitVec.ofNat 64 k ∧
      BitVec.setWidth 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k)) = true := by decide
  have hR : (List.range 5).all (fun r =>
    decide (BitVec.zeroExtend 64 (BitVec.truncate 32 ((BitVec.zeroExtend 64 (BitVec.ofNat 32 r) &&& 7#64) <<< 5)) =
      BitVec.ofNat 64 (min r 5 <<< 5))) = true := by decide
  obtain ⟨h4, h5, h7, h9, h10⟩ := of_decide_eq_true (List.all_eq_true.mp hI idx (List.mem_range.mpr (by omega)))
  have _ : min res 5 ≤ 5 := Nat.min_le_right _ _
  have hShl : BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n)) <<< 4) =
      BitVec.ofNat 32 n <<< 4 := by apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq]
  refine ⟨by bv_omega, hShl, by bv_omega, h4, h5, by bv_omega, h7, by bv_omega, h9, h10,
    fun _ => of_decide_eq_true (List.all_eq_true.mp hR res (List.mem_range.mpr (by omega))), ?_⟩
  intro a b hab hr; constructor <;> intro h
  · have : BitVec.ofNat 32 res = 0#32 := by rw [← hab, h, BitVec.sub_self]
    bv_omega
  · subst h; bv_omega

private theorem enframe_step1 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s : State} {F : SepProp} {oom : State → SepProp}
    {start storage metaPtr : BitVec 64} {stride req idx off : Nat} {slotBs metaBytes : List (BitVec 8)}
    (hFit0 : req + 4 ≤ stride) (hFit : 16 * off + req ≤ stride - 4) (hOff255 : off ≤ 255)
    (hSlotLen : slotBs.length = stride) (hMetaLen : metaBytes.length = 40)
    (hMemGet : pack64 (metaBytes.getD 16 0#8) (metaBytes.getD 17 0#8) (metaBytes.getD 18 0#8) (metaBytes.getD 19 0#8)
      (metaBytes.getD 20 0#8) (metaBytes.getD 21 0#8) (metaBytes.getD 22 0#8) (metaBytes.getD 23 0#8) + 16#64 = storage)
    (hOffSE : BitVec.signExtend 64 (BitVec.ofNat 32 off <<< 4) = BitVec.ofNat 64 (16 * off))
    (hpc : s.pc = b + miOff_enframe_c4) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = start) (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off)
    (hx2 : s.readReg64 (.gpr 2#5) = storage) (hx4 : s.readReg64 (.gpr 4#5) = 0#64)
    (hx6 : s.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_e8) s
      (((start - 4#64) ↦ₛ slotBs) ∗ (metaPtr ↦ₛ metaBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
         s1.readReg64 (.gpr 2#5) = storage ∧ s1.readReg64 (.gpr 4#5) = 0#64 ∧
         s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4) ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧ s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P1 ⊢ ((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗ (metaPtr ↦ₛ metaBytes) ∗ F))
      oom := by
  have _ := hb
  obtain ⟨hZeroEq, hShlEq, hTr16, _, _, _, _, _, _, _, _, _⟩ := enframe_bv_aux off 0 0 0 hOff255 (Nat.zero_le _)
  wp_steps
  wp_if hcond
  · have hOff0 : off = 0 := hZeroEq hcond
    cases s
    refine SepWP.done rfl hrun ⟨⟨hsp, rfl, rfl, hProc, hcsHi, ?_, hx2, hx4, hx6, hx20, hx23⟩, ?_⟩
    · rw [State.readReg64_setPC, hx0, hOff0]; exact (BitVec.add_zero start).symm
    · dsimp only [enframeB1]; simp only [hOff0, ↓reduceIte]; exact Entails.refl _
  · have hOffNe : off ≠ 0 := fun h0 => hcond (by subst h0; rfl)
    wp_steps 2; wp_str8_perm m1 hm1; wp_str16_perm m2 hm2; wp_step; wp_str8_perm m3 hm3; wp_steps 2
    refine SepWP.done rfl hrun ⟨⟨by simpa using hsp, rfl, by simpa using hm3.trans (hm2.trans hm1), hProc,
      untouchedCS_step hcsHi (by simp) (by simp) (by simp) rfl,
      by simp, ?_, by simpa using hx4, by simpa using hx6, by simpa using hx20, by simpa using hx23⟩, ?_⟩
    · simp [← ByteSlice.pack64_eq_readLE_8]; simpa only [List.getD_eq_getElem?_getD] using hMemGet
    · dsimp only [enframeB1]; simp only [hOffNe, ↓reduceIte]; exact Entails.refl _

private theorem enframe_step2 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s1 : State} {F : SepProp} {oom : State → SepProp}
    {start storage : BitVec 64} {stride req idx off totOff16 res : Nat} {bs1 : List (BitVec 8)}
    (hFit0 : req + 4 ≤ stride) (hFit : 16 * off + req ≤ stride - 4) (hIdx31 : idx ≤ 31)
    (hResEq : res = stride - 4 - (16 * off + req)) (hResLt : res < 1048576)
    (hLen1 : bs1.length = stride) (hLen2 : (enframeB2 bs1 off idx totOff16).length = stride)
    (hLen3 : (enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res).length = stride)
    (hBs3Idx : (enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res).getD (16 * off + 1) 0#8 = BitVec.ofNat 8 idx)
    (hPS4 : (start + BitVec.ofNat 64 (16 * off) - storage) >>> 4 = BitVec.ofNat 64 totOff16)
    (hSub32 : BitVec.truncate 32 ((start + BitVec.ofNat 64 (stride - 4)) - (start + BitVec.ofNat 64 (16 * off))) -
      BitVec.truncate 32 (BitVec.ofNat 64 req) = BitVec.ofNat 32 res)
    (hNegAddr : res ≠ 0 → (start + BitVec.ofNat 64 (stride - 4)) + BitVec.signExtend 64 (0#32 - BitVec.ofNat 32 res) =
      start - 4#64 + BitVec.ofNat 64 (4 + 16 * off + req))
    (hSle4 : res ≠ 0 → (BitVec.ofNat 32 res).sle 4#32 = decide (res ≤ 4))
    (hpc1 : s1.pc = b + miOff_enframe_e8) (hrun1 : s1.status = .Running)
    (hProc1 : MallocngProcPreserved s0 s1) (hcs1 : MallocImplUntouchedCS s0 s1)
    (hx0_1 : s1.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off))
    (hx2_1 : s1.readReg64 (.gpr 2#5) = storage) (hx4_1 : s1.readReg64 (.gpr 4#5) = 0#64)
    (hx6_1 : s1.readReg64 (.gpr 6#5) = start + BitVec.ofNat 64 (stride - 4))
    (hx20_1 : s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx23_1 : s1.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_enframe_28) s1
      (((start - 4#64) ↦ₛ bs1) ∗ F)
      (fun s2 P2 =>
        (s2.sp = s1.sp ∧ s2.brk = s1.brk ∧ s2.mem.perm = s1.mem.perm ∧
         MallocngProcPreserved s0 s2 ∧ MallocImplUntouchedCS s0 s2 ∧
         s2.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
         s2.readReg64 (.gpr 1#5) = BitVec.ofNat 64 idx ∧
         s2.readReg64 (.gpr 4#5) = BitVec.ofNat 64 (min res 5 <<< 5)) ∧
        (P2 ⊢ ((start - 4#64) ↦ₛ enframeB3 (enframeB2 bs1 off idx totOff16) off req stride res) ∗ F))
      oom := by
  have _ := hb; subst hResEq
  obtain ⟨_, _, _, hIdx255, hIdxZ8, hTot16, _, _, hIdxZ64, hIdxSW, hLe4R, hEqRes0⟩ :=
    enframe_bv_aux 0 idx totOff16 (stride - 4 - (16 * off + req)) (Nat.zero_le _) hIdx31
  wp_steps 2; wp_str8_perm m1 hm1; wp_steps 2; wp_str16_perm m2 hm2; wp_step
  wp_conv_pre => change ((start - 4#64) ↦ₛ enframeB2 bs1 off idx totOff16) ∗ F
  wp_step
  wp_if hBeq
  · have hRes0 : stride - 4 - (16 * off + req) = 0 := (hEqRes0 _ _ hSub32 hResLt).mp hBeq
    refine SepWP.done rfl hrun1 ⟨⟨rfl, rfl, by simpa using hm2.trans hm1, hProc1,
      untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
      by simpa using hx0_1, by simp [hIdxSW], ?_⟩, ?_⟩
    · rw [hRes0]; simpa using hx4_1
    · dsimp only [enframeB3]; simp only [hRes0, ↓reduceIte]; exact Entails.refl _
  · have hResNe : stride - 4 - (16 * off + req) ≠ 0 := fun h0 => hBeq ((hEqRes0 _ _ hSub32 hResLt).mpr h0)
    have hAddrN := hNegAddr hResNe; have hSle := hSle4 hResNe
    wp_steps 2; wp_str8_perm m3 hm3; wp_step
    wp_if hLeCond
    · have hLe4 : stride - 4 - (16 * off + req) ≤ 4 := of_decide_eq_true hLeCond
      have hShl4 := hLe4R hLe4; wp_steps
      have hMinSW : BitVec.setWidth 64 (BitVec.ofNat 32 (min (stride - 4 - (16 * off + req)) 5 <<< 5)) =
          BitVec.ofNat 64 (min (stride - 4 - (16 * off + req)) 5 <<< 5) := by
        have : min (stride - 4 - (16 * off + req)) 5 ≤ 5 := Nat.min_le_right _ _; bv_omega
      have hB3Eq : enframeB3 (enframeB2 bs1 off idx totOff16) off req stride (stride - 4 - (16 * off + req)) =
          ByteSlice.write8 (enframeB2 bs1 off idx totOff16) (4 + 16 * off + req) 0#8 := by
        dsimp only [enframeB3]; simp only [hResNe, hLe4, ↓reduceIte]
      refine SepWP.done rfl hrun1 ⟨⟨rfl, rfl, by simpa using hm3.trans (hm2.trans hm1), hProc1,
        untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
        by simpa using hx0_1, ?_, by simp [hMinSW]⟩, by rw [hB3Eq]; exact Entails.refl _⟩
      simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
        State.readReg64_writeReg64, ← hB3Eq, hBs3Idx]; exact hIdxZ64
    · have hGe5 : 5 ≤ stride - 4 - (16 * off + req) := by
        have := of_decide_eq_false (Bool.eq_false_of_ne_true hLeCond); omega
      have hNotLe4 : ¬ stride - 4 - (16 * off + req) ≤ 4 := by omega
      wp_str8_perm m4 hm4; wp_step; wp_str32_perm m5 hm5; wp_step
      have hS5 : stride - 4 - 1 = stride - 5 := by omega
      have hB3Eq : enframeB3 (enframeB2 bs1 off idx totOff16) off req stride (stride - 4 - (16 * off + req)) =
          ByteSlice.write32 (ByteSlice.write8 (ByteSlice.write8 (enframeB2 bs1 off idx totOff16)
            (4 + 16 * off + req) 0#8) (stride - 5) 0#8) (stride - 4)
            (BitVec.ofNat 32 (stride - 4 - (16 * off + req))) := by
        dsimp only [enframeB3]; simp only [hResNe, hNotLe4, ↓reduceIte]
      refine SepWP.done rfl hrun1 ⟨⟨rfl, rfl, by simpa using hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1))), hProc1,
        untouchedCS_step hcs1 (by simp) (by simp) (by simp) rfl,
        by simpa using hx0_1, ?_, ?_⟩, by rw [hS5, hB3Eq]; exact Entails.refl _⟩
      · simp only [State.readReg64_setMem, State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64, hS5, ← hB3Eq, hBs3Idx]; exact hIdxZ64
      · rw [show min (stride - 4 - (16 * off + req)) 5 = 5 by omega]; simp

private theorem enframe_step3 [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b) {s0 s2 : State} {F : SepProp} {oom : State → SepProp}
    {start : BitVec 64} {stride idx off res : Nat} {bs3 : List (BitVec 8)}
    (hFit : 16 * off + 4 ≤ stride) (hIdx31 : idx ≤ 31) (hLen3 : bs3.length = stride)
    (hR5Or : BitVec.truncate 8 (BitVec.ofNat 32 (min res 5 <<< 5) + BitVec.ofNat 32 idx) =
      BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
    (hpc2 : s2.pc = b + miOff_enframe_28) (hrun2 : s2.status = .Running)
    (hsp2 : s2.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc2 : MallocngProcPreserved s0 s2) (hcs2 : MallocImplUntouchedCS s0 s2)
    (hx0_2 : s2.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off))
    (hx1_2 : s2.readReg64 (.gpr 1#5) = BitVec.ofNat 64 idx)
    (hx4_2 : s2.readReg64 (.gpr 4#5) = BitVec.ofNat 64 (min res 5 <<< 5)) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s2
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ bs3) ∗ F)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.brk = s2.brk ∧ sf.mem.perm = s2.mem.perm ∧
        MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
        sf.readReg64 (.gpr 0#5) = start + BitVec.ofNat 64 (16 * off) ∧
        (P_f ⊢ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          ((start - 4#64) ↦ₛ ByteSlice.write8 bs3 (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))) ∗ F))
      oom := by
  have _ := hb
  obtain ⟨_, _, _, _, _, _, hIdx31M, hAdd8, _, _, _, _⟩ := enframe_bv_aux 0 idx 0 res (Nat.zero_le _) hIdx31
  wp_conv_pre => unfold MallocImplSavedRegs; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro vPad
  wp_steps 2; wp_str8_perm m1 hm1; wp_steps 6
  refine SepWP.done rfl hrun2 ⟨rfl, rfl, by simpa using hm1, hProc2, ?_, by simpa using hx0_2, ?_⟩
  · rcases hcs2 with ⟨h26, h27, h28, hv⟩
    refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simpa using h26, by simpa using h27, by simpa using h28, by simp, ?_⟩
    simpa [calleeSavedVRegs] using hv
  · refine sepConj_mono ?_ (Entails.refl _); unfold MallocImplSavedRegs
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
        (Entails.sepExists_intro vPad)))))))))

private def mallocImplFineSuccessBody [MallocngMultiPlacement] (ro : Bool) (γ : GhostName)
    (tp brkStart : BitVec 64) (bL bP : FineBudget) (ivs0 : List (BitVec 64 × Nat))
    (req : Nat) (s0 sf : State) : SepProp :=
  ∃∗ p : BitVec 64, ∃∗ bs : List (BitVec 8), ∃∗ st' : MallocngSt, ∃∗ bCoarse' : MallocngBudget,
    ⌜sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
     MallocngBlockWf p req ∧ bs.length = req ∧
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
    MallocngRuntime maddrs tp ∗ (p ↦ₛ bs) ∗ MallocngBlockTokenK γ p req 0

set_option maxHeartbeats 400000 in
private theorem mallocImpl_enframe_finish_fine [MallocngMultiPlacement] {ro : Bool}
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req idx off : Nat} {st0 st1 : MallocngSt} {g : GroupDesc}
    {s0 s : State} {oom : State → SepProp}
    (hCount0 : MallocngCountIvsWF bud ivs0 st0) (hCnt1 : totalLiveCount st1 = totalLiveCount st0)
    (hMetaLe1 : st1.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101)
    (hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hFine1 : FineSplitInv bL bP st1) (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hFit0 : req + 4 ≤ g.stride) (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSmAllow : req ≤ MmapThresholdReq → g.sc < 48 ∧ allowedPhysClass (nomSc req) g.sc = true)
    (hLgSc : MmapThresholdReq < req → g.sc = 63)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = mbase 9 + miOff_enframe_c4) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = g.slotStart idx) (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off)
    (hx2 : s.readReg64 (.gpr 2#5) = g.storage) (hx4 : s.readReg64 (.gpr 4#5) = 0#64)
    (hx6 : s.readReg64 (.gpr 6#5) = g.slotEnd idx) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
        MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf))
      oom := by
  rw [mallocngBlockProg_eq_b09]
  have hb : BlkBase 9 (mbase 9) := rfl
  generalize mbase 9 = b at hpc hb ⊢
  have hgw := hwf1.groups_wf g hg
  have hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hgw.2.2.2.2.2.2.1
  obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
  obtain ⟨hIdxCnt, _, hStartNat, _, hEndNat, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hIdx31 : idx ≤ 31 := by have := hgw.2.1; dsimp [GroupDesc.cnt] at hIdxCnt; omega
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let start := g.slotStart idx
  let p := start + BitVec.ofNat 64 (16 * off)
  let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
  let totOff16 := (p.toNat - g.storage.toNat) / 16
  let res := (g.slotEnd idx).toNat - (p.toNat + req)
  have hStartEq : start.toNat = g.mem.toNat + 16 + idx * g.stride := hStartNat
  have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
  have hFit4 : 16 * off + 4 ≤ g.stride :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_add_right _ req) hFit) 4)
      (Nat.le_of_eq (Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_left 4 req) hFit0)))
  have hPNat : p.toNat = start.toNat + 16 * off := bv64_add_toNat (by omega)
  have hResEq : res = g.stride - 4 - (16 * off + req) := by dsimp only [res]; omega
  obtain ⟨hBs1L, hBs2L, hBs3L, hNewL, hBs3Idx, hB0, hBP4, hBP3, hBP2, hBR1, hBR5, hZeroU⟩ :=
    enframe_slotBytes_props hgw hIdx hClaimed hOff255 hFit hZeroMm
  obtain ⟨hBlkWf, hFresh, hPOffLe, hSc24_26, hwf2, hg'Mem, hCntEq, hDynEq, hExtSlot, hAbsSlot, hPnEq, hMpEq⟩ :=
    enframeClaimed_absorb (b := bud) hwf1 hg hIdx hClaimed hReqMax hOff255 hFit hSc2 hSc24 hSc63
      hNewL hB0 hBP4 hBP3 hBP2 hBR1 hBR5
  obtain ⟨hSlackLt, _, _, _, _, _, hOffProps⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
  have hResLt : res < 1048576 :=
    Nat.lt_of_le_of_lt (by rw [hResEq]; exact Nat.sub_le_sub_left (Nat.le_add_left _ _) _) hSlackLt
  obtain ⟨hOffSE, _, hPS4, _, _, _, hSub32, _, hNegAddr, hSle4, _, _, hR5Or⟩ := hOffProps off hOff255 hFit
  have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
  let liveMap' : MallocngLiveMap := st1.liveMap.insert p req 0
  let newSlotBs := ByteSlice.write8 (enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res)
    (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
  let val' := writeBytesToMap st1.byteVal (start - 4#64) newSlotBs
  let rwTail := ByteMap st1.masterDom
    (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
  let coreStatic := (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1)
  let envTail := stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
    MallocngBlockTokenK γ p req 0 ∗ MallocngLiveAuth γ liveMap' ∗ coreStatic ∗ rwTail
  dsimp only [MallocngCoreStInflightModeA]
  rw [hExtSlot, hExtMeta]
  wp_conv_pre => simp only [hwf1, pure_true, emp_sepConj]
  refine sepWP_bupd_focus (mallocngBlockK_alloc_bupd γ st1.liveMap p req 0 hBlkWf hFresh) (h := ?_)
  have hPre1 : ((MallocngLiveAuth γ liveMap' ∗ MallocngBlockTokenK γ p req 0) ∗
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
      (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
      ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1) ∗ MallocngRuntime maddrs tp) =
      (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) := by
    dsimp only [envTail, coreStatic]
    generalize MallocngBlockTokenK γ p req 0 = tok, (MallocngLiveAuth γ liveMap') = gm,
      ((start - 4#64) ↦ₛ slotBs) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA, rwTail = rT,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = lbA, MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pnA,
      MappedSet st1.masterDom (OwnedMappedByte st1) = mpA
    ac_rfl
  rw [hPre1]
  refine SepWP.seq_entails_emp
    (enframe_step1 hb hFit0 hFit hOff255 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
      (by rw [(metaBytes_ops g 0 0#32 .claimed).1]; rfl) hOffSE hpc hrun hsp hProc hcsHi
      hx0 hx1 hx2 hx4 hx6 hx20 hx22 hx23) ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx0_1, hx2_1, hx4_1, hx6_1, hx20_1, hx23_1⟩
  have hPre2 : (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) =
      (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB1 slotBs off) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre2]
  refine SepWP.seq_entails_emp
    (enframe_step2 hb hFit0 hFit hIdx31 hResEq hResLt hBs1L hBs2L hBs3L hBs3Idx
      hPS4 hSub32 hNegAddr hSle4 hpc1 hrun1 hProc1 hcs1 hx0_1 hx2_1 hx4_1 hx6_1 hx20_1 hx23_1) ?_
  rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx4_2⟩
  have hPre3 : (((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) = sA,
      (g.metaPtr ↦ₛ g.metaBytes) = mA, MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre3]
  refine SepWP.mono
    (enframe_step3 hb hFit4 hIdx31 hBs3L hR5Or hpc2 hrun2 (hsp2.trans hsp1) hsp_align
      hProc2 hcs2 hx0_2 hx1_2 hx4_2) ?_
  rintro sf P_f _ _ ⟨hsf_sp, hsf_brk, hsf_perm, hsf_proc, hsf_cs, hsf_x0, hPf⟩
  have hBrkEq : sf.brk = s.brk := hsf_brk.trans (hbrk2.trans hbrk1)
  have hPermEq : sf.mem.perm = s.mem.perm := hsf_perm.trans (hperm2.trans hperm1)
  refine ⟨hsf_sp, hBrkEq, hPermEq, hsf_proc, hsf_cs, Entails.trans hPf ?_⟩
  let effCost := max req MallocngMinBlockCost
  let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
  let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
  let bf := mallocngAllocBudget true req bud
  have hReasm : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      ((MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624) ∗
       (MallocngRoTablesA maddrs ∗
        (MallocngLiveAuth γ st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
         (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st2.auxvPtr ∗
         MallocngAuxvStateRo ro γ st2.auxvPtr st2.auxvSnap ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
         ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
         MappedSet st2.masterDom (OwnedMappedByte st2)) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ readBytesFromMap val' p req) ∗ MallocngBlockTokenK γ p req 0)) := by
    have hM1 : ((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail) =
        (p ↦ₛ readBytesFromMap val' p req) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by
      dsimp only [rwTail]; rw [← hExtMeta]; exact hAbsSlot
    have hLAdj : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
        (((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail)) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
         MallocngBlockTokenK γ p req 0 ∗ MallocngLiveAuth γ liveMap' ∗ coreStatic) := by
      dsimp only [envTail]
      generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, ((start - 4#64) ↦ₛ newSlotBs) = nA,
        (g.metaPtr ↦ₛ g.metaBytes) = mA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
        MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
        MallocngBlockTokenK γ p req 0 = tok, MallocngLiveAuth γ liveMap' = gm, coreStatic = cS, rwTail = rT
      ac_rfl
    have hSt2F : st2.liveMap = liveMap' ∧ st2.ctx = st1.ctx ∧ st2.auxvPtr = st1.auxvPtr ∧ st2.auxvSnap = st1.auxvSnap := ⟨rfl, rfl, rfl, rfl⟩
    rw [hLAdj, hM1]; dsimp only [coreStatic]
    rw [hPnEq, hMpEq, hSt2F.1, hSt2F.2.1, hSt2F.2.2.1, hSt2F.2.2.2]
    generalize (p ↦ₛ readBytesFromMap val' p req) = uA,
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal = rw2A,
      (MallocngLiveAuth γ liveMap') = gm, MallocngBlockTokenK γ p req 0 = tok,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = lbA, MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal = pnA,
      MappedSet st2.masterDom (OwnedMappedByte st2) = mpA
    ac_rfl
  rw [hReasm]; unfold mallocImplFineSuccessBody
  refine sepConj_mono (savedRegs_entails_stackFrame s0) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  refine Entails.trans ?_ (Entails.sepExists_intro (readBytesFromMap val' p req))
  refine Entails.trans ?_ (Entails.sepExists_intro st2)
  refine Entails.trans ?_ (Entails.sepExists_intro bf)
  have hNoOrph2 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem :=
    mallocngNoOrphanMappings_congr_perm rfl hDynEq rfl hPermEq hNoOrph1
  have hCountIvs2 : MallocngCountIvsWF bf (dynamicRootRegions st2) st2 :=
    mallocngCountIvsWF_after_alloc hCount0 (hCntEq.trans (congrArg (· + 1) hCnt1)) hMetaLe1 hwf2
      (hGrp1.map_ite g.metaPtr fun hm hs => hGrp1 g hg hm hs)
  have hSc24_22 : g'.sc = 24 → nominalSlotCap 22 < req := by
    have h2 := (sc24_props_of_coarse hSc2 hSc24).2
    simpa [g', mkReplaceSlotGroup] using h2
  have hPreRel : FinePreEnframeRel bL bP req p st2 g' idx :=
    ⟨st1, g, hFine1, hwf1.groups_nodup.1, hg, hIdx, hClaimed, hSmAllow, hLgSc,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hPure : sf.readReg64 .x0 = p ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
      MallocngBlockWf p req ∧ (readBytesFromMap val' p req).length = req ∧
      MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem ∧
      MallocngCountIvsWF bf (dynamicRootRegions st2) st2 ∧
      ∃ g' ∈ st2.groups, ∃ idx' : Nat, ∃ hIdx' : idx' < g'.slots.length,
        g'.slots[idx']'hIdx' = .liveUser p req effCost ∧
        p.toNat - (g'.slotStart idx').toNat ≤ 255 * 16 ∧
        (g'.isMmapped = true → readBytesFromMap val' p req = List.replicate req 0#8) ∧
        (24 ≤ g'.sc ∧ g'.sc ≤ 26 → nominalSlotCap 23 < req) ∧
        (g'.sc = 24 → nominalSlotCap 22 < req) ∧
        (g'.sc = 63 → g'.maplen * 4096 ≤ req + 4115) ∧
        FinePreEnframeRel bL bP req p st2 g' idx' :=
    ⟨hsf_x0, hsf_proc.2.2.1.trans htp0, hsf_proc.2.2.2.1.trans hbrkS0, hBlkWf,
      readBytesFromMap_length .., hNoOrph2, hCountIvs2, g', hg'Mem, idx,
      by simpa [g', mkReplaceSlotGroup] using hIdx,
      by simp [g', mkReplaceSlotGroup], hPOffLe, hZeroU, hSc24_26, hSc24_22,
      by simpa [g', mkReplaceSlotGroup] using hSc63_4115, hPreRel⟩
  have hCoreEq : MallocngCoreStModeA ro γ maddrs brkStart sf.brk bf.liveCost bf.peakCost st2 =
      (MallocngLiveAuth γ st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st2.auxvPtr ∗
       MallocngAuxvStateRo ro γ st2.auxvPtr st2.auxvSnap ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
       ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
       MappedSet st2.masterDom (OwnedMappedByte st2)) := by
    have hwf2' : MallocngWFInflight 0 maddrs.base brkStart s.brk bf.liveCost bf.peakCost st2 := hwf2
    rw [hBrkEq]; dsimp only [MallocngCoreStModeA, MallocngCoreStInflightModeA]
    rw [propext ⟨fun _ => trivial, fun _ => hwf2'⟩, pure_true, emp_sepConj]
  rw [propext ⟨fun _ => trivial, fun _ => hPure⟩, pure_true, emp_sepConj, hCoreEq]
  exact Entails.refl _

set_option maxHeartbeats 400000 in
private theorem mallocImpl_join_epilogue_fine [MallocngMultiPlacement] {ro : Bool}
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req idx stepB : Nat} {cycVal : BitVec 64}
    {st0 st1 : MallocngSt} {g : GroupDesc} {s0 s : State} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0) (hCnt1 : totalLiveCount st1 = totalLiveCount st0)
    (hMetaLe1 : st1.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101)
    (hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hFine1 : FineSplitInv bL bP st1) (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize) (hFit0 : req + 4 ≤ g.stride)
    (hSmAllow : req ≤ MmapThresholdReq → g.sc < 48 ∧ allowedPhysClass (nomSc req) g.sc = true)
    (hLgSc : MmapThresholdReq < req → g.sc = 63)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hDelta : MallocngMappedDelta 16 stepB s0.mem s.mem)
    (hpc : s.pc = mbase 9 + miOff_call_unlock) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = maddrs.lock) (hx19 : s.readReg64 (.gpr 19#5) = cycVal)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr) (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta 16 stepB s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  refine SepWP.mono (oom := fun _ => ⌜False⌝) (post := fun sf P_f =>
    sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
    MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf)) ?_ ?_
  · have hgw := hwf1.groups_wf g hg
    obtain ⟨hStrPos, _⟩ := group_stride_pos_and_align hgw
    obtain ⟨hTst0, hZ, hNZ⟩ := getStride_props hgw
    obtain ⟨_, hStrSubReq, hStrSub4, hShr4, hMadd, hW1Fit, _⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
    have hSlot0 : ((readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride)[0]?).getD 0#8 = 0#8 := by
      have hSW := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
      have h0lt : 0 < (readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride).length := by
        rw [readBytesFromMap_length]; omega
      rw [List.getElem?_eq_getElem h0lt, Option.getD_some, readBytesFromMap_getElem _ _ _ 0 h0lt]
      simpa using hSW.1
    obtain ⟨hMemMeta, _, _, _, _, hPkMeta, _⟩ := metaBytes_ops g 0 0#32 .claimed
    have hExtSlot := slot_extract hwf1 hNoRes hg hIdx hClaimed
    have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
    let start := g.slotStart idx
    let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
    let rwTail := ByteMap st1.masterDom
      (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
    let roTail := (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
      (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗ (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
      (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)
    let coreRest := MallocngLiveAuth γ st1.liveMap ∗ (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
      (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗
      MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1)
    let unlockFrame := MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail ∗ ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      coreRest ∗ MallocngRuntime maddrs tp
    have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail) := rfl
    have hPreInit : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
        MallocngRuntime maddrs tp) = ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) := by
      rw [hRoSplit]; dsimp only [MallocngCoreStInflightModeA, unlockFrame, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx, (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp, (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, MallocngLiveAuth γ st1.liveMap = pGm, MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreInit]
    have hSpAl : s.spAligned = true := by dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
    wp_step
    have hunlock := VerifiedLibraries.Mallocng.Proofs.placed_unlockNoop_perm_ok
      (P := blkPC_b09.rebase b (fun _ => none)) maddrs.lock
    rw [at_bl_target_b09 hb 23 miOff_call_unlock] at hunlock
    refine SepWP.call_subroutine_frame (F := unlockFrame) (x := ()) (ret_pc := b + miOff_after_unlock)
      hunlock rfl (by simp [arm64_norm, hrun]) (by simpa [State.spAligned, arm64_norm] using hSpAl)
      (by dsimp only [miOff_call_unlock, miOff_after_unlock, Reg.lr]; simp [arm64_norm])
      (fun R' hm => by
        rw [sepConj_assoc] at hm; refine Satisfies.mono (sepConj_mono_left ?_) hm
        dsimp only [withCL]; rw [sepConj_comm]
        exact Entails.pure_right hcl (Entails.pure_right (by simpa [arm64_norm] using hx0) (Entails.refl _)))
      (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
      (fun su hpc_u hrun_u hsp_u hcs_u => ?_)
      (fun R' sf _ ho => by dsimp only [withCL] at ho; exact False.elim (not_satisfies_false_sepConj ho))
    dsimp only [withCL]; rw [sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProc_u0, hbrk_u, hperm_u⟩
    apply SepWP.weaken_pre (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl unlockFrame))
    have hProc_u : MallocngProcPreserved s su :=
      ⟨hProc_u0.1, hProc_u0.2.1, hProc_u0.2.2.1, hProc_u0.2.2.2.1,
       hProc_u0.2.2.2.2.1, hProc_u0.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_writeReg64] using hProc_u0.2.2.2.2.2.2⟩
    have hsp_su : su.sp = s0.sp - 80#64 := hsp_u.trans hsp
    have hProc_su : MallocngProcPreserved s0 su := procPres_trans hProc hProc_u
    have hcs_su : MallocImplUntouchedCS s0 su :=
      untouchedCS_step hcsHi (hcs_u.2.2.2.2.2.2.2.1.trans (by simp))
        (hcs_u.2.2.2.2.2.2.2.2.1.trans (by simp)) (hcs_u.2.2.2.2.2.2.2.2.2.1.trans (by simp))
        (by simpa [calleeSavedVRegs] using hcs_u.2.2.2.2.2.2.2.2.2.2.2)
    have hPreG : ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
         (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) := by
      dsimp only [unlockFrame]
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreG]
    refine SepWP.seq_entails_emp
      (getStride_step hb (by simp [GroupDesc.metaBytes]) hPkMeta hTst0
        (fun h => ⟨(hZ h).2.1, (hZ h).2.2⟩) hNZ hpc_u hrun_u hsp_su hProc_su hcs_su
        (hcs_u.1.trans (by simpa using hx19)) (hcs_u.2.1.trans (by simpa using hx20))
        (hcs_u.2.2.1.trans (by simpa using hx21)) (hcs_u.2.2.2.1.trans (by simpa using hx22))
        (hcs_u.2.2.2.2.1.trans (by simpa using hx23))) ?_
    rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    have hPreH : ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
        (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) =
        (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
         ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) := by
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreH]
    refine SepWP.seq_entails_emp
      (enframe_head_step hb hFit0 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
        (by rw [hMemMeta]; rfl) hSlot0 hStrSubReq hStrSub4 hMadd
        hpc1 hrun1 hsp1 hProc1 hcs1 hx4_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1) ?_
    rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx20_2, hx22_2, hx23_2⟩
    refine SepWP.seq_entails_emp
      (enframe_mask_step hb hShr4 hW1Fit hpc2 hrun2 hsp2 hProc2 hcs2
        hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 hx5_2 hx6_2 hx20_2 hx22_2 hx23_2) ?_
    rintro s3 hpc3 hrun3 ⟨off, hOff255, hFit, hsp3, hbrk3, hperm3, hProc3, hcs3, hx0_3, hx1_3, hx2_3, hx4_3, hx6_3, hx20_3, hx22_3, hx23_3⟩
    have hBrk3 : s3.brk = s.brk := hbrk3.trans (hbrk2.trans (hbrk1.trans hbrk_u))
    have hPerm3 : s3.mem.perm = s.mem.perm := hperm3.trans (hperm2.trans (hperm1.trans hperm_u))
    have hwf3 : MallocngWFInflight 1 maddrs.base brkStart s3.brk bud.liveCost bud.peakCost st1 := hBrk3 ▸ hwf1
    have hNoOrph3 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s3.mem :=
      mallocngNoOrphanMappings_congr_perm rfl rfl rfl hPerm3 hNoOrph1
    have hPreF : (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ coreRest ∗ MallocngRuntime maddrs tp)) =
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s3.brk bud.liveCost bud.peakCost st1 ∗
         MallocngRuntime maddrs tp) := by
      rw [hRoSplit]; dsimp only [MallocngCoreStInflightModeA, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf3⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx, (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp, (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, MallocngLiveAuth γ st1.liveMap = pGm, MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreF]; subst hb_eq; rw [← mallocngBlockProg_eq_b09]
    exact SepWP.mono (mallocImpl_enframe_finish_fine hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph3 hwf3 hFine1 hNoRes
      hg hIdx hClaimed hReqMax hFit0 hOff255 hFit hSmAllow hLgSc hSc2 hSc24 hSc63 hSc63_4115 hZeroMm htp0 hbrkS0
      hpc3 hrun3 hsp3 hsp_align hProc3 hcs3 hx0_3 hx1_3 hx2_3 hx4_3 hx6_3 hx20_3 hx22_3 hx23_3)
      (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.trans hBrk3, h3.trans hPerm3, h4, h5, h6⟩)
  · rintro sf P_f _ _ ⟨hsf_sp, _, hsf_perm, hsf_proc, hsf_cs, hPf⟩
    refine ⟨Entails.trans hPf (Entails.pure_right ⟨hsf_proc, mappedDelta_congr_perm_right hDelta hsf_perm⟩
      (Entails.refl _)), hsf_sp, hsf_cs⟩

/-! ## 2. OOM & Large `mmap` Fine Path (`131051 < req ≤ MallocngMaxAllocSize`) -/

private theorem stepOom_of_mmap_large [MallocngMultiPlacement]
    {maxMeta req len : Nat} {s0 s_pre sf : State}
    (hLenLo : 4096 ≤ len) (hLenMod : len % 4096 = 0) (hLen4115 : len ≤ req + 4115)
    (hProc : MallocngProcPreserved s0 s_pre) (hPerm0 : s_pre.mem.perm = s0.mem.perm)
    (hoom : sf.fs = s_pre.fs ∧ sf.trace = s_pre.trace ∧ sf.sigActions = s_pre.sigActions ∧
      sf.mem.perm = s_pre.mem.perm ∧ MallocngMappedDelta 0 0 s_pre.mem sf.mem ∧
      (MallocngSanitizedSvc msvc → MallocngNoGapOrPhys sf len)) :
    MallocngStepOomCond msvc (FineStepBound maxMeta req) s0 sf := by
  obtain ⟨hfs, htr, hsig, hperm_f, _, hgap⟩ := hoom
  have hPermF : sf.mem.perm = s0.mem.perm := hperm_f.trans hPerm0
  have hd0 : MallocngMappedDelta 0 0 s0.mem sf.mem :=
    ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPermF ▸ ha)⟩
  have hBound : len ≤ FineStepBound maxMeta req := by
    have := fineStepBound_large_le maxMeta len req (by omega)
    omega
  exact placedOomCond_to_stepOomCond (Nat.le_refl 16) (Nat.le_refl _)
    (MallocngPlacedOomCond.of_delta
      (hfs.trans hProc.1) (htr.trans hProc.2.1) (hsig.trans hProc.2.2.2.2.2.2)
      hd0 (Nat.zero_le 16) (Nat.zero_le _)
      (fun hSan => ⟨len, hLenLo, hLenMod, by omega, hgap hSan⟩))

private theorem stepOom_of_allocMeta_after_mmap [MallocngMultiPlacement]
    {maxMeta req len : Nat} {s0 s_pre sf : State}
    (hLen4115 : len ≤ req + 4115)
    (hProc : MallocngProcPreserved s0 s_pre)
    (hDelta : MallocngMappedDelta 1 len s0.mem s_pre.mem)
    (hoom : MallocngPlacedOomCond msvc 1 (FineMetaStep maxMeta) s_pre sf) :
    MallocngStepOomCond msvc (FineStepBound maxMeta req) s0 sf := by
  have hApp := MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hDelta hoom
  have hBound : len + FineMetaStep maxMeta ≤ FineStepBound maxMeta req := by
    have := fineStepBound_large_le maxMeta len req (by omega)
    omega
  exact placedOomCond_to_stepOomCond (by decide : 1 + 1 ≤ 16) hBound hApp

private theorem stepOom_of_allocSlot_fine [MallocngMultiPlacement]
    {maxMeta req sc : Nat} {s0 s_pre sf : State}
    (hSc48 : sc < 48)
    (hProc : MallocngProcPreserved s0 s_pre)
    (hPerm0 : s_pre.mem.perm = s0.mem.perm)
    (hoom : MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
      ((allocSlotDepthBound sc + 1) * FineMetaStep maxMeta + 1048576) s_pre sf) :
    MallocngStepOomCond msvc (FineStepBound maxMeta req) s0 sf := by
  have hd0 : MallocngMappedDelta 0 0 s0.mem s_pre.mem :=
    ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPerm0 ▸ ha)⟩
  have hApp := MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hd0 hoom
  have hdLe : allocSlotDepthBound sc ≤ 3 := allocSlotDepthBound_le_three sc
  have hBound := fineStepBound_slot_le maxMeta req sc hSc48
  exact placedOomCond_to_stepOomCond (by omega) (by rw [Nat.zero_add]; exact hBound) hApp

@[simp, arm64_norm, wp_norm]
private theorem pageOf_add_zext_lo12Of_fine (T : BitVec 64) :
    pageOf T + BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = T := by
  have h : BitVec.zeroExtend 64 ((lo12Of T).truncate 12) = lo12Of T := by
    unfold lo12Of; bv_bits
  rw [h, pageOf_add_lo12Of]

private theorem ctxBytes_length_fine (c : CtxFields)
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (hPad : c.seqPad.length = 7) :
    c.toBytes.length = 928 := by
  obtain ⟨hPre, hSuf, hEq, _⟩ := ctxBytes_seq_split hAct hUse hUnm hBnc hPad
  have h := congrArg List.length hEq
  simp only [List.length_append, List.length_singleton] at hPre hSuf h
  omega

private theorem extract_fresh_mmap_disjoint_A_fine [MallocngMultiPlacement] {ro : Bool}
    {prog : Program} {target_pc : BitVec 64} {s : State} {oom : State → SepProp}
    {post : State → SepProp → Prop}
    {inflight : Nat} {γ : GhostName} {brkStart mb : BitVec 64}
    {liveCost peakCost len : Nat} {st1 : MallocngSt} {Rest : SepProp}
    (hMbAl : mb.toNat % 4096 = 0) (hLenAl : len % 4096 = 0)
    (hLenPos : 4096 ≤ len) (hMbBound : mb.toNat + len ≤ 2 ^ 48)
    (hk : (∀ r ∈ dynamicRootRegions st1, DisjointRegions r.1 r.2 mb len) →
      SepWP prog target_pc s
        ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
         MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ Rest)
        post oom) :
    SepWP prog target_pc s
      ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ Rest)
      post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨
      (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
      MallocngCoreStInflightModeA ro inflight γ maddrs brkStart s.brk liveCost peakCost st1 ∗ (Rest ∗ R) := by
    simpa [sepConj_assoc] using hm
  exact SepWP.to_reaches_pc (hk (fresh_mmap_disjoint_mode_A hm' hMbAl hLenAl hLenPos hMbBound)) hm

private theorem unmapSeq_loop_bv_fine (ctx : BitVec 64) (k : Nat) :
    (ctx + BitVec.ofNat 64 (848 + k)) + 1#64 = ctx + BitVec.ofNat 64 (848 + (k + 1)) ∧
    BitVec.ofNat 64 (848 + k) + 1#64 = BitVec.ofNat 64 (848 + (k + 1)) ∧
    (k + 1 < 32 → 880#64 ≠ BitVec.ofNat 64 (848 + (k + 1))) ∧
    (k + 1 = 32 → 880#64 = BitVec.ofNat 64 (848 + (k + 1))) := by
  refine ⟨by bv_omega, by bv_omega, fun _ => by bv_omega, fun heq => ?_⟩
  have hk : k = 31 := by omega
  subst hk; bv_omega

set_option maxHeartbeats 400000 in
private theorem unmapSeq_zero_loop_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 : State} {mb : BitVec 64} {req : Nat} {oom : State → SepProp}
    (tail : List (BitVec 8)) :
    ∀ {k : Nat} {s : State} {F : SepProp},
      k + tail.length = 32 → 1 ≤ tail.length →
      s.pc = b + miOff_seq_zero_loop → s.status = .Running → s.sp = s0.sp - 80#64 →
      MallocngProcPreserved s0 s → MallocImplUntouchedCS s0 s →
      s.readReg64 (.gpr 1#5) = maddrs.ctx + BitVec.ofNat 64 (848 + k) →
      s.readReg64 (.gpr 2#5) = maddrs.ctx + 880#64 →
      s.readReg64 (.gpr 19#5) = mb →
      s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req →
      s.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_seq_zero_mov1) s
        (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦ₛ tail) ∗ F)
        (fun s1 P1 =>
          (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
           MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
           s1.readReg64 (.gpr 0#5) = maddrs.ctx ∧
           s1.readReg64 (.gpr 19#5) = mb ∧
           s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
           s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
           s1.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
          (P1 ⊢ ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦ₛ List.replicate tail.length 0#8) ∗ F))
        oom := by
  have _ := hb
  induction tail with
  | nil => intro _ _ _ _ hPos; simp at hPos
  | cons b0 tail' ih =>
    intro k s F hk _ hpc hrun hsp hProc hcs hx1 hx2 hx19 hx20 hx24 hx25
    dsimp only [miOff_seq_zero_loop, miOff_seq_zero_mov1] at hpc ⊢
    obtain ⟨hPtrNext, hPtrOff, hNeLt, hEq32⟩ := unmapSeq_loop_bv_fine maddrs.ctx k
    rw [pointsToBytes_cons, sepConj_assoc]
    wp_str8_perm m1 hm1
    wp_steps 2
    rcases tail' with _ | ⟨b1, rest⟩
    · simp only [List.length_singleton] at hk
      have hEq := hEq32 hk
      wp_if hBr
      · exact False.elim (hBr (by simpa [hx2, hPtrOff] using hEq))
      · wp_step
        apply SepWP.done
        · simp only [arm64_norm]
        · exact hrun
        · refine ⟨⟨by simpa using hsp, rfl, hm1,
            by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
            untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
            by simp, by simp [hx19], by simp [hx20], by simp [hx24], by simp [hx25]⟩, ?_⟩
          simp only [List.length_singleton, List.replicate_succ, List.replicate_zero,
            pointsToBytes_cons, pointsToBytes_nil, sepConj_assoc]
          exact Entails.refl _
    · simp only [List.length_cons] at hk
      have hNe := hNeLt (by omega)
      wp_if hBr
      · rw [hPtrNext]
        have hFrameSwap :
            (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) ∗
             (((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) ∗ F)) =
            (((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) ∗
             (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) ∗ F)) := by
          generalize ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) = p0,
            ((maddrs.ctx + BitVec.ofNat 64 (848 + (k + 1))) ↦ₛ (b1 :: rest)) = p1
          ac_rfl
        rw [hFrameSwap]
        refine SepWP.mono
          (ih (k := k + 1) (by simp only [List.length_cons]; omega) (by simp)
            (by simp only [arm64_norm]) hrun (by simpa using hsp)
            (by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc])
            (untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
            (by simp) (by simp [hx2]) (by simp [hx19]) (by simp [hx20])
            (by simp [hx24]) (by simp [hx25])) ?_
        rintro s2 P2 _ _ ⟨⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx19_2, hx20_2, hx24_2, hx25_2⟩, hP2⟩
        refine ⟨⟨hsp2, hbrk2, hperm2.trans hm1, hProc2, hcs2, hx0_2, hx19_2, hx20_2, hx24_2, hx25_2⟩,
          Entails.trans hP2 ?_⟩
        simp only [List.length_cons, List.replicate_succ, pointsToBytes_cons, ← hPtrNext]
        exact Entails.of_eq (by
          generalize ((maddrs.ctx + BitVec.ofNat 64 (848 + k)) ↦₈ 0#8) = p0,
            (((maddrs.ctx + BitVec.ofNat 64 (848 + k)) + 1#64) ↦ₛ List.replicate (rest.length + 1) 0#8) = p1
          ac_rfl)
      · exact False.elim (hNe (by simpa [hx2, hPtrOff] using hBr))

private theorem seq_bv_helpers_fine :
    (∀ mb : BitVec 64, mb ≠ BitVec.allOnes 64 → mb + 1#64 ≠ 0#64) ∧
    (∀ b8 : BitVec 8, (BitVec.zeroExtend 32 b8 == 0xff#32) = (b8 == 0xff#8)) ∧
    (∀ b8 : BitVec 8, BitVec.truncate 8 (BitVec.zeroExtend 32 b8 + 1#32) = b8 + 1#8) := by
  refine ⟨fun mb hne heq => hne ?_, fun b8 => by bv_bits, fun b8 => by bv_bits⟩
  apply BitVec.eq_of_toNat_eq
  have hlt := mb.isLt
  have h0 : (mb + 1#64).toNat = 0 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_allOnes] at h0 ⊢
  omega

set_option maxHeartbeats 400000 in
private theorem mallocImpl_large_seq_prep_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {mb : BitVec 64} {req : Nat}
    {c : CtxFields} {oom : State → SepProp}
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (hPad : c.seqPad.length = 7)
    (hMbNe1 : mb ≠ BitVec.allOnes 64)
    (hpc : s.pc = b + miOff_after_mmap) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = mb) (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    let c' := if c.seq = 0xff#8 then { c with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
              else { c with seq := c.seq + 1#8 }
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_call_alloc_meta) s
      ((maddrs.ctx ↦ₛ c.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 19#5) = mb ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
         s1.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) ∧
        (P1 ⊢ (maddrs.ctx ↦ₛ c'.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F))
      oom := by
  intro c'
  have _ := hb
  obtain ⟨hCmnNe, _, hAdd1⟩ := seq_bv_helpers_fine
  have hCtxOps := ctxBytes_ops c hAct hUse hUnm hBnc hPad
  have hCtxLen : c.toBytes.length = 928 := ctxBytes_length_fine c hAct hUse hUnm hBnc hPad
  have hGetSeq : c.toBytes.getD 912 0#8 = c.seq := hCtxOps.2.2.2.2.1
  have hGetSeqOpt : c.toBytes[912]?.getD 0#8 = c.seq := by
    simpa only [List.getD_eq_getElem?_getD] using hGetSeq
  have hWriteInc : ByteSlice.write8 c.toBytes 912 (c.seq + 1#8) =
      ({ c with seq := c.seq + 1#8 }).toBytes := hCtxOps.2.2.2.2.2 (c.seq + 1#8)
  generalize hCtxBs : c.toBytes = ctxBs at hCtxLen hGetSeq hGetSeqOpt hWriteInc ⊢
  dsimp only [miOff_after_mmap, miOff_call_alloc_meta] at hpc ⊢
  wp_steps
  wp_if hCmn
  · exact False.elim (hCmnNe mb hMbNe1 (by simpa [hx0] using hCmn))
  wp_steps
  wp_if hSeqFF
  · have hSeqEq : c.seq = 0xff#8 := by revert hSeqFF; bv_bits
    dsimp only [c']
    simp only [hSeqEq, ↓reduceIte]
    wp_steps 2
    obtain ⟨hPreLen, hSufLen, hSplitEq, hRejoin⟩ := ctxBytes_seq_split hAct hUse hUnm hBnc hPad
    let pre848 := unpack64 c.secret ++ unpack32 c.initDone ++ unpack32 c.mmapCounter ++
      unpack64 c.freeMetaHead ++ unpack64 c.availMeta ++ unpack64 c.availMetaCount ++
      unpack64 c.availMetaAreaCount ++ unpack64 c.metaAllocShift ++ unpack64 c.metaAreaHead ++
      unpack64 c.metaAreaTail ++ unpack64 c.availMetaAreas ++
      c.active.flatMap unpack64 ++ c.usageByClass.flatMap unpack64
    let suf15 := c.seqPad ++ unpack64 c.brk
    let rest48 := c.bounces ++ [c.seq] ++ suf15
    have hCtxSplit :
        (maddrs.ctx ↦ₛ ctxBs) =
          (((maddrs.ctx + BitVec.ofNat 64 (848 + 0)) ↦ₛ c.unmapSeq) ∗
           ((maddrs.ctx ↦ₛ pre848) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48))) := by
      have hAssoc : ctxBs = pre848 ++ (c.unmapSeq ++ rest48) := by
        rw [← hCtxBs]; simpa [pre848, rest48, suf15, List.append_assoc] using hSplitEq
      rw [hAssoc, pointsToBytes_append, hPreLen,
          pointsToBytes_append_off maddrs.ctx 848 880 c.unmapSeq rest48 (by omega)]
      dsimp only [Nat.add_zero]
      generalize (maddrs.ctx ↦ₛ pre848) = pPre,
        ((maddrs.ctx + 848#64) ↦ₛ c.unmapSeq) = pUnm,
        ((maddrs.ctx + 880#64) ↦ₛ rest48) = pRest
      ac_rfl
    rw [hCtxSplit, sepConj_assoc, sepConj_assoc]
    refine SepWP.seq_entails_emp
      (unmapSeq_zero_loop_fine (s0 := s0) (mb := mb) (req := req) hb c.unmapSeq (k := 0)
        (by omega) (by omega)
        (by dsimp only [miOff_seq_zero_loop]; simp only [arm64_norm]; try bv_lin) hrun (by simpa using hsp)
        (by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc])
        (untouchedCS_step hcs (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [calleeSavedVRegs]))
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hx20) (by simp [arm64_norm]) (by simp [arm64_norm])) ?_
    rintro sL hpcL hrunL ⟨hspL, hbrkL, hpermL, hProcL, hcsL, hx0L, hx19L, hx20L, hx24L, hx25L⟩
    dsimp only [miOff_seq_zero_mov1] at hpcL
    let cZero := { c with unmapSeq := List.replicate 32 0#8, seq := c.seq }
    have hCtxRejoin :
        (((maddrs.ctx + BitVec.ofNat 64 (848 + 0)) ↦ₛ List.replicate c.unmapSeq.length 0#8) ∗
         ((maddrs.ctx ↦ₛ pre848) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48) ∗
          (((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F))) =
        ((maddrs.ctx ↦ₛ cZero.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ F) := by
      rw [hUnm]
      have hZeroBytes : cZero.toBytes = pre848 ++ (List.replicate 32 0#8 ++ rest48) := by
        have h1 := (hRejoin c.seq (List.replicate 32 0#8)).symm
        simpa [cZero, pre848, rest48, suf15, List.append_assoc] using h1
      have hSplit2 :
          (maddrs.ctx ↦ₛ cZero.toBytes) =
            ((maddrs.ctx ↦ₛ pre848) ∗
             (((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) ∗ ((maddrs.ctx + 880#64) ↦ₛ rest48))) := by
        rw [hZeroBytes, pointsToBytes_append, hPreLen,
            pointsToBytes_append_off maddrs.ctx 848 880 (List.replicate 32 0#8) rest48 (by simp)]
      rw [hSplit2]; dsimp only [Nat.add_zero]
      generalize (maddrs.ctx ↦ₛ pre848) = pPre,
        ((maddrs.ctx + 848#64) ↦ₛ List.replicate 32 0#8) = pUnm,
        ((maddrs.ctx + 880#64) ↦ₛ rest48) = pRest,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pLb
      ac_rfl
    rw [hCtxRejoin]
    have hOpsZero := ctxBytes_ops cZero hAct hUse (by simp [cZero]) hBnc hPad
    have hZeroLen : cZero.toBytes.length = 928 :=
      ctxBytes_length_fine cZero hAct hUse (by simp [cZero]) hBnc hPad
    have hWrite1 : ByteSlice.write8 cZero.toBytes 912 1#8 =
        ({ c with unmapSeq := List.replicate 32 0#8, seq := 1#8 }).toBytes := hOpsZero.2.2.2.2.2 1#8
    generalize hZeroBs : cZero.toBytes = zeroBs at hZeroLen hWrite1 ⊢
    wp_step; wp_str8_perm mS hmS; wp_step
    apply SepWP.done
    · simp only [arm64_norm]; try bv_lin
    · exact hrunL
    · refine ⟨⟨by simpa using hspL, hbrkL, hmS.trans hpermL,
        by dsimp only [MallocngProcPreserved] at hProcL ⊢; simp [arm64_norm, hProcL],
        untouchedCS_step hcsL (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [hx19L], by simp [hx20L], by simp [hx24L], by simp [hx25L]⟩, ?_⟩
      simpa [hWrite1] using Entails.refl _
  · have hSeqNe : c.seq ≠ 0xff#8 := by intro hEq; rw [hEq] at hSeqFF; simp at hSeqFF
    dsimp only [c']
    simp only [hSeqNe, ↓reduceIte]
    wp_step; wp_str8_perm mS hmS
    apply SepWP.done
    · simp only [arm64_norm]; try bv_lin
    · exact hrun
    · refine ⟨⟨by simpa using hsp, rfl, hmS,
        by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
        untouchedCS_step hcs (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [calleeSavedVRegs]),
        by simp [arm64_norm], by simpa [arm64_norm] using hx20, by simp [arm64_norm], by simp [arm64_norm]⟩, ?_⟩
      have hVal : BitVec.truncate 8 (BitVec.zeroExtend 32 c.seq + 1#32) = c.seq + 1#8 := hAdd1 c.seq
      simpa [hGetSeqOpt, hVal, hWriteInc] using Entails.refl _

set_option maxHeartbeats 400000 in
private theorem mallocImpl_large_post_meta_fine [MallocngMultiPlacement]
    {b : BitVec 64} (hb : BlkBase 9 b)
    {s0 s : State} {F : SepProp} {m mb : BitVec 64} {req len : Nat}
    {c : CtxFields} {oom : State → SepProp}
    (hAct : c.active.length = 48) (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32) (hBnc : c.bounces.length = 32) (hPad : c.seqPad.length = 7)
    (hLenLo : 4096 ≤ len) (hmNe0 : m ≠ 0#64)
    (hPkEq : (((BitVec.ofNat 64 req + 0x1013#64) &&& 0xfffffffffffff000#64) ||| 0xfe0#64) =
      (mkLargeGroup m mb len).packedWord)
    (hpc : s.pc = b + miOff_after_alloc_meta) (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = m) (hx19 : s.readReg64 (.gpr 19#5) = mb)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    let gNew := mkLargeGroup m mb len
    let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
    SepWP (blkPC_b09.rebase b (fun _ => none)) (b + miOff_call_unlock) s
      ((m ↦ₛ List.replicate 40 0#8) ∗ (mb ↦ₛ List.replicate len 0#8) ∗
       (maddrs.ctx ↦ₛ c.toBytes) ∗ F)
      (fun s1 P1 =>
        (s1.sp = s0.sp - 80#64 ∧ s1.brk = s.brk ∧ s1.mem.perm = s.mem.perm ∧
         MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
         s1.readReg64 (.gpr 0#5) = maddrs.lock ∧
         s1.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 (c.mmapCounter + 1#32) ∧
         s1.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s1.readReg64 (.gpr 21#5) = 0#64 ∧
         s1.readReg64 (.gpr 22#5) = m ∧
         s1.readReg64 (.gpr 23#5) = 0#64) ∧
        (P1 ⊢ (m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
          (maddrs.ctx ↦ₛ ({ c with mmapCounter := c.mmapCounter + 1#32 }).toBytes) ∗ F))
      oom := by
  intro gNew groupBytes
  have _ := hb
  obtain ⟨hm1Len, hm2Len, hm3Len, hm4Eq, hMbWrite⟩ := large_meta_mem_writes m mb len (by omega)
  have hCtxOps := ctxBytes_ops c hAct hUse hUnm hBnc hPad
  have hCtxLen : c.toBytes.length = 928 := ctxBytes_length_fine c hAct hUse hUnm hBnc hPad
  have hGetMmc :
      pack32 (c.toBytes[12]?.getD 0#8) (c.toBytes[13]?.getD 0#8)
        (c.toBytes[14]?.getD 0#8) (c.toBytes[15]?.getD 0#8) = c.mmapCounter := by
    simpa only [List.getD_eq_getElem?_getD] using hCtxOps.1
  have hCtxWrite : ByteSlice.write32 c.toBytes 12 (c.mmapCounter + 1#32) =
      ({ c with mmapCounter := c.mmapCounter + 1#32 }).toBytes := hCtxOps.2.1 (c.mmapCounter + 1#32)
  generalize hCtxBs : c.toBytes = ctxBs at hCtxLen hGetMmc hCtxWrite ⊢
  generalize hm0 : List.replicate 40 0#8 = m0Bs at hm1Len hm2Len hm3Len hm4Eq ⊢
  have hm0Len : m0Bs.length = 40 := by subst hm0; rfl
  generalize hmb0 : List.replicate len 0#8 = mb0Bs at hMbWrite ⊢
  have hmb0Len : mb0Bs.length = len := by subst hmb0; simp
  dsimp only [miOff_after_alloc_meta, miOff_call_unlock] at hpc ⊢
  wp_steps 2
  wp_if hCbz
  · exact False.elim (hmNe0 (by simpa [hx0] using hCbz))
  wp_step
  wp_str64_perm mm1 hmm1; wp_str64_perm mm2 hmm2; wp_steps 2
  wp_str32_perm mm3 hmm3; wp_steps 6
  wp_str32_perm mm4 hmm4; wp_str32_perm mm5 hmm5; wp_str64_perm mm6 hmm6; wp_steps 2
  apply SepWP.done
  · simp only [arm64_norm]; try bv_lin
  · exact hrun
  · refine ⟨⟨by simpa using hsp, rfl,
      hmm6.trans (hmm5.trans (hmm4.trans (hmm3.trans (hmm2.trans hmm1)))),
      by dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc],
      untouchedCS_step hcs (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
      by simp, by simp [hGetMmc], by simp [hx20], by simp, by simp, by simp⟩, ?_⟩
    simpa [hx0, hx19, hx20, hPkEq, hGetMmc, hm4Eq, hMbWrite, hCtxWrite, gNew, groupBytes]
      using Entails.refl _

set_option maxHeartbeats 400000 in
private theorem mallocImpl_large_fine [MallocngMultiPlacement] {ro : Bool}
    (hMeta : AllocMetaFineStmt ro)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (hGt : 131051 < req) (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_large_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcs : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧
          MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) req) s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  obtain ⟨hRawPos, hRawMax, hAdd20Nat, hLenLo, hLenMod, _, hLen4115,
    _hLenStep, _hMetaStep, _hSumStep, hFitNew, hMapBound, hPkNew⟩ :=
    large_mmap_len_bounds (peakCount := bud.peakCount) hGt hReqMax
  let rawLen := req + 20
  let len := pageAlignUp rawLen
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  have hRtUnpack :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      (∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
        ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) := by
    unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepExists_congr fun errnoVal => ?_
    generalize ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr
    ac_rfl
  rw [hRtUnpack]
  apply SepWP.exists_elim; intro errnoVal
  dsimp only [miOff_large_entry] at hpc
  wp_steps 8
  have hmmap := VerifiedLibraries.Mallocng.Proofs.placed_mmapRw_large_ok
    (P := blkPC_b09.rebase b (fun _ => none)) tp errnoVal rawLen hRawPos hRawMax
  dsimp only at hmmap
  rw [at_bl_target_b09 hb 16 miOff_call_mmap] at hmmap
  let mmapFrame :=
    stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs ∗
    MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  refine SepWP.call_subroutine_frame (F := mmapFrame) (x := ()) (ret_pc := b + miOff_after_mmap)
    hmmap rfl
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_call_mmap, miOff_after_mmap, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, mmapFrame, State.setPC, State.writeReg64, State.writeReg32]
      rw [stackFrame_eq_stackFrameAt 64 (by decide) (by simpa [arm64_norm] using hsp),
          stackFrameAt_624_eq (s0.sp - 80#64) 64 (by decide)]
      simp only [sepConj_assoc]
      refine Entails.pure_right ⟨by simpa [arm64_norm] using hProc.2.2.1.trans htp0,
        rfl, hAdd20Nat, rfl, rfl, rfl, rfl⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ = pCL,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
        stackFrameAt (s0.sp - 80#64) 64 = pS1,
        stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) = pS2,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (stepOom_of_mmap_large hLenLo hLenMod hLen4115 ?_ hPerm0 hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc ⊢
      simp [arm64_norm, hProc])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro mb
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_m0, hbrk_m, hx0_m, hMbNe0, hMbNe1, hMbDiv, hMbBound, hDelta_m, hInReg_m⟩
  rw [stackFrame_eq_stackFrameAt 64 (by decide) (by simpa [arm64_norm] using hsp)]
  have hPullCL :
      ((stackFrameAt (s0.sp - 80#64) 64 ∗ ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗ mmapFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
       (stackFrameAt (s0.sp - 80#64) 624 ∗
        (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st0 ∗
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) := by
    have hBrkEq : sm.brk = s.brk := hbrk_m
    rw [hBrkEq]; dsimp only [mmapFrame]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) 64 (by decide)]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ = pCL,
      stackFrameAt (s0.sp - 80#64) 64 = pS1,
      stackFrameAt ((s0.sp - 80#64) - 64#64) (624 - 64) = pS2,
      ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
    ac_rfl
  rw [hPullCL]
  apply SepWP.pure_elim; intro hcl_m
  have hProc_m : MallocngProcPreserved s0 sm := by
    refine procPres_trans ?_ ⟨hProc_m0.1, hProc_m0.2.1, hProc_m0.2.2.1, hProc_m0.2.2.2.1,
      hProc_m0.2.2.2.2.1, hProc_m0.2.2.2.2.2.1,
      by simpa [sigActions_setPC, sigActions_writeReg64, sigActions_writeReg32] using hProc_m0.2.2.2.2.2.2⟩
    dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc]
  have hsp_sm : sm.sp = s0.sp - 80#64 := hsp_m.trans (by simpa [arm64_norm] using hsp)
  have hcs_sm : MallocImplUntouchedCS s0 sm :=
    untouchedCS_step hcs (hcs_m.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_m.2.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_m.2.2.2.2.2.2.2.2.2.1.trans (by simp))
      (by simpa [calleeSavedVRegs] using hcs_m.2.2.2.2.2.2.2.2.2.2.2)
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req :=
    hcs_m.2.1.trans (by simpa [arm64_norm] using hx20)
  have hDelta0_sm : MallocngMappedDelta 1 len s0.mem sm.mem := by
    obtain ⟨ivs, hl, hs, hc⟩ := hDelta_m
    exact ⟨ivs, hl, hs, fun a ha => (hc a ha).imp (fun hm => hPerm0 ▸ hm) id⟩
  have hInReg0_sm : MmapNewInRegion mb len s0.mem sm.mem :=
    fun a ha => (hInReg_m a ha).imp (fun hm => hPerm0 ▸ hm) id
  have hwf_sm : MallocngWFInflight 0 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st0 := hbrk_m ▸ hwf0
  let st_seq := updateSeqSt st0
  have hwf_seq0 : MallocngWF maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st_seq :=
    updateSeqSt_wf hwf_sm
  let coreBody0 :=
    MallocngLiveAuth γ st0.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr ∗ MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap ∗
    ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗
    ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
    MappedSet st0.masterDom (OwnedMappedByte st0)
  let seqFrame :=
    stackFrameAt (s0.sp - 80#64) 624 ∗
    (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs ∗
    coreBody0 ∗
    ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  have hToSeq :
      (stackFrameAt (s0.sp - 80#64) 624 ∗
       (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st0 ∗
       ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) =
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ seqFrame) := by
    dsimp only [MallocngCoreStInflightModeA, coreBody0, seqFrame]
    rw [propext ⟨fun _ => trivial, fun _ => hwf_sm⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
      MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
    ac_rfl
  rw [hToSeq]
  refine sepWP_seq_cl (mid := b + miOff_call_alloc_meta) hcl_m ?_
  refine SepWP.mono
    (mallocImpl_large_seq_prep_fine hb hwf_sm.ctx_lens.1 hwf_sm.ctx_lens.2.1
      hwf_sm.ctx_lens.2.2.1 hwf_sm.ctx_lens.2.2.2.1 (by simp [hwf_sm.ctx_lens.2.2.2.2.1])
      hMbNe1 hpc_m hrun_m hsp_sm hProc_m hcs_sm hx0_m hx20_sm) ?_
  rintro s_q P_q hpc_q hrun_q ⟨⟨hsp_q, hbrk_q, hperm_q, hProc_q, hcs_q, hx19_q, hx20_q, hx24_q, hx25_q⟩, hPq⟩ hcl_q
  apply SepWP.weaken_pre hPq
  have hwf_seq : MallocngWFInflight 0 maddrs.base brkStart s_q.brk bud.liveCost bud.peakCost st_seq :=
    hbrk_q ▸ hwf_seq0
  have hCtxSeqEq :
      (if st0.ctx.seq = 0xff#8 then { st0.ctx with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
       else { st0.ctx with seq := st0.ctx.seq + 1#8 }) = st_seq.ctx := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hRebundleSeq :
      ((maddrs.ctx ↦ₛ (if st0.ctx.seq = 0xff#8 then { st0.ctx with unmapSeq := List.replicate 32 0#8, seq := 1#8 }
        else { st0.ctx with seq := st0.ctx.seq + 1#8 }).toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ seqFrame) ⊢
      stackFrameAt (s0.sp - 80#64) 624 ∗
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s_q.brk bud.liveCost bud.peakCost st_seq ∗
      MallocngRuntime maddrs tp ∗
      (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
      MallocngRoTablesA maddrs := by
    rw [hCtxSeqEq]
    have hRtIntro :
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64) ⊢
          MallocngRuntime maddrs tp := by
      unfold MallocngRuntime
      exact sepConj_mono_left (Entails.sepExists_right errnoVal (Entails.refl _))
    have hCoreEq :
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s_q.brk bud.liveCost bud.peakCost st_seq =
          ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ coreBody0) := by
      have hSameAtoms :
          MallocngLiveAuth γ st_seq.liveMap = MallocngLiveAuth γ st0.liveMap ∧
          MallocngAuxvPtrCell ro maddrs.libc st_seq.auxvPtr = MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr ∧
          MallocngAuxvStateRo ro γ st_seq.auxvPtr st_seq.auxvSnap = MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap ∧
          ByteMap st_seq.masterDom (OwnedRwByte st_seq) st_seq.byteVal =
            ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∧
          ProtNoneByteMap st_seq.masterDom (OwnedProtNoneByte st_seq) st_seq.byteVal =
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∧
          MappedSet st_seq.masterDom (OwnedMappedByte st_seq) =
            MappedSet st0.masterDom (OwnedMappedByte st0) := by
        dsimp only [st_seq, updateSeqSt]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      dsimp only [MallocngCoreStInflightModeA, coreBody0]
      rw [propext ⟨fun _ => trivial, fun _ => hwf_seq⟩, pure_true, emp_sepConj,
          hSameAtoms.1, hSameAtoms.2.1, hSameAtoms.2.2.1, hSameAtoms.2.2.2.1,
          hSameAtoms.2.2.2.2.1, hSameAtoms.2.2.2.2.2]
      generalize (maddrs.ctx ↦ₛ st_seq.ctx.toBytes) = pCtx,
        MallocngLiveAuth γ st0.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
        MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
        ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
        ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
        MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
      ac_rfl
    rw [hCoreEq]; dsimp only [seqFrame]
    have hRearr :
        ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗
         (stackFrameAt (s0.sp - 80#64) 624 ∗ (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
          MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ coreBody0 ∗
          ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) =
        (stackFrameAt (s0.sp - 80#64) 624 ∗ ((maddrs.ctx ↦ₛ st_seq.ctx.toBytes) ∗ coreBody0) ∗
         (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
         (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs) := by
      generalize (maddrs.ctx ↦ₛ st_seq.ctx.toBytes) = pCtx,
        ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        (mb ↦ₛ List.replicate len 0#8) = pMb,
        memMapped mb len = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        coreBody0 = pCb,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
        ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48
      ac_rfl
    rw [hRearr]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hRtIntro))
  apply SepWP.weaken_pre hRebundleSeq
  have hSpAl_q : s_q.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp_q]; exact sp_sub_80_aligned hsp_align
  have hMetaSeqEq : st_seq.metaAreas = st0.metaAreas := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hGrpsSeqEq : st_seq.groups = st0.groups := by
    dsimp only [st_seq, updateSeqSt]; split <;> rfl
  have hCntSeq : totalLiveCount st_seq ≤ bud.peakCount := by
    have hEqCnt : totalLiveCount st_seq = totalLiveCount st0 := by
      dsimp only [st_seq, updateSeqSt]; split <;> rfl
    have := hCount0.1; have := hCount0.2.1; omega
  have hFineSeq : FineSplitInv bL bP st_seq :=
    FineSplitInv.of_eq hFine0 (by rw [hMetaSeqEq]; exact hFine0.meta_le) hGrpsSeqEq
  have hMaStepSeq : st_seq.metaAreas.length ≤ fineMaxMetaAreas bL + 5 := by
    rw [hMetaSeqEq]; omega
  dsimp only [miOff_call_alloc_meta] at hpc_q
  wp_step
  have hMetaCall := call_placed_allocMeta_fine hMeta (P := blkPC_b09.rebase b (fun _ => none))
    0 (by decide) γ tp brkStart bud.liveCost bud.peakCost bud.peakCount
    bL bP (fineMaxMetaAreas bL) st_seq hCntSeq hFineSeq hMaStepSeq
  rw [at_bl_target_b09 hb 7 miOff_call_alloc_meta] at hMetaCall
  let metaFrame :=
    stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) ∗
    (mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    MallocngRoTablesA maddrs
  have hDelta0_q : MallocngMappedDelta 1 len s0.mem s_q.mem :=
    mappedDelta_congr_perm_right hDelta0_sm hperm_q
  refine SepWP.call_subroutine_frame (F := metaFrame) (x := ()) (ret_pc := b + miOff_after_alloc_meta)
    hMetaCall rfl
    (by simp [arm64_norm, hrun_q])
    (by simpa [State.spAligned, arm64_norm] using hSpAl_q)
    (by dsimp only [miOff_call_alloc_meta, miOff_after_alloc_meta, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, metaFrame, State.setPC, State.writeReg64]
      rw [stackFrame_eq_stackFrameAt 224 (by decide) (by simpa [arm64_norm] using hsp_q),
          stackFrameAt_624_eq (s0.sp - 80#64) 224 (by decide)]
      simp only [sepConj_assoc]
      refine Entails.pure_right
        ⟨by simpa [arm64_norm] using hProc_q.2.2.1.trans htp0,
         by simpa [arm64_norm] using hProc_q.2.2.2.1.trans hbrkS0⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_q.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl_q (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_q.mem⌝ = pCL,
        stackFrameAt (s0.sp - 80#64) 224 = pS1,
        stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) = pS2,
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s_q.brk bud.liveCost bud.peakCost st_seq = pCr,
        MallocngRuntime maddrs tp = pRt,
        (mb ↦ₛ List.replicate len 0#8) = pMb,
        memMapped mb len = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun s_a hpc_a hrun_a hsp_a hcs_a => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (stepOom_of_allocMeta_after_mmap hLen4115 ?_ hDelta0_q hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc_q ⊢
      simp [arm64_norm, hProc_q])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro m
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_a0, hx0_a, hmNe0, _, _, _, _, hRes1, hGrpsEq1, _, _, hCnt1_eq, _, hMetaMax_a,
    hFine1, _, _, _, _, _, _, hNoOrph_a, hDelta_a⟩
  rw [stackFrame_eq_stackFrameAt 224 (by decide) (by simpa [arm64_norm] using hsp_q)]
  have hPullCL_a :
      ((stackFrameAt (s0.sp - 80#64) 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
        MallocngCoreStInflightModeA ro (0 + 1) γ maddrs brkStart s_a.brk bud.liveCost bud.peakCost st1) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ ∗ metaFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ ∗
       ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
        MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_a.brk bud.liveCost bud.peakCost st1 ∗
        ((m ↦ₛ List.replicate 40 0#8) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         MallocngRoTablesA maddrs ∗
         MallocngRuntime maddrs tp))) := by
    dsimp only [metaFrame, Nat.zero_add]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) 224 (by decide)]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_a.mem⌝ = pCL,
      stackFrameAt (s0.sp - 80#64) 224 = pS1,
      stackFrameAt ((s0.sp - 80#64) - 224#64) (624 - 224) = pS2,
      MallocngRuntime maddrs tp = pRt,
      (m ↦ₛ List.replicate 40 0#8) = pM,
      MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_a.brk bud.liveCost bud.peakCost st1 = pCr,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo
    ac_rfl
  rw [hPullCL_a]
  apply SepWP.pure_elim; intro hcl_a
  apply extract_fresh_mmap_disjoint_A_fine (Nat.mod_eq_zero_of_dvd hMbDiv) hLenMod hLenLo hMbBound
  intro hDisjDyn
  have hUnpackCore1 :
      ((mb ↦ₛ List.replicate len 0#8) ∗ memMapped mb len ∗
       MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_a.brk bud.liveCost bud.peakCost st1 ∗
       ((m ↦ₛ List.replicate 40 0#8) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) =
      (⌜MallocngWFInflight 1 maddrs.base brkStart s_a.brk bud.liveCost bud.peakCost st1⌝ ∗
       ((m ↦ₛ List.replicate 40 0#8) ∗ (mb ↦ₛ List.replicate len 0#8) ∗
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
        (memMapped mb len ∗
         MallocngLiveAuth γ st1.liveMap ∗
         (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
         ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
         ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
         MappedSet st1.masterDom (OwnedMappedByte st1) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) := by
    dsimp only [MallocngCoreStInflightModeA]
    generalize ⌜MallocngWFInflight 1 maddrs.base brkStart s_a.brk bud.liveCost bud.peakCost st1⌝ = pWF,
      (mb ↦ₛ List.replicate len 0#8) = pMb,
      memMapped mb len = pMp,
      (m ↦ₛ List.replicate 40 0#8) = pM,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
      MallocngLiveAuth γ st1.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb8,
      MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
      MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hUnpackCore1]
  apply SepWP.pure_elim; intro hwf1
  have hProc_sa : MallocngProcPreserved s0 s_a := by
    refine procPres_trans ?_
      ⟨hProc_a0.1, hProc_a0.2.1, hProc_a0.2.2.1, hProc_a0.2.2.2.1,
       hProc_a0.2.2.2.2.1, hProc_a0.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_writeReg64] using hProc_a0.2.2.2.2.2.2⟩
    dsimp only [MallocngProcPreserved] at hProc_q ⊢; simp [arm64_norm, hProc_q]
  have hsp_sa : s_a.sp = s0.sp - 80#64 := hsp_a.trans (by simpa [arm64_norm] using hsp_q)
  have hcs_sa : MallocImplUntouchedCS s0 s_a :=
    untouchedCS_step hcs_q (hcs_a.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_a.2.2.2.2.2.2.2.2.1.trans (by simp))
      (hcs_a.2.2.2.2.2.2.2.2.2.1.trans (by simp))
      (by simpa [calleeSavedVRegs] using hcs_a.2.2.2.2.2.2.2.2.2.2.2)
  have hx19_sa : s_a.readReg64 (.gpr 19#5) = mb := hcs_a.1.trans (by simpa [arm64_norm] using hx19_q)
  have hx20_sa : s_a.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req := hcs_a.2.1.trans (by simpa [arm64_norm] using hx20_q)
  have hx24_sa : s_a.readReg64 (.gpr 24#5) = pageOf maddrs.lock :=
    hcs_a.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hx24_q)
  have hx25_sa : s_a.readReg64 (.gpr 25#5) = pageOf maddrs.ctx :=
    hcs_a.2.2.2.2.2.2.1.trans (by simpa [arm64_norm] using hx25_q)
  refine sepWP_seq_cl (mid := b + miOff_call_unlock) hcl_a ?_
  refine SepWP.mono
    (mallocImpl_large_post_meta_fine hb hwf1.ctx_lens.1 hwf1.ctx_lens.2.1
      hwf1.ctx_lens.2.2.1 hwf1.ctx_lens.2.2.2.1 (by simp [hwf1.ctx_lens.2.2.2.2.1])
      hLenLo hmNe0 (hPkNew m mb) hpc_a hrun_a hsp_sa hProc_sa hcs_sa
      hx0_a hx19_sa hx20_sa hx24_sa hx25_sa) ?_
  rintro s_u P_u hpc_u hrun_u
    ⟨⟨hsp_u, hbrk_u, hperm_u, hProc_u, hcs_u, hx0_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u⟩, hPu⟩ hcl_u
  apply SepWP.weaken_pre hPu
  have hRes1Eq : st1.reservedMetas = [m] := by
    have h0Res : st_seq.reservedMetas = [] := by
      have : st_seq.reservedMetas = st0.reservedMetas := by dsimp [st_seq, updateSeqSt]; split <;> rfl
      rw [this]
      have hInf0 := hwf0.inflight_wf
      cases hr : st0.reservedMetas with
      | nil => rfl
      | cons _ _ => rw [hr] at hInf0; simp at hInf0
    rwa [h0Res] at hRes1
  have hDynSeqEq : dynamicRootRegions st_seq = dynamicRootRegions st0 := by
    dsimp only [st_seq, updateSeqSt, dynamicRootRegions]; split <;> rfl
  have hNoOrph_a' : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s_q.mem s_a.mem := by
    rw [hCount0.2.2.1, ← hDynSeqEq]; exact hNoOrph_a
  have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
    hbrk_u ▸ hwf1
  obtain ⟨hNoRes2, hCnt2, hMetaLen2, hg2, hSlotsPos2, hClaimed2, hSc2_63, hMap2,
    hZeroMm2, hNoOrph2, hwf2, hBundle2⟩ :=
    large_group_bundle (γ := γ) (ivs0 := ivs0)
      (m0 := s0.mem) (m1 := sm.mem) (m2 := s_q.mem) (m3 := s_a.mem) (mf := s_u.mem)
      hwf1_u hRes1Eq hMbNe0 hMbDiv hLenLo hLenMod hMbBound
      hInReg0_sm hperm_q hNoOrph_a' hperm_u hDisjDyn
  let gNew := mkLargeGroup m mb len
  let st2 := mkLargeGroupSt st1 m mb len
  let groupBytes := unpack64 m ++ List.replicate (len - 8) 0#8
  have hToJoin :
      ((m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
       (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
       (memMapped mb len ∗ MallocngLiveAuth γ st1.liveMap ∗
        (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
        MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
        MappedSet st1.masterDom (OwnedMappedByte st1) ∗
        stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) ⊢
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_u.brk bud.liveCost bud.peakCost st2 ∗
      MallocngRuntime maddrs tp := by
    have hRearr :
        ((m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗
         (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
         (memMapped mb len ∗ MallocngLiveAuth γ st1.liveMap ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
          MappedSet st1.masterDom (OwnedMappedByte st1) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗
          MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) =
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         (MallocngLiveAuth γ st1.liveMap ∗
          (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) ∗
          (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
          MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗ MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
          (m ↦ₛ gNew.metaBytes) ∗ (mb ↦ₛ groupBytes) ∗ memMapped mb len ∗
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
          MappedSet st1.masterDom (OwnedMappedByte st1)) ∗
         MallocngRuntime maddrs tp) := by
      generalize (m ↦ₛ gNew.metaBytes) = pM,
        (mb ↦ₛ groupBytes) = pMb,
        (maddrs.ctx ↦ₛ ({ st1.ctx with mmapCounter := st1.ctx.mmapCounter + 1#32 }).toBytes) = pCtx,
        memMapped mb len = pMp,
        MallocngLiveAuth γ st1.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb8,
        MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hRearr]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hBundle2)))
  apply SepWP.weaken_pre hToJoin
  have hCnt2_0 : totalLiveCount st2 = totalLiveCount st0 := by
    have hSeq0 : totalLiveCount st_seq = totalLiveCount st0 := by
      dsimp only [st_seq, updateSeqSt]; split <;> rfl
    exact hCnt2.trans (hCnt1_eq.trans hSeq0)
  have hMetaLe2 : st2.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 := by
    have hMeta0 := hCount0.2.2.2.2.1
    have hPeakLe : bud.peakCount ≤ (mallocngAllocBudget true req bud).peakCount := by
      dsimp [mallocngAllocBudget]; omega
    have hDivLe : (88 + 8 * bud.peakCount) / 101 ≤
        (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 :=
      Nat.div_le_div_right (by omega)
    dsimp only [st2, len, rawLen] at hMetaLen2 ⊢
    rw [hMetaLen2]
    have hMax : max st_seq.metaAreas.length (1 + (88 + 8 * bud.peakCount) / 101) =
        1 + (88 + 8 * bud.peakCount) / 101 := Nat.max_eq_right (by rw [hMetaSeqEq]; exact hMeta0)
    omega
  have hFine2 : FineSplitInv bL bP st2 :=
    fineSplitInv_insert_large63 hFine1 rfl
      (by rintro _ hs _ _ _ rfl; simp [mkLargeGroup] at hs)
      hFine1.meta_le rfl
  have hDelta_u : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem s_u.mem := by
    dsimp only [State.setPC, State.writeReg64] at hDelta_a
    have hSum : MallocngMappedDelta (1 + 1) (len + FineMetaStep (fineMaxMetaAreas bL)) s0.mem s_a.mem :=
      MallocngMappedDelta.trans hDelta0_q hDelta_a
    have hFineSum : len + FineMetaStep (fineMaxMetaAreas bL) ≤ FineStepBound (fineMaxMetaAreas bL) req := by
      have hL : len ≤ req + 4115 := hLen4115
      have := fineStepBound_large_le (fineMaxMetaAreas bL) len req (by omega)
      omega
    exact mappedDelta_congr_perm_right
      (MallocngMappedDelta.mono (by decide : 1 + 1 ≤ 16) hFineSum hSum) hperm_u
  subst hb_eq
  rw [← mallocngBlockProg_eq_b09]
  have hGrp2 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st2.groups := by
    have hG0 := hCount0.2.2.2.2.2.mono (V := (mallocngAllocBudget true req bud).peakCount + 6)
      (by dsimp [mallocngAllocBudget]; omega)
    have hG1 : st1.groups = st0.groups := hGrpsEq1.trans hGrpsSeqEq
    dsimp only [st2, mkLargeGroupSt]
    exact Cost.GroupsGrpBound.cons (hG1 ▸ hG0) fun _ hs => absurd hs (by dsimp only [mkLargeGroup]; decide)
  have hThr : MmapThresholdReq = 131051 := rfl
  exact mallocImpl_join_epilogue_fine hcl_u hCount0 hCnt2_0 hMetaLe2 hGrp2 hNoOrph2 hwf2 hFine2 hNoRes2
    hg2 hSlotsPos2 hClaimed2 hReqMax (hFitNew m mb)
    (fun hLe => absurd hLe (by omega))
    (fun _ => hSc2_63)
    (fun ⟨_, hlt48⟩ => by omega)
    (fun h24 => by omega)
    (fun _ => by rw [hMap2]; exact hMapBound)
    (fun _ => by rw [hMap2]; have := hLenMod; have := hLen4115; omega)
    hZeroMm2 htp0 hbrkS0 hDelta_u
    hpc_u hrun_u hsp_u hsp_align hProc_u hcs_u
    hx0_u hx19_u hx20_u
    (by simpa using hx21_u)
    (by simpa [gNew, mkLargeGroup] using hx22_u)
    (by simpa using hx23_u)

/-! ## 3. Small/Medium Slab Fine Path (`req ≤ 131051`) -/

private theorem bit31_all_32_fine :
    (List.range 32).all (fun k => decide ((BitVec.ofNat 32 k).getLsbD 31 = false)) = true := by
  decide

private theorem bit31_false_of_readReg32_ofNat_fine {v : BitVec 64} {idx : Nat}
    (h32 : BitVec.truncate 32 v = BitVec.ofNat 32 idx) (hIdx : idx ≤ 31) :
    v.getLsbD 31 = false ∧ v[31] = false ∧
    BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
  have h1 : (BitVec.truncate 32 v).getLsbD 31 = v.getLsbD 31 := by simp
  have h2 : (BitVec.ofNat 32 idx).getLsbD 31 = false :=
    of_decide_eq_true (List.all_eq_true.mp bit31_all_32_fine idx (List.mem_range.mpr (by omega)))
  have hg : v.getLsbD 31 = false := by rw [← h1, h32, h2]
  have hz : BitVec.zeroExtend 64 (BitVec.truncate 32 v) = BitVec.ofNat 64 idx := by
    rw [h32]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  exact ⟨hg, hg, hz⟩

private theorem and_u32_eq_zeroExtend_truncate_fine (v : BitVec 64) :
    v &&& 4294967295#64 = BitVec.zeroExtend 64 (BitVec.truncate 32 v) := by bv_bits

private theorem sc_sxtw_shl3_all_fine :
    (List.range 48).all (fun k =>
      decide ((BitVec.signExtend 64 (BitVec.ofNat 32 k) <<< 3) = BitVec.ofNat 64 (8 * k) ∧
        (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 k)) <<< 3) =
          BitVec.ofNat 64 (8 * k))) = true := by decide

private theorem sc_sxtw_shl3_bv_fine {sc : Nat} (hsc : sc < 48) :
    (BitVec.signExtend 64 (BitVec.ofNat 32 sc) <<< 3) = BitVec.ofNat 64 (8 * sc) ∧
    (BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 sc)) <<< 3) =
      BitVec.ofNat 64 (8 * sc) :=
  of_decide_eq_true (List.all_eq_true.mp sc_sxtw_shl3_all_fine sc (List.mem_range.mpr hsc))

private theorem tryAvail_bv_props_fine {av : BitVec 32} (hAvNe : av ≠ 0#32) :
    let iso := (-av) &&& av
    let hashIdx := ((iso * 0x076be629#32) >>> 27).toNat
    hashIdx < 32 ∧
    BitVec.zeroExtend 64
      ((0#32 + (0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) * 0x076be629#32) >>> 27) =
      BitVec.ofNat 64 hashIdx ∧
    BitVec.truncate 32 (BitVec.zeroExtend 64 av - BitVec.zeroExtend 64 (0#32 - av &&& av)) =
      av - iso ∧
    (∀ b : BitVec 8, (BitVec.ofNat 64 b.toNat) &&& 255#64 = BitVec.ofNat 64 b.toNat) := by
  dsimp only
  obtain ⟨_, _, hHashLt, _, hNegIso, _, _, _⟩ := ctz32DeBruijn_spec hAvNe
  have hSub0 : ∀ x : BitVec 32, 0#32 - x = -x := BitVec.zero_sub
  have hZ : BitVec.zeroExtend 64
      ((0#32 + (0#32 - (0#32 - av &&& av) &&& (0#32 - av &&& av)) * 0x076be629#32) >>> 27) =
      BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat := by
    rw [hSub0 av, hSub0 ((-av) &&& av), BitVec.zero_add, hNegIso]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hTrSub : BitVec.truncate 32 (BitVec.zeroExtend 64 av - BitVec.zeroExtend 64 (0#32 - av &&& av)) =
      av - ((-av) &&& av) := by rw [hSub0 av]; bv_bits
  have hB : ∀ b : BitVec 8, (BitVec.ofNat 64 b.toNat) &&& 255#64 = BitVec.ofNat 64 b.toNat := by
    intro b; apply BitVec.eq_of_toNat_eq; have hb := b.isLt
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega)]
    change b.toNat &&& (2 ^ 8 - 1) = b.toNat
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt hb
  exact ⟨hHashLt, hZ, hTrSub, hB⟩

private theorem bv32_le_or_fine (a b : BitVec 32) : a.toNat ≤ (a ||| b).toNat := by
  change a ≤ a ||| b; bv_bits

private theorem active_group_stride_ge_fine {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hg : g ∈ st.groups) (_hSc : g.sc < 48) (hAvNe : g.availMask ≠ 0#32) :
    slotStride g.sc ≤ g.stride := by
  by_cases hZ : (g.lastIdx == 0 && decide (0 < g.maplen)) = true
  · have hZ' : g.lastIdx = 0 ∧ 0 < g.maplen := by simpa using hZ
    have hgWf := hwf.groups_wf g hg
    have hCnt1 : g.cnt = 1 := by dsimp [GroupDesc.cnt]; omega
    have hLen1 : g.slots.length = 1 := hgWf.2.2.1.trans hCnt1
    have hOrLt : (g.availMask ||| g.freedMask).toNat < 2 := by
      have h := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; rw [hCnt1] at h; exact h
    have hAvLt : g.availMask.toNat < 2 := Nat.lt_of_le_of_lt (bv32_le_or_fine _ _) hOrLt
    have hAv1 : g.availMask = 1#32 := by
      apply BitVec.eq_of_toNat_eq
      have h0 : g.availMask.toNat ≠ 0 := fun hz => hAvNe (BitVec.eq_of_toNat_eq (by simpa using hz))
      change g.availMask.toNat = 1; omega
    have hBit0 : g.availMask.getLsbD 0 = true := by rw [hAv1]; decide
    have hSlot0 := (hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 (by omega)).2.1.mp hBit0
    have hEmp : g.isEmpty = true := by
      unfold GroupDesc.isEmpty
      rcases hS : g.slots with _ | ⟨s_hd, _ | _⟩
      · simp [hS] at hLen1
      · simp only [hS, List.getElem_cons_zero] at hSlot0; subst hSlot0; rfl
      · simp [hS] at hLen1
    have hMapGe := (hwf.empty_groups_bound g hg hEmp).2.2.2.2.2.2 hZ'.1
    have hStr : g.stride = g.maplen * 4096 - 16 := by
      unfold GroupDesc.stride; simp only [hZ, ↓reduceIte]
    omega
  · have hZF : (g.lastIdx == 0 && decide (0 < g.maplen)) = false := by
      cases hB : (g.lastIdx == 0 && decide (0 < g.maplen)) <;> simp_all
    have hStr : g.stride = slotStride g.sc := by
      unfold GroupDesc.stride; simp only [hZF, Bool.false_eq_true, ↓reduceIte]
    omega

set_option maxHeartbeats 400000 in
private theorem mallocImpl_allocSlot_slow_fine [MallocngMultiPlacement] {ro : Bool}
    (hSlot : AllocSlotFineStmt ro)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req sc : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (hRoomSc : stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)
    (hReqMax : req ≤ MallocngMaxAllocSize) (hReqThr : req ≤ MmapThresholdReq)
    (hSc48 : sc < 48) (hAllow : allowedPhysClass (nomSc req) sc = true)
    (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_alloc_prep) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧
          MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) req) s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  have hReqLt64 : req < 2 ^ 64 := by have := mallocngMaxAllocSize_eq; omega
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  have hDepthLe : 0 + allocSlotDepthBound sc ≤ 6 := by
    have := allocSlotDepthBound_le_three sc; omega
  let stkNeed := (allocSlotDepthBound sc + 1) * 96 + 224
  have hStkLe : stkNeed ≤ 624 := by
    have := allocSlotDepthBound_le_three sc; dsimp [stkNeed]; omega
  have hLiveCntLe : totalLiveCount st0 ≤ bud.peakCount := by
    have := hCount0.1; have := hCount0.2.1; omega
  obtain ⟨hReqLo, _⟩ := allocSlotReqLo_le_of_allowedPhysClass hReqThr hSc48 hAllow
  have hClaim0 : totalClaimedSlots st0 = 0 :=
    Nat.eq_zero_of_le_zero (totalClaimedSlots_le_inflight hwf0)
  have hRoom : AllocSlotOccRoom bP st0 sc := Or.inl hRoomSc
  have hMaStep : st0.metaAreas.length ≤ fineMaxMetaAreas bL + (3 - allocSlotDepthBound sc) := by
    omega
  dsimp only [miOff_alloc_prep] at hpc
  wp_steps 3
  have hSlotCall := call_placed_allocSlot_fine hSlot (P := blkPC_b09.rebase b (fun _ => none))
    sc req 0 hSc48 hReqLo hFitSc hDepthLe γ tp brkStart bud.liveCost bud.peakCost bud.peakCount
    bL bP (fineMaxMetaAreas bL) st0 hLiveCntLe hClaim0 hFine0 hRoom hMaStep
  rw [at_bl_target_b09 hb 8 miOff_call_slot] at hSlotCall
  let slotFrame :=
    stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64)
  refine SepWP.call_subroutine_frame (F := slotFrame) (x := ()) (ret_pc := b + miOff_after_slot)
    hSlotCall rfl
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_call_slot, miOff_after_slot, Reg.lr]; simp [arm64_norm])
    (fun R' hm => by
      refine Satisfies.mono (Entails.trans (sepConj_mono_left ?_) (Entails.of_eq (sepConj_assoc _ _ R'))) hm
      dsimp only [withCL, slotFrame]
      rw [stackFrame_eq_stackFrameAt stkNeed (by omega) (by simpa [arm64_norm] using hsp),
          stackFrameAt_624_eq (s0.sp - 80#64) stkNeed hStkLe]
      simp only [sepConj_assoc]
      refine Entails.pure_right
        ⟨by simpa [arm64_norm] using hProc.2.2.1.trans htp0,
         by simpa [arm64_norm] using hProc.2.2.2.1.trans hbrkS0,
         by simp [arm64_norm]; omega,
         by simp [arm64_norm]; exact hReqLt64⟩ ?_
      have hPureCL : (emp : SepProp) ⊢ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ := by
        simpa [sepConj_emp] using Entails.pure_right hcl (Entails.refl emp)
      refine Entails.trans (Entails.trans (Entails.of_eq (emp_sepConj _).symm) (sepConj_mono_left hPureCL)) (Entails.of_eq ?_)
      dsimp only [State.setPC, State.writeReg64]
      generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝ = pCL,
        stackFrameAt (s0.sp - 80#64) stkNeed = pS1,
        stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) = pS2,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRoTablesA maddrs = pRo,
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
        MallocngRuntime maddrs tp = pRt
      ac_rfl)
    (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
    (fun sm hpc_m hrun_m hsp_m hcs_m => ?_)
    (fun R' sf _ hoom => by
      dsimp only [withCL] at hoom
      rw [satisfies_pure_sepConj] at hoom
      refine Satisfies.pure_intro
        (stepOom_of_allocSlot_fine hSc48 ?_ hPerm0 hoom.1)
        (Satisfies.drop_left hoom.2)
      dsimp only [MallocngProcPreserved] at hProc ⊢
      simp [arm64_norm, hProc])
  dsimp only [withCL]
  rw [sepConj_assoc, sepExists_sepConj_left]
  apply SepWP.exists_elim; intro st1
  rw [sepExists_sepConj_left]
  apply SepWP.exists_elim; intro idx
  rw [sepConj_assoc]
  apply SepWP.pure_elim
  rintro ⟨hProc_m0, hRes1, _hLiveMap1, _hEff1, hCnt1, _hMetaAdd1, hMetaMax1, hFine1, _hClassLe,
    hx0_m, hIdx31, ⟨g, hg1, hAct1, hIdxLt, hGsc, hFitG, hMetaEq, hClaimed1, hZeroMm1⟩,
    hNoOrph_st, hDelta_m, hGrpT⟩
  have hsp_sm : sm.sp = s0.sp - 80#64 := by simpa [arm64_norm] using hsp_m.trans hsp
  rw [stackFrame_eq_stackFrameAt stkNeed (by omega) (by simpa [arm64_norm] using hsp)]
  let coreRest1 :=
    MallocngLiveAuth γ st1.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr ∗
    MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap ∗
    ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
    MappedSet st1.masterDom (OwnedMappedByte st1)
  have hPullAll :
      ((stackFrameAt (s0.sp - 80#64) stkNeed ∗ MallocngRoTablesA maddrs ∗
        MallocngRuntime maddrs tp ∗
        MallocngCoreStInflightModeA ro (0 + 1) γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st1) ∗
       ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗ slotFrame) =
      (⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ ∗
       ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ ∗
       ((maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
        (coreRest1 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) := by
    dsimp only [slotFrame, MallocngCoreStInflightModeA, coreRest1, Nat.zero_add]
    rw [stackFrameAt_624_eq (s0.sp - 80#64) stkNeed hStkLe]
    generalize ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem⌝ = pCL,
      ⌜MallocngWFInflight 1 maddrs.base brkStart sm.brk bud.liveCost bud.peakCost st1⌝ = pWf1,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
      MallocngLiveAuth γ st1.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb8,
      MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
      MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
      stackFrameAt (s0.sp - 80#64) stkNeed = pS1,
      stackFrameAt ((s0.sp - 80#64) - BitVec.ofNat 64 stkNeed) (624 - stkNeed) = pS2,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPullAll]
  apply SepWP.pure_elim; intro hcl_m
  apply SepWP.pure_elim; intro hwf1
  obtain ⟨hActLen1, hUseLen1, hUnmLen1, hBncLen1, hPadLen1, _⟩ := hwf1.ctx_lens
  have hPadLen1_7 : st1.ctx.seqPad.length = 7 := by rw [hPadLen1]; rfl
  have hCtxOps1 := ctxBytes_ops st1.ctx hActLen1 hUseLen1 hUnmLen1 hBncLen1 hPadLen1_7
  have hCtxLen1 : st1.ctx.toBytes.length = 928 :=
    ctxBytes_length_fine st1.ctx hActLen1 hUseLen1 hUnmLen1 hBncLen1 hPadLen1_7
  have hGetAct1 := hCtxOps1.2.2.1 sc hSc48
  have hGetMmc1 := hCtxOps1.1
  clear hCtxOps1
  generalize hCtx1Gen : st1.ctx.toBytes = ctx1Bs at hCtxLen1 hGetAct1 hGetMmc1 ⊢
  have hcs_m' := hcs_m
  obtain ⟨hc19, hc20, _, _, _, hc24, hc25, _⟩ := hcs_m'
  have hx19_sm : sm.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc := by
    simpa [arm64_norm] using hc19.trans (by simp [arm64_norm, hx19])
  have hx20_sm : sm.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req := by
    simpa [arm64_norm] using hc20.trans (by simp [arm64_norm, hx20])
  have hx24_sm : sm.readReg64 (.gpr 24#5) = pageOf maddrs.lock := by
    simpa [arm64_norm] using hc24.trans (by simp [arm64_norm, hx24])
  have hx25_sm : sm.readReg64 (.gpr 25#5) = pageOf maddrs.ctx := by
    simpa [arm64_norm] using hc25.trans (by simp [arm64_norm, hx25])
  have hProc_sm : MallocngProcPreserved s0 sm := by
    refine procPres_trans ?_ hProc_m0
    dsimp only [MallocngProcPreserved] at hProc ⊢; simp [arm64_norm, hProc]
  have hcsHi_sm : MallocImplUntouchedCS s0 sm :=
    untouchedCS_of_calleeSaved
      (untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm])
        (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
        (by first | rfl | simp [calleeSavedVRegs, arm64_norm])) hcs_m
  obtain ⟨hBit31_g, hBit31_e, hZIdx⟩ := bit31_false_of_readReg32_ofNat_fine hx0_m hIdx31
  obtain ⟨hExtSc3, hShlSc3⟩ := sc_sxtw_shl3_bv_fine hSc48
  have hSxMSc := sxtw_sbfm_ofNat hSc48
  have hZ32 : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 idx)) = BitVec.ofNat 64 idx := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hIdxB31 : (BitVec.ofNat 64 idx).getLsbD 31 = false := by
    have hAll : (List.range 32).all (fun k => decide ((BitVec.ofNat 64 k).getLsbD 31 = false)) = true := by decide
    exact of_decide_eq_true (List.all_eq_true.mp hAll idx (List.mem_range.mpr (by omega)))
  refine SepWP.seq (mid := b + miOff_slot_ldr22)
    (Mid := fun s2 P2 =>
      (s2.sp = s0.sp - 80#64 ∧ s2.brk = sm.brk ∧ s2.mem = sm.mem ∧
       MallocngProcPreserved s0 s2 ∧ MallocImplUntouchedCS s0 s2 ∧
       s2.readReg64 (.gpr 2#5) = maddrs.ctx + BitVec.ofNat 64 (8 * sc) ∧
       s2.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 st1.ctx.mmapCounter ∧
       s2.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
       s2.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
       s2.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx ∧
       s2.readReg64 (.gpr 24#5) = pageOf maddrs.lock) ∧
      (P2 ⊢ (maddrs.ctx ↦ₛ ctx1Bs) ∗
        (coreRest1 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) ?_ ?_
  · dsimp only [miOff_after_slot, miOff_slot_ldr22] at hpc_m ⊢
    dsimp only [Reg.x0] at hBit31_g hBit31_e hZIdx
    wp_steps
    apply SepWP.done
    · simp
    · simp [hrun_m]
    · refine ⟨⟨by simp [hsp_sm], rfl, rfl,
        by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc_sm,
        untouchedCS_step hcsHi_sm (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]),
        by simp [arm64_norm],
        by simp [arm64_norm],
        by simpa using hx20_sm,
        by simp only [arm64_norm, BitVec.ushiftRight_zero]; rw [and_u32_eq_zeroExtend_truncate_fine, hZ32, BitVec.or_zero],
        by simp only [arm64_norm],
        by simpa using hx24_sm⟩, Entails.refl _⟩
  · rintro s2 P2 hpc2 hrun2 ⟨⟨hsp2, hbrk2, hmem2, hProc2, hcs2, hx2_2, hx19_2, hx20_2, hx21_2, hx23_2, hx24_2⟩, hP2⟩
    apply SepWP.weaken_pre hP2
    have hAddr80 : (maddrs.ctx + BitVec.ofNat 64 (8 * sc)) + 80#64 =
        maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    refine SepWP.step_ldr64
      (s' := (s2.writeReg64 (.gpr 22#5) g.metaPtr).setPC (b + miOff_slot_b19c))
      hpc2 hrun2 (by dsimp only [miOff_slot_ldr22]; simp only [arm64_norm]; rfl) rfl
      (ea := maddrs.ctx + BitVec.ofNat 64 (80 + 8 * sc)) (wb := none)
      (by simp [evalAddrMode, hx2_2, hAddr80])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl)
      (by rw [applyWriteback, hGetAct1, ← hMetaEq, BitVec.add_assoc]; rfl) ?_
    refine SepWP.seq (mid := b + miOff_call_unlock)
      (Mid := fun s_u P_u =>
        (s_u.sp = s0.sp - 80#64 ∧ s_u.brk = sm.brk ∧ s_u.mem = sm.mem ∧
         MallocngProcPreserved s0 s_u ∧ MallocImplUntouchedCS s0 s_u ∧
         s_u.readReg64 (.gpr 0#5) = maddrs.lock ∧
         s_u.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 st1.ctx.mmapCounter ∧
         s_u.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req ∧
         s_u.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx ∧
         s_u.readReg64 (.gpr 22#5) = g.metaPtr ∧
         s_u.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) ∧
        (P_u ⊢ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
          MallocngRoTablesA maddrs ∗
          MallocngCoreStInflightModeA ro 1 γ maddrs brkStart sm.brk bud.liveCost bud.peakCost st1 ∗
          MallocngRuntime maddrs tp)) ?_ ?_
    · dsimp only [miOff_slot_b19c, miOff_call_unlock]
      wp_steps
      apply SepWP.done
      · simp
      · simp [hrun2]
      · refine ⟨⟨by simp [hsp2], hbrk2, hmem2,
          by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc2,
          untouchedCS_step hcs2 (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
            (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
          by first | simp [arm64_norm] | simp [hx24_2, arm64_norm] | simp [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, hx24_2, arm64_norm],
          by first | simpa using hx19_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx19_2,
          by first | simpa using hx20_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx20_2,
          by first | simpa using hx21_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx21_2,
          by simp [arm64_norm, hMetaEq],
          by first | simpa using hx23_2 | simpa [State.readReg64, State.writeReg64, State.setPC, RegFile.read, RegFile.write, arm64_norm] using hx23_2⟩, ?_⟩
        rw [← hCtx1Gen]
        dsimp only [MallocngCoreStInflightModeA, coreRest1]
        rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj]
        refine Entails.of_eq ?_
        generalize (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
          MallocngLiveAuth γ st1.liveMap = pGm,
          (maddrs.lock ↦₃₂ 0#32) = pLk,
          (maddrs.replaced ↦₃₂ 0#32) = pRp,
          (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
          MallocngAuxvPtrCell ro maddrs.libc st1.auxvPtr = pLb8,
          MallocngAuxvStateRo ro γ st1.auxvPtr st1.auxvSnap = pAx,
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal = pRw,
          ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
          MappedSet st1.masterDom (OwnedMappedByte st1) = pMs,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
    · rintro s_u P_u hpc_u hrun_u ⟨⟨hsp_u, hbrk_u, hmem_u, hProc_u, hcs_u, hx0_u, hx19_u, hx20_u, hx21_u, hx22_u, hx23_u⟩, hPu⟩
      rw [← hbrk_u] at hPu
      apply SepWP.weaken_pre hPu
      have hcl_u : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_u.mem := hmem_u ▸ hcl_m
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u ▸ hwf1
      have hNoRes0 : st0.reservedMetas = [] := by
        have hInf := hwf0.inflight_wf
        cases hR : st0.reservedMetas with
        | nil => rfl
        | cons _ _ => rw [hR] at hInf; simp at hInf
      have hNoRes1 : st1.reservedMetas = [] := hRes1.trans hNoRes0
      have hMetaLe1 : st1.metaAreas.length ≤
          1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 := by
        have hMeta0 := hCount0.2.2.2.2.1
        have hPeakLe : bud.peakCount ≤ (mallocngAllocBudget true req bud).peakCount := by
          dsimp [mallocngAllocBudget]; omega
        have hDivLe : (88 + 8 * bud.peakCount) / 101 ≤
            (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 :=
          Nat.div_le_div_right (by omega)
        have hMax : max st0.metaAreas.length (1 + (88 + 8 * bud.peakCount) / 101) =
            1 + (88 + 8 * bud.peakCount) / 101 := Nat.max_eq_right hMeta0
        omega
      dsimp only [State.setPC, State.writeReg64] at hNoOrph_st hDelta_m
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem := by
        rw [hCount0.2.2.1, hmem_u]
        unfold MallocngNoOrphanMappings at hNoOrph_st ⊢
        simpa [hPerm0] using hNoOrph_st
      have hDelta_u : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem s_u.mem := by
        rw [hmem_u]
        have hdLe := allocSlotDepthBound_le_three sc
        have hbStep := fineStepBound_slot_le (fineMaxMetaAreas bL) req sc hSc48
        obtain ⟨ivs, hl, hs, hc⟩ := hDelta_m
        exact ⟨ivs, by omega, Nat.le_trans hs hbStep,
          fun a ha => (hc a ha).imp (fun hm => hPerm0 ▸ hm) id⟩
      subst hb_eq
      rw [← mallocngBlockProg_eq_b09]
      have hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups :=
        (hGrpT (bud.peakCount + 6) (by omega) hCount0.2.2.2.2.2).mono
          (by dsimp [mallocngAllocBudget]; omega)
      exact mallocImpl_join_epilogue_fine hcl_u hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph1 hwf1_u hFine1 hNoRes1
        hg1 hIdxLt hClaimed1 hReqMax hFitG
        (fun _ => ⟨hGsc ▸ hSc48, hGsc ▸ hAllow⟩)
        (fun hGt => absurd hGt (by omega))
        (fun h => by rw [hGsc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hGsc ▸ h))
        (fun h => by rw [hGsc] at h; omega)
        (fun h => by rw [hGsc] at h; omega)
        hZeroMm1 htp0 hbrkS0 hDelta_u
        hpc_u hrun_u hsp_u hsp_align hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u

private theorem tryAvail_cbz_step_fine [MallocngMultiPlacement] {b target : BitVec 64}
    (hb : BlkBase 9 b) {s0 s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = b + miOff_try_avail) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx22 : s.readReg64 (.gpr 22#5) = 0#64)
    (hSlow : ∀ s' : State, s'.pc = b + miOff_alloc_prep → s'.status = .Running →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem = s.mem →
      MallocngProcPreserved s0 s' → MallocImplUntouchedCS s0 s' →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) →
      s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s' P post oom) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) target s P post oom := by
  have _ := hb
  dsimp only [miOff_try_avail] at hpc
  simp [State.readReg64] at hx22
  wp_step
  wp_if hCbz
  · exact hSlow _ rfl (by simp [hrun]) (by simp) rfl rfl
      (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc)
      (untouchedCS_step hcsHi (by simp) (by simp) (by simp) (by simp [calleeSavedVRegs]))
      (by simp) (by simp) (by simp) (by simp)
  · exact absurd hx22 hCbz

set_option maxHeartbeats 400000 in
private theorem tryAvail_nonnull_step_fine [MallocngMultiPlacement] {b target : BitVec 64}
    (hb : BlkBase 9 b) {metaPtr : BitVec 64} (hMetaNe : metaPtr ≠ 0#64)
    {metaBs ctxBs debBs : List (BitVec 8)}
    (hmLen : metaBs.length = 40) (hCtxLen : ctxBs.length = 928) (hDebLen : debBs.length = 32)
    {av mmc : BitVec 32}
    (hPkAv : pack32 (metaBs.getD 24 0#8) (metaBs.getD 25 0#8) (metaBs.getD 26 0#8) (metaBs.getD 27 0#8) = av)
    (hPkMmc : pack32 (ctxBs.getD 12 0#8) (ctxBs.getD 13 0#8) (ctxBs.getD 14 0#8) (ctxBs.getD 15 0#8) = mmc)
    {F : SepProp} {s0 s : State}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = b + miOff_try_avail) (hrun : s.status = .Running)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx22 : s.readReg64 (.gpr 22#5) = metaPtr)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx)
    (hSlow : ∀ s' : State, s'.pc = b + miOff_alloc_prep → s'.status = .Running →
      s'.sp = s.sp → s'.brk = s.brk → s'.mem = s.mem →
      MallocngProcPreserved s0 s' → MallocImplUntouchedCS s0 s' →
      s'.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) →
      s'.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s'.readReg64 (.gpr 24#5) = pageOf maddrs.lock →
      s'.readReg64 (.gpr 25#5) = pageOf maddrs.ctx →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s'
        ((metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom)
    (hFast : ∀ (_hAvNe : av ≠ 0#32) (s_u : State),
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_u.mem →
      s_u.pc = b + miOff_call_unlock → s_u.status = .Running →
      s_u.sp = s.sp → s_u.brk = s.brk → s_u.mem.perm = s.mem.perm →
      MallocngProcPreserved s0 s_u → MallocImplUntouchedCS s0 s_u →
      s_u.readReg64 (.gpr 0#5) = maddrs.lock →
      s_u.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 mmc →
      s_u.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) →
      s_u.readReg64 (.gpr 21#5) = BitVec.ofNat 64 (debBs.getD (((((-av) &&& av) * 0x076be629#32) >>> 27).toNat) 0#8).toNat →
      s_u.readReg64 (.gpr 22#5) = metaPtr →
      s_u.readReg64 (.gpr 23#5) = BitVec.ofNat 64 (debBs.getD (((((-av) &&& av) * 0x076be629#32) >>> 27).toNat) 0#8).toNat →
      SepWP (blkPC_b09.rebase b (fun _ => none)) target s_u
        ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
         (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) target s
      ((metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) post oom := by
  have _ := hb
  dsimp only [miOff_try_avail] at hpc
  wp_step
  wp_if hCbz
  · exfalso; simp [hMetaNe] at hCbz
  · wp_step
    try rw [hPkAv]
    wp_steps 3
    wp_if hAvZero
    · exact hSlow _ rfl (by simp [hrun]) (by simp) rfl rfl
        (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc)
        (untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
          (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]))
        (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
        (by first | exact hx24 | simpa [arm64_norm] using hx24)
        (by first | exact hx25 | simpa [arm64_norm] using hx25)
    · have hAvNe : av ≠ 0#32 := by rintro rfl; simp at hAvZero
      obtain ⟨hHashLt, _, _, hAnd255⟩ := tryAvail_bv_props_fine hAvNe
      obtain ⟨_, _, _, _, hNegIso, _, _, _⟩ := ctz32DeBruijn_spec hAvNe
      have hHashZ : BitVec.zeroExtend 64 ((((-av) &&& av) * 0x076be629#32) >>> 27) =
          BitVec.ofNat 64 ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat := by
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      generalize hHashEq : ((((-av) &&& av) * 0x076be629#32) >>> 27).toNat = hashIdx at hHashLt hHashZ hFast
      have hZHash : BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 hashIdx)) =
          BitVec.ofNat 64 hashIdx := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        have h32 : hashIdx < 2 ^ 32 := Nat.lt_trans hHashLt (by decide : 32 < 2 ^ 32)
        have h64 : hashIdx < 2 ^ 64 := Nat.lt_trans hHashLt (by decide : 32 < 2 ^ 64)
        rw [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32, Nat.mod_eq_of_lt h64]
      refine SepWP.seq (mid := b + miOff_try_str)
        (Mid := fun s_m Pm =>
          (s_m.sp = s.sp ∧ s_m.brk = s.brk ∧ s_m.mem = s.mem ∧
           MallocngProcPreserved s0 s_m ∧ MallocImplUntouchedCS s0 s_m ∧
           s_m.readReg32 (.gpr 0#5) = ((-av) &&& av) * 0x076be629#32 ∧
           s_m.readReg32 (.gpr 1#5) = av - ((-av) &&& av) ∧
           s_m.readReg64 (.gpr 3#5) = maddrs.debruijnFree ∧
           s_m.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
           s_m.readReg64 (.gpr 22#5) = metaPtr ∧
           s_m.readReg64 (.gpr 24#5) = pageOf maddrs.lock ∧
           s_m.readReg64 (.gpr 25#5) = maddrs.ctx) ∧
          (Pm ⊢ (metaPtr ↦ₛ metaBs) ∗ (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F)) ?_ ?_
      · dsimp only [miOff_try_str]; wp_steps
        apply SepWP.done
        · simp
        · simp [hrun]
        · refine ⟨⟨by simp, rfl, rfl,
            by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc,
            untouchedCS_step hcsHi (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
              (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
            by simp only [arm64_norm, BitVec.zero_sub, BitVec.zero_add, hNegIso],
            by simp only [arm64_norm, BitVec.zero_sub],
            by simp [arm64_norm],
            by first | rfl | simp [arm64_norm],
            by first | exact hx22 | simpa [arm64_norm] using hx22,
            by first | exact hx24 | simpa [arm64_norm] using hx24,
            by first | simp [arm64_norm] | simp [arm64_norm, hx25]⟩, Entails.refl _⟩
      · rintro s_m Pm hpc_m hrun_m ⟨⟨hsp_m, hbrk_m, hmem_m, hProc_m, hcs_m, hx0_m, hx1_m, hx3_m, hx20_m, hx22_m, hx24_m, hx25_m⟩, hPm⟩
        dsimp only [miOff_try_str] at hpc_m
        apply SepWP.weaken_pre hPm
        have hcl_sm : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_m.mem := hmem_m ▸ hcl
        apply step_str32_perm_kf
        · exact hpc_m
        · exact hrun_m
        · simp only [arm64_norm]; rfl
        · rfl
        · simp only [evalAddrMode, hx22_m]; rfl
        · exact hx1_m
        · wp_sep_access
        · wp_norm_lhs
        intro m_w hm_w _hkf
        have hcl_mw := hcl_sm.of_keepsFrozen _hkf; clear _hkf
        have hPerm1 : m_w.perm = s.mem.perm := hm_w.trans (congrArg Memory.perm hmem_m)
        refine SepWP.step_ldr32
          rfl (by simp [hrun_m]) (by simp only [arm64_norm]; rfl) rfl
          (ea := maddrs.ctx + 12#64) (wb := none)
          (by change (s_m.readReg64 (.gpr 25#5) + 12#64, none) = (maddrs.ctx + 12#64, none); rw [hx25_m])
          (SepLoad32.right ((SepLoad32.of_pointsToBytes (off := 12) rfl (by rw [hCtxLen]; decide) rfl).congr_val hPkMmc))
          (by wp_norm_lhs) ?_
        wp_step
        refine SepWP.seq (mid := b + miOff_try_ldrb)
          (Mid := fun s1 P1 =>
            (s1.sp = s.sp ∧ s1.brk = s.brk ∧ s1.mem = m_w ∧
             MallocngProcPreserved s0 s1 ∧ MallocImplUntouchedCS s0 s1 ∧
             s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 hashIdx ∧
             s1.readReg64 (.gpr 3#5) = maddrs.debruijnFree ∧
             s1.readReg64 (.gpr 19#5) = BitVec.zeroExtend 64 mmc ∧
             s1.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
             s1.readReg64 (.gpr 22#5) = metaPtr ∧
             s1.readReg64 (.gpr 24#5) = pageOf maddrs.lock) ∧
            (P1 ⊢ (maddrs.debruijnFree ↦ᵣ debBs) ∗
              ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
               (maddrs.ctx ↦ₛ ctxBs) ∗ F))) ?_ ?_
        · apply SepWP.done
          · dsimp only [miOff_try_ldrb]; simp
          · simp [hrun_m]
          · refine ⟨⟨by simp [hsp_m], hbrk_m, rfl,
              by repeat (first | apply procPres_setMem | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc_m,
              untouchedCS_step hcs_m (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
                (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]),
              by dsimp only [State.readReg32] at hx0_m; simp only [arm64_norm, hx0_m]; exact hHashZ,
              by simpa [arm64_norm] using hx3_m,
              by simp only [arm64_norm],
              by simpa [arm64_norm] using hx20_m,
              by simpa [arm64_norm] using hx22_m,
              by simpa [arm64_norm] using hx24_m⟩, ?_⟩
            refine Entails.of_eq ?_
            generalize (metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) = pM,
              (maddrs.ctx ↦ₛ ctxBs) = pCtx,
              (maddrs.debruijnFree ↦ᵣ debBs) = pDeb
            ac_rfl
        · rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hmem1, hProc1, hcs1, hx0_1, hx3_1, hx19_1, hx20_1, hx22_1, hx24_1⟩, hP1⟩
          apply SepWP.weaken_pre hP1
          have hAndIdx : (BitVec.ofNat 64 (debBs.getD hashIdx 0#8).toNat) &&& 255#64 =
              BitVec.ofNat 64 (debBs.getD hashIdx 0#8).toNat := hAnd255 (debBs.getD hashIdx 0#8)
          generalize hIdxEq : (debBs.getD hashIdx 0#8).toNat = idx at hAndIdx hFast
          refine SepWP.step_ldr8
            (s' := (s1.writeReg64 (.gpr 23#5) (BitVec.ofNat 64 idx)).setPC (b + miOff_try_after_ldrb))
            hpc1 hrun1 (by dsimp only [miOff_try_ldrb]; simp only [arm64_norm]; rfl) rfl
            (ea := maddrs.debruijnFree + BitVec.ofNat 64 hashIdx) (wb := none)
            (by simp only [evalAddrMode, extendVal, hx3_1, hx0_1]; rw [hZHash, BitVec.shiftLeft_zero])
            (SepLoad8.of_pointsToBytesRO rfl (Nat.succ_le_of_lt (hDebLen.symm ▸ hHashLt)) rfl)
            (by dsimp only [miOff_try_ldrb, miOff_try_after_ldrb]; rw [applyWriteback, writeReg_W32_zext8, hIdxEq, BitVec.add_assoc]; rfl) ?_
          dsimp only [miOff_try_after_ldrb]
          wp_steps 2
          have hRest :
              ((maddrs.debruijnFree ↦ᵣ debBs) ∗
               ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
                (maddrs.ctx ↦ₛ ctxBs) ∗ F)) =
              ((metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) ∗
               (maddrs.ctx ↦ₛ ctxBs) ∗ (maddrs.debruijnFree ↦ᵣ debBs) ∗ F) := by
            generalize (metaPtr ↦ₛ ByteSlice.write32 metaBs 24 (av - ((-av) &&& av))) = pM,
              (maddrs.ctx ↦ₛ ctxBs) = pCtx,
              (maddrs.debruijnFree ↦ᵣ debBs) = pDeb
            ac_rfl
          rw [hRest]
          exact hFast hAvNe _ (by simpa [hmem1] using hcl_mw)
            (by dsimp only [miOff_call_unlock]; rfl) (by simp [hrun1])
            (by simp [hsp1]) hbrk1 (by simpa [hmem1] using hPerm1)
            (by repeat (first | apply procPres_setPC | apply procPres_advancePC | apply procPres_setPState | apply procPres_writeReg64 | apply procPres_writeReg32); exact hProc1)
            (untouchedCS_step hcs1 (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [arm64_norm])
              (by first | rfl | simp [arm64_norm]) (by first | rfl | simp [calleeSavedVRegs, arm64_norm]))
            (by simp only [arm64_norm])
            (by simpa [arm64_norm] using hx19_1)
            (by simpa [arm64_norm] using hx20_1)
            (by simp only [arm64_norm])
            (by simpa [arm64_norm] using hx22_1)
            (by simp only [arm64_norm])

set_option maxHeartbeats 400000 in
private theorem mallocImpl_tryAvail_or_slow_fine [MallocngMultiPlacement] {ro : Bool}
    (hSlot : AllocSlotFineStmt ro)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req sc : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (hRoomSc : stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)
    (hReqMax : req ≤ MallocngMaxAllocSize) (hReqThr : req ≤ MmapThresholdReq)
    (hSc48 : sc < 48) (hAct : sc < st0.ctx.active.length)
    (hAllow : allowedPhysClass (nomSc req) sc = true)
    (hFitSc : req ≤ nominalSlotCap sc)
    (hSc2 : 2 ≤ sc ∧ sc < 48 → nominalSlotCap (sc - 2) < max req 16)
    (hSc24 : sc = 24 → nominalSlotCap 23 < req)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_try_avail) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx19 : s.readReg64 (.gpr 19#5) = BitVec.ofNat 64 sc)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = st0.ctx.active[sc]'hAct)
    (hx24 : s.readReg64 (.gpr 24#5) = pageOf maddrs.lock)
    (hx25 : s.readReg64 (.gpr 25#5) = pageOf maddrs.ctx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧
          MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) req) s0 sf⌝) := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b at hpc ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  by_cases hActZero : st0.ctx.active[sc]'hAct = 0#64
  · refine tryAvail_cbz_step_fine hb hpc hrun hProc hcsHi (hx22.trans hActZero) ?_
    intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
    rw [← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
    exact mallocImpl_allocSlot_slow_fine hSlot (hmem' ▸ hcl) hCount0 (by rw [hbrk']; exact hwf0)
      hFine0 hMa0 hRoomSc hReqMax hReqThr hSc48 hAllow hFitSc hSc2 hSc24
      htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
      (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
      (hx19'.trans hx19) (hx20'.trans hx20) (hx24'.trans hx24) (hx25'.trans hx25)
  · have hActNe : st0.ctx.active[sc]'hAct ≠ 0#64 := hActZero
    obtain ⟨hActLen, hUseLen, hUnmLen, hBncLen, hPadLen, hActLLen⟩ := hwf0.ctx_lens
    have hActL : sc < st0.activeLists.length := by omega
    have hwf_s : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
    obtain ⟨g, hg, hMetaEq, hGsc, _⟩ := active_head_group_of_nonzero hwf_s hAct hActL hActNe
    have hMetaNe : g.metaPtr ≠ 0#64 := hMetaEq ▸ hActNe
    have hNoRes0 : st0.reservedMetas = [] := by
      have hInf := hwf0.inflight_wf
      cases hR : st0.reservedMetas with
      | nil => rfl
      | cons _ _ => rw [hR] at hInf; simp at hInf
    have hExt0 := meta_extract hwf_s hNoRes0 hg
    obtain ⟨_, hPkAv, _, _, _, _, hWrAv⟩ :=
      metaBytes_ops g (ctz32DeBruijn g.availMask) (g.availMask - ((-g.availMask) &&& g.availMask)) .claimed
    have hmLen : g.metaBytes.length = 40 := by simp [GroupDesc.metaBytes]
    have hPadLen7 : st0.ctx.seqPad.length = 7 := by rw [hPadLen]; rfl
    have hGetMmc0 := (ctxBytes_ops st0.ctx hActLen hUseLen hUnmLen hBncLen hPadLen7).1
    have hCtxLen0 : st0.ctx.toBytes.length = 928 :=
      ctxBytes_length_fine st0.ctx hActLen hUseLen hUnmLen hBncLen hPadLen7
    have hDebLen : mallocngDebruijn32Table.length = 32 := debruijn32Table_length
    generalize hRoOther :
      ((maddrs.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
       (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗
       (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
       (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes)) = roOther
    have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗ roOther) := by
      rw [← hRoOther]; dsimp only [MallocngRoTablesA, MallocngRoTablesAt]
      generalize (maddrs.sizeClasses ↦ᵣ mallocngSizeClassBytes) = p1,
        (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = p2,
        (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) = p3,
        (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = p4,
        (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = p5
      ac_rfl
    generalize hCoreTail :
      (MallocngLiveAuth γ st0.liveMap ∗
       (maddrs.lock ↦₃₂ 0#32) ∗
       (maddrs.replaced ↦₃₂ 0#32) ∗
       (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr ∗
       MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap ∗
       ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal ∗
       ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
       MappedSet st0.masterDom (OwnedMappedByte st0)) = coreTail0
    have hCoreSplit0 :
        MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
      rw [← hCoreTail]
      have hwf0' : MallocngWFInflight 0 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
      dsimp only [MallocngCoreStInflightModeA]
      rw [propext ⟨fun _ => trivial, fun _ => hwf0'⟩, pure_true, emp_sepConj, hExt0]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        MallocngLiveAuth γ st0.liveMap = pGm,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
        MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
        ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
        ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
        MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
      ac_rfl
    have hPreFocus :
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
         MallocngRuntime maddrs tp) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗
         (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
         (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
         (roOther ∗ coreTail0 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) := by
      rw [hCoreSplit0, hRoSplit]
      generalize (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
        (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreFocus]
    refine tryAvail_nonnull_step_fine hb hMetaNe hmLen hCtxLen0 hDebLen hPkAv hGetMmc0
      hcl hpc hrun hProc hcsHi (hx22.trans hMetaEq.symm) hx24 hx25 ?_ ?_
    · intro s' hpc' hrun' hsp' hbrk' hmem' hProc' hcs' hx19' hx20' hx24' hx25'
      rw [← hPreFocus, ← hbrk', ← hb_eq, ← mallocngBlockProg_eq_b09]
      exact mallocImpl_allocSlot_slow_fine hSlot (hmem' ▸ hcl) hCount0 (by rw [hbrk']; exact hwf0)
        hFine0 hMa0 hRoomSc hReqMax hReqThr hSc48 hAllow hFitSc hSc2 hSc24
        htp0 hbrkS0 (by rw [hmem']; exact hPerm0)
        (by rwa [hb_eq]) hrun' (hsp'.trans hsp) hsp_align hProc' hcs'
        (hx19'.trans hx19) (hx20'.trans hx20) hx24' hx25'
    · intro hAvNe s_u hcl_u hpc_u hrun_u hsp_u hbrk_u hperm_u hProc_u hcs_u
        hx0_u hx19_u hx20_u hx21_u hx22_u hx23_u
      clear hRoOther hDebLen
      obtain ⟨hIdxSlots, hIdx32, hg'Mm, hMetaLen1, hCnt1, hDynEq1, hwf1, hg'Mem,
        _, hRwAbsorb, hPnEq, hMpEq⟩ := claimFreeAvail_absorb hwf_s hg hAvNe
      have hIdxEq : (mallocngDebruijn32Table.getD (((((-g.availMask) &&& g.availMask) * 0x076be629#32) >>> 27).toNat) 0#8).toNat =
          ctz32DeBruijn g.availMask := rfl
      rw [hIdxEq] at hx21_u hx23_u
      generalize hIdxGen : ctz32DeBruijn g.availMask = idx at hWrAv hIdxSlots hIdx32 hg'Mm hMetaLen1 hCnt1 hDynEq1 hwf1 hg'Mem hRwAbsorb hPnEq hMpEq hx21_u hx23_u
      let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
      let g' := mkReplaceSlotGroup g idx newAvail .claimed
      let val' := writeBytesToMap st0.byteVal g.metaPtr g'.metaBytes
      let st1 := mkReplaceSlotSt st0 g idx newAvail .claimed val' st0.liveMap
      have hPostEq :
          ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 (g.availMask - ((-g.availMask) &&& g.availMask))) ∗
           (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
           (roOther ∗ coreTail0 ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRuntime maddrs tp)) =
          (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
           MallocngRoTablesA maddrs ∗
           MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 ∗
           MallocngRuntime maddrs tp) := by
        have hCore1Eq :
            MallocngCoreStInflightModeA ro 1 γ maddrs brkStart s_u.brk bud.liveCost bud.peakCost st1 =
            ((g.metaPtr ↦ₛ g'.metaBytes) ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗ coreTail0) := by
          rw [hbrk_u, ← hCoreTail]
          have hwf1' : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1 := hwf1
          dsimp only [MallocngCoreStInflightModeA]
          rw [propext ⟨fun _ => trivial, fun _ => hwf1'⟩, pure_true, emp_sepConj]
          dsimp only [st1]
          rw [← hRwAbsorb, ← hPnEq, ← hMpEq]
          dsimp only [mkReplaceSlotSt]
          change (MallocngLiveAuth γ st0.liveMap ∗ (maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
            (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
            MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr ∗ MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap ∗
            ((g.metaPtr ↦ₛ g'.metaBytes) ∗
              ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal) ∗
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
            MappedSet st0.masterDom (OwnedMappedByte st0)) = _
          generalize (g.metaPtr ↦ₛ g'.metaBytes) = pM,
            (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
            MallocngLiveAuth γ st0.liveMap = pGm,
            (maddrs.lock ↦₃₂ 0#32) = pLk,
            (maddrs.replaced ↦₃₂ 0#32) = pRp,
            (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
            MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
            MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
            ByteMap st0.masterDom (fun a => OwnedRwByte st0 a ∧ ¬ InRegion g.metaPtr 40 a) st0.byteVal = pRw,
            ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
            MappedSet st0.masterDom (OwnedMappedByte st0) = pMs
          ac_rfl
        change ((g.metaPtr ↦ₛ ByteSlice.write32 g.metaBytes 24 newAvail) ∗ _) = _
        rw [hWrAv, hCore1Eq, hRoSplit]
        generalize (g.metaPtr ↦ₛ g'.metaBytes) = pM,
          (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
          (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) = pDeb,
          MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
          stackFrameAt (s0.sp - 80#64) 624 = pSf,
          MallocngRuntime maddrs tp = pRt
        ac_rfl
      rw [hPostEq]
      clear hPostEq hPreFocus hRoSplit hCoreTail hIdxEq hIdxGen
      have hwf1_u : MallocngWFInflight 1 maddrs.base brkStart s_u.brk bud.liveCost bud.peakCost st1 :=
        hbrk_u.symm ▸ hwf1
      have hPerm_u : s_u.mem.perm = s0.mem.perm := hperm_u.trans hPerm0
      have hMetaLe1 : st1.metaAreas.length ≤
          1 + (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 := by
        have hMeta0 := hCount0.2.2.2.2.1
        have hPeakLe : bud.peakCount ≤ (mallocngAllocBudget true req bud).peakCount := by
          dsimp [mallocngAllocBudget]; omega
        have hDivLe : (88 + 8 * bud.peakCount) / 101 ≤
            (88 + 8 * (mallocngAllocBudget true req bud).peakCount) / 101 :=
          Nat.div_le_div_right (by omega)
        rw [hMetaLen1]; omega
      have hMono1 : GroupsFreeMono st0.groups st1.groups :=
        GroupsFreeMono.map_ite hg g.metaPtr rfl rfl rfl rfl rfl
          (SlotUserSub.set_nonUser g.slots idx .claimed (fun _ _ _ h => by cases h))
      have hFine1 : FineSplitInv bL bP st1 :=
        FineSplitInv.of_groupsFreeMono hFine0 hwf_s hwf1
          (by rw [hMetaLen1]; exact hFine0.meta_le) hMono1
      have hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s_u.mem :=
        mallocngNoOrphanMappings_of_perm_eq (hDynEq1.trans hCount0.2.2.1.symm) hPerm_u
      have hDelta_u : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem s_u.mem :=
        ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPerm_u ▸ ha)⟩
      have hIdxSlots' : idx < g'.slots.length := by simpa [g', mkReplaceSlotGroup] using hIdxSlots
      have hClaimed' : g'.slots[idx]'hIdxSlots' = .claimed := by simp [g', mkReplaceSlotGroup]
      have hG'Sc : g'.sc = sc := by simpa [g', mkReplaceSlotGroup] using hGsc
      have hFitG' : req + 4 ≤ g'.stride := by
        have hStrGe : slotStride sc ≤ g.stride :=
          hGsc ▸ active_group_stride_ge_fine hwf_s hg (hGsc ▸ hSc48) hAvNe
        have hStrEq : g'.stride = g.stride := rfl
        have hSzPos := (sizeClass_bounds (sc := sc) hSc48).1
        dsimp [nominalSlotCap, slotStride] at hFitSc hStrGe
        omega
      subst hb_eq
      rw [← mallocngBlockProg_eq_b09]
      have hGrp1 : Cost.GroupsGrpBound ((mallocngAllocBudget true req bud).peakCount + 6) st1.groups := by
        have hG0 := hCount0.2.2.2.2.2.mono (V := (mallocngAllocBudget true req bud).peakCount + 6)
          (by dsimp [mallocngAllocBudget]; omega)
        exact hG0.map_ite g.metaPtr fun hm hs => hG0 g hg hm hs
      exact mallocImpl_join_epilogue_fine hcl_u hCount0 hCnt1 hMetaLe1 hGrp1 hNoOrph1 hwf1_u hFine1 hNoRes0
        hg'Mem hIdxSlots' hClaimed' hReqMax hFitG'
        (fun _ => ⟨hG'Sc ▸ hSc48, hG'Sc ▸ hAllow⟩)
        (fun hGt => absurd hGt (by omega))
        (fun h => by rw [hG'Sc] at h ⊢; exact hSc2 h)
        (fun h => hSc24 (hG'Sc ▸ h))
        (fun h => by rw [hG'Sc] at h; omega)
        (fun h => by rw [hG'Sc] at h; omega)
        (fun hMm => by rw [hg'Mm] at hMm; cases hMm)
        htp0 hbrkS0 hDelta_u
        hpc_u hrun_u (hsp_u.trans hsp) hsp_align hProc_u hcs_u
        hx0_u hx19_u (hx20_u.trans hx20) hx21_u hx22_u hx23_u

set_option maxHeartbeats 400000 in
private theorem mallocImpl_small_med_fine [MallocngMultiPlacement] {ro : Bool}
    (hSlot : AllocSlotFineStmt ro)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat}
    {st0 : MallocngSt} {s0 s : State}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (hRoom0 : req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
      ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
        stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)
    (hReq : req ≤ 131051)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hpc : s.pc = mbase 9 + miOff_small_entry) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧
          MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) req) s0 sf⌝) := by
  have hReqMax : req ≤ MallocngMaxAllocSize := by
    have := mallocngMaxAllocSize_eq; omega
  have hReqThr : req ≤ MmapThresholdReq := hReq
  let sc0 := sizeToClassUnits ((req + 3) / 16)
  obtain ⟨hsc0_lt, _, _⟩ := sizeToClass_spec hReq
  let stcFrame :=
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
    MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0
  have hPreStc :
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) =
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ stcFrame) := by
    dsimp only [stcFrame]
    generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s.brk bud.liveCost bud.peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    ac_rfl
  rw [hPreStc]
  refine sepWP_seq_cl (mid := mbase 9 + miOff_after_lock) hcl ?_
  refine SepWP.mono
    (mallocImpl_sizeToClass_lock_step (F := stcFrame) hReq rfl hpc hrun hsp hProc hcsHi hx20) ?_
    (fun _ _ _ h => (not_satisfies_false_sepConj h).elim)
  rintro s1 P1 hpc1 hrun1 ⟨⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx19_1, hx20_1, hx21_1, hx24_1⟩, hP1⟩ hcl1
  apply SepWP.weaken_pre hP1
  have hwf1_0 : MallocngWF maddrs.base brkStart s1.brk bud.liveCost bud.peakCost st0 :=
    hbrk1 ▸ hwf0
  let coarseRest :=
    MallocngLiveAuth γ st0.liveMap ∗
    (maddrs.lock ↦₃₂ 0#32) ∗
    (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗
    MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr ∗
    MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap ∗
    ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal ∗
    MappedSet st0.masterDom (OwnedMappedByte st0) ∗
    MallocngRoTablesA maddrs ∗
    MallocngRuntime maddrs tp ∗
    MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
    stackFrameAt (s0.sp - 80#64) 624
  have hCoreToCoarse :
      (MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗ stcFrame) =
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
       ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ coarseRest) := by
    have hwf0' : MallocngWFInflight 0 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st0 := hwf0
    dsimp only [stcFrame, MallocngCoreStInflightModeA, coarseRest]
    rw [propext ⟨fun _ => trivial, fun _ => hwf0'⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
      MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  have hCoarseBack : ∀ (brk' : BitVec 64)
      (_hwf' : MallocngWF maddrs.base brkStart brk' bud.liveCost bud.peakCost st0),
      ((maddrs.ctx ↦ₛ st0.ctx.toBytes) ∗
       ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal ∗ coarseRest) =
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart brk' bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp) := by
    intro brk' hwf'
    have hwf'' : MallocngWFInflight 0 maddrs.base brkStart brk' bud.liveCost bud.peakCost st0 := hwf'
    dsimp only [MallocngCoreStInflightModeA, coarseRest]
    rw [propext ⟨fun _ => trivial, fun _ => hwf''⟩, pure_true, emp_sepConj]
    generalize (maddrs.ctx ↦ₛ st0.ctx.toBytes) = pCtx,
      ByteMap st0.masterDom (OwnedRwByte st0) st0.byteVal = pRw,
      MallocngLiveAuth γ st0.liveMap = pGm,
      (maddrs.lock ↦₃₂ 0#32) = pLk,
      (maddrs.replaced ↦₃₂ 0#32) = pRp,
      (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
      MallocngAuxvPtrCell ro maddrs.libc st0.auxvPtr = pLb8,
      MallocngAuxvStateRo ro γ st0.auxvPtr st0.auxvSnap = pAx,
      ProtNoneByteMap st0.masterDom (OwnedProtNoneByte st0) st0.byteVal = pPn,
      MappedSet st0.masterDom (OwnedMappedByte st0) = pMs,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  rw [hCoreToCoarse]
  exact mallocImpl_coarse_step hwf1_0 hsc0_lt hpc1 hrun1 hsp1 hProc1 hcs1 hx19_1 hx20_1 hx21_1 hx24_1
    (fun sc s_t P_t hChoice hScLt hAct hpc_t hrun_t hsp_t hbrk_t hmem_t hProc_t hcs_t
         hx19_t hx20_t hx22_t hx24_t hx25_t hPt => by
      obtain ⟨_, hFitSc, hSc2, hSc24, _⟩ := coarseBump_sc_props hReq hChoice
      have hAllow : allowedPhysClass (nomSc req) sc = true :=
        allowedPhysClass_of_coarseChoice hScLt hChoice
      have hRoomSc := hRoom0 hReqMax hReqThr sc hScLt hAllow
      have hwf_t : MallocngWF maddrs.base brkStart s_t.brk bud.liveCost bud.peakCost st0 :=
        hbrk_t ▸ hwf1_0
      have hcl_t : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_t.mem := hmem_t ▸ hcl1
      have hPerm_t : s_t.mem.perm = s0.mem.perm := by
        rw [hmem_t]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPt (Entails.of_eq (hCoarseBack s_t.brk hwf_t)))
      exact mallocImpl_tryAvail_or_slow_fine hSlot hcl_t hCount0 hwf_t hFine0 hMa0 hRoomSc
        hReqMax hReqThr hScLt hAct hAllow hFitSc hSc2 hSc24 htp0 hbrkS0 hPerm_t
        hpc_t hrun_t hsp_t hsp_align hProc_t hcs_t
        hx19_t hx20_t hx22_t hx24_t hx25_t)
    (fun sc s_p P_p hChoice hScLt hpc_p hrun_p hsp_p hbrk_p hmem_p hProc_p hcs_p
         hx19_p hx20_p hx24_p hx25_p hPp => by
      obtain ⟨_, hFitSc, hSc2, hSc24, _⟩ := coarseBump_sc_props hReq hChoice
      have hAllow : allowedPhysClass (nomSc req) sc = true :=
        allowedPhysClass_of_coarseChoice hScLt hChoice
      have hRoomSc := hRoom0 hReqMax hReqThr sc hScLt hAllow
      have hwf_p : MallocngWF maddrs.base brkStart s_p.brk bud.liveCost bud.peakCost st0 :=
        hbrk_p ▸ hwf1_0
      have hcl_p : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s_p.mem := hmem_p ▸ hcl1
      have hPerm_p : s_p.mem.perm = s0.mem.perm := by
        rw [hmem_p]; exact hperm1.trans hPerm0
      apply SepWP.weaken_pre (Entails.trans hPp (Entails.of_eq (hCoarseBack s_p.brk hwf_p)))
      exact mallocImpl_allocSlot_slow_fine hSlot hcl_p hCount0 hwf_p hFine0 hMa0 hRoomSc
        hReqMax hReqThr hScLt hAllow hFitSc hSc2 hSc24 htp0 hbrkS0 hPerm_p
        hpc_p hrun_p hsp_p hsp_align hProc_p hcs_p
        hx19_p hx20_p hx24_p hx25_p)

/-! ## 4. Prologue, `ENOMEM` Branch, Dispatch, & `placed_libcMallocImpl_fine_raw_ok` -/

private abbrev miOff_save_cs_fine     : BitVec 64 := words_insn_off% mallocImplWords 0xa90153f3#32 0
private abbrev miOff_call_errno_fine  : BitVec 64 := reloc_call_off% mallocImplRelocs "___errno_location" 0
private abbrev miOff_after_errno_fine : BitVec 64 := words_insn_off% mallocImplWords 0xaa0003e1#32 0

private theorem ult_ofNat_iff_fine {c req : Nat} (hc : c < 2 ^ 64) (hr : req < 2 ^ 64) :
    ((BitVec.ofNat 64 c).ult (BitVec.ofNat 64 req) = true) ↔ c < req := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hr,
    decide_eq_true_eq]

private theorem stackFrame_704_split_prologue_fine (s0 : State) :
    stackFrame s0 704 =
      ((∃∗ v29 : BitVec 64, (s0.sp - 80#64) ↦₆₄ v29) ∗
       (∃∗ v30 : BitVec 64, ((s0.sp - 80#64) + 8#64) ↦₆₄ v30) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624) := by
  let sp1 := s0.sp - 80#64
  have hSplit : stackFrame s0 704 = (memRegion sp1 80 ∗ stackFrameAt sp1 624) := by
    unfold stackFrame
    rw [← stackFrameAt_eq_memRegion s0.sp 704, show (704 : Nat) = 80 + 624 from rfl,
        stackFrameAt_split s0.sp 80 624, stackFrameAt_eq_memRegion s0.sp 80]
  rw [hSplit,
      memRegion_split' (b := sp1) (b' := sp1 + 8#64) (n := 8) (k := 72) rfl rfl (by decide),
      memRegion_split' (b := sp1 + 8#64) (b' := sp1 + 16#64) (n := 8) (k := 64) rfl (by bv_lin) (by decide),
      memRegion_eight sp1, memRegion_eight (sp1 + 8#64)]
  simp only [sepConj_assoc]; rfl

private theorem enomem_repack_stackFrame_fine (s0 : State) :
    (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
     (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
     memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
     stackFrameAt (s0.sp - 80#64) 624) ⊢ stackFrame s0 704 := by
  rw [stackFrame_704_split_prologue_fine s0]
  exact sepConj_mono (Entails.sepExists_intro _)
    (sepConj_mono (Entails.sepExists_intro _) (Entails.refl _))

private theorem memRegion_64_unpack_fine (sp1 : BitVec 64) :
    memRegion (sp1 + 16#64) 64 =
      ((∃∗ v19 : BitVec 64, (sp1 + 16#64) ↦₆₄ v19) ∗
       (∃∗ v20 : BitVec 64, (sp1 + 24#64) ↦₆₄ v20) ∗
       (∃∗ v21 : BitVec 64, (sp1 + 32#64) ↦₆₄ v21) ∗
       (∃∗ v22 : BitVec 64, (sp1 + 40#64) ↦₆₄ v22) ∗
       (∃∗ v23 : BitVec 64, (sp1 + 48#64) ↦₆₄ v23) ∗
       (∃∗ v24 : BitVec 64, (sp1 + 56#64) ↦₆₄ v24) ∗
       (∃∗ v25 : BitVec 64, (sp1 + 64#64) ↦₆₄ v25) ∗
       (∃∗ vPad : BitVec 64, (sp1 + 72#64) ↦₆₄ vPad)) := by
  rw [memRegion_split' (b := sp1 + 16#64) (b' := sp1 + 24#64) (n := 8) (k := 56) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 24#64) (b' := sp1 + 32#64) (n := 8) (k := 48) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 32#64) (b' := sp1 + 40#64) (n := 8) (k := 40) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 40#64) (b' := sp1 + 48#64) (n := 8) (k := 32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 48#64) (b' := sp1 + 56#64) (n := 8) (k := 24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 56#64) (b' := sp1 + 64#64) (n := 8) (k := 16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp1 + 64#64) (b' := sp1 + 72#64) (n := 8) (k := 8) rfl (by bv_lin) (by decide),
      memRegion_eight (sp1 + 16#64), memRegion_eight (sp1 + 24#64),
      memRegion_eight (sp1 + 32#64), memRegion_eight (sp1 + 40#64),
      memRegion_eight (sp1 + 48#64), memRegion_eight (sp1 + 56#64),
      memRegion_eight (sp1 + 64#64), memRegion_eight (sp1 + 72#64)]

private structure AllGprCSPreservedFine (s0 s : State) : Prop where
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5)
  x20 : s.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5)
  x21 : s.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5)
  x22 : s.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5)
  x23 : s.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5)
  x24 : s.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5)
  x25 : s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5)
  x26 : s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5)
  x27 : s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5)
  x28 : s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5)
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0

private theorem allGprCS_of_calleeSaved_fine {s0 s1 s2 : State}
    (h1 : AllGprCSPreservedFine s0 s1) (h2 : CalleeSavedPreserved s1 s2) :
    AllGprCSPreservedFine s0 s2 := by
  obtain ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, _, cv⟩ := h2
  exact ⟨c19.trans h1.x19, c20.trans h1.x20, c21.trans h1.x21, c22.trans h1.x22,
    c23.trans h1.x23, c24.trans h1.x24, c25.trans h1.x25, c26.trans h1.x26,
    c27.trans h1.x27, c28.trans h1.x28, cv.trans h1.vregs⟩

private theorem allGprCS_bl_step_fine {s0 s : State} {lr pc' : BitVec 64}
    (h1 : AllGprCSPreservedFine s0 s) :
    AllGprCSPreservedFine s0 ((s.writeReg64 (.gpr 30#5) lr).setPC pc') :=
  ⟨by simpa using h1.x19, by simpa using h1.x20, by simpa using h1.x21,
   by simpa using h1.x22, by simpa using h1.x23, by simpa using h1.x24,
   by simpa using h1.x25, by simpa using h1.x26, by simpa using h1.x27,
   by simpa using h1.x28, by simpa [calleeSavedVRegs] using h1.vregs⟩

set_option maxHeartbeats 400000 in
private theorem mallocImpl_enomem_fine [MallocngMultiPlacement] {ro : Bool}
    {b : BitVec 64} (hb : BlkBase 9 b)
    {γ : GhostName} {tp brkStart : BitVec 64} {bCoarse : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {st0 : MallocngSt} {s0 s : State}
    {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hCount0 : MallocngCountIvsWF bCoarse ivs0 st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = b + miOff_call_errno_fine) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hbrk : s.brk = s0.brk) (hperm : s.mem.perm = s0.mem.perm)
    (hProc : MallocngProcPreserved s0 s) (hcs : AllGprCSPreservedFine s0 s) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngRuntime maddrs tp ∗
       MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0)
      (fun sf P_f =>
        (P_f ⊢
          ⌜MallocngProcPreserved s0 sf ∧
           MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) 0) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗
          (⌜sf.readReg64 .x0 = 0#64 ∧ sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart⌝ ∗
           MallocngRoTablesA maddrs ∗
           MallocngRuntime maddrs tp ∗
           ∃∗ st' : MallocngSt, ∃∗ bCoarse' : MallocngBudget,
             ⌜MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
              MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
              FineSplitInv bL bP st' ∧
              st'.groups = st'.groups ∧
              st'.metaAreas.length ≤ fineMaxMetaAreas bL⌝ ∗
             MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st')) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  have hUnpack :
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngRuntime maddrs tp ∗
       MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) =
      (∃∗ errnoVal : BitVec 32,
        ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 ∗
         ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) := by
    unfold MallocngRuntime
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepExists_congr fun errnoVal => ?_
    generalize ((tp - 0xa4#64) ↦₃₂ errnoVal) = pEr,
      ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
      ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 = pCr,
      ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
      (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
      memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
      stackFrameAt (s0.sp - 80#64) 624 = pSf
    ac_rfl
  rw [hUnpack]
  apply SepWP.exists_elim; intro errnoVal
  let errRest :=
    ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
    (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
    memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
    stackFrameAt (s0.sp - 80#64) 624 ∗
    MallocngRoTablesA maddrs ∗
    MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 ∗
    ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)
  change SepWP _ _ _ (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) _ _
  have hSpAl : s.spAligned = true := by
    dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
  dsimp only [miOff_call_errno_fine] at hpc
  wp_step
  have herr := VerifiedLibraries.Mallocng.Proofs.placed_errnoLocation_perm_ok
    (P := blkPC_b09.rebase b (fun _ => none))
  rw [at_bl_target_b09 hb 0 miOff_call_errno_fine] at herr
  dsimp only [miOff_call_errno_fine] at herr
  let errnoFrame := ((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest
  have hPreErr : (((tp - 0xa4#64) ↦₃₂ errnoVal) ∗ errRest) ⊢
      (emp ∗ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem⌝) ∗ errnoFrame := by
    rw [emp_sepConj]
    exact Entails.pure_right hcl (Entails.refl _)
  apply SepWP.weaken_pre hPreErr
  refine SepWP.call_subroutine_frame (F := errnoFrame) (x := ()) (ret_pc := b + miOff_after_errno_fine)
    herr (by subst hb; rfl)
    (by simp [arm64_norm, hrun])
    (by simpa [State.spAligned, arm64_norm] using hSpAl)
    (by dsimp only [miOff_after_errno_fine]; simp [arm64_norm])
    (fun R' hm => by simpa [withCL, sepConj_assoc, arm64_norm] using hm)
    (fun R' sf _ hp => not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => not_satisfies_false_sepConj he)
    ?_
    (fun R' sf _ ho => False.elim (not_satisfies_false_sepConj ho))
  intro s_e hpc_e hrun_e hsp_e hcs_e
  dsimp only [withCL]
  rw [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hProc_e, hbrk_e, hperm_e, hx0_e⟩
  apply SepWP.pure_elim; intro _hcl_e
  have hsp_se : s_e.sp = s0.sp - 80#64 := by simpa [arm64_norm] using hsp_e.trans hsp
  have hbrk_se : s_e.brk = s0.brk := by simpa [arm64_norm] using hbrk_e.trans hbrk
  have hperm_se : s_e.mem.perm = s0.mem.perm := by simpa [arm64_norm] using hperm_e.trans hperm
  have hProc_se : MallocngProcPreserved s0 s_e :=
    procPres_trans (procPres_setPC (procPres_writeReg64 hProc)) hProc_e
  have hcs_se : AllGprCSPreservedFine s0 s_e :=
    allGprCS_of_calleeSaved_fine (allGprCS_bl_step_fine hcs) hcs_e
  have hx0_tp : s_e.readReg64 (.gpr 0#5) = tp - 0xa4#64 := by
    have htp_s : s.tpidrEl0 = tp := hProc.2.2.1.trans htp0
    simpa [Reg.x0, htp_s] using hx0_e
  clear hx0_e
  dsimp only [errnoFrame, errRest]
  dsimp only [miOff_after_errno_fine] at hpc_e
  wp_steps 3
  wp_str32_perm m_er hm_er
  have hSpAl_se : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := sp_sub_80_aligned hsp_align
  generalize hsp1_eq : s0.sp - 80#64 = sp1 at hsp_se hSpAl_se ⊢
  wp_steps 3
  subst hsp1_eq
  have hSpAdd : (s0.sp - 80#64) + 80#64 = s0.sp := by bv_lin
  apply SepWP.done
  · simp [arm64_norm]
  · simp [arm64_norm, hrun_e]
  · refine ⟨?_, by simp [arm64_norm, hSpAdd], ?_⟩
    · have hPermF : m_er.perm = s0.mem.perm := hm_er.trans hperm_se
      have hDeltaF : MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) 0) s0.mem m_er :=
        ⟨[], Nat.zero_le _, Nat.zero_le _, fun a ha => Or.inl (hPermF ▸ ha)⟩
      have hNoOrphF : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st0) s0.mem m_er :=
        VerifiedLibraries.Mallocng.Proofs.mallocngNoOrphanMappings_of_perm_eq hCount0.2.2.1.symm hPermF
      refine Entails.pure_right ⟨by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [arm64_norm, hProc_se.1, hProc_se.2.1, hProc_se.2.2.1, hProc_se.2.2.2.1,
            hProc_se.2.2.2.2.1, hProc_se.2.2.2.2.2.1, hProc_se.2.2.2.2.2.2], hDeltaF⟩ ?_
      have hRearr :
          (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
           (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624 ∗
            MallocngRoTablesA maddrs ∗
            MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 ∗
            ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64))) =
          ((((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
            (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
            memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
            stackFrameAt (s0.sp - 80#64) 624) ∗
           (MallocngRoTablesA maddrs ∗
            (((tp - 0xa4#64) ↦₃₂ 12#32) ∗
             ((maddrs.libc + 3#64) ↦₈ 0#8) ∗ ((maddrs.libc + 48#64) ↦₆₄ 4096#64)) ∗
            MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0)) := by
        generalize ((tp - 0xa4#64) ↦₃₂ 12#32) = pEr,
          ((maddrs.libc + 3#64) ↦₈ 0#8) = pL3,
          ((maddrs.libc + 48#64) ↦₆₄ 4096#64) = pL48,
          MallocngRoTablesA maddrs = pRo,
          MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 = pCr,
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
          (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
          memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
          stackFrameAt (s0.sp - 80#64) 624 = pSf
        ac_rfl
      rw [hRearr]
      refine sepConj_mono (enomem_repack_stackFrame_fine s0) ?_
      refine Entails.pure_right
        ⟨by simp [arm64_norm],
         by simp [arm64_norm, hProc_se.2.2.1, htp0],
         by simp [arm64_norm, hProc_se.2.2.2.1, hbrkS0]⟩ ?_
      refine sepConj_mono (Entails.refl _) (sepConj_mono ?_ ?_)
      · unfold MallocngRuntime
        exact sepConj_mono (Entails.sepExists_intro 12#32) (Entails.refl _)
      · refine Entails.trans ?_ (Entails.sepExists_intro st0)
        refine Entails.trans ?_ (Entails.sepExists_intro bCoarse)
        refine Entails.pure_right ⟨hNoOrphF, hCount0.2.2.1 ▸ hCount0, hFine0, rfl, hMa0⟩ ?_
        (try simp only [arm64_norm, hbrk_se])
        exact Entails.refl _
    · exact ⟨by simpa [arm64_norm] using hcs_se.x19,
        by simpa [arm64_norm] using hcs_se.x20,
        by simpa [arm64_norm] using hcs_se.x21,
        by simpa [arm64_norm] using hcs_se.x22,
        by simpa [arm64_norm] using hcs_se.x23,
        by simpa [arm64_norm] using hcs_se.x24,
        by simpa [arm64_norm] using hcs_se.x25,
        by simpa [arm64_norm] using hcs_se.x26,
        by simpa [arm64_norm] using hcs_se.x27,
        by simpa [arm64_norm] using hcs_se.x28,
        by simp [arm64_norm],
        by simpa [calleeSavedVRegs] using hcs_se.vregs⟩

set_option maxHeartbeats 400000 in
private theorem mallocImpl_save_cs_dispatch_fine [MallocngMultiPlacement] {ro : Bool}
    (hMeta : AllocMetaFineStmt ro) (hSlot : AllocSlotFineStmt ro)
    {b : BitVec 64} (hb : BlkBase 9 b)
    {γ : GhostName} {tp brkStart : BitVec 64} {bud : MallocngBudget} {bL bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat}
    {st0 : MallocngSt} {s0 s1 : State}
    (hcl1 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s1.mem)
    (hCount0 : MallocngCountIvsWF bud ivs0 st0)
    (hwf0 : MallocngWF maddrs.base brkStart s1.brk bud.liveCost bud.peakCost st0)
    (hFine0 : FineSplitInv bL bP st0)
    (hMa0 : st0.metaAreas.length ≤ fineMaxMetaAreas bL)
    (hRoom0 : req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
      ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
        stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hPerm1 : s1.mem.perm = s0.mem.perm)
    (hpc1 : s1.pc = b + miOff_save_cs_fine) (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hx0_1 : s1.readReg64 (.gpr 0#5) = BitVec.ofNat 64 req)
    (hProc1 : MallocngProcPreserved s0 s1) (hcs1 : AllGprCSPreservedFine s0 s1) :
    SepWP (blkPC_b09.rebase b (fun _ => none)) (s0.readReg64 (.gpr 30#5)) s1
      (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
       (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
       memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
       stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ ⌜MallocngProcPreserved s0 sf ∧
          MallocngMappedDelta 16 (FineStepBound (fineMaxMetaAreas bL) req) s0.mem sf.mem⌝ ∗
          stackFrame s0 704 ∗ mallocImplFineSuccessBody ro γ tp brkStart bL bP ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) req) s0 sf⌝) := by
  have _ := hb
  have hReq2_64 : req < 2 ^ 64 := by
    have := mallocngMaxAllocSize_eq; omega
  have hSpAl1 : ((s0.sp - 80#64) &&& 15#64 == 0#64) = true := sp_sub_80_aligned hsp_align
  generalize hsp1_eq : s0.sp - 80#64 = sp1 at hsp1 hSpAl1 ⊢
  rw [memRegion_64_unpack_fine sp1]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v19
  apply SepWP.exists_elim; intro v20
  apply SepWP.exists_elim; intro v21
  apply SepWP.exists_elim; intro v22
  apply SepWP.exists_elim; intro v23
  apply SepWP.exists_elim; intro v24
  apply SepWP.exists_elim; intro v25
  apply SepWP.exists_elim; intro vPad
  dsimp only [miOff_save_cs_fine] at hpc1
  wp_stp64_cl m2 hm2 hcl1 hcl2
  wp_steps 2
  wp_stp64_cl m3 hm3 hcl2 hcl3
  wp_steps 2
  wp_stp64_cl m4 hm4 hcl3 hcl4
  wp_str64_cl m5 hm5 hcl4 hcl5
  wp_step
  have hPerm5 : m5.perm = s0.mem.perm :=
    hm5.trans (hm4.trans (hm3.trans (hm2.trans hPerm1)))
  refine SepWP.weaken_pre (?_ : _ ⊢
      MallocImplSavedRegs s0 sp1 ∗ stackFrameAt sp1 624 ∗
      MallocngRoTablesA maddrs ∗
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 ∗
      MallocngRuntime maddrs tp) ?_
  · generalize stackFrameAt sp1 624 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s1.brk bud.liveCost bud.peakCost st0 = pCr,
      MallocngRuntime maddrs tp = pRt
    have hA24 : (sp1 + 16#64) + 8#64 = sp1 + 24#64 := by bv_lin
    have hA40 : (sp1 + 32#64) + 8#64 = sp1 + 40#64 := by bv_lin
    have hA56 : (sp1 + 48#64) + 8#64 = sp1 + 56#64 := by bv_lin
    (try simp only [arm64_norm])
    (try rw [hA24]); (try rw [hA40]); (try rw [hA56])
    rw [hcs1.x19, hcs1.x20, hcs1.x21, hcs1.x22, hcs1.x23, hcs1.x24, hcs1.x25]
    unfold MallocImplSavedRegs
    simp only [sepConj_assoc]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (Entails.sepExists_intro _))))))))))
  subst hsp1_eq
  have hb_eq : mbase 9 = b := hb.symm
  subst hb_eq
  wp_if hHiLarge
  · have hGt131 : 131051 < req := by
      (try rw [hx0_1] at hHiLarge)
      rw [ult_ofNat_iff_fine (by decide) hReq2_64] at hHiLarge
      exact hHiLarge
    rw [← mallocngBlockProg_eq_b09]
    exact mallocImpl_large_fine hMeta hcl5 hCount0 hwf0 hFine0 hMa0 hGt131 hReqMax
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_large_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)
  · have hLe131 : req ≤ 131051 := by
      have hF : ¬ 131051 < req := fun hLt =>
        hHiLarge (by (try rw [hx0_1]); exact (ult_ofNat_iff_fine (by decide) hReq2_64).mpr hLt)
      omega
    rw [← mallocngBlockProg_eq_b09]
    exact mallocImpl_small_med_fine hSlot hcl5 hCount0 hwf0 hFine0 hMa0 hRoom0 hLe131
      htp0 hbrkS0 hPerm5 (by dsimp only [miOff_small_entry]; rfl)
      (by simp [arm64_norm, hrun1]) (by simpa [arm64_norm] using hsp1) hsp_align
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp [arm64_norm, hProc1.1, hProc1.2.1, hProc1.2.2.1, hProc1.2.2.2.1,
              hProc1.2.2.2.2.1, hProc1.2.2.2.2.2.1, hProc1.2.2.2.2.2.2])
      ⟨by simpa [arm64_norm] using hcs1.x26, by simpa [arm64_norm] using hcs1.x27,
       by simpa [arm64_norm] using hcs1.x28, by simpa [calleeSavedVRegs] using hcs1.vregs⟩
      (by simp only [arm64_norm]; try exact hx0_1)

private def rawPreSpatialFine [MallocngMultiPlacement] (ro : Bool)
    (γ : GhostName) (tp brkStart : BitVec 64) (bL bP : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) (s0 : State) : SepProp :=
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

set_option maxHeartbeats 400000 in
theorem placed_libcMallocImpl_fine_raw_ok {ro : Bool}
    (hMeta : AllocMetaFineStmt ro) (hSlot : AllocSlotFineStmt ro) : LibcMallocImplFineRawStmt ro := by
  intro _ γ tp brkStart bL bP ivs0 req
  dsimp only [libcMallocImplFineRawSpec]
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  apply subroutine_ok_of_sepWP_init
  intro _ R s0 hpc hrun hpre hspAl0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hspAl0
  let rawSp := rawPreSpatialFine ro γ tp brkStart bL bP ivs0 req s0
  have hpre1 : s0.mem ⊨
      ⌜s0.mem = m0 ∧ (s0.readReg64 .x0).toNat = req ∧
       s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
      (rawSp ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [rawSp, rawPreSpatialFine]
    change (⌜s0.mem = m0⌝ ∗ (⌜(s0.readReg64 .x0).toNat = req ∧
        s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        rawPreSpatialFine ro γ tp brkStart bL bP ivs0 req s0)) ∗ R ⊢ _
    rw [← sepConj_assoc]
    refine Entails.trans (Entails.of_eq (by ac_rfl) :
      _ ⊢ ⌜s0.mem = m0⌝ ∗
          ⌜(s0.readReg64 .x0).toNat = req ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
          (rawPreSpatialFine ro γ tp brkStart bL bP ivs0 req s0 ∗ R)) ?_
    apply Entails.pure_left; intro hm0
    apply Entails.pure_left; rintro ⟨hx0, htp0, hbrkS0⟩
    exact Entails.pure_right ⟨hm0, hx0, htp0, hbrkS0⟩ (Entails.refl _)
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨⟨hm0, hx0_nat, htp0, hbrkS0⟩, hpre_sp⟩ := hpre1
  have hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hm0 ▸ hcl0
  have hReq2_64 : req < 2 ^ 64 := hx0_nat ▸ (s0.readReg64 .x0).isLt
  have hx0_bv : s0.readReg64 (.gpr 0#5) = BitVec.ofNat 64 req := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hReq2_64]
    simpa [Reg.x0] using hx0_nat
  refine ⟨rawSp, hpre_sp, ?_⟩
  have hPullEx :
      rawSp ⊢
      ∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧
         FineSplitInv bL bP st0 ∧
         st0.metaAreas.length ≤ fineMaxMetaAreas bL ∧
         (req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
           ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
             stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)⌝ ∗
        (stackFrame s0 704 ∗
         MallocngRoTablesA maddrs ∗
         MallocngRuntime maddrs tp ∗
         MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) := by
    dsimp only [rawSp, rawPreSpatialFine]
    simp only [sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro st0
    apply Entails.sepExists_elim; intro bCoarse
    refine Entails.trans ?_ (Entails.sepExists_intro st0)
    refine Entails.trans ?_ (Entails.sepExists_intro bCoarse)
    generalize
      (MallocngCountIvsWF bCoarse ivs0 st0 ∧
       FineSplitInv bL bP st0 ∧
       st0.metaAreas.length ≤ fineMaxMetaAreas bL ∧
       (req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
         ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
           stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)) = pPure,
      stackFrame s0 704 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 = pCr
    exact Entails.of_eq (by ac_rfl)
  apply SepWP.weaken_pre hPullEx
  apply SepWP.exists_elim; intro st0
  apply SepWP.exists_elim; intro bCoarse
  apply SepWP.pure_elim; rintro ⟨hCount0, hFine0, hMa0, hRoom0⟩
  rw [stackFrame_704_split_prologue_fine s0]
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro v29
  apply SepWP.exists_elim; intro v30
  rw [mallocngBlockProg_eq_b09]
  have hpc0 : s0.pc = mbase 9 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 9 = b at hpc0 ⊢
  have hb : BlkBase 9 b := hb_eq.symm
  wp_stp64_cl m1 hm1 hcl hcl1
  wp_steps 5
  have hMaxVal : (9223372036854771710#64 : BitVec 64) = BitVec.ofNat 64 MallocngMaxAllocSize := by
    rw [mallocngMaxAllocSize_eq]
  have hMax2_64 : MallocngMaxAllocSize < 2 ^ 64 := by
    rw [mallocngMaxAllocSize_eq]; decide
  wp_if hHiMax
  · have hGtMax : MallocngMaxAllocSize < req := by
      rw [hMaxVal, ult_ofNat_iff_fine hMax2_64 hReq2_64] at hHiMax
      exact hHiMax
    have hNotLe : ¬ req ≤ MallocngMaxAllocSize := by omega
    have hOkFalse : decide (req ≤ MallocngMaxAllocSize) = false := decide_eq_false hNotLe
    conv => arg 6; ext sf; rw [hOkFalse]; dsimp only [Bool.false_eq_true, ↓reduceIte]
    refine SepWP.mono
      (mallocImpl_enomem_fine
        (oom := fun sf => ⌜MallocngStepOomCond msvc (FineStepBound (fineMaxMetaAreas bL) 0) s0 sf⌝)
        hb hcl1 hCount0 hFine0 hMa0 htp0 hbrkS0
        (by dsimp only [miOff_call_errno_fine]; rfl)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        hsp_align
        (by simp [arm64_norm])
        (by simpa [arm64_norm] using hm1)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩) ?_
    rintro sf P_f _ _ ⟨hEnt, hsp_f, hcs_f⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hsp_f, hcs_f⟩
    have hIteF : ∀ (α : Sort _) (t e : α), (if req ≤ MallocngMaxAllocSize then t else e) = e := by
      intro _ _ _
      split
      · next h => exact absurd h hNotLe
      · rfl
    dsimp only
    rw [hOkFalse, hIteF]
    exact hEnt
  · have hReqMax : req ≤ MallocngMaxAllocSize := by
      have hF : ¬ MallocngMaxAllocSize < req := fun hLt =>
        hHiMax (by rw [hMaxVal]; exact (ult_ofNat_iff_fine hMax2_64 hReq2_64).mpr hLt)
      omega
    have hOkTrue : decide (req ≤ MallocngMaxAllocSize) = true := decide_eq_true hReqMax
    have hCoreDup :
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngRuntime maddrs tp ∗
         MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) ⊢
        ⌜MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0⌝ ∗
        (((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) ∗
         (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) ∗
         memRegion ((s0.sp - 80#64) + 16#64) 64 ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗
         MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 ∗
         MallocngRuntime maddrs tp) := by
      dsimp only [MallocngCoreStModeA]
      have hDupWf :
          MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 ⊢
            ⌜MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0⌝ ∗
            MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 := by
        dsimp only [MallocngCoreStInflightModeA]
        apply Entails.pure_left; intro hwf0
        exact Entails.pure_right hwf0 (Entails.pure_right hwf0 (Entails.refl _))
      refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right hDupWf)))))) ?_
      generalize MallocngCoreStInflightModeA ro 0 γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 = pBody,
        ((s0.sp - 80#64) ↦₆₄ s0.readReg64 (.gpr 29#5)) = p29,
        (((s0.sp - 80#64) + 8#64) ↦₆₄ s0.readReg64 (.gpr 30#5)) = p30,
        memRegion ((s0.sp - 80#64) + 16#64) 64 = pMid,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocngRoTablesA maddrs = pRo,
        MallocngRuntime maddrs tp = pRt,
        MallocngWF maddrs.base brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0 = pWf
      exact Entails.of_eq (by ac_rfl)
    apply SepWP.weaken_pre hCoreDup
    apply SepWP.pure_elim; intro hwf0
    conv => arg 6; ext sf; rw [hOkTrue]; dsimp only [↓reduceIte]
    refine SepWP.mono
      (mallocImpl_save_cs_dispatch_fine hMeta hSlot hb hcl1 hCount0
        (by simpa [arm64_norm] using hwf0) hFine0 hMa0 hRoom0 hReqMax htp0 hbrkS0
        (by simpa [arm64_norm] using hm1)
        (by dsimp only [miOff_save_cs_fine]; rfl)
        (by simp [arm64_norm, hrun])
        (by simp [arm64_norm])
        hsp_align
        (by simpa [arm64_norm] using hx0_bv)
        (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [arm64_norm])
        ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
         by simp [arm64_norm], by simp [arm64_norm], by simp [calleeSavedVRegs]⟩) ?_
    rintro sf P_f _ _ ⟨hEnt, hsp_f, hcs_f⟩
    refine ⟨fun hm => Satisfies.mono (sepConj_mono_left ?_) hm, hsp_f, hcs_f⟩
    have hIteT : ∀ (α : Sort _) (t e : α), (if req ≤ MallocngMaxAllocSize then t else e) = t := by
      intro _ _ _
      split
      · rfl
      · next h => exact absurd hReqMax h
    dsimp only
    rw [hOkTrue, hIteT]
    exact hEnt

private theorem b04_tail_to_b09_fine [MallocngMultiPlacement] {spec : Spec Unit}
    (h9 : subroutine_ok (mallocngBlockProg mmpl 9 msvc) (mbase 9) (withCL mmpl spec))
    (hPrePC : ∀ s0 pc', spec.pre () (s0.setPC pc') = spec.pre () s0)
    (hPostPC : ∀ s0 pc' sf, spec.post () (s0.setPC pc') sf = spec.post () s0 sf)
    (hOomPC : ∀ s0 pc' sf, spec.onOom () (s0.setPC pc') sf = spec.onOom () s0 sf)
    (hNoPanic : ∀ s0 sf, spec.onPanic () s0 sf = ⌜False⌝)
    (hNoExit : ∀ code s0 sf, spec.onExit () code s0 sf = ⌜False⌝) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4) (withCL mmpl spec) := by
  apply subroutine_ok_of_sepWP_init
  intro u R s0 hpc hrun hpre hspAl0
  cases u
  have hpre_cl : s0.mem ⊨ ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ ∗ (spec.pre () s0 ∗ R) := by
    refine Satisfies.mono ?_ hpre
    dsimp only [withCL]
    rw [sepConj_comm (spec.pre () s0), sepConj_assoc]
    exact Entails.refl _
  rw [satisfies_pure_sepConj] at hpre_cl
  have hcl0 : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem := hpre_cl.1
  refine ⟨(withCL mmpl spec).pre () s0, hpre, ?_⟩
  rw [mallocngBlockProg_eq_b04]
  have hpc0 : s0.pc = mbase 4 + 0#64 := by rw [hpc, BitVec.add_zero]
  generalize hb_eq : mbase 4 = b4 at hpc0 ⊢
  have hb4 : BlkBase 4 b4 := hb_eq.symm
  have _ := hb4
  wp_step
  subst hb_eq
  have hTarget9 : mbase 4 + (mbase 9 - mbase 4) = mbase 9 := by bv_arith
  rw [hTarget9]
  refine sepWP_of_other_mallocng_block (j := 9) (svc := msvc) (by decide) hcl0
    (fun pc => externAt?_placedProgram_rebase_none _ _ _ _ pc) rfl ?_
  refine SepWP.call_subroutine_frame (F := emp) (x := ()) (ret_pc := s0.readReg64 .lr) h9
    rfl hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL] at hp
      rw [hNoPanic] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL] at he
      rw [hNoExit] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · dsimp only [withCL] at hm ⊢
    rw [hPrePC]
    simpa [emp_sepConj] using hm
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    dsimp only [withCL] at hm ⊢
    rw [hPostPC] at hm
    simpa [sepConj_emp] using hm
  · dsimp only [withCL] at ho ⊢
    rw [hOomPC] at ho
    simpa [emp_sepConj] using ho

private theorem fine_raw_pre_of_model_env [MallocngMultiPlacement] {ro : Bool}
    {γ : GhostName} {tp brkStart : BitVec 64} {bgt bP : FineBudget}
    {ivs0 : List (BitVec 64 × Nat)} {req : Nat} {s0 : State}
    (hSplit : ∀ st0, MallocngFineInv bgt ivs0 st0 → FineSplitInv bgt bP st0)
    (hRoom : ∀ st0, MallocngFineInv bgt ivs0 st0 →
      req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
      ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
        stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc) :
    (⌜(s0.readReg64 .x0).toNat = req⌝ ∗
     stackFrame s0 704 ∗
     MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0) ⊢
    (⌜(s0.readReg64 .x0).toNat = req ∧ s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
     stackFrame s0 704 ∗
     MallocngRoTablesA maddrs ∗
     MallocngRuntime maddrs tp ∗
     ∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
       ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧
        FineSplitInv bgt bP st0 ∧
        st0.metaAreas.length ≤ fineMaxMetaAreas bgt ∧
        (req ≤ MallocngMaxAllocSize → req ≤ MmapThresholdReq →
          ∀ sc < 48, allowedPhysClass (nomSc req) sc = true →
            stLiveUserInClass st0 sc + 1 ≤ peakPhysOfBudget bP sc)⌝ ∗
       MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) := by
  dsimp only [MallocngModelEnv]
  rw [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
  dsimp only [FineCoreModeImpl]
  have hRearr :
      (⌜(s0.readReg64 .x0).toNat = req⌝ ∗
       stackFrame s0 704 ∗
       ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
       (MallocngRoTablesA maddrs ∗
        ∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
          ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧ MallocngFineInv bgt ivs0 st0⌝ ∗
          MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) ∗
       MallocngRuntime maddrs tp) =
      (⌜(s0.readReg64 .x0).toNat = req⌝ ∗
       ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
       stackFrame s0 704 ∗
       MallocngRoTablesA maddrs ∗
       MallocngRuntime maddrs tp ∗
       (∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
         ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧ MallocngFineInv bgt ivs0 st0⌝ ∗
         MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0)) := by
    generalize ⌜(s0.readReg64 .x0).toNat = req⌝ = pX0,
      ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ = pTp,
      stackFrame s0 704 = pSf,
      MallocngRoTablesA maddrs = pRo,
      MallocngRuntime maddrs tp = pRt,
      (∃∗ st0 : MallocngSt, ∃∗ bCoarse : MallocngBudget,
        ⌜MallocngCountIvsWF bCoarse ivs0 st0 ∧ MallocngFineInv bgt ivs0 st0⌝ ∗
        MallocngCoreStModeA ro γ maddrs brkStart s0.brk bCoarse.liveCost bCoarse.peakCost st0) = pEx
    ac_rfl
  rw [hRearr]
  apply Entails.pure_left; intro hx0
  apply Entails.pure_left; rintro ⟨htp, hbrk⟩
  refine Entails.pure_right ⟨hx0, htp, hbrk⟩ ?_
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  apply Entails.sepExists_elim; intro st0
  refine Entails.trans ?_ (Entails.sepExists_intro st0)
  apply Entails.sepExists_elim; intro bCoarse
  refine Entails.trans ?_ (Entails.sepExists_intro bCoarse)
  apply Entails.pure_left; rintro ⟨hCnt0, hFine0⟩
  exact Entails.pure_right ⟨hCnt0, hSplit st0 hFine0, hFine0.meta_le, hRoom st0 hFine0⟩ (Entails.refl _)

theorem placed_libcMallocImpl_fine_ok {ro : Bool} (hRaw : LibcMallocImplFineRawStmt ro) : LibcMallocImplFineStmt ro := by
  intro _ γ tp brkStart bgt ivs0 req
  by_cases hReq : req ≤ MallocngMaxAllocSize
  · refine subroutine_ok_mono (hRaw γ tp brkStart bgt (fineStepAlloc req bgt) ivs0 req)
      (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => ?_) (hoom := fun _ _ _ _ ho => ho)
    · dsimp only [libcMallocImplFineSpec, libcMallocImplFineRawSpec, withCL] at hp ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hp
      exact fine_raw_pre_of_model_env
        (fun _ hFine0 => hFine0.toGroupsInv.toSplit
          (fineBudgetInv_stepAlloc req hFine0.budget_inv) (finePeaksLe_stepAlloc req bgt))
        (fun _ hFine0 _ hMed sc hsc hAllow =>
          fineLiveUser_room_alloc hFine0.toGroupsInv hMed hsc hAllow)
    · dsimp only [libcMallocImplFineSpec, libcMallocImplFineRawSpec, withCL] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hq
      simp only [hReq, decide_true, ↓reduceIte]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      apply Entails.sepExists_elim; intro p
      refine Entails.trans ?_ (Entails.sepExists_intro p)
      apply Entails.sepExists_elim; intro bs
      refine Entails.trans ?_ (Entails.sepExists_intro bs)
      apply Entails.sepExists_elim; intro st'
      refine Entails.trans ?_ (Entails.sepExists_intro st')
      apply Entails.sepExists_elim; intro bCoarse'
      refine Entails.trans ?_ (Entails.sepExists_intro bCoarse')
      apply Entails.pure_left
      rintro ⟨hx0, htp, hbrk, hWf, hLen, hNoOrph, hCnt',
        g', hg', idx, hIdx, hSlot, hOff, hZero, _h24, _h24b, _h63,
        st1, g, hSplit1, hNd1, hg1, hIdx1, hCl1, hSm1, hLg1, hMeta, hSc, hCntG, hMl, hPar, hSl, hMa, hGs⟩
      have hGrp' : FineGroupsInv (fineStepAlloc req bgt) st' :=
        fineGroupsInv_enframe_alloc hSplit1 hNd1 hg1 hIdx1 hCl1 hSm1 hLg1
          hMeta hSc hCntG hMl hPar hSl hMa hGs
      exact Entails.pure_right
        ⟨hx0, htp, hbrk, hWf, hLen, hNoOrph, hCnt', hGrp'.toFineInv rfl,
         g', hg', idx, hIdx, hSlot, hOff, hZero⟩ (Entails.refl _)
  · refine subroutine_ok_mono (hRaw γ tp brkStart bgt bgt ivs0 req)
      (fun _ _ _ hp => ?_) (fun _ _ _ sf hq => ?_) (hoom := fun _ _ _ _ ho => ho)
    · dsimp only [libcMallocImplFineSpec, libcMallocImplFineRawSpec, withCL] at hp ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hp
      exact fine_raw_pre_of_model_env
        (fun _ hFine0 => hFine0.toGroupsInv)
        (fun _ _ hLe => absurd hLe hReq)
    · dsimp only [libcMallocImplFineSpec, libcMallocImplFineRawSpec, withCL] at hq ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_left ?_)) hq
      simp only [hReq, decide_false, Bool.false_eq_true, ↓reduceIte]
      refine sepConj_mono_right (sepConj_mono_right ?_)
      apply Entails.pure_left; rintro ⟨hx0, htp, hbrk⟩
      refine Entails.pure_right hx0 ?_
      dsimp only [MallocngModelPostEnv, MallocngModelEnv]
      simp only [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
      dsimp only [FineCoreModeImpl]
      conv => lhs; simp only [sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro st'
      apply Entails.sepExists_elim; intro bCoarse'
      refine Entails.trans ?_ (Entails.sepExists_intro (dynamicRootRegions st'))
      have hMovePure : ∀ (pPr : Prop),
          MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
            (⌜pPr⌝ ∗ MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st') =
          ⌜pPr⌝ ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
            MallocngRuntime maddrs tp := by
        intro pPr
        generalize MallocngRoTablesA maddrs = pRo,
          MallocngRuntime maddrs tp = pRt,
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' = pCr,
          (⌜pPr⌝ : SepProp) = pP
        ac_rfl
      rw [hMovePure]
      apply Entails.pure_left; rintro ⟨hNoOrph, hCnt', hSplit', _, _⟩
      have hFine' : MallocngFineInv bgt (dynamicRootRegions st') st' :=
        FineGroupsInv.toFineInv hSplit' rfl
      refine Entails.pure_right hNoOrph (Entails.pure_right ⟨htp, hbrk⟩ ?_)
      have hCoreEx :
          MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ⊢
            ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
              ⌜MallocngCountIvsWF bCoarse (dynamicRootRegions st') st ∧
               MallocngFineInv bgt (dynamicRootRegions st') st⌝ ∗
              MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st := by
        refine Entails.trans ?_ (Entails.sepExists_intro st')
        refine Entails.trans ?_ (Entails.sepExists_intro bCoarse')
        exact Entails.pure_right ⟨hCnt', hFine'⟩ (Entails.refl _)
      rw [← sepConj_assoc]
      exact sepConj_mono_left (sepConj_mono_right hCoreEx)

theorem placed_defaultMalloc_fine_ok {ro : Bool} (hImpl : LibcMallocImplFineStmt ro) : DefaultMallocFineStmt ro := by
  intro _ γ tp brkStart bgt ivs0 req
  exact b04_tail_to_b09_fine (hImpl γ tp brkStart bgt ivs0 req)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ => rfl)

private theorem stackFrameAt_1024_split_fine (s0 : State) :
    stackFrameAt s0.sp mallocngStackBytes =
      (stackFrame s0 704 ∗ stackFrameAt (s0.sp - 704#64) 320) := by
  change stackFrameAt s0.sp (704 + 320) = _
  rw [stackFrameAt_split s0.sp 704 320, stackFrameAt_eq_memRegion s0.sp 704]

private theorem fine_malloc_success_post_entails [MallocngMultiPlacement] {ro : Bool}
    (γ : GhostName) (tp brkStart : BitVec 64) (bgt : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : BitVec 64) (s0 sf : State)
    (hReq : req.toNat ≤ MallocngMaxAllocSize) :
    let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
    let bgt' := if ok then fineStepAlloc req.toNat bgt else bgt
    (∃∗ p : BitVec 64,
     ∃∗ bs : List (BitVec 8),
     ∃∗ st' : MallocngSt,
     ∃∗ bCoarse' : MallocngBudget,
       ⌜sf.readReg64 .x0 = p ∧
        sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
        MallocngBlockWf p req.toNat ∧
        bs.length = req.toNat ∧
        MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
        MallocngCountIvsWF bCoarse' (dynamicRootRegions st') st' ∧
        MallocngFineInv bgt' (dynamicRootRegions st') st' ∧
        ∃ g' ∈ st'.groups, ∃ idx : Nat, ∃ hIdx : idx < g'.slots.length,
          g'.slots[idx]'hIdx = .liveUser p req.toNat (max req.toNat MallocngMinBlockCost) ∧
          p.toNat - (g'.slotStart idx).toNat ≤ 255 * 16 ∧
          (g'.isMmapped = true → bs = List.replicate req.toNat 0#8)⌝ ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
       MallocngRuntime maddrs tp ∗
       (p ↦ₛ bs) ∗
       MallocngBlockTokenK γ p req.toNat 0) ⊢
      ⌜(OptOwn (MallocngModelBlock (mallocngFineModeIface ro) γ)).pureWf (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none)⌝ ∗
      (OptOwn (MallocngModelBlock (mallocngFineModeIface ro) γ)).interp (sf.readReg64 .x0)
        (if ok then some (req.toNat, 16) else none) ∗
      MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf := by
  intro ok bgt'
  have hOkTrue : ok = true := decide_eq_true hReq
  apply Entails.sepExists_elim; intro p
  apply Entails.sepExists_elim; intro bs
  apply Entails.sepExists_elim; intro st'
  apply Entails.sepExists_elim; intro bCoarse'
  apply Entails.pure_left
  rintro ⟨hx0_f, htp_f, hbrkS_f, ⟨hp_ne, hp_al, hp_48, _⟩, hbs_len, hNoOrph, hCnt, hFine, _⟩
  have hp_64 : p.toNat + req.toNat < 2 ^ 64 := by omega
  rw [hOkTrue]
  simp only [↓reduceIte, OptOwn_pureWf_some, OptOwn_interp_some, MallocngModelBlock, mallocngFineModeIface_block_eq]
  rw [hx0_f]
  refine Entails.pure_right ⟨hp_ne, hp_ne, hp_al, hp_64⟩ ?_
  have hBsReg : (p ↦ₛ bs) ⊢ memRegion p req.toNat := by
    rw [← hbs_len]
    exact pointsToBytes_entails_memRegion p bs
  have hTok : MallocngBlockTokenK γ p req.toNat 0 ⊢ MallocngTightBlock γ p req.toNat 16 :=
    mallocngBlockTokenK_to_tight γ p req.toNat 0 16 (Nat.zero_le _)
  have hPostEnv :
      MallocngRoTablesA maddrs ∗
        MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
        MallocngRuntime maddrs tp ⊢
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt' ivs0 s0 sf := by
    dsimp only [MallocngModelPostEnv, MallocngModelEnv]
    simp only [mallocngFineModeIface_heap_eq, mallocngFineModeIface_core_eq]
    dsimp only [FineCoreModeImpl]
    refine Entails.trans ?_ (Entails.sepExists_intro (dynamicRootRegions st'))
    refine Entails.pure_right hNoOrph (Entails.pure_right ⟨htp_f, hbrkS_f⟩ ?_)
    have hCoreEx :
        MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ⊢
          ∃∗ st : MallocngSt, ∃∗ bCoarse : MallocngBudget,
            ⌜MallocngCountIvsWF bCoarse (dynamicRootRegions st') st ∧
             MallocngFineInv bgt' (dynamicRootRegions st') st⌝ ∗
            MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st := by
      refine Entails.trans ?_ (Entails.sepExists_intro st')
      refine Entails.trans ?_ (Entails.sepExists_intro bCoarse')
      exact Entails.pure_right ⟨hCnt, hFine⟩ (Entails.refl _)
    rw [← sepConj_assoc]
    exact sepConj_mono_left (sepConj_mono_right hCoreEx)
  have hRearr :
      MallocngRoTablesA maddrs ∗
        MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
        MallocngRuntime maddrs tp ∗
        (p ↦ₛ bs) ∗
        MallocngBlockTokenK γ p req.toNat 0 =
      (MallocngBlockTokenK γ p req.toNat 0 ∗ (p ↦ₛ bs)) ∗
        (MallocngRoTablesA maddrs ∗
         MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' ∗
         MallocngRuntime maddrs tp) := by
    generalize MallocngRoTablesA maddrs = pRo,
      MallocngCoreStModeA ro γ maddrs brkStart sf.brk bCoarse'.liveCost bCoarse'.peakCost st' = pCr,
      MallocngRuntime maddrs tp = pRt,
      (p ↦ₛ bs) = pBs,
      MallocngBlockTokenK γ p req.toNat 0 = pBlk
    ac_rfl
  rw [hRearr]
  exact sepConj_mono (sepConj_mono hTok hBsReg) hPostEnv

private theorem fine_malloc_withCL_of_defaultMalloc [MallocngMultiPlacement] {ro : Bool}
    (hDef : DefaultMallocFineStmt ro) (γ : GhostName) :
    subroutine_ok (mallocngBlockProg mmpl 4 msvc) (mbase 4)
      (withCL mmpl (mallocngModelMallocSpec mallocngFineCostModel (mallocngFineModeIface ro) msvc γ maddrs (mbase 4))) := by
  apply subroutine_ok_of_sepWP_init
  intro x R s0 hpc hrun hpre hspAl0
  rcases x with ⟨req, sp, tp, brkStart, bgt, ivs0⟩
  have hPurePre : s0.readReg64 .x0 = req ∧ s0.sp = sp := by
    have hp := hpre
    dsimp only [withCL, mallocngModelMallocSpec, ToBaseSpec.toSpec] at hp
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    have hp1 := hp.1
    simp only [ctype_simp, and_true] at hp1
    exact hp1
  rcases hPurePre with ⟨hx0, hsp⟩
  subst hsp
  refine ⟨(withCL mmpl (mallocngModelMallocSpec mallocngFineCostModel (mallocngFineModeIface ro)
      msvc γ maddrs (mbase 4))).pre (req, s0.sp, tp, brkStart, bgt, ivs0) s0, hpre, ?_⟩
  refine SepWP.call_subroutine_frame
    (F := stackFrameAt (s0.sp - 704#64) 320)
    (x := ()) (ret_pc := s0.readReg64 .lr)
    (hDef γ tp brkStart bgt ivs0 req.toNat)
    hpc hrun hspAl0 rfl
    (fun R' hm => ?_)
    (fun R' sf _ hp => by
      dsimp only [withCL, libcMallocImplFineSpec] at hp
      exact not_satisfies_false_sepConj hp)
    (fun R' code sf _ he => by
      dsimp only [withCL, libcMallocImplFineSpec] at he
      exact not_satisfies_false_sepConj he)
    (fun sf hpc_f hrun_f hsp_f hcs_f => ?_)
    (fun R' sf _ ho => ?_)
  · rw [← sepConj_assoc]
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, mallocngModelMallocSpec, ToBaseSpec.toSpec, libcMallocImplFineSpec]
    simp only [ctype_simp]
    rw [stackFrameAt_1024_split_fine s0, sepConj_assoc]
    apply Entails.pure_left; intro _
    have hx0_nat : (s0.readReg64 .x0).toNat = req.toNat := by rw [hx0]
    refine Entails.trans (Entails.pure_right hx0_nat (Entails.refl _)) ?_
    generalize ⌜(s0.readReg64 .x0).toNat = req.toNat⌝ = pReq,
      MallocngModelEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart bgt ivs0 s0 = pEnv,
      stackFrame s0 704 = pSf1,
      stackFrameAt (s0.sp - 704#64) 320 = pSf2,
      ⌜VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem⌝ = pCl
    exact Entails.of_eq (by ac_rfl)
  · refine SepWP.done hpc_f hrun_f ⟨?_, hsp_f, hcs_f⟩
    intro hm
    refine Satisfies.mono (sepConj_mono_left ?_) hm
    dsimp only [withCL, mallocngModelMallocSpec, ToBaseSpec.toSpec, libcMallocImplFineSpec,
      MallocngCallAccounting]
    rw [fine_stepB_ite (decide (req.toNat ≤ MallocngMaxAllocSize)) (.alloc req.toNat) bgt]
    dsimp only [evReqBytes]
    have hBgtEq :
        (if decide (req.toNat ≤ MallocngMaxAllocSize) = true then
          mallocngFineCostModel.step (.alloc req.toNat) bgt else bgt) =
        (if decide (req.toNat ≤ MallocngMaxAllocSize) = true then
          fineStepAlloc req.toNat bgt else bgt) := rfl
    rw [hBgtEq]
    have hPostRearr : ∀ (pAcc pSf1 br pCl pSf2 : SepProp),
        ((pAcc ∗ pSf1 ∗ br) ∗ pCl) ∗ pSf2 = (pAcc ∗ (br ∗ (pSf1 ∗ pSf2))) ∗ pCl := by
      intros; ac_rfl
    rw [hPostRearr]
    refine sepConj_mono_left ?_
    rw [← stackFrameAt_1024_split_fine s0]
    apply Entails.pure_left; intro hAcc
    refine Entails.trans (sepConj_mono_left (P' :=
        ⌜(OptOwn (MallocngModelBlock (mallocngFineModeIface ro) γ)).pureWf (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none)⌝ ∗
        (OptOwn (MallocngModelBlock (mallocngFineModeIface ro) γ)).interp (sf.readReg64 .x0)
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then some (req.toNat, 16) else none) ∗
        MallocngModelPostEnv mallocngFineCostModel (mallocngFineModeIface ro) γ maddrs tp brkStart
          (if decide (req.toNat ≤ MallocngMaxAllocSize) then fineStepAlloc req.toNat bgt else bgt)
          ivs0 s0 sf) ?_) ?_
    · by_cases hReq : req.toNat ≤ MallocngMaxAllocSize
      · have hM := fine_malloc_success_post_entails (ro := ro) γ tp brkStart bgt ivs0 req s0 sf hReq
        dsimp only at hM
        simp only [hReq, ↓reduceIte] at hM ⊢
        exact hM
      · simp only [hReq, decide_false, Bool.false_eq_true, ↓reduceIte,
          OptOwn_pureWf_none, OptOwn_interp_none]
        exact Entails.pure_right trivial (Entails.refl _)
    · rw [sepConj_assoc]
      apply Entails.pure_left; intro hPureWf
      refine Entails.pure_right ⟨hPureWf, hAcc⟩ ?_
      rw [sepConj_assoc]
      exact Entails.refl _
  · dsimp only [withCL, mallocngModelMallocSpec, ToBaseSpec.toSpec, libcMallocImplFineSpec] at ho ⊢
    rw [fine_stepB_ite (decide (req.toNat ≤ MallocngMaxAllocSize)) (.alloc req.toNat) bgt]
    dsimp only [evReqBytes]
    rw [← sepConj_assoc, sepConj_comm _ (stackFrameAt (s0.sp - 704#64) 320), sepConj_assoc] at ho
    exact Satisfies.drop_left ho

theorem fine_malloc_entry_ok {ro : Bool} (hDef : DefaultMallocFineStmt ro)
    (mpl : Obj.MultiPlacement) (svc : State → State)
    (hPl : VerifiedLibraries.mallocngLib.Placeable mpl) (hSvc : MallocngSvcValid svc)
    (γ : GhostName) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngModelMallocSpec mallocngFineCostModel (mallocngFineModeIface ro) svc γ
        (mallocngAddrsOfPlacement mpl)) := by
  letI : MallocngMultiPlacement := ⟨mpl, svc, hPl, hSvc⟩
  refine ⟨by decide, 4, 0, rfl, ?_⟩
  rw [fnAddr_malloc mpl]
  exact withCL_to_withCodeLoaded (fine_malloc_withCL_of_defaultMalloc hDef γ)

end VerifiedLibraries.Mallocng.Proofs.Cost.Fine
