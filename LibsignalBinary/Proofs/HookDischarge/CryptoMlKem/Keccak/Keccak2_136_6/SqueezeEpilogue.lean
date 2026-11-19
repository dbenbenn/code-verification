/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B02` (`keccak2::<136, 6>`): inline 32-byte squeeze and epilogue

Proof of segment `[0x08d0 → 0x0934]` (`26` instructions) of `mlkemBlk02`: deinterleaves lanes
`0..3` of the two `Keccak-f[1600]` output states (`ZIP1`/`ZIP2` + `LD2 {v0.2d, v1.2d}`) into
`(out0 ↦ₛ sha3_256List in0)` and `(out1 ↦ₛ sha3_256List in1)`, deallocates the `1024`-byte
local stack frame (`1040`-byte total stack footprint), restores all 20 callee-saved registers
(`x19..x30`, `d8..d15`), and returns to `s0.readReg64 .lr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.SqueezeEpilogue

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (
  simdDeinterleaveReg_2d_0
  simdDeinterleaveReg_2d_1
  step_simdLd2_2d
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  sha3_256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
  keccakXorRate17
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorb_17_eq
  keccakLastBlock
  memRegion32_cells
  pointsTo64_4_eq_bytes
  sha3_256List_eq_lanes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  Loop2Regs
  Loop2SpillMem
  SavedFrame02
  blk02_code_eq
  blk02_tree_size
  blkLib02
  blkPC02
  blkPl02
  blkPlaceable02
  blkTree02
  entails_sub
  loop2SpillMem_entails_memRegion
  savedFrame02_entails_memRegion
  stack1040_split
  trunc64_zext128_extractLsb0
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x08d0 → 0x0934]
end

private theorem calleeSavedVRegs_eq_of_readVReg128 (s0 sf : State)
    (h8  : sf.readVReg128 8#5  = ((s0.readVReg128 8#5).extractLsb' 0 64).zeroExtend 128)
    (h9  : sf.readVReg128 9#5  = ((s0.readVReg128 9#5).extractLsb' 0 64).zeroExtend 128)
    (h10 : sf.readVReg128 10#5 = ((s0.readVReg128 10#5).extractLsb' 0 64).zeroExtend 128)
    (h11 : sf.readVReg128 11#5 = ((s0.readVReg128 11#5).extractLsb' 0 64).zeroExtend 128)
    (h12 : sf.readVReg128 12#5 = ((s0.readVReg128 12#5).extractLsb' 0 64).zeroExtend 128)
    (h13 : sf.readVReg128 13#5 = ((s0.readVReg128 13#5).extractLsb' 0 64).zeroExtend 128)
    (h14 : sf.readVReg128 14#5 = ((s0.readVReg128 14#5).extractLsb' 0 64).zeroExtend 128)
    (h15 : sf.readVReg128 15#5 = ((s0.readVReg128 15#5).extractLsb' 0 64).zeroExtend 128) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  unfold calleeSavedVRegs VRegFile.calleeSaved
  change ((sf.readVReg128 8#5).truncate 64, (sf.readVReg128 9#5).truncate 64,
          (sf.readVReg128 10#5).truncate 64, (sf.readVReg128 11#5).truncate 64,
          (sf.readVReg128 12#5).truncate 64, (sf.readVReg128 13#5).truncate 64,
          (sf.readVReg128 14#5).truncate 64, (sf.readVReg128 15#5).truncate 64) =
         ((s0.readVReg128 8#5).truncate 64, (s0.readVReg128 9#5).truncate 64,
          (s0.readVReg128 10#5).truncate 64, (s0.readVReg128 11#5).truncate 64,
          (s0.readVReg128 12#5).truncate 64, (s0.readVReg128 13#5).truncate 64,
          (s0.readVReg128 14#5).truncate 64, (s0.readVReg128 15#5).truncate 64)
  rw [h8, h9, h10, h11, h12, h13, h14, h15]
  simp only [trunc64_zext128_extractLsb0]

private theorem out_cells_eq_sha3_256 (out : BitVec 64) (msg : List (BitVec 8)) :
    let f := keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 msg (msg.length / 136))
      (keccakLastBlock 136 0x06#8 msg))
    (((out ↦₆₄ f.getD 0 0#64) ∗ ((out + 8#64) ↦₆₄ f.getD 1 0#64)) ∗
     (((out + 16#64) ↦₆₄ f.getD 2 0#64) ∗ ((out + 24#64) ↦₆₄ f.getD 3 0#64))) =
      (out ↦ₛ sha3_256List msg) := by
  intro f
  rw [pointsTo64_4_eq_bytes, sha3_256List_eq_lanes msg]
  dsimp only
  rw [keccakAbsorb_17_eq 0x06#8 msg]

private theorem cells4_entails_memRegion32 (a w0 w1 w2 w3 : BitVec 64) :
    (((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) ∗
     (((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3))) ⊢ memRegion a 32 := by
  rw [memRegion_split' (b' := a + 8#64) (n := 8) (k := 24) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 16#64) (n := 8) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := a + 24#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (pointsTo64_entails_memRegion _ _)))

private theorem quad_entails_memRegion32 (sp o0 o1 o2 o3 w0 w1 w2 w3 : BitVec 64)
    (h1 : (sp + o0) + 8#64 = sp + o1 := by bv_omega)
    (h2 : (sp + o0) + 16#64 = sp + o2 := by bv_omega)
    (h3 : (sp + o0) + 24#64 = sp + o3 := by bv_omega) :
    (((sp + o0) ↦₆₄ w0) ∗ ((sp + o1) ↦₆₄ w1)) ∗
    (((sp + o2) ↦₆₄ w2) ∗ ((sp + o3) ↦₆₄ w3)) ⊢ memRegion (sp + o0) 32 := by
  rw [← h1, ← h2, ← h3]
  exact cells4_entails_memRegion32 (sp + o0) w0 w1 w2 w3

private theorem split400_squeeze_eq (sp : BitVec 64) :
    memRegion (sp + 176#64) 400 =
      memRegion (sp + 176#64) 32 ∗
      memRegion (sp + 208#64) 32 ∗
      memRegion (sp + 240#64) 32 ∗
      memRegion (sp + 272#64) 8 ∗
      memRegion (sp + 280#64) 8 ∗
      memRegion (sp + 288#64) 208 ∗
      memRegion (sp + 496#64) 32 ∗
      memRegion (sp + 528#64) 32 ∗
      memRegion (sp + 560#64) 8 ∗
      memRegion (sp + 568#64) 8 := by
  rw [memRegion_split' (b' := sp + 208#64) (n := 32) (k := 368) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 240#64) (n := 32) (k := 336) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 272#64) (n := 32) (k := 304) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 280#64) (n := 8)  (k := 296) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 288#64) (n := 8)  (k := 288) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 496#64) (n := 208) (k := 80) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 528#64) (n := 32) (k := 48) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 560#64) (n := 32) (k := 16) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 568#64) (n := 8)  (k := 8)  rfl (by bv_omega) (by decide)]

private theorem seg_08d0_to_0908 [MlKemPlacement] (b sp out0 out1 : BitVec 64)
    (s : State)
    (hpc : s.pc = b + 0x08d0#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx9 : s.readReg64 .x9 = sp + 208#64)
    (hx20 : s.readReg64 .x20 = out0)
    (hx19 : s.readReg64 .x19 = out1)
    (f0 f1 : KeccakState)
    (hregs : Loop2Regs s f0 f1) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x0908#64) s
      (Loop2SpillMem sp f0 f1 ∗ memRegion (sp + 176#64) 400 ∗
        memRegion out0 32 ∗ memRegion out1 32)
      (sepPost
        (fun sm => sm.sp = sp)
        (memRegion sp 176 ∗ memRegion (sp + 176#64) 400 ∗
          (((out0 ↦₆₄ f0.getD 0 0#64) ∗ ((out0 + 8#64) ↦₆₄ f0.getD 1 0#64)) ∗
           (((out0 + 16#64) ↦₆₄ f0.getD 2 0#64) ∗ ((out0 + 24#64) ↦₆₄ f0.getD 3 0#64))) ∗
          (((out1 ↦₆₄ f1.getD 0 0#64) ∗ ((out1 + 8#64) ↦₆₄ f1.getD 1 0#64)) ∗
           (((out1 + 16#64) ↦₆₄ f1.getD 2 0#64) ∗ ((out1 + 24#64) ↦₆₄ f1.getD 3 0#64))))) := by
  rcases hregs with ⟨hv31, hv6, hv18, hv17, _hv28, _hv26, _hv23, _hv22, _hv20, _hv15,
    _hv9, _hv29, _hv25, _hv12, _hv7, _hv8, _hv27, _hv21, _hv3, _hv4⟩
  dsimp only [keccak2Lane] at hv31 hv6 hv18 hv17
  rw [split400_squeeze_eq sp]
  refine memRegion32_cells (sp + 176#64) (by sep_focus) fun _a0 _a1 _a2 _a3 => ?_
  refine memRegion32_cells (sp + 208#64) (by sep_focus) fun _b0 _b1 _b2 _b3 => ?_
  refine memRegion32_cells (sp + 240#64) (by sep_focus) fun _c0 _c1 _c2 _c3 => ?_
  refine SepWP.memRegion8_cell (sp + 272#64) fun _d0 => ?_
  refine SepWP.memRegion8_cell (sp + 280#64) fun _d1 => ?_
  refine memRegion32_cells (sp + 496#64) (by sep_focus) fun _e0 _e1 _e2 _e3 => ?_
  refine memRegion32_cells (sp + 528#64) (by sep_focus) fun _g0 _g1 _g2 _g3 => ?_
  refine SepWP.memRegion8_cell (sp + 560#64) fun _h0 => ?_
  refine SepWP.memRegion8_cell (sp + 568#64) fun _h1 => ?_
  refine memRegion32_cells out0 (by sep_focus) fun _o00 _o01 _o02 _o03 => ?_
  refine memRegion32_cells out1 (by sep_focus) fun _o10 _o11 _o12 _o13 => ?_
  dsimp only [Loop2SpillMem]
  wp_steps 9
  apply step_simdLd2_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_sep_access
  · wp_norm_lhs
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  rw [sepPost_apply]
  refine ⟨by wp_norm_lhs, ?_⟩
  have h400 :
        ((((((sp + 176#64) ↦₆₄ f0.getD 0 0#64) ∗ ((sp + 184#64) ↦₆₄ f1.getD 0 0#64)) ∗
           (((sp + 192#64) ↦₆₄ f0.getD 1 0#64) ∗ ((sp + 200#64) ↦₆₄ f1.getD 1 0#64))) ∗
          ((((sp + 208#64) ↦₆₄ f0.getD 2 0#64) ∗ ((sp + 216#64) ↦₆₄ f1.getD 2 0#64)) ∗
           (((sp + 224#64) ↦₆₄ f0.getD 3 0#64) ∗ ((sp + 232#64) ↦₆₄ f1.getD 3 0#64))) ∗
          ((((sp + 240#64) ↦₆₄ f0.getD 4 0#64) ∗ ((sp + 248#64) ↦₆₄ f1.getD 4 0#64)) ∗
           (((sp + 256#64) ↦₆₄ (s.readVReg128 28#5).extractLsb' 0 64) ∗
            ((sp + 264#64) ↦₆₄ (s.readVReg128 28#5).extractLsb' 64 64))) ∗
          ((sp + 272#64) ↦₆₄ f0.getD 6 0#64) ∗
          ((sp + 280#64) ↦₆₄ f1.getD 6 0#64) ∗
          memRegion (sp + 288#64) 208 ∗
          ((((sp + 496#64) ↦₆₄ (s.readVReg128 8#5).extractLsb' 0 64) ∗
            ((sp + 504#64) ↦₆₄ (s.readVReg128 8#5).extractLsb' 64 64)) ∗
           (((sp + 512#64) ↦₆₄ (s.readVReg128 27#5).extractLsb' 0 64) ∗
            ((sp + 520#64) ↦₆₄ (s.readVReg128 27#5).extractLsb' 64 64))) ∗
          ((((sp + 528#64) ↦₆₄ (s.readVReg128 21#5).extractLsb' 0 64) ∗
            ((sp + 536#64) ↦₆₄ (s.readVReg128 21#5).extractLsb' 64 64)) ∗
           (((sp + 544#64) ↦₆₄ (s.readVReg128 3#5).extractLsb' 0 64) ∗
            ((sp + 552#64) ↦₆₄ (s.readVReg128 3#5).extractLsb' 64 64))) ∗
          ((sp + 560#64) ↦₆₄ (s.readVReg128 4#5).extractLsb' 0 64) ∗
          ((sp + 568#64) ↦₆₄ (s.readVReg128 4#5).extractLsb' 64 64))) ⊢
          memRegion (sp + 176#64) 400 := by
      rw [split400_squeeze_eq sp]
      exact sepConj_mono (quad_entails_memRegion32 sp 176#64 184#64 192#64 200#64 _ _ _ _) <|
        sepConj_mono (quad_entails_memRegion32 sp 208#64 216#64 224#64 232#64 _ _ _ _) <|
        sepConj_mono (quad_entails_memRegion32 sp 240#64 248#64 256#64 264#64 _ _ _ _) <|
        sepConj_mono (pointsTo64_entails_memRegion _ _) <|
        sepConj_mono (pointsTo64_entails_memRegion _ _) <|
        sepConj_mono (Entails.refl _) <|
        sepConj_mono (quad_entails_memRegion32 sp 496#64 504#64 512#64 520#64 _ _ _ _) <|
        sepConj_mono (quad_entails_memRegion32 sp 528#64 536#64 544#64 552#64 _ _ _ _) <|
        sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)
  have h176 := loop2SpillMem_entails_memRegion sp f0 f1
  dsimp only [Loop2SpillMem] at h176
  refine entails_sub h400 (by sep_frame) ?_
  exact entails_sub h176 (by sep_frame) (by sep_frame)

private theorem seg_0908_to_ret [MlKemPlacement] (b : BitVec 64)
    (F : SepProp) (s0 sm : State)
    (hsp0 : s0.spAligned = true)
    (hpc : sm.pc = b + 0x0908#64)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s0.sp - 1024#64) :
    SepWP (blkPC02.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
      (SavedFrame02 s0.sp s0 ∗ F)
      (sepPost
        (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ F)) := by
  dsimp only [SavedFrame02]
  have hsp160 : ((s0.sp - 1024#64) + 864#64 : BitVec 64) = s0.sp - 160#64 := by bv_omega
  have hsp160_align : (((s0.sp - 1024#64) + 864#64) &&& 15#64 == 0#64) = true := by
    rw [hsp160]
    exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by bv_omega), ?_⟩, ?_⟩
  · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
    exact calleeSavedVRegs_eq_of_readVReg128 s0 _
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · have h160 := savedFrame02_entails_memRegion s0.sp s0
    dsimp only [SavedFrame02] at h160
    exact entails_sub h160 (by sep_frame) (by sep_frame)

/-- Step `[0x08d0 → 0x0934]` (inline 32-byte 2-way `SHA3-256` squeeze + stack teardown + `RET`). -/
theorem seg_squeeze_epilogue [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (out0 out1 : BitVec 64) (in0 in1 : List (BitVec 8))
    (F : SepProp) (s0 s : State)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + 0x08d0#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 1024#64)
    (hx9 : s.readReg64 .x9 = (s0.sp - 1024#64) + 208#64)
    (hx20 : s.readReg64 .x20 = out0)
    (hx19 : s.readReg64 .x19 = out1)
    (hregs : Loop2Regs s
      (keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 in0 (in0.length / 136))
        (keccakLastBlock 136 0x06#8 in0)))
      (keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 in1 (in1.length / 136))
        (keccakLastBlock 136 0x06#8 in1)))) :
    let sp := s0.sp - 1024#64
    let f0 := keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 in0 (in0.length / 136))
      (keccakLastBlock 136 0x06#8 in0))
    let f1 := keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 in1 (in1.length / 136))
      (keccakLastBlock 136 0x06#8 in1))
    SepWP (blkPC02.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackAt sp 16 ∗ Loop2SpillMem sp f0 f1 ∗ memRegion (sp + 176#64) 400 ∗
        memRegion (sp + 576#64) 288 ∗ SavedFrame02 s0.sp s0 ∗
        memRegion out0 32 ∗ memRegion out1 32 ∗ F)
      (sepPost
        (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((out0 ↦ₛ sha3_256List in0) ∗ (out1 ↦ₛ sha3_256List in1) ∗
          stackAt s0.sp 1040 ∗ F)) := by
  intro sp f0 f1
  refine SepWP.bind_sepPost
    (F := stackAt sp 16 ∗ memRegion (sp + 576#64) 288 ∗ SavedFrame02 s0.sp s0 ∗ F)
    (seg_08d0_to_0908 b sp out0 out1 s hpc hrun hsp_align hsp hx9 hx20 hx19 f0 f1 hregs)
    (by sep_frame) ?_
  intro sm hpc_m hrun_m hsp_m
  dsimp only [f0, f1]
  rw [out_cells_eq_sha3_256 out0 in0, out_cells_eq_sha3_256 out1 in1]
  refine (fun h hpre => SepWP.weaken_pre hpre h)
    (SepWP.mono
      (seg_0908_to_ret b
        ((out0 ↦ₛ sha3_256List in0) ∗ (out1 ↦ₛ sha3_256List in1) ∗
          stackAt sp 16 ∗ memRegion sp 176 ∗ memRegion (sp + 176#64) 400 ∗
          memRegion (sp + 576#64) 288 ∗ F)
        s0 sm hsp0 hpc_m hrun_m hsp_m) ?_)
    (by sep_frame)
  intro sf Qf _ _ hpost
  rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  rw [stack1040_split s0.sp]
  dsimp only [sp]
  sep_frame

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.SqueezeEpilogue
