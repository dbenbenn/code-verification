/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute2 -- proof-setup: allow-public-import
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.Squeeze2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B01` (`keccak2::<136, 31>`): final permute, `B08` squeeze, and epilogue

Proof of segment `[0x05e4 → 0x094c]` of `mlkemBlk01`: runs `Permute2.permute2_rounds`
(`[0x05e4 → 0x08c8]`), stores all 25 permuted 2-way lanes into `[sp1 + 192, sp1 + 592)`
(`[0x08c8 → 0x091c]`), calls `B08` (`squeeze2::<136>`) at `+0x091c` for `outLen ∈ {32, 128}`,
restores `SavedCalleeFrame`, and returns to `s0.readReg64 .lr` at `+0x094c`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.SqueezeEpilogue

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (
  mlkemData01Bytes
  mlkemMultiLib
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2ShakeArgs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  add_off_reloc_cancel
  add_reloc_cancel
  add_zero_reloc_cancel
  mbase
  mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk
  mlkemMpl
  resolve_blk08
  seq_codeLoaded_lr
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakExtractRate
  keccakF1600
  shake256List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Mem
  Keccak2Mem_entails_memRegion
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccak2Lane
  keccakXorRate17
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  extractLsb_hi_append
  extractLsb_lo_append
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorbPrefix17
  keccakAbsorb_17_eq
  keccakLastBlock
  shake256List_eq_take_extract
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.LoadSqueeze.Squeeze2 (
  Squeeze2Args
  squeeze2_136_block_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  SavedCalleeFrame
  Spill11
  blk01_code_eq
  blk01_tree_size
  blkLib01
  blkPC01
  blkPl01
  blkPlaceable01
  blkTree01
  entails_sub
  savedCalleeFrame_entails_memRegion160
  spill11_entails_memRegion176
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Prologue (
  memRegion400_cells
  sepWP_seq_cl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute2 (
  P2RoundRegs
  P2Scalars
  permute2_rounds
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x08c8 → 0x094c]
end

private theorem trunc64_zext128_extractLsb0 (v : BitVec 128) :
    ((v.extractLsb' 0 64).zeroExtend 128).truncate 64 = v.truncate 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

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

private theorem take_extract_eq_shake256 {outLen : Nat} (msg : List (BitVec 8))
    (hout : outLen = 32 ∨ outLen = 128) :
    (keccakExtractRate 17
      (keccakF1600 (keccakXorRate17 (keccakAbsorbPrefix17 msg (msg.length / 136))
        (keccakLastBlock 136 0x1f#8 msg)))).take outLen =
      shake256List outLen msg := by
  rw [← keccakAbsorb_17_eq 0x1f#8 msg, ← shake256List_eq_take_extract msg hout]

private theorem stack1136_split (sp0 : BitVec 64) :
    let sp1 := sp0 - 1040#64
    stackAt sp0 1136 =
      stackAt sp1 96 ∗
      memRegion sp1 8 ∗
      memRegion (sp1 + 8#64) 8 ∗
      memRegion (sp1 + 16#64) 176 ∗
      memRegion (sp1 + 192#64) 400 ∗
      memRegion (sp1 + 592#64) 288 ∗
      memRegion (sp0 - 160#64) 160 := by
  intro sp1
  unfold stackAt
  have hbase : sp0 - BitVec.ofNat 64 1136 = sp1 - BitVec.ofNat 64 96 := by
    dsimp [sp1]; bv_omega
  rw [hbase,
      memRegion_split (sp1 - BitVec.ofNat 64 96) 96 1040 (by decide),
      show (sp1 - BitVec.ofNat 64 96) + 96#64 = sp1 by dsimp [sp1]; bv_omega,
      memRegion_split sp1 8 1032 (by decide),
      memRegion_split (sp1 + 8#64) 8 1024 (by decide),
      show (sp1 + 8#64) + 8#64 = sp1 + 16#64 by bv_omega,
      memRegion_split (sp1 + 16#64) 176 848 (by decide),
      show (sp1 + 16#64) + 176#64 = sp1 + 192#64 by bv_omega,
      memRegion_split (sp1 + 192#64) 400 448 (by decide),
      show (sp1 + 192#64) + 400#64 = sp1 + 592#64 by bv_omega,
      memRegion_split (sp1 + 592#64) 288 160 (by decide),
      show (sp1 + 592#64) + 288#64 = sp0 - 160#64 by dsimp [sp1]; bv_omega]

private theorem spAligned_of_sp_eq {s1 s2 : State} {v : BitVec 64}
    (ha : s2.spAligned = true) (h2 : s2.sp = v) (h1 : s1.sp = v) : s1.spAligned = true := by
  rw [State.spAligned, h1, ← h2, ← State.spAligned]
  exact ha

private theorem seg_08c8_to_091c [MlKemPlacement] (b sp1 out0 out1 : BitVec 64) (outLen : Nat)
    (f0 f1 : KeccakState)
    (s16 s32 s48 s64 s80 s96 s112 : BitVec 128) (F : SepProp) (s : State)
    (hpc : s.pc = b + 0x08c8#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = sp1)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 outLen)
    (hx21 : s.readReg64 .x21 = out1)
    (hx22 : s.readReg64 .x22 = out0)
    (hregs : P2RoundRegs s f0 f1) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x091c#64) s
      (((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 outLen) ∗
        Spill11 sp1 s16 s32 s48 s64 s80 s96 s112
          (keccak2Lane f0 f1 2) (keccak2Lane f0 f1 3)
          (keccak2Lane f0 f1 6) (keccak2Lane f0 f1 4) ∗
        memRegion (sp1 + 192#64) 400 ∗ F)
      (sepPost
        (fun sm =>
          sm.sp = sp1 ∧ sm.spAligned = true ∧
          sm.readReg64 .x0 = sp1 + 192#64 ∧
          sm.readReg64 .x1 = out0 ∧
          sm.readReg64 .x2 = BitVec.ofNat 64 outLen ∧
          sm.readReg64 .x3 = out1 ∧
          sm.readReg64 .x4 = BitVec.ofNat 64 outLen ∧
          sm.readReg64 .x5 = BitVec.ofNat 64 outLen)
        (((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 outLen) ∗
          memRegion (sp1 + 16#64) 176 ∗
          Keccak2Mem (sp1 + 192#64) f0 f1 ∗ F)) := by
  rcases hregs with ⟨hv1, hv2, hv3, hv8, hv9, hv11, hv12, hv14, hv15, hv17, hv18,
    hv20, hv21, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30⟩
  dsimp only [keccak2Lane] at hv1 hv2 hv3 hv8 hv9 hv11 hv12 hv14 hv15 hv17 hv18
  dsimp only [keccak2Lane] at hv20 hv21 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30
  refine memRegion400_cells (sp1 + 192#64) (by sep_focus)
    fun _c0 _c1 _c2 _c3 _c4 _c5 _c6 _c7 _c8 _c9 _c10 _c11 _c12 _c13 _c14 _c15
        _d0 _d1 _d2 _d3 _d4 _d5 _d6 _d7 _d8 _d9 _d10 _d11 _d12 _d13 _d14 _d15
        _e0 _e1
        _f0 _f1 _f2 _f3 _f4 _f5 _f6 _f7 _f8 _f9 _f10 _f11 _f12 _f13 _f14 _f15 => ?_
  unfold Spill11
  dsimp only [keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  wp_steps 21
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) ?_
  rw [sepPost_apply]
  refine ⟨⟨by wp_norm_lhs, spAligned_of_sp_eq hsp_align hsp (by wp_norm_lhs),
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩, ?_⟩
  refine entails_sub
    (Rest := ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 outLen) ∗ Keccak2Mem (sp1 + 192#64) f0 f1 ∗ F)
    (spill11_entails_memRegion176 sp1 s16 s32 s48 s64 s80 s96 s112
      (keccak2Lane f0 f1 2) (keccak2Lane f0 f1 3)
      (keccak2Lane f0 f1 6) (keccak2Lane f0 f1 4))
    ?_ (by sep_frame)
  unfold Spill11 Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
    Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
  dsimp only [keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  sep_entail

private theorem seg_091c_to_0920 [MlKemPlacement] (b sp1 out0 out1 : BitVec 64) (outLen : Nat)
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (hout : outLen = 32 ∨ outLen = 128)
    (f0 f1 : KeccakState) (F : SepProp) (s : State)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x091c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = sp1)
    (hx0 : s.readReg64 .x0 = sp1 + 192#64)
    (hx1 : s.readReg64 .x1 = out0)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 outLen)
    (hx3 : s.readReg64 .x3 = out1)
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 outLen)
    (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 outLen) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x0920#64) s
      (stackAt sp1 96 ∗ Keccak2Mem (sp1 + 192#64) f0 f1 ∗
        memRegion out0 outLen ∗ memRegion out1 outLen ∗ F)
      (sepPost
        (fun sm => sm.sp = sp1 ∧ sm.spAligned = true)
        (stackAt sp1 96 ∗ memRegion (sp1 + 192#64) 400 ∗
          (out0 ↦ₛ (keccakExtractRate 17 f0).take outLen) ∗
          (out1 ↦ₛ (keccakExtractRate 17 f1).take outLen) ∗ F)) := by
  unfold Keccak2Mem Keccak2Rate17Mem
  refine SepWP.weaken_pre
    (show _ ⊢ Keccak2Rate16Mem (sp1 + 192#64) f0 f1 ∗
      memRegion out0 outLen ∗ memRegion out1 outLen ∗ stackAt s.sp 96 ∗
      (Keccak2Vec16Mem (sp1 + 192#64) f0 f1 ∗ Keccak2Cap8Mem (sp1 + 192#64) f0 f1 ∗ F) by
      rw [hsp]; sep_frame) ?_
  wp_step
  wp_mlkem_call squeeze2_136_block_ok
    ({ statePtr := sp1 + 192#64, out0 := out0, out1 := out1, outLen := outLen,
       st0 := f0, st1 := f1 } : Squeeze2Args)
  have hsp' : sf.sp = sp1 := hsp_sf.trans hsp
  have halign' : sf.spAligned = true := by
    rw [State.spAligned, hsp', ← hsp, ← State.spAligned]; exact hsp_align
  refine SepWP.done hpc_sf hrun_sf ?_
  rw [sepPost_apply]
  refine ⟨⟨hsp', halign'⟩, ?_⟩
  rw [hsp]
  have h400 := Keccak2Mem_entails_memRegion (sp1 + 192#64) f0 f1
  unfold Keccak2Mem Keccak2Rate17Mem at h400
  exact entails_sub h400 (by sep_frame) (by sep_frame)

private theorem seg_0920_to_ret [MlKemPlacement] (b : BitVec 64)
    (F : SepProp) (s0 sm : State)
    (hsp0 : s0.spAligned = true)
    (hpc : sm.pc = b + 0x0920#64)
    (hrun : sm.status = .Running)
    (hsp : sm.sp = s0.sp - 1040#64) :
    SepWP (blkPC01.rebase b (fun _ => none)) (s0.readReg64 .lr) sm
      (SavedCalleeFrame s0.sp s0 ∗ F)
      (sepPost
        (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ F)) := by
  dsimp only [SavedCalleeFrame]
  have hsp160 : ((s0.sp - 1040#64) + 880#64 : BitVec 64) = s0.sp - 160#64 := by bv_omega
  have hsp160_align : (((s0.sp - 1040#64) + 880#64) &&& 15#64 == 0#64) = true := by
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
  · have h160 := savedCalleeFrame_entails_memRegion160 s0.sp s0
    dsimp only [SavedCalleeFrame] at h160
    exact entails_sub h160 (by sep_frame) (by sep_frame)

public section
section
attribute [local irreducible] Keccak2Mem SavedCalleeFrame Spill11

/-- Full final permute + `B08` squeeze + callee-saved restore + `RET` (`[0x05e4 → lr]`). -/
theorem squeeze_epilogue_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (a : Keccak2ShakeArgs) (hlen : a.in0.length = a.in1.length)
    (hout : a.outLen = 32 ∨ a.outLen = 128)
    (s0 : State) (rcBase : BitVec 64)
    (s16 s32 s48 s64 s80 s96 s112 : BitVec 128)
    (F : SepProp) (s : State)
    (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hpc : s.pc = b + 0x05e4#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hsp : s.sp = s0.sp - 1040#64)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 a.outLen)
    (hx21 : s.readReg64 .x21 = a.out1)
    (hx22 : s.readReg64 .x22 = a.out0)
    (hx27 : s.readReg64 .x27 = rcBase)
    (hrr : P2RoundRegs s
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in0 (a.in0.length / 136))
        (keccakLastBlock 136 0x1f#8 a.in0))
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 (a.in0.length / 136))
        (keccakLastBlock 136 0x1f#8 a.in1))) :
    let sp1 := s0.sp - 1040#64
    let xst0 := keccakXorRate17 (keccakAbsorbPrefix17 a.in0 (a.in0.length / 136))
      (keccakLastBlock 136 0x1f#8 a.in0)
    let xst1 := keccakXorRate17 (keccakAbsorbPrefix17 a.in1 (a.in0.length / 136))
      (keccakLastBlock 136 0x1f#8 a.in1)
    SepWP (blkPC01.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackAt sp1 96 ∗ memRegion sp1 8 ∗ ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗
        Spill11 sp1 s16 s32 s48 s64 s80 s96 s112
          (keccak2Lane xst0 xst1 2) (keccak2Lane xst0 xst1 3)
          (keccak2Lane xst0 xst1 6) (keccak2Lane xst0 xst1 4) ∗
        memRegion (sp1 + 192#64) 400 ∗ memRegion (sp1 + 592#64) 288 ∗
        SavedCalleeFrame s0.sp s0 ∗
        memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗
        (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
      (sepPost
        (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
          (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗
          stackAt s0.sp 1136 ∗
          (rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  intro sp1 xst0 xst1
  let f0 := keccakF1600 xst0
  let f1 := keccakF1600 xst1
  let F_perm : SepProp :=
    stackAt sp1 96 ∗ memRegion sp1 8 ∗ ((sp1 + 8#64) ↦₆₄ BitVec.ofNat 64 a.outLen) ∗
      memRegion (sp1 + 192#64) 400 ∗ memRegion (sp1 + 592#64) 288 ∗
      SavedCalleeFrame s0.sp s0 ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗ F
  refine SepWP.weaken_pre
    (show _ ⊢ Spill11 sp1 s16 s32 s48 s64 s80 s96 s112
        (keccak2Lane xst0 xst1 2) (keccak2Lane xst0 xst1 3)
        (keccak2Lane xst0 xst1 6) (keccak2Lane xst0 xst1 4) ∗
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F_perm) by dsimp only [F_perm]; sep_frame) ?_
  refine sepWP_seq_cl hcl
    (permute2_rounds hb hbase s sp1 rcBase xst0 xst1 s16 s32 s48 s64 s80 s96 s112 F_perm
      hpc hrun hsp hsp_align hx8 hx27 hrr) ?_
  intro s1 Q1 hpc1 hrun1 hcl1 ⟨hscal1, hrr1, s16', s32', s48', s64', s80', s96', s112', hQ1⟩
  let F_store : SepProp :=
    stackAt sp1 96 ∗ memRegion sp1 8 ∗ memRegion (sp1 + 592#64) 288 ∗
      SavedCalleeFrame s0.sp s0 ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗
      (rcBase ↦ᵣ mlkemData01Bytes) ∗ F
  have hwp2 := seg_08c8_to_091c b sp1 a.out0 a.out1 a.outLen f0 f1
    s16' s32' s48' s64' s80' s96' s112' F_store s1 hpc1 hrun1
    (hscal1.spAligned hsp_align) (hscal1.1.trans hsp)
    (hscal1.2.1.trans hx20) (hscal1.2.2.1.trans hx21) (hscal1.2.2.2.1.trans hx22) hrr1
  refine (fun h h1 => SepWP.weaken_pre h1 h) (sepWP_seq_cl hcl1 hwp2 ?_)
    (Entails.trans hQ1 (by dsimp only [f0, f1, F_perm, F_store]; sep_frame))
  intro s2 Q2 hpc2 hrun2 hcl2 hpost2
  rw [sepPost_apply] at hpost2
  rcases hpost2 with ⟨⟨hsp2, halign2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2⟩, hQ2⟩
  let F_sq : SepProp :=
    memRegion sp1 8 ∗ memRegion (sp1 + 8#64) 8 ∗ memRegion (sp1 + 16#64) 176 ∗
      memRegion (sp1 + 592#64) 288 ∗ SavedCalleeFrame s0.sp s0 ∗
      (rcBase ↦ᵣ mlkemData01Bytes) ∗ F
  have hQ2' : Q2 ⊢ stackAt sp1 96 ∗ Keccak2Mem (sp1 + 192#64) f0 f1 ∗
      memRegion a.out0 a.outLen ∗ memRegion a.out1 a.outLen ∗ F_sq := by
    refine Entails.trans hQ2 ?_
    exact entails_sub (pointsTo64_entails_memRegion (sp1 + 8#64) (BitVec.ofNat 64 a.outLen))
      (by sep_frame) (by dsimp only [F_store, F_sq]; sep_frame)
  have hwp3 := seg_091c_to_0920 b sp1 a.out0 a.out1 a.outLen hb hbase hout f0 f1 F_sq s2
    hcl2 hpc2 hrun2 halign2 hsp2 hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 hx5_2
  refine (fun h h2 => SepWP.weaken_pre h2 h) (SepWP.seq hwp3 ?_) hQ2'
  intro s3 Q3 hpc3 hrun3 hpost3
  rw [sepPost_apply] at hpost3
  rcases hpost3 with ⟨⟨hsp3, _⟩, hQ3⟩
  have hf1_eq : f1 = keccakF1600
      (keccakXorRate17 (keccakAbsorbPrefix17 a.in1 (a.in1.length / 136))
        (keccakLastBlock 136 0x1f#8 a.in1)) := by
    dsimp only [f1, xst1]; rw [hlen]
  have hout0_eq : (keccakExtractRate 17 f0).take a.outLen = shake256List a.outLen a.in0 :=
    take_extract_eq_shake256 a.in0 hout
  have hout1_eq : (keccakExtractRate 17 f1).take a.outLen = shake256List a.outLen a.in1 := by
    rw [hf1_eq]; exact take_extract_eq_shake256 a.in1 hout
  rw [hout0_eq, hout1_eq] at hQ3
  let F_ep : SepProp :=
    stackAt sp1 96 ∗ memRegion sp1 8 ∗ memRegion (sp1 + 8#64) 8 ∗
      memRegion (sp1 + 16#64) 176 ∗ memRegion (sp1 + 192#64) 400 ∗
      memRegion (sp1 + 592#64) 288 ∗
      (a.out0 ↦ₛ shake256List a.outLen a.in0) ∗
      (a.out1 ↦ₛ shake256List a.outLen a.in1) ∗
      (rcBase ↦ᵣ mlkemData01Bytes) ∗ F
  have hwp4 := seg_0920_to_ret b F_ep s0 s3 hsp0 hpc3 hrun3 hsp3
  refine (fun h h3 => SepWP.weaken_pre h3 h) (SepWP.mono hwp4 ?_)
    (Entails.trans hQ3 (by dsimp only [F_sq, F_ep]; sep_frame))
  intro sf Qf _ _ hpost4
  rw [sepPost_apply] at hpost4
  refine ⟨hpost4.1, Entails.trans hpost4.2 ?_⟩
  rw [stack1136_split s0.sp]
  dsimp only [sp1, F_ep]
  sep_frame

end
end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.SqueezeEpilogue
