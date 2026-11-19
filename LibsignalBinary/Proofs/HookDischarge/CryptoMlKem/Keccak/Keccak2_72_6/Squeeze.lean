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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B00` (`keccak2::<72, 6>`): 64-byte squeeze and epilogue

Proof of segment `[0x09ec → 0x0a5c]` (`29` instructions) of `mlkemBlk00`: deinterleaves lanes
`0..7` of the two `Keccak-f[1600]` output states into `(out0 ↦ₛ sha3_512List in0)` and
`(out1 ↦ₛ sha3_512List in1)`, deallocates the `720`-byte stack frame, restores all 20
callee-saved registers (`x19..x28`, `fp, lr`, `d8..d15`), and returns to `s0.readReg64 .lr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Squeeze

open Arm64 ProofLib ProofLib.GenPlacedFetches SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  keccakZeroState
  sha3_512List
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  keccak2Lane
  keccakXorRate9
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  keccakAbsorb_9_lt72
  keccakLastBlock
  memRegion64_cells
  pointsTo64_8_eq_bytes
  sha3_512List_eq_lanes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Base (
  LaneSlot
  LoopRegs
  LoopSpillMem
  LoopSpillMem_entails_memRegion224
  SavedFrame00
  blk00_code_eq
  blk00_tree_size
  blkLib00
  blkPC00
  blkPl00
  blkPlaceable00
  blkTree00
  savedFrame00_entails_memRegion160
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC00 blkLib00 blkTree00 blk00_code_eq blk00_tree_size
  via_placement blkPl00 blkPlaceable00 [0x09ec → 0x0a5c]
end

private theorem truncate64_zeroExtend128_truncate64 (v : BitVec 128) :
    ((v.truncate 64).zeroExtend 128).truncate 64 = v.truncate 64 := by
  ext i hi
  simp [BitVec.getElem_setWidth]

private theorem calleeSavedVRegs_eq_of_readVReg128 (s0 sf : State)
    (h8  : sf.readVReg128 8#5  = ((s0.readVReg128 8#5).truncate 64).zeroExtend 128)
    (h9  : sf.readVReg128 9#5  = ((s0.readVReg128 9#5).truncate 64).zeroExtend 128)
    (h10 : sf.readVReg128 10#5 = ((s0.readVReg128 10#5).truncate 64).zeroExtend 128)
    (h11 : sf.readVReg128 11#5 = ((s0.readVReg128 11#5).truncate 64).zeroExtend 128)
    (h12 : sf.readVReg128 12#5 = ((s0.readVReg128 12#5).truncate 64).zeroExtend 128)
    (h13 : sf.readVReg128 13#5 = ((s0.readVReg128 13#5).truncate 64).zeroExtend 128)
    (h14 : sf.readVReg128 14#5 = ((s0.readVReg128 14#5).truncate 64).zeroExtend 128)
    (h15 : sf.readVReg128 15#5 = ((s0.readVReg128 15#5).truncate 64).zeroExtend 128) :
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
  simp only [truncate64_zeroExtend128_truncate64]

private theorem out_cells_eq_sha3_512 (out : BitVec 64) (msg : List (BitVec 8))
    (hmsg : msg.length < 72) :
    let f := keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 msg))
    ((((out ↦₆₄ f.getD 0 0#64) ∗ ((out + 8#64) ↦₆₄ f.getD 1 0#64)) ∗
      (((out + 16#64) ↦₆₄ f.getD 2 0#64) ∗ ((out + 24#64) ↦₆₄ f.getD 3 0#64))) ∗
     ((((out + 32#64) ↦₆₄ f.getD 4 0#64) ∗ ((out + 40#64) ↦₆₄ f.getD 5 0#64)) ∗
      (((out + 48#64) ↦₆₄ f.getD 6 0#64) ∗ ((out + 56#64) ↦₆₄ f.getD 7 0#64)))) =
      (out ↦ₛ sha3_512List msg) := by
  intro f
  rw [pointsTo64_8_eq_bytes, sha3_512List_eq_lanes msg]
  dsimp only
  rw [keccakAbsorb_9_lt72 0x06#8 msg hmsg]

private theorem entails_sub {A B P Rest Q : SepProp}
    (hAB : A ⊢ B) (h1 : P ⊢ A ∗ Rest) (h2 : B ∗ Rest ⊢ Q) : P ⊢ Q :=
  Entails.trans h1 (Entails.trans (sepConj_mono_left hAB) h2)

private theorem stack720_restore_entails (sp0 : BitVec 64) (s0 : State)
    (f0 f1 : KeccakState) :
    let sp := sp0 - 720#64
    memRegion sp 176 ∗ LoopSpillMem sp f0 f1 ∗ memRegion (sp + 400#64) 160 ∗
      SavedFrame00 sp0 s0 ⊢ stackAt sp0 720 := by
  intro sp
  unfold stackAt
  have hsplit :
      memRegion (sp0 - BitVec.ofNat 64 720) 720 =
        memRegion sp 176 ∗ memRegion (sp + 176#64) 224 ∗
          memRegion (sp + 400#64) 160 ∗ memRegion (sp0 - 160#64) 160 := by
    change memRegion sp 720 = _
    rw [memRegion_split sp 176 544 (by decide),
        memRegion_split (sp + 176#64) 224 320 (by decide),
        show (sp + 176#64) + 224#64 = sp + 400#64 by dsimp [sp]; bv_omega,
        memRegion_split (sp + 400#64) 160 160 (by decide),
        show (sp + 400#64) + 160#64 = sp0 - 160#64 by dsimp [sp]; bv_omega]
  rw [hsplit]
  exact sepConj_mono (Entails.refl _) <|
    sepConj_mono (LoopSpillMem_entails_memRegion224 sp f0 f1) <|
    sepConj_mono (Entails.refl _) (savedFrame00_entails_memRegion160 sp0 s0)

public section

/-- Step `[0x09ec → 0x0a5c]` (64-byte 2-way `SHA3-512` squeeze + stack teardown + `RET`). -/
theorem squeeze_epilogue_ok [MlKemPlacement] (b : BitVec 64)
    (_hb : MlKemBase blkPl00 b) (_hbase : blkPl00.base = b)
    (out0 out1 : BitVec 64) (in0 in1 : List (BitVec 8))
    (hin0 : in0.length < 72) (hin1 : in1.length < 72)
    (rcBase : BitVec 64) (F : SepProp) (s0 s : State)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + 0x09ec#64)
    (hregs : LoopRegs s (s0.sp - 720#64) rcBase out0 out1 24
      (keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 in0)))
      (keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 in1)))) :
    let sp := s0.sp - 720#64
    let f0 := keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 in0))
    let f1 := keccakF1600 (keccakXorRate9 keccakZeroState (keccakLastBlock 72 0x06#8 in1))
    SepWP (blkPC00.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (memRegion sp 176 ∗ LoopSpillMem sp f0 f1 ∗ memRegion (sp + 400#64) 160 ∗
        SavedFrame00 s0.sp s0 ∗ memRegion out0 64 ∗ memRegion out1 64 ∗ F)
      (sepPost
        (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((out0 ↦ₛ sha3_512List in0) ∗ (out1 ↦ₛ sha3_512List in1) ∗
          stackAt s0.sp 720 ∗ F)) := by
  intro sp f0 f1
  rcases hregs with ⟨hrun, hsp_align, hsp, hx29, _hx25, hx20, hx19, _hx8,
    hv18, hv29, hv20, _hv10, _hv0, _hv28, _hv12, _hv8, _hv7, _hv13,
    _hv6, _hv15, _hv11, _hv14, _hv30, _hv27, _hv1, _hv5, _hv25, _hv26⟩
  dsimp only [keccak2Lane] at hv18 hv29 hv20
  refine memRegion64_cells out0 (by sep_focus)
    fun _o00 _o01 _o02 _o03 _o04 _o05 _o06 _o07 => ?_
  refine memRegion64_cells out1 (by sep_focus)
    fun _o10 _o11 _o12 _o13 _o14 _o15 _o16 _o17 => ?_
  dsimp only [sp, f0, f1, LoopSpillMem, LaneSlot, SavedFrame00]
  have hsp160 : ((s0.sp - 720#64) + 560#64 : BitVec 64) = s0.sp - 160#64 := by bv_omega
  have hsp160_align : (((s0.sp - 720#64) + 560#64) &&& 15#64 == 0#64) = true := by
    rw [hsp160]
    exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  · rw [sepPost_apply]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine Eq.trans (by wp_norm_lhs) ?_
      bv_omega
    · refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
      exact calleeSavedVRegs_eq_of_readVReg128 s0 _
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    · rw [← out_cells_eq_sha3_512 out0 in0 hin0, ← out_cells_eq_sha3_512 out1 in1 hin1]
      have hstk := stack720_restore_entails s0.sp s0 f0 f1
      dsimp only [f0, f1, LoopSpillMem, LaneSlot, SavedFrame00] at hstk ⊢
      exact entails_sub hstk (by sep_frame) (by sep_frame)

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6.Squeeze
