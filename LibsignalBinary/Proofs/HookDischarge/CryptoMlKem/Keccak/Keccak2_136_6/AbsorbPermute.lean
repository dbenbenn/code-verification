/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase
import ProofLib.ProgramReflection
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbRoundAB
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B02` (`keccak2::<136, 6>`): full-block inlined `keccak_f1600` (`+0x00b0 → +0x0428`)

Proof of segment `[0x00b0 → 0x0428]` of `mlkemBlk02` (`round1_partC`, `round1_step`,
`loop1_rounds`, and `seg_absorb_permute`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbPermute

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakF1600
  keccakF1600Round
  keccakRhoOffset
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (
  Keccak2Cap8Mem
  Keccak2Mem
  Keccak2Q0Mem
  Keccak2Q1Mem
  Keccak2Q2Mem
  Keccak2Q3Mem
  Keccak2Rate16Mem
  Keccak2Rate17Mem
  Keccak2Vec16Mem
  keccak2Lane
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC
  keccakD
  keccakRhoPi
  keccakRhoPiSrc
  keccakRoundLane
  keccakRunFrom
  keccakRunFrom_24
  keccakRunFrom_step
  keccakRunFrom_zero
  keccakTheta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (
  memRegion128_cells
  memRegion32_cells
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base (
  Loop1Regs
  Loop1SpillMem
  blk02_code_eq
  blk02_tree_size
  blkLib02
  blkPC02
  blkPl02
  blkPlaceable02
  blkTree02
  entails_sub
  loop1SpillMem_entails_memRegion
  step_ld1r_keccakRc
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase (
  AbsorbRegsPreserved
  Loop1MidMem
  Round1MidB
  Round1Post
  Round1RegsB
  add1_eq_ofNat
  bne192_target_eq
  bne_k_target_eq
  cells128_entails_memRegion
  chi0_lane_eq
  chi_lane_eq
  laneRhoPi
  laneShlTheta
  laneTheta
  orr_self_64
  rhopi_of_theta
  spAligned_of_sp_eq
  writeVReg128_eq_self
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbRoundAB (
  round1_partA
  round1_partB
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

set_option linter.literalFetch false in
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x00b0 → 0x00ec]

set_option linter.literalFetch false in
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x02dc → 0x0428]

attribute [local simp, local arm64_norm, local wp_norm] orr_self_64
attribute [local irreducible] blkPC02 keccakC keccakD keccakTheta keccakRhoPi keccakRoundLane

set_option maxRecDepth 20000 in
private theorem round1_partC [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (s0 sm : State) (sp rcBase : BitVec 64) (r : Nat) (st0 st1 : KeccakState)
    (F Pm : SepProp)
    (hr : r < 24)
    (hpc : sm.pc = b + 0x02dc#64)
    (hrun : sm.status = .Running)
    (hsp0 : s0.sp = sp)
    (hmid : Round1MidB s0 sp rcBase r st0 st1 F sm Pm) :
    SepWP (blkPC02.rebase b (fun _ => none))
      (if r + 1 < 24 then b + 0x00f0#64 else b + 0x03e4#64) sm Pm
      (Round1Post s0 sp rcBase r st0 st1 F) := by
  rcases hmid with ⟨hpres, hx24, hsp_align, hx8, hx9, hz, hregs, hmem⟩
  have hsp : sm.sp = sp := hpres.1.trans hsp0
  refine SepWP.weaken_pre hmem ?_
  rcases hregs with ⟨hv0, hv3, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv14, hv15, hv16, hv17,
    hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  simp only [laneTheta, laneRhoPi, laneShlTheta] at hv0 hv3 hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv14 hv15 hv16 hv17
  simp only [laneTheta, laneRhoPi] at hv18 hv19 hv20 hv21 hv22 hv23 hv24 hv25 hv26 hv27 hv28 hv29 hv30 hv31
  unfold Loop1MidMem
  generalize ht0_9 : keccakTheta st0 9 = t0_9; generalize ht1_9 : keccakTheta st1 9 = t1_9
  generalize ht0_4 : keccakTheta st0 4 = t0_4; generalize ht1_4 : keccakTheta st1 4 = t1_4
  generalize ht0_19 : keccakTheta st0 19 = t0_19; generalize ht1_19 : keccakTheta st1 19 = t1_19
  generalize ht0_14 : keccakTheta st0 14 = t0_14; generalize ht1_14 : keccakTheta st1 14 = t1_14
  generalize hrp0_0 : keccakRhoPi st0 0 = rp0_0; generalize hrp1_0 : keccakRhoPi st1 0 = rp1_0
  generalize hrp0_1 : keccakRhoPi st0 1 = rp0_1; generalize hrp1_1 : keccakRhoPi st1 1 = rp1_1
  generalize hrp0_2 : keccakRhoPi st0 2 = rp0_2; generalize hrp1_2 : keccakRhoPi st1 2 = rp1_2
  generalize hrp0_3 : keccakRhoPi st0 3 = rp0_3; generalize hrp1_3 : keccakRhoPi st1 3 = rp1_3
  generalize hrp0_4 : keccakRhoPi st0 4 = rp0_4; generalize hrp1_4 : keccakRhoPi st1 4 = rp1_4
  generalize hrp0_5 : keccakRhoPi st0 5 = rp0_5; generalize hrp1_5 : keccakRhoPi st1 5 = rp1_5
  generalize hrp0_7 : keccakRhoPi st0 7 = rp0_7; generalize hrp1_7 : keccakRhoPi st1 7 = rp1_7
  generalize hrp0_8 : keccakRhoPi st0 8 = rp0_8; generalize hrp1_8 : keccakRhoPi st1 8 = rp1_8
  generalize hrp0_9 : keccakRhoPi st0 9 = rp0_9; generalize hrp1_9 : keccakRhoPi st1 9 = rp1_9
  generalize hrp0_10 : keccakRhoPi st0 10 = rp0_10; generalize hrp1_10 : keccakRhoPi st1 10 = rp1_10
  generalize hrp0_11 : keccakRhoPi st0 11 = rp0_11; generalize hrp1_11 : keccakRhoPi st1 11 = rp1_11
  generalize hrp0_12 : keccakRhoPi st0 12 = rp0_12; generalize hrp1_12 : keccakRhoPi st1 12 = rp1_12
  generalize hrp0_14 : keccakRhoPi st0 14 = rp0_14; generalize hrp1_14 : keccakRhoPi st1 14 = rp1_14
  generalize hrp0_16 : keccakRhoPi st0 16 = rp0_16; generalize hrp1_16 : keccakRhoPi st1 16 = rp1_16
  generalize hrp0_17 : keccakRhoPi st0 17 = rp0_17; generalize hrp1_17 : keccakRhoPi st1 17 = rp1_17
  generalize hrp0_18 : keccakRhoPi st0 18 = rp0_18; generalize hrp1_18 : keccakRhoPi st1 18 = rp1_18
  generalize hrp0_19 : keccakRhoPi st0 19 = rp0_19; generalize hrp1_19 : keccakRhoPi st1 19 = rp1_19
  generalize hrp0_20 : keccakRhoPi st0 20 = rp0_20; generalize hrp1_20 : keccakRhoPi st1 20 = rp1_20
  generalize hrp0_21 : keccakRhoPi st0 21 = rp0_21; generalize hrp1_21 : keccakRhoPi st1 21 = rp1_21
  generalize hrp0_23 : keccakRhoPi st0 23 = rp0_23; generalize hrp1_23 : keccakRhoPi st1 23 = rp1_23
  generalize hrp0_24 : keccakRhoPi st0 24 = rp0_24; generalize hrp1_24 : keccakRhoPi st1 24 = rp1_24
  rw [ht0_9, ht1_9] at hv0 hv7; rw [ht0_4, ht1_4] at hv3 hv21
  rw [ht0_19, ht1_19] at hv25; rw [ht0_14, ht1_14] at hv30
  rw [hrp0_21, hrp1_21] at hv6; rw [hrp0_16, hrp1_16] at hv8; rw [hrp0_0, hrp1_0] at hv9
  rw [hrp0_24, hrp1_24] at hv10; rw [hrp0_7, hrp1_7] at hv11; rw [hrp0_18, hrp1_18] at hv12
  rw [hrp0_4, hrp1_4] at hv14; rw [hrp0_12, hrp1_12] at hv15; rw [hrp0_2, hrp1_2] at hv16
  rw [hrp0_19, hrp1_19] at hv17; rw [hrp0_11, hrp1_11] at hv18; rw [hrp0_3, hrp1_3] at hv19
  rw [hrp0_8, hrp1_8] at hv20; rw [hrp0_9, hrp1_9] at hv22; rw [hrp0_5, hrp1_5] at hv23
  rw [hrp0_1, hrp1_1] at hv24; rw [hrp0_20, hrp1_20] at hv26; rw [hrp0_10, hrp1_10] at hv27
  rw [hrp0_17, hrp1_17] at hv28; rw [hrp0_14, hrp1_14] at hv29; rw [hrp0_23, hrp1_23] at hv31
  let s_in :=
    (((((((((((((((((((((((((((sm.writeVReg128 0#5 ((t1_9 <<< 20) ++ (t0_9 <<< 20))).writeVReg128
      3#5 ((t1_4 <<< 27) ++ (t0_4 <<< 27))).writeVReg128 6#5 (rp1_21 ++ rp0_21)).writeVReg128
      7#5 (t1_9 ++ t0_9)).writeVReg128 8#5 (rp1_16 ++ rp0_16)).writeVReg128
      9#5 (rp1_0 ++ rp0_0)).writeVReg128 10#5 (rp1_24 ++ rp0_24)).writeVReg128
      11#5 (rp1_7 ++ rp0_7)).writeVReg128 12#5 (rp1_18 ++ rp0_18)).writeVReg128
      14#5 (rp1_4 ++ rp0_4)).writeVReg128 15#5 (rp1_12 ++ rp0_12)).writeVReg128
      16#5 (rp1_2 ++ rp0_2)).writeVReg128 17#5 (rp1_19 ++ rp0_19)).writeVReg128
      18#5 (rp1_11 ++ rp0_11)).writeVReg128 19#5 (rp1_3 ++ rp0_3)).writeVReg128
      20#5 (rp1_8 ++ rp0_8)).writeVReg128 21#5 (t1_4 ++ t0_4)).writeVReg128
      22#5 (rp1_9 ++ rp0_9)).writeVReg128 23#5 (rp1_5 ++ rp0_5)).writeVReg128
      24#5 (rp1_1 ++ rp0_1)).writeVReg128 25#5 (t1_19 ++ t0_19)).writeVReg128
      26#5 (rp1_20 ++ rp0_20)).writeVReg128 27#5 (rp1_10 ++ rp0_10)).writeVReg128
      28#5 (rp1_17 ++ rp0_17)).writeVReg128 29#5 (rp1_14 ++ rp0_14)).writeVReg128
      30#5 (t1_14 ++ t0_14)).writeVReg128 31#5 (rp1_23 ++ rp0_23))
  have hs_in : s_in = sm := by
    dsimp only [s_in]
    rw [writeVReg128_eq_self hv0, writeVReg128_eq_self hv3, writeVReg128_eq_self hv6,
        writeVReg128_eq_self hv7, writeVReg128_eq_self hv8, writeVReg128_eq_self hv9,
        writeVReg128_eq_self hv10, writeVReg128_eq_self hv11, writeVReg128_eq_self hv12,
        writeVReg128_eq_self hv14, writeVReg128_eq_self hv15, writeVReg128_eq_self hv16,
        writeVReg128_eq_self hv17, writeVReg128_eq_self hv18, writeVReg128_eq_self hv19,
        writeVReg128_eq_self hv20, writeVReg128_eq_self hv21, writeVReg128_eq_self hv22,
        writeVReg128_eq_self hv23, writeVReg128_eq_self hv24, writeVReg128_eq_self hv25,
        writeVReg128_eq_self hv26, writeVReg128_eq_self hv27, writeVReg128_eq_self hv28,
        writeVReg128_eq_self hv29, writeVReg128_eq_self hv30, writeVReg128_eq_self hv31]
  conv => arg 3; rw [← hs_in]
  dsimp only [s_in]
  wp_steps 45
  apply step_ld1r_keccakRc (rcBase := rcBase) r hr
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · symm; reg64_lhs; exact hx9
  · wp_norm_lhs
  wp_steps 20
  have hrp0_6 : t0_9.rotateLeft 20 = keccakRhoPi st0 6 := rhopi_of_theta st0 6 9 20 rfl rfl ht0_9.symm
  have hrp1_6 : t1_9.rotateLeft 20 = keccakRhoPi st1 6 := rhopi_of_theta st1 6 9 20 rfl rfl ht1_9.symm
  have hrp0_13 : t0_19.rotateLeft 8 = keccakRhoPi st0 13 := rhopi_of_theta st0 13 19 8 rfl rfl ht0_19.symm
  have hrp1_13 : t1_19.rotateLeft 8 = keccakRhoPi st1 13 := rhopi_of_theta st1 13 19 8 rfl rfl ht1_19.symm
  have hrp0_15 : t0_4.rotateLeft 27 = keccakRhoPi st0 15 := rhopi_of_theta st0 15 4 27 rfl rfl ht0_4.symm
  have hrp1_15 : t1_4.rotateLeft 27 = keccakRhoPi st1 15 := rhopi_of_theta st1 15 4 27 rfl rfl ht1_4.symm
  have hrp0_22 : t0_14.rotateLeft 39 = keccakRhoPi st0 22 := rhopi_of_theta st0 22 14 39 rfl rfl ht0_14.symm
  have hrp1_22 : t1_14.rotateLeft 39 = keccakRhoPi st1 22 := rhopi_of_theta st1 22 14 39 rfl rfl ht1_14.symm
  apply SepWP.done
  · rw [← bne192_target_eq hr]; wp_norm_lhs
  · wp_norm_lhs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AbsorbRegsPreserved.trans hpres
      ⟨by rw [hsp]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  · wp_norm_lhs
  · exact spAligned_of_sp_eq (by rw [hsp]; wp_norm_lhs) hsp_align
  · wp_norm_lhs
  · dsimp only [Loop1Regs, keccak2Lane]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← chi0_lane_eq st0 (keccakRcAt r) hrp0_0.symm hrp0_1.symm hrp0_2.symm,
          ← chi0_lane_eq st1 (keccakRcAt r) hrp1_0.symm hrp1_1.symm hrp1_2.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 1 1 2 3 rfl (by decide) rfl rfl rfl hrp0_1.symm hrp0_2.symm hrp0_3.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 1 1 2 3 rfl (by decide) rfl rfl rfl hrp1_1.symm hrp1_2.symm hrp1_3.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 2 2 3 4 rfl (by decide) rfl rfl rfl hrp0_2.symm hrp0_3.symm hrp0_4.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 2 2 3 4 rfl (by decide) rfl rfl rfl hrp1_2.symm hrp1_3.symm hrp1_4.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 3 3 4 0 rfl (by decide) rfl rfl rfl hrp0_3.symm hrp0_4.symm hrp0_0.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 3 3 4 0 rfl (by decide) rfl rfl rfl hrp1_3.symm hrp1_4.symm hrp1_0.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 4 4 0 1 rfl (by decide) rfl rfl rfl hrp0_4.symm hrp0_0.symm hrp0_1.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 4 4 0 1 rfl (by decide) rfl rfl rfl hrp1_4.symm hrp1_0.symm hrp1_1.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 5 5 6 7 rfl (by decide) rfl rfl rfl hrp0_5.symm hrp0_6 hrp0_7.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 5 5 6 7 rfl (by decide) rfl rfl rfl hrp1_5.symm hrp1_6 hrp1_7.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 6 6 7 8 rfl (by decide) rfl rfl rfl hrp0_6 hrp0_7.symm hrp0_8.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 6 6 7 8 rfl (by decide) rfl rfl rfl hrp1_6 hrp1_7.symm hrp1_8.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 9 9 5 6 rfl (by decide) rfl rfl rfl hrp0_9.symm hrp0_5.symm hrp0_6,
          ← chi_lane_eq st1 (keccakRcAt r) 9 9 5 6 rfl (by decide) rfl rfl rfl hrp1_9.symm hrp1_5.symm hrp1_6]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 10 10 11 12 rfl (by decide) rfl rfl rfl hrp0_10.symm hrp0_11.symm hrp0_12.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 10 10 11 12 rfl (by decide) rfl rfl rfl hrp1_10.symm hrp1_11.symm hrp1_12.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 11 11 12 13 rfl (by decide) rfl rfl rfl hrp0_11.symm hrp0_12.symm hrp0_13,
          ← chi_lane_eq st1 (keccakRcAt r) 11 11 12 13 rfl (by decide) rfl rfl rfl hrp1_11.symm hrp1_12.symm hrp1_13]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 12 12 13 14 rfl (by decide) rfl rfl rfl hrp0_12.symm hrp0_13 hrp0_14.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 12 12 13 14 rfl (by decide) rfl rfl rfl hrp1_12.symm hrp1_13 hrp1_14.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 13 13 14 10 rfl (by decide) rfl rfl rfl hrp0_13 hrp0_14.symm hrp0_10.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 13 13 14 10 rfl (by decide) rfl rfl rfl hrp1_13 hrp1_14.symm hrp1_10.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 15 15 16 17 rfl (by decide) rfl rfl rfl hrp0_15 hrp0_16.symm hrp0_17.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 15 15 16 17 rfl (by decide) rfl rfl rfl hrp1_15 hrp1_16.symm hrp1_17.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 16 16 17 18 rfl (by decide) rfl rfl rfl hrp0_16.symm hrp0_17.symm hrp0_18.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 16 16 17 18 rfl (by decide) rfl rfl rfl hrp1_16.symm hrp1_17.symm hrp1_18.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 17 17 18 19 rfl (by decide) rfl rfl rfl hrp0_17.symm hrp0_18.symm hrp0_19.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 17 17 18 19 rfl (by decide) rfl rfl rfl hrp1_17.symm hrp1_18.symm hrp1_19.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 18 18 19 15 rfl (by decide) rfl rfl rfl hrp0_18.symm hrp0_19.symm hrp0_15,
          ← chi_lane_eq st1 (keccakRcAt r) 18 18 19 15 rfl (by decide) rfl rfl rfl hrp1_18.symm hrp1_19.symm hrp1_15]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 19 19 15 16 rfl (by decide) rfl rfl rfl hrp0_19.symm hrp0_15 hrp0_16.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 19 19 15 16 rfl (by decide) rfl rfl rfl hrp1_19.symm hrp1_15 hrp1_16.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 20 20 21 22 rfl (by decide) rfl rfl rfl hrp0_20.symm hrp0_21.symm hrp0_22,
          ← chi_lane_eq st1 (keccakRcAt r) 20 20 21 22 rfl (by decide) rfl rfl rfl hrp1_20.symm hrp1_21.symm hrp1_22]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 21 21 22 23 rfl (by decide) rfl rfl rfl hrp0_21.symm hrp0_22 hrp0_23.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 21 21 22 23 rfl (by decide) rfl rfl rfl hrp1_21.symm hrp1_22 hrp1_23.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 22 22 23 24 rfl (by decide) rfl rfl rfl hrp0_22 hrp0_23.symm hrp0_24.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 22 22 23 24 rfl (by decide) rfl rfl rfl hrp1_22 hrp1_23.symm hrp1_24.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 23 23 24 20 rfl (by decide) rfl rfl rfl hrp0_23.symm hrp0_24.symm hrp0_20.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 23 23 24 20 rfl (by decide) rfl rfl rfl hrp1_23.symm hrp1_24.symm hrp1_20.symm]; vreg_lhs
    · rw [← chi_lane_eq st0 (keccakRcAt r) 24 24 20 21 rfl (by decide) rfl rfl rfl hrp0_24.symm hrp0_20.symm hrp0_21.symm,
          ← chi_lane_eq st1 (keccakRcAt r) 24 24 20 21 rfl (by decide) rfl rfl rfl hrp1_24.symm hrp1_20.symm hrp1_21.symm]; vreg_lhs
  · refine entails_sub
      (Rest := (rcBase ↦ᵣ mlkemData01Bytes) ∗
        (((sp + 128#64) ↦₆₄ (keccakF1600Round st0 (keccakRcAt r)).getD 7 0#64) ∗
         ((sp + 136#64) ↦₆₄ (keccakF1600Round st1 (keccakRcAt r)).getD 7 0#64)) ∗
        (((sp + 144#64) ↦₆₄ (keccakF1600Round st0 (keccakRcAt r)).getD 8 0#64) ∗
         ((sp + 152#64) ↦₆₄ (keccakF1600Round st1 (keccakRcAt r)).getD 8 0#64)) ∗
        (((sp + 160#64) ↦₆₄ (keccakF1600Round st0 (keccakRcAt r)).getD 14 0#64) ∗
         ((sp + 168#64) ↦₆₄ (keccakF1600Round st1 (keccakRcAt r)).getD 14 0#64)) ∗ F)
      (cells128_entails_memRegion sp
        (st0.getD 11 0#64) (st1.getD 11 0#64) (st0.getD 23 0#64) (st1.getD 23 0#64)
        (st0.getD 24 0#64) (st1.getD 24 0#64) (st0.getD 13 0#64) (st1.getD 13 0#64)
        (st0.getD 19 0#64) (st1.getD 19 0#64) (st0.getD 18 0#64) (st1.getD 18 0#64)
        (st0.getD 9 0#64) (st1.getD 9 0#64) (~~~rp0_1 &&& rp0_2) (~~~rp1_1 &&& rp1_2)) ?_
      (by unfold Loop1SpillMem; sep_entail)
    rw [← chi_lane_eq st0 (keccakRcAt r) 7 7 8 9 rfl (by decide) rfl rfl rfl hrp0_7.symm hrp0_8.symm hrp0_9.symm,
        ← chi_lane_eq st1 (keccakRcAt r) 7 7 8 9 rfl (by decide) rfl rfl rfl hrp1_7.symm hrp1_8.symm hrp1_9.symm,
        ← chi_lane_eq st0 (keccakRcAt r) 8 8 9 5 rfl (by decide) rfl rfl rfl hrp0_8.symm hrp0_9.symm hrp0_5.symm,
        ← chi_lane_eq st1 (keccakRcAt r) 8 8 9 5 rfl (by decide) rfl rfl rfl hrp1_8.symm hrp1_9.symm hrp1_5.symm,
        ← chi_lane_eq st0 (keccakRcAt r) 14 14 10 11 rfl (by decide) rfl rfl rfl hrp0_14.symm hrp0_10.symm hrp0_11.symm,
        ← chi_lane_eq st1 (keccakRcAt r) 14 14 10 11 rfl (by decide) rfl rfl rfl hrp1_14.symm hrp1_10.symm hrp1_11.symm]
    sep_entail

/-- One complete round (`+0x00f0 → +0x03e0`) of Loop 1 (`keccak_f1600`). -/
private theorem round1_step [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (s : State) (sp rcBase : BitVec 64) (r : Nat) (st0 st1 : KeccakState) (F : SepProp)
    (hr : r < 24)
    (hpc : s.pc = b + 0x00f0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (8 * r))
    (hx25 : s.readReg64 .x25 = rcBase)
    (hregs : Loop1Regs s st0 st1) :
    SepWP (blkPC02.rebase b (fun _ => none))
      (if r + 1 < 24 then b + 0x00f0#64 else b + 0x03e4#64) s
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0 st1 ∗ F)
      (Round1Post s sp rcBase r st0 st1 F) :=
  SepWP.seq (round1_partA hb hbase s sp rcBase r st0 st1 F hpc hrun hsp hsp_align hx8 hx25 hregs)
    fun smA PmA hpcA hrunA hmidA =>
      SepWP.seq (round1_partB hb hbase s smA sp rcBase r st0 st1 F PmA hpcA hrunA hsp hmidA)
        fun smB PmB hpcB hrunB hmidB =>
          round1_partC hb hbase s smB sp rcBase r st0 st1 F PmB hr hpcB hrunB hsp hmidB

/-! ## 24-round countdown (`loop1_rounds`) and full absorb-permute segment (`seg_absorb_permute`) -/

/-- Execute rounds `r .. 23` (`r + rem = 24`, `0 < rem`) from `+0x00f0` to `+0x03e4`. -/
private theorem loop1_rounds [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b) :
    ∀ (rem r : Nat) (s : State) (sp rcBase : BitVec 64) (st0 st1 : KeccakState) (F : SepProp),
      r + rem = 24 →
      0 < rem →
      s.pc = b + 0x00f0#64 →
      s.status = .Running →
      s.sp = sp →
      s.spAligned = true →
      s.readReg64 .x8 = BitVec.ofNat 64 (8 * r) →
      s.readReg64 .x25 = rcBase →
      Loop1Regs s st0 st1 →
      SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x03e4#64) s
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0 st1 ∗ F)
        (fun sf Q =>
          AbsorbRegsPreserved s sf ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.spAligned = true ∧
          Loop1Regs sf (keccakRunFrom r st0) (keccakRunFrom r st1) ∧
          (Q ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
            Loop1SpillMem sp (keccakRunFrom r st0) (keccakRunFrom r st1) ∗ F)) := by
  intro rem
  induction rem with
  | zero =>
    intro _ _ _ _ _ _ _ _ hpos
    exact absurd hpos (Nat.lt_irrefl 0)
  | succ rem ih =>
    intro r s sp rcBase st0 st1 F hsum _ hpc hrun hsp halign hx8 hx25 hregs
    by_cases hrem : rem = 0
    · subst hrem
      have hr : r = 23 := by omega
      subst hr
      have hstep := round1_step hb hbase s sp rcBase 23 st0 st1 F (by decide)
        hpc hrun hsp halign hx8 hx25 hregs
      simp only [show ¬(23 + 1 < 24) by decide, ↓reduceIte] at hstep
      refine SepWP.mono hstep fun sf Q _ _ hpost => ?_
      rcases hpost with ⟨hpres, hx24, halign', _, hregs', hQ⟩
      rw [keccakRunFrom_step 23 (by decide) st0, keccakRunFrom_24,
          keccakRunFrom_step 23 (by decide) st1, keccakRunFrom_24]
      exact ⟨hpres, hx24, halign', hregs', hQ⟩
    · have hr : r < 24 := by omega
      have hlt : r + 1 < 24 := by omega
      have hstep := round1_step hb hbase s sp rcBase r st0 st1 F hr
        hpc hrun hsp halign hx8 hx25 hregs
      simp only [hlt, ↓reduceIte] at hstep
      refine SepWP.seq hstep fun sm Pm hpcm hrunm hpost => ?_
      rcases hpost with ⟨hpres1, hx24_1, halign1, hx8_1, hregs1, hPm⟩
      have hsp1 : sm.sp = sp := hpres1.1.trans hsp
      have hx25_1 : sm.readReg64 .x25 = rcBase := hpres1.2.2.2.2.2.2.1.trans hx25
      refine SepWP.weaken_pre hPm ?_
      refine SepWP.mono
        (ih (r + 1) sm sp rcBase
          (keccakF1600Round st0 (keccakRcAt r)) (keccakF1600Round st1 (keccakRcAt r)) F
          (by omega) (by omega) hpcm hrunm hsp1 halign1 hx8_1 hx25_1 hregs1)
        fun sf Q _ _ ⟨hpres2, hx24_2, halign2, hregs2, hQ⟩ => ?_
      rw [keccakRunFrom_step r hr st0, keccakRunFrom_step r hr st1]
      exact ⟨AbsorbRegsPreserved.trans hpres1 hpres2, hx24_2.trans hx24_1, halign2, hregs2, hQ⟩

public section

set_option maxRecDepth 20000 in
/-- Full post-`B09` permute + loop-latch segment (`+0x00b0 → +0x009c / +0x042c`). -/
theorem seg_absorb_permute [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl02 b) (hbase : blkPl02.base = b)
    (s : State) (sp rcBase : BitVec 64) (k nBlocks : Nat)
    (st0 st1 : KeccakState) (F : SepProp)
    (hk : k < nBlocks)
    (hn : nBlocks < 2 ^ 64)
    (hpc : s.pc = b + 0x00b0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 nBlocks)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 k)
    (hx25 : s.readReg64 .x25 = rcBase) :
    SepWP (blkPC02.rebase b (fun _ => none))
      (if k + 1 < nBlocks then b + 0x009c#64 else b + 0x042c#64) s
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗
       memRegion sp 176 ∗
       Keccak2Mem (sp + 176#64) st0 st1 ∗
       F)
      (fun sf Q =>
        AbsorbRegsPreserved s sf ∧
        sf.spAligned = true ∧
        sf.readReg64 .x24 = BitVec.ofNat 64 (k + 1) ∧
        (Q ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗
          memRegion sp 176 ∗
          Keccak2Mem (sp + 176#64) (keccakF1600 st0) (keccakF1600 st1) ∗
          F)) := by
  -- 1. Load state into Loop1Regs + Loop1SpillMem (+0x00b0 → +0x00f0, 16 instructions)
  have hload :
      SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x00f0#64) s
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗
         memRegion sp 176 ∗
         Keccak2Mem (sp + 176#64) st0 st1 ∗
         F)
        (fun s1 P1 =>
          AbsorbRegsPreserved s s1 ∧
          s1.readReg64 .x24 = BitVec.ofNat 64 k ∧
          s1.spAligned = true ∧
          s1.readReg64 .x8 = 0#64 ∧
          Loop1Regs s1 st0 st1 ∧
          (P1 ⊢ (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0 st1 ∗
            (memRegion (sp + 176#64) 400 ∗ F))) := by
    rw [memRegion_split' (b := sp) (b' := sp + 128#64) (n := 128) (k := 48) rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 128#64) (b' := sp + 160#64) (n := 32) (k := 16) rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 160#64) (b' := sp + 168#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
    refine memRegion32_cells (sp + 128#64) (by sep_focus) fun u0 u1 u2 u3 => ?_
    refine SepWP.memRegion8_cell (sp + 160#64) fun u4 => ?_
    refine SepWP.memRegion8_cell (sp + 168#64) fun u5 => ?_
    unfold Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
      Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
    wp_steps 16
    apply SepWP.done
    · wp_norm_lhs
    · wp_norm_lhs
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by rw [hsp]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
        by wp_norm_lhs, by rw [hx23]; wp_norm_lhs, by rw [hx25]; wp_norm_lhs, by wp_norm_lhs⟩
    · wp_norm_lhs; try exact hx24
    · exact spAligned_of_sp_eq (by rw [hsp]; wp_norm_lhs) hsp_align
    · wp_norm_lhs
    · dsimp only [Loop1Regs, keccak2Lane]
      refine ⟨by vreg_lhs, by vreg_lhs, by vreg_lhs, by vreg_lhs,
        by vreg_lhs, by vreg_lhs, by vreg_lhs, by vreg_lhs,
        by vreg_lhs, by vreg_lhs, by vreg_lhs, by vreg_lhs,
        by vreg_lhs, by vreg_lhs, by vreg_lhs, by vreg_lhs,
        by vreg_lhs, by vreg_lhs, by vreg_lhs, by vreg_lhs,
        by vreg_lhs, by vreg_lhs⟩
    · have hkc :
          Keccak2Mem (sp + 176#64) st0 st1 ⊢ memRegion (sp + 176#64) 400 :=
        LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs.Keccak2Mem_entails_memRegion _ _ _
      refine entails_sub (Rest := (rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0 st1 ∗ F)
        hkc ?_ (by sep_entail)
      unfold Loop1SpillMem Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
        Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
      rw [← hsp]
      sep_entail
  -- 2. Run 24 rounds (+0x00f0 → +0x03e4)
  refine SepWP.seq hload fun s1 P1 hpc1 hrun1 ⟨hpres1, hx24_1, halign1, hx8_1, hregs1, hP1⟩ => ?_
  have hsp1 : s1.sp = sp := hpres1.1.trans hsp
  have hx25_1 : s1.readReg64 .x25 = rcBase := hpres1.2.2.2.2.2.2.1.trans hx25
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.seq
    (loop1_rounds hb hbase 24 0 s1 sp rcBase st0 st1 (memRegion (sp + 176#64) 400 ∗ F)
      rfl (by decide) hpc1 hrun1 hsp1 halign1 hx8_1 hx25_1 hregs1)
    fun s2 P2 hpc2 hrun2 ⟨hpres2, hx24_2, halign2, hregs2, hP2⟩ => ?_
  rw [keccakRunFrom_zero st0, keccakRunFrom_zero st1] at hregs2 hP2
  -- 3. Store Keccak2Mem (sp + 176) + increment/branch (+0x03e4 → +0x0428, 18 instructions)
  have hpres12 := AbsorbRegsPreserved.trans hpres1 hpres2
  have hsp2 : s2.sp = sp := hpres12.1.trans hsp
  have hx23_2 : s2.readReg64 .x23 = BitVec.ofNat 64 nBlocks := hpres12.2.2.2.2.2.1.trans hx23
  have hx24_2' : s2.readReg64 .x24 = BitVec.ofNat 64 k := hx24_2.trans hx24_1
  refine SepWP.weaken_pre hP2 ?_
  set out0 := keccakF1600 st0
  set out1 := keccakF1600 st1
  rcases hregs2 with ⟨hv9, hv6, hv24, hv16, hv19, hv30, hv7, hv11, hv5, hv22,
    hv18, hv15, hv29, hv23, hv27, hv12, hv3, hv8, hv28, hv17, hv4, hv2⟩
  simp only [keccak2Lane] at hv9 hv6 hv24 hv16 hv19 hv30 hv7 hv11 hv5 hv22 hv18
  simp only [keccak2Lane] at hv15 hv29 hv23 hv27 hv12 hv3 hv8 hv28 hv17 hv4 hv2
  let s2_in :=
    ((((((((((((((((((((((s2.writeVReg128 9#5 (out1.getD 0 0#64 ++ out0.getD 0 0#64)).writeVReg128
      6#5 (out1.getD 1 0#64 ++ out0.getD 1 0#64)).writeVReg128
      24#5 (out1.getD 2 0#64 ++ out0.getD 2 0#64)).writeVReg128
      16#5 (out1.getD 3 0#64 ++ out0.getD 3 0#64)).writeVReg128
      19#5 (out1.getD 4 0#64 ++ out0.getD 4 0#64)).writeVReg128
      30#5 (out1.getD 5 0#64 ++ out0.getD 5 0#64)).writeVReg128
      7#5 (out1.getD 6 0#64 ++ out0.getD 6 0#64)).writeVReg128
      11#5 (out1.getD 9 0#64 ++ out0.getD 9 0#64)).writeVReg128
      5#5 (out1.getD 10 0#64 ++ out0.getD 10 0#64)).writeVReg128
      22#5 (out1.getD 11 0#64 ++ out0.getD 11 0#64)).writeVReg128
      18#5 (out1.getD 12 0#64 ++ out0.getD 12 0#64)).writeVReg128
      15#5 (out1.getD 13 0#64 ++ out0.getD 13 0#64)).writeVReg128
      29#5 (out1.getD 15 0#64 ++ out0.getD 15 0#64)).writeVReg128
      23#5 (out1.getD 16 0#64 ++ out0.getD 16 0#64)).writeVReg128
      27#5 (out1.getD 17 0#64 ++ out0.getD 17 0#64)).writeVReg128
      12#5 (out1.getD 18 0#64 ++ out0.getD 18 0#64)).writeVReg128
      3#5 (out1.getD 19 0#64 ++ out0.getD 19 0#64)).writeVReg128
      8#5 (out1.getD 20 0#64 ++ out0.getD 20 0#64)).writeVReg128
      28#5 (out1.getD 21 0#64 ++ out0.getD 21 0#64)).writeVReg128
      17#5 (out1.getD 22 0#64 ++ out0.getD 22 0#64)).writeVReg128
      4#5 (out1.getD 23 0#64 ++ out0.getD 23 0#64)).writeVReg128
      2#5 (out1.getD 24 0#64 ++ out0.getD 24 0#64))
  have hs2_in : s2_in = s2 := by
    dsimp only [s2_in]
    rw [writeVReg128_eq_self hv9, writeVReg128_eq_self hv6, writeVReg128_eq_self hv24,
        writeVReg128_eq_self hv16, writeVReg128_eq_self hv19, writeVReg128_eq_self hv30,
        writeVReg128_eq_self hv7, writeVReg128_eq_self hv11, writeVReg128_eq_self hv5,
        writeVReg128_eq_self hv22, writeVReg128_eq_self hv18, writeVReg128_eq_self hv15,
        writeVReg128_eq_self hv29, writeVReg128_eq_self hv23, writeVReg128_eq_self hv27,
        writeVReg128_eq_self hv12, writeVReg128_eq_self hv3, writeVReg128_eq_self hv8,
        writeVReg128_eq_self hv28, writeVReg128_eq_self hv17, writeVReg128_eq_self hv4,
        writeVReg128_eq_self hv2]
  conv => arg 3; rw [← hs2_in]
  dsimp only [s2_in]
  -- Split memRegion (sp + 176) 400 = 128 + 128 + 128 + 16
  rw [show memRegion (sp + 176#64) 400 =
        memRegion (sp + 176#64) 272 ∗ memRegion (sp + 448#64) 128 from
        memRegion_split' (b' := sp + 448#64) (n := 272) (k := 128) rfl (by bv_omega) (by decide),
      show memRegion (sp + 176#64) 272 =
        memRegion (sp + 176#64) 256 ∗ memRegion (sp + 432#64) 16 from
        memRegion_split' (b' := sp + 432#64) (n := 256) (k := 16) rfl (by bv_omega) (by decide),
      show memRegion (sp + 176#64) 256 =
        memRegion (sp + 176#64) 128 ∗ memRegion (sp + 304#64) 128 from
        memRegion_split' (b' := sp + 304#64) (n := 128) (k := 128) rfl (by bv_omega) (by decide),
      show memRegion (sp + 432#64) 16 =
        memRegion (sp + 432#64) 8 ∗ memRegion (sp + 440#64) 8 from
        memRegion_split' (b' := sp + 440#64) (n := 8) (k := 8) rfl (by bv_omega) (by decide)]
  refine memRegion128_cells (sp + 176#64) (by sep_focus)
    fun c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 => ?_
  refine memRegion128_cells (sp + 304#64) (by sep_focus)
    fun d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 => ?_
  refine SepWP.memRegion8_cell (sp + 432#64) fun e0 => ?_
  refine SepWP.memRegion8_cell (sp + 440#64) fun e1 => ?_
  refine memRegion128_cells (sp + 448#64) (by sep_focus)
    fun f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 => ?_
  unfold Loop1SpillMem
  wp_steps 18
  apply SepWP.done
  · rw [← bne_k_target_eq hk hn]; wp_norm_lhs
  · wp_norm_lhs
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact AbsorbRegsPreserved.trans hpres12
      ⟨by rw [hsp2]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by wp_norm_lhs, by rw [hx23_2]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  · exact spAligned_of_sp_eq (by rw [hsp2]; wp_norm_lhs) halign2
  · reg64_lhs
    exact add1_eq_ofNat k
  · refine entails_sub (Rest := (rcBase ↦ᵣ mlkemData01Bytes) ∗ Keccak2Mem (sp + 176#64) out0 out1 ∗ F)
      (loop1SpillMem_entails_memRegion sp out0 out1) ?_ (by sep_entail)
    unfold Loop1SpillMem Keccak2Mem Keccak2Rate17Mem Keccak2Rate16Mem
      Keccak2Q0Mem Keccak2Q1Mem Keccak2Q2Mem Keccak2Q3Mem Keccak2Vec16Mem Keccak2Cap8Mem
    rw [← hsp2]
    sep_entail


end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbPermute
