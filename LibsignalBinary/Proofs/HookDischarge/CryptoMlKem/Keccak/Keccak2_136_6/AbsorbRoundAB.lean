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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase
import ProofLib.ProgramReflection
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B02` (`keccak2::<136, 6>`): loop 1 single-round parts A and B (`+0x00f0 → +0x02dc`)

Proof of segment `[0x00f0 → 0x02d8]` of `mlkemBlk02` (`round1_partA` and `round1_partB`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbRoundAB

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState
  keccakRhoOffset
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (keccak2Lane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC
  keccakD
  keccakRhoPi
  keccakRhoPiSrc
  keccakRoundLane
  keccakTheta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Sponge (memRegion128_cells)
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
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.RoundBase (
  AbsorbRegsPreserved
  Loop1MidMem
  Round1MidA
  Round1MidB
  Round1RegsA
  Round1RegsB
  add8_eq_ofNat
  d_comm_eq
  d_dir_eq
  laneD
  laneRhoPi
  laneShlTheta
  laneTheta
  orr_self_64
  rhopi0_of_theta
  rhopi_of_theta
  spAligned_of_sp_eq
  theta_comm_eq
  theta_dir_eq
  writeVReg128_eq_self
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

set_option linter.literalFetch false in
gen_placed_fetches blkPC02 blkLib02 blkTree02 blk02_code_eq blk02_tree_size
  via_placement blkPl02 blkPlaceable02 [0x00f0 → 0x02d8]

attribute [local simp, local arm64_norm, local wp_norm] orr_self_64
attribute [local irreducible] blkPC02 keccakC keccakD keccakTheta keccakRhoPi keccakRoundLane

public section

set_option maxRecDepth 20000 in
theorem round1_partA [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (s : State) (sp rcBase : BitVec 64) (r : Nat) (st0 st1 : KeccakState) (F : SepProp)
    (hpc : s.pc = b + 0x00f0#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (8 * r))
    (hx25 : s.readReg64 .x25 = rcBase)
    (hregs : Loop1Regs s st0 st1) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x01d4#64) s
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ Loop1SpillMem sp st0 st1 ∗ F)
      (Round1MidA s sp rcBase r st0 st1 F) := by
  rcases hregs with ⟨hv9, hv6, hv24, hv16, hv19, hv30, hv7, hv11, hv5, hv22,
    hv18, hv15, hv29, hv23, hv27, hv12, hv3, hv8, hv28, hv17, hv4, hv2⟩
  simp only [keccak2Lane] at hv9 hv6 hv24 hv16 hv19 hv30 hv7 hv11 hv5 hv22 hv18
  simp only [keccak2Lane] at hv15 hv29 hv23 hv27 hv12 hv3 hv8 hv28 hv17 hv4 hv2
  unfold Loop1SpillMem
  generalize ha0 : st0.getD 0 0#64 = a0; generalize hb0 : st1.getD 0 0#64 = b0
  generalize ha1 : st0.getD 1 0#64 = a1; generalize hb1 : st1.getD 1 0#64 = b1
  generalize ha2 : st0.getD 2 0#64 = a2; generalize hb2 : st1.getD 2 0#64 = b2
  generalize ha3 : st0.getD 3 0#64 = a3; generalize hb3 : st1.getD 3 0#64 = b3
  generalize ha4 : st0.getD 4 0#64 = a4; generalize hb4 : st1.getD 4 0#64 = b4
  generalize ha5 : st0.getD 5 0#64 = a5; generalize hb5 : st1.getD 5 0#64 = b5
  generalize ha6 : st0.getD 6 0#64 = a6; generalize hb6 : st1.getD 6 0#64 = b6
  generalize ha7 : st0.getD 7 0#64 = a7; generalize hb7 : st1.getD 7 0#64 = b7
  generalize ha8 : st0.getD 8 0#64 = a8; generalize hb8 : st1.getD 8 0#64 = b8
  generalize ha9 : st0.getD 9 0#64 = a9; generalize hb9 : st1.getD 9 0#64 = b9
  generalize ha10 : st0.getD 10 0#64 = a10; generalize hb10 : st1.getD 10 0#64 = b10
  generalize ha11 : st0.getD 11 0#64 = a11; generalize hb11 : st1.getD 11 0#64 = b11
  generalize ha12 : st0.getD 12 0#64 = a12; generalize hb12 : st1.getD 12 0#64 = b12
  generalize ha13 : st0.getD 13 0#64 = a13; generalize hb13 : st1.getD 13 0#64 = b13
  generalize ha14 : st0.getD 14 0#64 = a14; generalize hb14 : st1.getD 14 0#64 = b14
  generalize ha15 : st0.getD 15 0#64 = a15; generalize hb15 : st1.getD 15 0#64 = b15
  generalize ha16 : st0.getD 16 0#64 = a16; generalize hb16 : st1.getD 16 0#64 = b16
  generalize ha17 : st0.getD 17 0#64 = a17; generalize hb17 : st1.getD 17 0#64 = b17
  generalize ha18 : st0.getD 18 0#64 = a18; generalize hb18 : st1.getD 18 0#64 = b18
  generalize ha19 : st0.getD 19 0#64 = a19; generalize hb19 : st1.getD 19 0#64 = b19
  generalize ha20 : st0.getD 20 0#64 = a20; generalize hb20 : st1.getD 20 0#64 = b20
  generalize ha21 : st0.getD 21 0#64 = a21; generalize hb21 : st1.getD 21 0#64 = b21
  generalize ha22 : st0.getD 22 0#64 = a22; generalize hb22 : st1.getD 22 0#64 = b22
  generalize ha23 : st0.getD 23 0#64 = a23; generalize hb23 : st1.getD 23 0#64 = b23
  generalize ha24 : st0.getD 24 0#64 = a24; generalize hb24 : st1.getD 24 0#64 = b24
  rw [ha0, hb0] at hv9; rw [ha1, hb1] at hv6; rw [ha2, hb2] at hv24; rw [ha3, hb3] at hv16
  rw [ha4, hb4] at hv19; rw [ha5, hb5] at hv30; rw [ha6, hb6] at hv7; rw [ha9, hb9] at hv11
  rw [ha10, hb10] at hv5; rw [ha11, hb11] at hv22; rw [ha12, hb12] at hv18; rw [ha13, hb13] at hv15
  rw [ha15, hb15] at hv29; rw [ha16, hb16] at hv23; rw [ha17, hb17] at hv27; rw [ha18, hb18] at hv12
  rw [ha19, hb19] at hv3; rw [ha20, hb20] at hv8; rw [ha21, hb21] at hv28; rw [ha22, hb22] at hv17
  rw [ha23, hb23] at hv4; rw [ha24, hb24] at hv2
  let s_in :=
    ((((((((((((((((((((((s.writeVReg128 9#5 (b0 ++ a0)).writeVReg128 6#5 (b1 ++ a1)).writeVReg128
      24#5 (b2 ++ a2)).writeVReg128 16#5 (b3 ++ a3)).writeVReg128 19#5 (b4 ++ a4)).writeVReg128
      30#5 (b5 ++ a5)).writeVReg128 7#5 (b6 ++ a6)).writeVReg128 11#5 (b9 ++ a9)).writeVReg128
      5#5 (b10 ++ a10)).writeVReg128 22#5 (b11 ++ a11)).writeVReg128 18#5 (b12 ++ a12)).writeVReg128
      15#5 (b13 ++ a13)).writeVReg128 29#5 (b15 ++ a15)).writeVReg128 23#5 (b16 ++ a16)).writeVReg128
      27#5 (b17 ++ a17)).writeVReg128 12#5 (b18 ++ a18)).writeVReg128 3#5 (b19 ++ a19)).writeVReg128
      8#5 (b20 ++ a20)).writeVReg128 28#5 (b21 ++ a21)).writeVReg128 17#5 (b22 ++ a22)).writeVReg128
      4#5 (b23 ++ a23)).writeVReg128 2#5 (b24 ++ a24))
  have hs_in : s_in = s := by
    dsimp only [s_in]
    rw [writeVReg128_eq_self hv9, writeVReg128_eq_self hv6, writeVReg128_eq_self hv24,
        writeVReg128_eq_self hv16, writeVReg128_eq_self hv19, writeVReg128_eq_self hv30,
        writeVReg128_eq_self hv7, writeVReg128_eq_self hv11, writeVReg128_eq_self hv5,
        writeVReg128_eq_self hv22, writeVReg128_eq_self hv18, writeVReg128_eq_self hv15,
        writeVReg128_eq_self hv29, writeVReg128_eq_self hv23, writeVReg128_eq_self hv27,
        writeVReg128_eq_self hv12, writeVReg128_eq_self hv3, writeVReg128_eq_self hv8,
        writeVReg128_eq_self hv28, writeVReg128_eq_self hv17, writeVReg128_eq_self hv4,
        writeVReg128_eq_self hv2]
  conv => arg 3; rw [← hs_in]
  dsimp only [s_in]
  refine memRegion128_cells sp (by sep_focus)
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 => ?_
  wp_steps 57
  have hd0_0 : ((((a9 ^^^ a4) ^^^ (a14 ^^^ a19)) ^^^ a24) ^^^
      ((((a6 ^^^ a1) ^^^ (a11 ^^^ a16)) ^^^ a21)).rotateLeft 1) = keccakD st0 0 :=
    d_dir_eq st0 0 rfl rfl ha4 ha9 ha14 ha19 ha24 ha1 ha6 ha11 ha16 ha21
  have hd1_0 : ((((b9 ^^^ b4) ^^^ (b14 ^^^ b19)) ^^^ b24) ^^^
      ((((b6 ^^^ b1) ^^^ (b11 ^^^ b16)) ^^^ b21)).rotateLeft 1) = keccakD st1 0 :=
    d_dir_eq st1 0 rfl rfl hb4 hb9 hb14 hb19 hb24 hb1 hb6 hb11 hb16 hb21
  have hd0_1 : (((((a7 ^^^ a2) ^^^ (a12 ^^^ a17)) ^^^ a22)).rotateLeft 1 ^^^
      (((a5 ^^^ a0) ^^^ (a10 ^^^ a15)) ^^^ a20)) = keccakD st0 1 :=
    d_comm_eq st0 1 rfl rfl ha0 ha5 ha10 ha15 ha20 ha2 ha7 ha12 ha17 ha22
  have hd1_1 : (((((b7 ^^^ b2) ^^^ (b12 ^^^ b17)) ^^^ b22)).rotateLeft 1 ^^^
      (((b5 ^^^ b0) ^^^ (b10 ^^^ b15)) ^^^ b20)) = keccakD st1 1 :=
    d_comm_eq st1 1 rfl rfl hb0 hb5 hb10 hb15 hb20 hb2 hb7 hb12 hb17 hb22
  have hd0_2 : (((((a8 ^^^ a3) ^^^ (a13 ^^^ a18)) ^^^ a23)).rotateLeft 1 ^^^
      (((a6 ^^^ a1) ^^^ (a11 ^^^ a16)) ^^^ a21)) = keccakD st0 2 :=
    d_comm_eq st0 2 rfl rfl ha1 ha6 ha11 ha16 ha21 ha3 ha8 ha13 ha18 ha23
  have hd1_2 : (((((b8 ^^^ b3) ^^^ (b13 ^^^ b18)) ^^^ b23)).rotateLeft 1 ^^^
      (((b6 ^^^ b1) ^^^ (b11 ^^^ b16)) ^^^ b21)) = keccakD st1 2 :=
    d_comm_eq st1 2 rfl rfl hb1 hb6 hb11 hb16 hb21 hb3 hb8 hb13 hb18 hb23
  have hd0_3 : (((((a9 ^^^ a4) ^^^ (a14 ^^^ a19)) ^^^ a24)).rotateLeft 1 ^^^
      (((a7 ^^^ a2) ^^^ (a12 ^^^ a17)) ^^^ a22)) = keccakD st0 3 :=
    d_comm_eq st0 3 rfl rfl ha2 ha7 ha12 ha17 ha22 ha4 ha9 ha14 ha19 ha24
  have hd1_3 : (((((b9 ^^^ b4) ^^^ (b14 ^^^ b19)) ^^^ b24)).rotateLeft 1 ^^^
      (((b7 ^^^ b2) ^^^ (b12 ^^^ b17)) ^^^ b22)) = keccakD st1 3 :=
    d_comm_eq st1 3 rfl rfl hb2 hb7 hb12 hb17 hb22 hb4 hb9 hb14 hb19 hb24
  have hd0_4 : ((((a8 ^^^ a3) ^^^ (a13 ^^^ a18)) ^^^ a23) ^^^
      ((((a5 ^^^ a0) ^^^ (a10 ^^^ a15)) ^^^ a20)).rotateLeft 1) = keccakD st0 4 :=
    d_dir_eq st0 4 rfl rfl ha3 ha8 ha13 ha18 ha23 ha0 ha5 ha10 ha15 ha20
  have hd1_4 : ((((b8 ^^^ b3) ^^^ (b13 ^^^ b18)) ^^^ b23) ^^^
      ((((b5 ^^^ b0) ^^^ (b10 ^^^ b15)) ^^^ b20)).rotateLeft 1) = keccakD st1 4 :=
    d_dir_eq st1 4 rfl rfl hb3 hb8 hb13 hb18 hb23 hb0 hb5 hb10 hb15 hb20
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hsp]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by rw [hx25]; wp_norm_lhs, by wp_norm_lhs⟩
  · wp_norm_lhs
  · exact spAligned_of_sp_eq (by rw [hsp]; wp_norm_lhs) hsp_align
  · rw [← add8_eq_ofNat]; wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · dsimp only [Round1RegsA, keccak2Lane, laneTheta, laneD, laneShlTheta]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha11, hb11]; vreg_lhs
    · rw [← theta_comm_eq st0 5 hd0_0 ha5, ← theta_comm_eq st1 5 hd1_0 hb5]; vreg_lhs
    · rw [← theta_comm_eq st0 10 hd0_0 ha10, ← theta_comm_eq st1 10 hd1_0 hb10]; vreg_lhs
    · rw [← theta_comm_eq st0 15 hd0_0 ha15, ← theta_comm_eq st1 15 hd1_0 hb15]; vreg_lhs
    · rw [← theta_comm_eq st0 1 hd0_1 ha1, ← theta_comm_eq st1 1 hd1_1 hb1]; vreg_lhs
    · rw [← theta_comm_eq st0 6 hd0_1 ha6, ← theta_comm_eq st1 6 hd1_1 hb6]; vreg_lhs
    · rw [← theta_comm_eq st0 5 hd0_0 ha5, ← theta_comm_eq st1 5 hd1_0 hb5]; vreg_lhs
    · rw [ha0, hb0]; vreg_lhs
    · rw [← theta_comm_eq st0 10 hd0_0 ha10, ← theta_comm_eq st1 10 hd1_0 hb10]; vreg_lhs
    · rw [← theta_comm_eq st0 20 hd0_0 ha20, ← theta_comm_eq st1 20 hd1_0 hb20]; vreg_lhs
    · rw [← hd0_0, ← hd1_0]; vreg_lhs
    · rw [← hd0_1, ← hd1_1]; vreg_lhs
    · rw [← hd0_2, ← hd1_2]; vreg_lhs
    · rw [ha3, hb3]; vreg_lhs
    · rw [ha22, hb22]; vreg_lhs
    · rw [ha12, hb12]; vreg_lhs
    · rw [ha17, hb17]; vreg_lhs
    · rw [ha7, hb7]; vreg_lhs
    · rw [ha16, hb16]; vreg_lhs
    · rw [← hd0_4, ← hd1_4]; vreg_lhs
    · rw [ha2, hb2]; vreg_lhs
    · rw [ha21, hb21]; vreg_lhs
    · rw [← hd0_3, ← hd1_3]; vreg_lhs
  · unfold Loop1MidMem
    rw [ha11, hb11, ha23, hb23, ha24, hb24, ha13, hb13,
        ha19, hb19, ha18, hb18, ha9, hb9, ha4, hb4,
        ha7, hb7, ha8, hb8, ha14, hb14, ← hsp]
    sep_entail

set_option maxRecDepth 20000 in
theorem round1_partB [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl02 b) (_hbase : blkPl02.base = b)
    (s0 sm : State) (sp rcBase : BitVec 64) (r : Nat) (st0 st1 : KeccakState)
    (F Pm : SepProp)
    (hpc : sm.pc = b + 0x01d4#64)
    (hrun : sm.status = .Running)
    (hsp0 : s0.sp = sp)
    (hmid : Round1MidA s0 sp rcBase r st0 st1 F sm Pm) :
    SepWP (blkPC02.rebase b (fun _ => none)) (b + 0x02dc#64) sm Pm
      (Round1MidB s0 sp rcBase r st0 st1 F) := by
  rcases hmid with ⟨hpres, hx24, hsp_align, hx8, hx9, hz, hregs, hmem⟩
  have hsp : sm.sp = sp := hpres.1.trans hsp0
  refine SepWP.weaken_pre hmem ?_
  rcases hregs with ⟨hv0, hv2, hv4, hv5, hv6, hv7, hv8, hv9, hv11, hv12,
    hv13, hv14, hv15, hv16, hv17, hv18, hv21, hv22, hv23, hv25, hv26, hv28, hv30⟩
  simp only [keccak2Lane, laneTheta, laneD, laneShlTheta] at hv0 hv2 hv4 hv5 hv6 hv7 hv8 hv9 hv11 hv12 hv13 hv14
  simp only [keccak2Lane, laneD] at hv15 hv16 hv17 hv18 hv21 hv22 hv23 hv25 hv26 hv28 hv30
  unfold Loop1MidMem
  generalize ha0 : st0.getD 0 0#64 = a0; generalize hb0 : st1.getD 0 0#64 = b0
  generalize ha2 : st0.getD 2 0#64 = a2; generalize hb2 : st1.getD 2 0#64 = b2
  generalize ha3 : st0.getD 3 0#64 = a3; generalize hb3 : st1.getD 3 0#64 = b3
  generalize ha4 : st0.getD 4 0#64 = a4; generalize hb4 : st1.getD 4 0#64 = b4
  generalize ha7 : st0.getD 7 0#64 = a7; generalize hb7 : st1.getD 7 0#64 = b7
  generalize ha8 : st0.getD 8 0#64 = a8; generalize hb8 : st1.getD 8 0#64 = b8
  generalize ha9 : st0.getD 9 0#64 = a9; generalize hb9 : st1.getD 9 0#64 = b9
  generalize ha11 : st0.getD 11 0#64 = a11; generalize hb11 : st1.getD 11 0#64 = b11
  generalize ha12 : st0.getD 12 0#64 = a12; generalize hb12 : st1.getD 12 0#64 = b12
  generalize ha13 : st0.getD 13 0#64 = a13; generalize hb13 : st1.getD 13 0#64 = b13
  generalize ha14 : st0.getD 14 0#64 = a14; generalize hb14 : st1.getD 14 0#64 = b14
  generalize ha16 : st0.getD 16 0#64 = a16; generalize hb16 : st1.getD 16 0#64 = b16
  generalize ha17 : st0.getD 17 0#64 = a17; generalize hb17 : st1.getD 17 0#64 = b17
  generalize ha18 : st0.getD 18 0#64 = a18; generalize hb18 : st1.getD 18 0#64 = b18
  generalize ha19 : st0.getD 19 0#64 = a19; generalize hb19 : st1.getD 19 0#64 = b19
  generalize ha21 : st0.getD 21 0#64 = a21; generalize hb21 : st1.getD 21 0#64 = b21
  generalize ha22 : st0.getD 22 0#64 = a22; generalize hb22 : st1.getD 22 0#64 = b22
  generalize ha23 : st0.getD 23 0#64 = a23; generalize hb23 : st1.getD 23 0#64 = b23
  generalize ha24 : st0.getD 24 0#64 = a24; generalize hb24 : st1.getD 24 0#64 = b24
  generalize ht0_1 : keccakTheta st0 1 = t0_1; generalize ht1_1 : keccakTheta st1 1 = t1_1
  generalize ht0_5 : keccakTheta st0 5 = t0_5; generalize ht1_5 : keccakTheta st1 5 = t1_5
  generalize ht0_6 : keccakTheta st0 6 = t0_6; generalize ht1_6 : keccakTheta st1 6 = t1_6
  generalize ht0_10 : keccakTheta st0 10 = t0_10; generalize ht1_10 : keccakTheta st1 10 = t1_10
  generalize ht0_15 : keccakTheta st0 15 = t0_15; generalize ht1_15 : keccakTheta st1 15 = t1_15
  generalize ht0_20 : keccakTheta st0 20 = t0_20; generalize ht1_20 : keccakTheta st1 20 = t1_20
  generalize hd0_0 : keccakD st0 0 = d0_0; generalize hd1_0 : keccakD st1 0 = d1_0
  generalize hd0_1 : keccakD st0 1 = d0_1; generalize hd1_1 : keccakD st1 1 = d1_1
  generalize hd0_2 : keccakD st0 2 = d0_2; generalize hd1_2 : keccakD st1 2 = d1_2
  generalize hd0_3 : keccakD st0 3 = d0_3; generalize hd1_3 : keccakD st1 3 = d1_3
  generalize hd0_4 : keccakD st0 4 = d0_4; generalize hd1_4 : keccakD st1 4 = d1_4
  rw [ha11, hb11] at hv0; rw [ht0_5, ht1_5] at hv2 hv8; rw [ht0_10, ht1_10] at hv4 hv11
  rw [ht0_15, ht1_15] at hv5; rw [ht0_1, ht1_1] at hv6; rw [ht0_6, ht1_6] at hv7
  rw [ha0, hb0] at hv9; rw [ht0_20, ht1_20] at hv12; rw [hd0_0, hd1_0] at hv13
  rw [hd0_1, hd1_1] at hv14; rw [hd0_2, hd1_2] at hv15; rw [ha3, hb3] at hv16
  rw [ha22, hb22] at hv17; rw [ha12, hb12] at hv18; rw [ha17, hb17] at hv21
  rw [ha7, hb7] at hv22; rw [ha16, hb16] at hv23; rw [hd0_4, hd1_4] at hv25
  rw [ha2, hb2] at hv26; rw [ha21, hb21] at hv28; rw [hd0_3, hd1_3] at hv30
  let s_in :=
    (((((((((((((((((((((((sm.writeVReg128 0#5 (b11 ++ a11)).writeVReg128
      2#5 (t1_5 ++ t0_5)).writeVReg128 4#5 (t1_10 ++ t0_10)).writeVReg128
      5#5 (t1_15 ++ t0_15)).writeVReg128 6#5 (t1_1 ++ t0_1)).writeVReg128
      7#5 (t1_6 ++ t0_6)).writeVReg128 8#5 ((t1_5 <<< 36) ++ (t0_5 <<< 36))).writeVReg128
      9#5 (b0 ++ a0)).writeVReg128 11#5 ((t1_10 <<< 3) ++ (t0_10 <<< 3))).writeVReg128
      12#5 (t1_20 ++ t0_20)).writeVReg128 13#5 (d1_0 ++ d0_0)).writeVReg128
      14#5 (d1_1 ++ d0_1)).writeVReg128 15#5 (d1_2 ++ d0_2)).writeVReg128
      16#5 (b3 ++ a3)).writeVReg128 17#5 (b22 ++ a22)).writeVReg128
      18#5 (b12 ++ a12)).writeVReg128 21#5 (b17 ++ a17)).writeVReg128
      22#5 (b7 ++ a7)).writeVReg128 23#5 (b16 ++ a16)).writeVReg128
      25#5 (d1_4 ++ d0_4)).writeVReg128 26#5 (b2 ++ a2)).writeVReg128
      28#5 (b21 ++ a21)).writeVReg128 30#5 (d1_3 ++ d0_3))
  have hs_in : s_in = sm := by
    dsimp only [s_in]
    rw [writeVReg128_eq_self hv0, writeVReg128_eq_self hv2, writeVReg128_eq_self hv4,
        writeVReg128_eq_self hv5, writeVReg128_eq_self hv6, writeVReg128_eq_self hv7,
        writeVReg128_eq_self hv8, writeVReg128_eq_self hv9, writeVReg128_eq_self hv11,
        writeVReg128_eq_self hv12, writeVReg128_eq_self hv13, writeVReg128_eq_self hv14,
        writeVReg128_eq_self hv15, writeVReg128_eq_self hv16, writeVReg128_eq_self hv17,
        writeVReg128_eq_self hv18, writeVReg128_eq_self hv21, writeVReg128_eq_self hv22,
        writeVReg128_eq_self hv23, writeVReg128_eq_self hv25, writeVReg128_eq_self hv26,
        writeVReg128_eq_self hv28, writeVReg128_eq_self hv30]
  conv => arg 3; rw [← hs_in]
  dsimp only [s_in]
  wp_steps 66
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact AbsorbRegsPreserved.trans hpres
      ⟨by rw [hsp]; wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
       by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  · wp_norm_lhs
  · exact spAligned_of_sp_eq (by rw [hsp]; wp_norm_lhs) hsp_align
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · dsimp only [Round1RegsB, laneTheta, laneRhoPi, laneShlTheta]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← theta_comm_eq st0 9 hd0_4.symm ha9, ← theta_comm_eq st1 9 hd1_4.symm hb9]; vreg_lhs
    · rw [← theta_comm_eq st0 4 hd0_4.symm ha4, ← theta_comm_eq st1 4 hd1_4.symm hb4]; vreg_lhs
    · rw [← rhopi_of_theta st0 21 8 55 rfl rfl (theta_comm_eq st0 8 hd0_3.symm ha8),
          ← rhopi_of_theta st1 21 8 55 rfl rfl (theta_comm_eq st1 8 hd1_3.symm hb8)]; vreg_lhs
    · rw [← theta_comm_eq st0 9 hd0_4.symm ha9, ← theta_comm_eq st1 9 hd1_4.symm hb9]; vreg_lhs
    · rw [← rhopi_of_theta st0 16 5 36 rfl rfl ht0_5.symm,
          ← rhopi_of_theta st1 16 5 36 rfl rfl ht1_5.symm]; vreg_lhs
    · rw [← rhopi0_of_theta st0 (theta_comm_eq st0 0 hd0_0.symm ha0),
          ← rhopi0_of_theta st1 (theta_comm_eq st1 0 hd1_0.symm hb0)]; vreg_lhs
    · rw [← rhopi_of_theta st0 24 21 2 rfl rfl (theta_comm_eq st0 21 hd0_1.symm ha21),
          ← rhopi_of_theta st1 24 21 2 rfl rfl (theta_comm_eq st1 21 hd1_1.symm hb21)]; vreg_lhs
    · rw [← rhopi_of_theta st0 7 10 3 rfl rfl ht0_10.symm,
          ← rhopi_of_theta st1 7 10 3 rfl rfl ht1_10.symm]; vreg_lhs
    · rw [← rhopi_of_theta st0 18 17 15 rfl rfl (theta_comm_eq st0 17 hd0_2.symm ha17),
          ← rhopi_of_theta st1 18 17 15 rfl rfl (theta_comm_eq st1 17 hd1_2.symm hb17)]; vreg_lhs
    · rw [← rhopi_of_theta st0 4 24 14 rfl rfl (theta_dir_eq st0 24 hd0_4.symm ha24),
          ← rhopi_of_theta st1 4 24 14 rfl rfl (theta_dir_eq st1 24 hd1_4.symm hb24)]; vreg_lhs
    · rw [← rhopi_of_theta st0 12 13 25 rfl rfl (theta_comm_eq st0 13 hd0_3.symm ha13),
          ← rhopi_of_theta st1 12 13 25 rfl rfl (theta_comm_eq st1 13 hd1_3.symm hb13)]; vreg_lhs
    · rw [← rhopi_of_theta st0 2 12 43 rfl rfl (theta_comm_eq st0 12 hd0_2.symm ha12),
          ← rhopi_of_theta st1 2 12 43 rfl rfl (theta_comm_eq st1 12 hd1_2.symm hb12)]; vreg_lhs
    · rw [← rhopi_of_theta st0 19 23 56 rfl rfl (theta_comm_eq st0 23 hd0_3.symm ha23),
          ← rhopi_of_theta st1 19 23 56 rfl rfl (theta_comm_eq st1 23 hd1_3.symm hb23)]; vreg_lhs
    · rw [← rhopi_of_theta st0 11 7 6 rfl rfl (theta_comm_eq st0 7 hd0_2.symm ha7),
          ← rhopi_of_theta st1 11 7 6 rfl rfl (theta_comm_eq st1 7 hd1_2.symm hb7)]; vreg_lhs
    · rw [← rhopi_of_theta st0 3 18 21 rfl rfl (theta_comm_eq st0 18 hd0_3.symm ha18),
          ← rhopi_of_theta st1 3 18 21 rfl rfl (theta_comm_eq st1 18 hd1_3.symm hb18)]; vreg_lhs
    · rw [← rhopi_of_theta st0 8 16 45 rfl rfl (theta_comm_eq st0 16 hd0_1.symm ha16),
          ← rhopi_of_theta st1 8 16 45 rfl rfl (theta_comm_eq st1 16 hd1_1.symm hb16)]; vreg_lhs
    · rw [← theta_comm_eq st0 4 hd0_4.symm ha4, ← theta_comm_eq st1 4 hd1_4.symm hb4]; vreg_lhs
    · rw [← rhopi_of_theta st0 9 22 61 rfl rfl (theta_comm_eq st0 22 hd0_2.symm ha22),
          ← rhopi_of_theta st1 9 22 61 rfl rfl (theta_comm_eq st1 22 hd1_2.symm hb22)]; vreg_lhs
    · rw [← rhopi_of_theta st0 5 3 28 rfl rfl (theta_comm_eq st0 3 hd0_3.symm ha3),
          ← rhopi_of_theta st1 5 3 28 rfl rfl (theta_comm_eq st1 3 hd1_3.symm hb3)]; vreg_lhs
    · rw [← rhopi_of_theta st0 1 6 44 rfl rfl ht0_6.symm,
          ← rhopi_of_theta st1 1 6 44 rfl rfl ht1_6.symm]; vreg_lhs
    · rw [← theta_dir_eq st0 19 hd0_4.symm ha19, ← theta_dir_eq st1 19 hd1_4.symm hb19]; vreg_lhs
    · rw [← rhopi_of_theta st0 20 2 62 rfl rfl (theta_comm_eq st0 2 hd0_2.symm ha2),
          ← rhopi_of_theta st1 20 2 62 rfl rfl (theta_comm_eq st1 2 hd1_2.symm hb2)]; vreg_lhs
    · rw [← rhopi_of_theta st0 10 1 1 rfl rfl ht0_1.symm,
          ← rhopi_of_theta st1 10 1 1 rfl rfl ht1_1.symm]; vreg_lhs
    · rw [← rhopi_of_theta st0 17 11 10 rfl rfl (theta_comm_eq st0 11 hd0_1.symm ha11),
          ← rhopi_of_theta st1 17 11 10 rfl rfl (theta_comm_eq st1 11 hd1_1.symm hb11)]; vreg_lhs
    · rw [← rhopi_of_theta st0 14 20 18 rfl rfl ht0_20.symm,
          ← rhopi_of_theta st1 14 20 18 rfl rfl ht1_20.symm]; vreg_lhs
    · rw [← theta_comm_eq st0 14 hd0_4.symm ha14, ← theta_comm_eq st1 14 hd1_4.symm hb14]; vreg_lhs
    · rw [← rhopi_of_theta st0 23 15 41 rfl rfl ht0_15.symm,
          ← rhopi_of_theta st1 23 15 41 rfl rfl ht1_15.symm]; vreg_lhs
  · unfold Loop1MidMem
    rw [ha11, hb11, ha23, hb23, ha24, hb24, ha13, hb13,
        ha19, hb19, ha18, hb18, ha9, hb9, ha4, hb4,
        ha7, hb7, ha8, hb8, ha14, hb14]
    sep_entail


end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6.AbsorbRoundAB
