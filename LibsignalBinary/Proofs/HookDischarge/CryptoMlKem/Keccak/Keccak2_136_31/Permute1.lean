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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base
import ProofLib.ProgramReflection
import ProofLib.GenDecodes
import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round
meta import ProofLib
meta import ProofLib.ProgramReflection
meta import ProofLib.GenDecodes
meta import ProofLib.GenPlacedFetches

/-!
# `B01` (`keccak2::<136, 31>`): first 24-round `keccak_f1600` loop

Proof of segment `[0x00f8 → 0x03e8]` of `mlkemBlk01`, stepping the first 24-round 2-way NEON
`keccak_f1600` loop (`+0x00f8 → +0x03ec`) cut at `Theta` (`+0x01cc`), `RhoPi` (`+0x02e4`), and
`ChiIota` (`+0x03e8`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute1

open Arm64 ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemData01Bytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (keccakRcAt mlkemData01Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1r_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  KeccakState keccakF1600 keccakF1600Round
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Defs (keccak2Lane)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Round (
  keccakC keccakD keccakRhoPi keccakRunFrom keccakRunFrom_24 keccakRunFrom_step
  keccakRunFrom_zero keccakTheta
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Base (
  Spill11 blk01_code_eq blk01_tree_size blkLib01 blkPC01 blkPl01 blkPlaceable01 blkTree01
  bv64_8mul_add8 cmp192_ne_of_lt keccakC_fold_0 keccakC_fold_1 keccakC_fold_2 keccakC_fold_3
  keccakC_fold_4 keccakChi0_fold keccakChi_fold keccakD_fold_0 keccakD_fold_1 keccakD_fold_2
  keccakD_fold_3 keccakD_fold_4 keccakRhoPi_fold keccakRhoPi_fold_0
  keccakTheta_fold_l keccakTheta_fold_r
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp (
  extractLsb_hi_append extractLsb_lo_append
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp

section
set_option linter.literalFetch false
gen_placed_fetches blkPC01 blkLib01 blkTree01 blk01_code_eq blk01_tree_size
  via_placement blkPl01 blkPlaceable01 [0x00f8 → 0x03e8]
end

public section

/-! ## Preserved scalar registers, round-head SIMD invariant, and folding equations -/

/-- Scalar registers (`sp, x19..x25, x27, fp`) preserved across `+0x00b8 → +0x0430`. -/
@[expose] def P1Scalars (s sf : State) : Prop :=
  sf.sp = s.sp ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
  sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
  sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
  sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
  sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .fp = s.readReg64 .fp

theorem P1Scalars.refl (s : State) : P1Scalars s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem P1Scalars.spAligned {s sf : State} (h : P1Scalars s sf) (ha : s.spAligned = true) :
    sf.spAligned = true := by
  simp only [State.spAligned, h.1]; exact ha

theorem P1Scalars.trans {s1 s2 s3 : State}
    (h12 : P1Scalars s1 s2) (h23 : P1Scalars s2 s3) : P1Scalars s1 s3 :=
  ⟨h23.1.trans h12.1, h23.2.1.trans h12.2.1, h23.2.2.1.trans h12.2.2.1,
   h23.2.2.2.1.trans h12.2.2.2.1, h23.2.2.2.2.1.trans h12.2.2.2.2.1,
   h23.2.2.2.2.2.1.trans h12.2.2.2.2.2.1, h23.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.1.trans h12.2.2.2.2.2.2.2.2.1,
   h23.2.2.2.2.2.2.2.2.2.trans h12.2.2.2.2.2.2.2.2.2⟩

theorem P1Scalars.setPC {s sf : State} (pc' : BitVec 64) (h : P1Scalars s sf) :
    P1Scalars s (sf.setPC pc') := h

/-- 22 SIMD registers holding lanes at `+0x00f8` (and `+0x03e8` / `+0x03ec`). -/
@[expose] def P1RoundRegs (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 2#5 = keccak2Lane st0 st1 24 ∧ s.readVReg128 3#5 = keccak2Lane st0 st1 19 ∧
  s.readVReg128 4#5 = keccak2Lane st0 st1 23 ∧ s.readVReg128 5#5 = keccak2Lane st0 st1 10 ∧
  s.readVReg128 6#5 = keccak2Lane st0 st1 1 ∧ s.readVReg128 7#5 = keccak2Lane st0 st1 6 ∧
  s.readVReg128 8#5 = keccak2Lane st0 st1 20 ∧ s.readVReg128 9#5 = keccak2Lane st0 st1 0 ∧
  s.readVReg128 11#5 = keccak2Lane st0 st1 9 ∧ s.readVReg128 12#5 = keccak2Lane st0 st1 18 ∧
  s.readVReg128 15#5 = keccak2Lane st0 st1 13 ∧ s.readVReg128 16#5 = keccak2Lane st0 st1 3 ∧
  s.readVReg128 17#5 = keccak2Lane st0 st1 22 ∧ s.readVReg128 18#5 = keccak2Lane st0 st1 12 ∧
  s.readVReg128 19#5 = keccak2Lane st0 st1 4 ∧ s.readVReg128 22#5 = keccak2Lane st0 st1 11 ∧
  s.readVReg128 23#5 = keccak2Lane st0 st1 16 ∧ s.readVReg128 24#5 = keccak2Lane st0 st1 2 ∧
  s.readVReg128 27#5 = keccak2Lane st0 st1 17 ∧ s.readVReg128 28#5 = keccak2Lane st0 st1 21 ∧
  s.readVReg128 29#5 = keccak2Lane st0 st1 15 ∧ s.readVReg128 30#5 = keccak2Lane st0 st1 5

private theorem p1RoundRegs_setPC {s : State} {st0 st1 : KeccakState} (pc' : BitVec 64)
    (h : P1RoundRegs s st0 st1) : P1RoundRegs (s.setPC pc') st0 st1 := h
private theorem setPC_pc (s : State) (pc' : BitVec 64) : (s.setPC pc').pc = pc' := by cases s; rfl
private theorem setPC_status {s : State} (pc' : BitVec 64) (h : s.status = .Running) : (s.setPC pc').status = .Running := by cases s; exact h
private theorem setPC_sp {s : State} {v : BitVec 64} (pc' : BitVec 64) (h : s.sp = v) : (s.setPC pc').sp = v := by cases s; exact h
private theorem setPC_spAligned {s : State} (pc' : BitVec 64) (h : s.spAligned = true) : (s.setPC pc').spAligned = true := by cases s; exact h
private theorem setPC_readReg64 {s : State} {r : Reg} {v : BitVec 64} (pc' : BitVec 64) (h : s.readReg64 r = v) : (s.setPC pc').readReg64 r = v := by cases s; exact h

private theorem theta_l_0 (s : KeccakState) : keccakD s 0 ^^^ s.getD 0 0#64 = keccakTheta s 0 := keccakTheta_fold_l s 0 0
private theorem theta_l_1 (s : KeccakState) : keccakD s 1 ^^^ s.getD 1 0#64 = keccakTheta s 1 := keccakTheta_fold_l s 1 1
private theorem theta_l_2 (s : KeccakState) : keccakD s 2 ^^^ s.getD 2 0#64 = keccakTheta s 2 := keccakTheta_fold_l s 2 2
private theorem theta_l_3 (s : KeccakState) : keccakD s 3 ^^^ s.getD 3 0#64 = keccakTheta s 3 := keccakTheta_fold_l s 3 3
private theorem theta_l_4 (s : KeccakState) : keccakD s 4 ^^^ s.getD 4 0#64 = keccakTheta s 4 := keccakTheta_fold_l s 4 4
private theorem theta_l_5 (s : KeccakState) : keccakD s 0 ^^^ s.getD 5 0#64 = keccakTheta s 5 := keccakTheta_fold_l s 0 5
private theorem theta_l_6 (s : KeccakState) : keccakD s 1 ^^^ s.getD 6 0#64 = keccakTheta s 6 := keccakTheta_fold_l s 1 6
private theorem theta_l_7 (s : KeccakState) : keccakD s 2 ^^^ s.getD 7 0#64 = keccakTheta s 7 := keccakTheta_fold_l s 2 7
private theorem theta_l_8 (s : KeccakState) : keccakD s 3 ^^^ s.getD 8 0#64 = keccakTheta s 8 := keccakTheta_fold_l s 3 8
private theorem theta_l_9 (s : KeccakState) : keccakD s 4 ^^^ s.getD 9 0#64 = keccakTheta s 9 := keccakTheta_fold_l s 4 9
private theorem theta_l_10 (s : KeccakState) : keccakD s 0 ^^^ s.getD 10 0#64 = keccakTheta s 10 := keccakTheta_fold_l s 0 10
private theorem theta_l_11 (s : KeccakState) : keccakD s 1 ^^^ s.getD 11 0#64 = keccakTheta s 11 := keccakTheta_fold_l s 1 11
private theorem theta_l_12 (s : KeccakState) : keccakD s 2 ^^^ s.getD 12 0#64 = keccakTheta s 12 := keccakTheta_fold_l s 2 12
private theorem theta_l_13 (s : KeccakState) : keccakD s 3 ^^^ s.getD 13 0#64 = keccakTheta s 13 := keccakTheta_fold_l s 3 13
private theorem theta_l_14 (s : KeccakState) : keccakD s 4 ^^^ s.getD 14 0#64 = keccakTheta s 14 := keccakTheta_fold_l s 4 14
private theorem theta_l_15 (s : KeccakState) : keccakD s 0 ^^^ s.getD 15 0#64 = keccakTheta s 15 := keccakTheta_fold_l s 0 15
private theorem theta_l_16 (s : KeccakState) : keccakD s 1 ^^^ s.getD 16 0#64 = keccakTheta s 16 := keccakTheta_fold_l s 1 16
private theorem theta_l_17 (s : KeccakState) : keccakD s 2 ^^^ s.getD 17 0#64 = keccakTheta s 17 := keccakTheta_fold_l s 2 17
private theorem theta_l_18 (s : KeccakState) : keccakD s 3 ^^^ s.getD 18 0#64 = keccakTheta s 18 := keccakTheta_fold_l s 3 18
private theorem theta_l_20 (s : KeccakState) : keccakD s 0 ^^^ s.getD 20 0#64 = keccakTheta s 20 := keccakTheta_fold_l s 0 20
private theorem theta_l_21 (s : KeccakState) : keccakD s 1 ^^^ s.getD 21 0#64 = keccakTheta s 21 := keccakTheta_fold_l s 1 21
private theorem theta_l_22 (s : KeccakState) : keccakD s 2 ^^^ s.getD 22 0#64 = keccakTheta s 22 := keccakTheta_fold_l s 2 22
private theorem theta_l_23 (s : KeccakState) : keccakD s 3 ^^^ s.getD 23 0#64 = keccakTheta s 23 := keccakTheta_fold_l s 3 23
private theorem theta_r_19 (s : KeccakState) : s.getD 19 0#64 ^^^ keccakD s 4 = keccakTheta s 19 := keccakTheta_fold_r s 4 19
private theorem theta_r_24 (s : KeccakState) : s.getD 24 0#64 ^^^ keccakD s 4 = keccakTheta s 24 := keccakTheta_fold_r s 4 24
private theorem rhopi_1 (s : KeccakState) : (keccakTheta s 6).rotateLeft 44 = keccakRhoPi s 1 := keccakRhoPi_fold s 6 44 1
private theorem rhopi_2 (s : KeccakState) : (keccakTheta s 12).rotateLeft 43 = keccakRhoPi s 2 := keccakRhoPi_fold s 12 43 2
private theorem rhopi_3 (s : KeccakState) : (keccakTheta s 18).rotateLeft 21 = keccakRhoPi s 3 := keccakRhoPi_fold s 18 21 3
private theorem rhopi_4 (s : KeccakState) : (keccakTheta s 24).rotateLeft 14 = keccakRhoPi s 4 := keccakRhoPi_fold s 24 14 4
private theorem rhopi_5 (s : KeccakState) : (keccakTheta s 3).rotateLeft 28 = keccakRhoPi s 5 := keccakRhoPi_fold s 3 28 5
private theorem rhopi_6 (s : KeccakState) : (keccakTheta s 9).rotateLeft 20 = keccakRhoPi s 6 := keccakRhoPi_fold s 9 20 6
private theorem rhopi_7 (s : KeccakState) : (keccakTheta s 10).rotateLeft 3 = keccakRhoPi s 7 := keccakRhoPi_fold s 10 3 7
private theorem rhopi_8 (s : KeccakState) : (keccakTheta s 16).rotateLeft 45 = keccakRhoPi s 8 := keccakRhoPi_fold s 16 45 8
private theorem rhopi_9 (s : KeccakState) : (keccakTheta s 22).rotateLeft 61 = keccakRhoPi s 9 := keccakRhoPi_fold s 22 61 9
private theorem rhopi_10 (s : KeccakState) : (keccakTheta s 1).rotateLeft 1 = keccakRhoPi s 10 := keccakRhoPi_fold s 1 1 10
private theorem rhopi_11 (s : KeccakState) : (keccakTheta s 7).rotateLeft 6 = keccakRhoPi s 11 := keccakRhoPi_fold s 7 6 11
private theorem rhopi_12 (s : KeccakState) : (keccakTheta s 13).rotateLeft 25 = keccakRhoPi s 12 := keccakRhoPi_fold s 13 25 12
private theorem rhopi_13 (s : KeccakState) : (keccakTheta s 19).rotateLeft 8 = keccakRhoPi s 13 := keccakRhoPi_fold s 19 8 13
private theorem rhopi_14 (s : KeccakState) : (keccakTheta s 20).rotateLeft 18 = keccakRhoPi s 14 := keccakRhoPi_fold s 20 18 14
private theorem rhopi_15 (s : KeccakState) : (keccakTheta s 4).rotateLeft 27 = keccakRhoPi s 15 := keccakRhoPi_fold s 4 27 15
private theorem rhopi_16 (s : KeccakState) : (keccakTheta s 5).rotateLeft 36 = keccakRhoPi s 16 := keccakRhoPi_fold s 5 36 16
private theorem rhopi_17 (s : KeccakState) : (keccakTheta s 11).rotateLeft 10 = keccakRhoPi s 17 := keccakRhoPi_fold s 11 10 17
private theorem rhopi_18 (s : KeccakState) : (keccakTheta s 17).rotateLeft 15 = keccakRhoPi s 18 := keccakRhoPi_fold s 17 15 18
private theorem rhopi_19 (s : KeccakState) : (keccakTheta s 23).rotateLeft 56 = keccakRhoPi s 19 := keccakRhoPi_fold s 23 56 19
private theorem rhopi_20 (s : KeccakState) : (keccakTheta s 2).rotateLeft 62 = keccakRhoPi s 20 := keccakRhoPi_fold s 2 62 20
private theorem rhopi_21 (s : KeccakState) : (keccakTheta s 8).rotateLeft 55 = keccakRhoPi s 21 := keccakRhoPi_fold s 8 55 21
private theorem rhopi_22 (s : KeccakState) : (keccakTheta s 14).rotateLeft 39 = keccakRhoPi s 22 := keccakRhoPi_fold s 14 39 22
private theorem rhopi_23 (s : KeccakState) : (keccakTheta s 15).rotateLeft 41 = keccakRhoPi s 23 := keccakRhoPi_fold s 15 41 23
private theorem rhopi_24 (s : KeccakState) : (keccakTheta s 21).rotateLeft 2 = keccakRhoPi s 24 := keccakRhoPi_fold s 21 2 24
private theorem chi_1 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 2) &&& keccakRhoPi s 3) ^^^ keccakRhoPi s 1 = (keccakF1600Round s rc).getD 1 0#64 := keccakChi_fold s rc 2 3 1 1
private theorem chi_2 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 3) &&& keccakRhoPi s 4) ^^^ keccakRhoPi s 2 = (keccakF1600Round s rc).getD 2 0#64 := keccakChi_fold s rc 3 4 2 2
private theorem chi_3 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 4) &&& keccakRhoPi s 0) ^^^ keccakRhoPi s 3 = (keccakF1600Round s rc).getD 3 0#64 := keccakChi_fold s rc 4 0 3 3
private theorem chi_4 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 0) &&& keccakRhoPi s 1) ^^^ keccakRhoPi s 4 = (keccakF1600Round s rc).getD 4 0#64 := keccakChi_fold s rc 0 1 4 4
private theorem chi_5 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 6) &&& keccakRhoPi s 7) ^^^ keccakRhoPi s 5 = (keccakF1600Round s rc).getD 5 0#64 := keccakChi_fold s rc 6 7 5 5
private theorem chi_6 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 7) &&& keccakRhoPi s 8) ^^^ keccakRhoPi s 6 = (keccakF1600Round s rc).getD 6 0#64 := keccakChi_fold s rc 7 8 6 6
private theorem chi_7 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 8) &&& keccakRhoPi s 9) ^^^ keccakRhoPi s 7 = (keccakF1600Round s rc).getD 7 0#64 := keccakChi_fold s rc 8 9 7 7
private theorem chi_8 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 9) &&& keccakRhoPi s 5) ^^^ keccakRhoPi s 8 = (keccakF1600Round s rc).getD 8 0#64 := keccakChi_fold s rc 9 5 8 8
private theorem chi_9 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 5) &&& keccakRhoPi s 6) ^^^ keccakRhoPi s 9 = (keccakF1600Round s rc).getD 9 0#64 := keccakChi_fold s rc 5 6 9 9
private theorem chi_10 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 11) &&& keccakRhoPi s 12) ^^^ keccakRhoPi s 10 = (keccakF1600Round s rc).getD 10 0#64 := keccakChi_fold s rc 11 12 10 10
private theorem chi_11 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 12) &&& keccakRhoPi s 13) ^^^ keccakRhoPi s 11 = (keccakF1600Round s rc).getD 11 0#64 := keccakChi_fold s rc 12 13 11 11
private theorem chi_12 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 13) &&& keccakRhoPi s 14) ^^^ keccakRhoPi s 12 = (keccakF1600Round s rc).getD 12 0#64 := keccakChi_fold s rc 13 14 12 12
private theorem chi_13 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 14) &&& keccakRhoPi s 10) ^^^ keccakRhoPi s 13 = (keccakF1600Round s rc).getD 13 0#64 := keccakChi_fold s rc 14 10 13 13
private theorem chi_14 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 10) &&& keccakRhoPi s 11) ^^^ keccakRhoPi s 14 = (keccakF1600Round s rc).getD 14 0#64 := keccakChi_fold s rc 10 11 14 14
private theorem chi_15 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 16) &&& keccakRhoPi s 17) ^^^ keccakRhoPi s 15 = (keccakF1600Round s rc).getD 15 0#64 := keccakChi_fold s rc 16 17 15 15
private theorem chi_16 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 17) &&& keccakRhoPi s 18) ^^^ keccakRhoPi s 16 = (keccakF1600Round s rc).getD 16 0#64 := keccakChi_fold s rc 17 18 16 16
private theorem chi_17 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 18) &&& keccakRhoPi s 19) ^^^ keccakRhoPi s 17 = (keccakF1600Round s rc).getD 17 0#64 := keccakChi_fold s rc 18 19 17 17
private theorem chi_18 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 19) &&& keccakRhoPi s 15) ^^^ keccakRhoPi s 18 = (keccakF1600Round s rc).getD 18 0#64 := keccakChi_fold s rc 19 15 18 18
private theorem chi_19 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 15) &&& keccakRhoPi s 16) ^^^ keccakRhoPi s 19 = (keccakF1600Round s rc).getD 19 0#64 := keccakChi_fold s rc 15 16 19 19
private theorem chi_20 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 21) &&& keccakRhoPi s 22) ^^^ keccakRhoPi s 20 = (keccakF1600Round s rc).getD 20 0#64 := keccakChi_fold s rc 21 22 20 20
private theorem chi_21 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 22) &&& keccakRhoPi s 23) ^^^ keccakRhoPi s 21 = (keccakF1600Round s rc).getD 21 0#64 := keccakChi_fold s rc 22 23 21 21
private theorem chi_22 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 23) &&& keccakRhoPi s 24) ^^^ keccakRhoPi s 22 = (keccakF1600Round s rc).getD 22 0#64 := keccakChi_fold s rc 23 24 22 22
private theorem chi_23 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 24) &&& keccakRhoPi s 20) ^^^ keccakRhoPi s 23 = (keccakF1600Round s rc).getD 23 0#64 := keccakChi_fold s rc 24 20 23 23
private theorem chi_24 (s : KeccakState) (rc : BitVec 64) : (~~~(keccakRhoPi s 20) &&& keccakRhoPi s 21) ^^^ keccakRhoPi s 24 = (keccakF1600Round s rc).getD 24 0#64 := keccakChi_fold s rc 20 21 24 24

/-- Live SIMD registers at `+0x01cc` (end of `Theta`). -/
private def P1ThetaRegs (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = keccakC st1 2 ++ keccakC st0 2 ∧
  s.readVReg128 1#5 = (keccakC st1 4).rotateLeft 1 ++ (keccakC st0 4).rotateLeft 1 ∧
  s.readVReg128 2#5 = keccakTheta st1 5 ++ keccakTheta st0 5 ∧
  s.readVReg128 3#5 = (keccakC st1 0).rotateLeft 1 ++ (keccakC st0 0).rotateLeft 1 ∧
  s.readVReg128 4#5 = keccakTheta st1 10 ++ keccakTheta st0 10 ∧
  s.readVReg128 5#5 = keccakTheta st1 15 ++ keccakTheta st0 15 ∧
  s.readVReg128 6#5 = keccakTheta st1 1 ++ keccakTheta st0 1 ∧
  s.readVReg128 7#5 = keccakTheta st1 6 ++ keccakTheta st0 6 ∧
  s.readVReg128 8#5 = st1.getD 20 0#64 ++ st0.getD 20 0#64 ∧
  s.readVReg128 9#5 = st1.getD 0 0#64 ++ st0.getD 0 0#64 ∧
  s.readVReg128 10#5 = keccakC st1 3 ++ keccakC st0 3 ∧
  s.readVReg128 11#5 = keccakC st1 0 ++ keccakC st0 0 ∧
  s.readVReg128 12#5 = keccakTheta st1 20 ++ keccakTheta st0 20 ∧
  s.readVReg128 13#5 = keccakD st1 0 ++ keccakD st0 0 ∧
  s.readVReg128 14#5 = keccakD st1 1 ++ keccakD st0 1 ∧
  s.readVReg128 15#5 = keccakD st1 2 ++ keccakD st0 2 ∧
  s.readVReg128 16#5 = st1.getD 3 0#64 ++ st0.getD 3 0#64 ∧
  s.readVReg128 17#5 = st1.getD 22 0#64 ++ st0.getD 22 0#64 ∧
  s.readVReg128 18#5 = st1.getD 12 0#64 ++ st0.getD 12 0#64 ∧
  s.readVReg128 21#5 = st1.getD 17 0#64 ++ st0.getD 17 0#64 ∧
  s.readVReg128 22#5 = st1.getD 7 0#64 ++ st0.getD 7 0#64 ∧
  s.readVReg128 23#5 = st1.getD 16 0#64 ++ st0.getD 16 0#64 ∧
  s.readVReg128 26#5 = st1.getD 2 0#64 ++ st0.getD 2 0#64 ∧
  s.readVReg128 28#5 = st1.getD 21 0#64 ++ st0.getD 21 0#64 ∧
  s.readVReg128 30#5 = keccakD st1 3 ++ keccakD st0 3

/-- Spill slots `sp1 + 16 .. sp1 + 176` at `+0x01cc` and `+0x02e4`. -/
private def P1ThetaSpill (sp1 : BitVec 64) (st0 st1 : KeccakState) : SepProp :=
  Spill11 sp1
    (keccak2Lane st0 st1 11) (keccak2Lane st0 st1 23) (keccak2Lane st0 st1 24)
    (keccak2Lane st0 st1 13) (keccak2Lane st0 st1 19) (keccak2Lane st0 st1 18)
    (keccak2Lane st0 st1 9)  (keccak2Lane st0 st1 4)  (keccak2Lane st0 st1 7)
    (keccak2Lane st0 st1 8)  (keccak2Lane st0 st1 14)

/-- Live SIMD registers at `+0x02e4` (end of `RhoPi`). -/
private def P1RhoPiRegs (s : State) (st0 st1 : KeccakState) : Prop :=
  s.readVReg128 0#5 = (keccakTheta st1 9 <<< 20) ++ (keccakTheta st0 9 <<< 20) ∧
  s.readVReg128 3#5 = (keccakTheta st1 4 <<< 27) ++ (keccakTheta st0 4 <<< 27) ∧
  s.readVReg128 6#5 = keccakRhoPi st1 21 ++ keccakRhoPi st0 21 ∧
  s.readVReg128 7#5 = keccakTheta st1 9 ++ keccakTheta st0 9 ∧
  s.readVReg128 8#5 = keccakRhoPi st1 16 ++ keccakRhoPi st0 16 ∧
  s.readVReg128 9#5 = keccakRhoPi st1 0 ++ keccakRhoPi st0 0 ∧
  s.readVReg128 10#5 = keccakRhoPi st1 24 ++ keccakRhoPi st0 24 ∧
  s.readVReg128 11#5 = keccakRhoPi st1 7 ++ keccakRhoPi st0 7 ∧
  s.readVReg128 12#5 = keccakRhoPi st1 18 ++ keccakRhoPi st0 18 ∧
  s.readVReg128 14#5 = keccakRhoPi st1 4 ++ keccakRhoPi st0 4 ∧
  s.readVReg128 15#5 = keccakRhoPi st1 12 ++ keccakRhoPi st0 12 ∧
  s.readVReg128 16#5 = keccakRhoPi st1 2 ++ keccakRhoPi st0 2 ∧
  s.readVReg128 17#5 = keccakRhoPi st1 19 ++ keccakRhoPi st0 19 ∧
  s.readVReg128 18#5 = keccakRhoPi st1 11 ++ keccakRhoPi st0 11 ∧
  s.readVReg128 19#5 = keccakRhoPi st1 3 ++ keccakRhoPi st0 3 ∧
  s.readVReg128 20#5 = keccakRhoPi st1 8 ++ keccakRhoPi st0 8 ∧
  s.readVReg128 21#5 = keccakTheta st1 4 ++ keccakTheta st0 4 ∧
  s.readVReg128 22#5 = keccakRhoPi st1 9 ++ keccakRhoPi st0 9 ∧
  s.readVReg128 23#5 = keccakRhoPi st1 5 ++ keccakRhoPi st0 5 ∧
  s.readVReg128 24#5 = keccakRhoPi st1 1 ++ keccakRhoPi st0 1 ∧
  s.readVReg128 25#5 = keccakTheta st1 19 ++ keccakTheta st0 19 ∧
  s.readVReg128 26#5 = keccakRhoPi st1 20 ++ keccakRhoPi st0 20 ∧
  s.readVReg128 27#5 = keccakRhoPi st1 10 ++ keccakRhoPi st0 10 ∧
  s.readVReg128 28#5 = keccakRhoPi st1 17 ++ keccakRhoPi st0 17 ∧
  s.readVReg128 29#5 = keccakRhoPi st1 14 ++ keccakRhoPi st0 14 ∧
  s.readVReg128 30#5 = keccakTheta st1 14 ++ keccakTheta st0 14 ∧
  s.readVReg128 31#5 = keccakRhoPi st1 23 ++ keccakRhoPi st0 23

/-! ## `Theta`, `RhoPi`, `ChiIota`, and 24-round loop -/

private theorem permute1_theta [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (s : State) (sp1 rcBase : BitVec 64) (r : Nat) (st0 st1 : KeccakState)
    (s16 s32 s48 s64 s80 s96 s112 s128 : BitVec 128) (F : SepProp)
    (hpc : s.pc = b + 0x00f8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp1)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (8 * r))
    (hx27 : s.readReg64 .x27 = rcBase)
    (hregs : P1RoundRegs s st0 st1) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x01cc#64) s
      (Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
        (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗ F)
      (fun sf Q =>
        P1Scalars s sf ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
        sf.readReg64 .x9 = rcBase + BitVec.ofNat 64 (8 * r) ∧
        sf.pstate = subsPState64 (BitVec.ofNat 64 (8 * (r + 1))) 192#64 ∧
        P1ThetaRegs sf st0 st1 ∧
        (Q ⊢ P1ThetaSpill sp1 st0 st1 ∗ F)) := by
  rcases hregs with ⟨hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv11, hv12, hv15, hv16,
    hv17, hv18, hv19, hv22, hv23, hv24, hv27, hv28, hv29, hv30⟩
  dsimp only [keccak2Lane] at *
  dsimp only [Spill11]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  refine ⟨⟨Eq.trans (by wp_norm_lhs) hsp.symm,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      Eq.trans (by wp_norm_lhs) hx27.symm, by wp_norm_lhs⟩,
    by wp_norm_lhs, ?_, ?_, ?_, ?_, ?_⟩
  · refine Eq.trans (by wp_norm_lhs) (bv64_8mul_add8 r)
  · wp_norm_lhs
  · refine Eq.trans (by wp_norm_lhs) ?_
    rw [bv64_8mul_add8]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (
      refine Eq.trans (by wp_norm_lhs) ?_
      simp only [BitVec.or_self,
        keccakC_fold_0, keccakC_fold_1, keccakC_fold_2, keccakC_fold_3, keccakC_fold_4,
        keccakD_fold_0, keccakD_fold_1, keccakD_fold_2, keccakD_fold_3,
        theta_l_1, theta_l_5, theta_l_6, theta_l_10, theta_l_15, theta_l_20])
  · dsimp only [P1ThetaSpill, Spill11, keccak2Lane]
    simp only [extractLsb_lo_append, extractLsb_hi_append]
    sep_entail

private theorem permute1_rhopi [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (s : State) (sp1 : BitVec 64) (st0 st1 : KeccakState) (F : SepProp)
    (hpc : s.pc = b + 0x01cc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp1)
    (hsp_align : s.spAligned = true)
    (hregs : P1ThetaRegs s st0 st1) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x02e4#64) s
      (P1ThetaSpill sp1 st0 st1 ∗ F)
      (fun sf Q =>
        P1Scalars s sf ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.pstate = s.pstate ∧
        P1RhoPiRegs sf st0 st1 ∧
        (Q ⊢ P1ThetaSpill sp1 st0 st1 ∗ F)) := by
  rcases hregs with ⟨hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7, hv8, hv9, hv10, hv11, hv12,
    hv13, hv14, hv15, hv16, hv17, hv18, hv21, hv22, hv23, hv26, hv28, hv30⟩
  dsimp only [P1ThetaSpill, Spill11, keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  refine ⟨⟨Eq.trans (by wp_norm_lhs) hsp.symm,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (
      refine Eq.trans (by wp_norm_lhs) ?_
      simp only [keccakD_fold_4,
        theta_l_0, theta_l_2, theta_l_3, theta_l_4, theta_l_7, theta_l_8, theta_l_9,
        theta_l_11, theta_l_12, theta_l_13, theta_l_14, theta_l_16, theta_l_17, theta_l_18,
        theta_l_21, theta_l_22, theta_l_23, theta_r_19, theta_r_24,
        keccakRhoPi_fold_0, rhopi_1, rhopi_2, rhopi_3, rhopi_4, rhopi_5, rhopi_7,
        rhopi_8, rhopi_9, rhopi_10, rhopi_11, rhopi_12, rhopi_14, rhopi_16, rhopi_17,
        rhopi_18, rhopi_19, rhopi_20, rhopi_21, rhopi_23, rhopi_24])
  · sep_entail

attribute [local irreducible] keccakF1600Round

private theorem permute1_chiiota [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl01 b) (_hbase : blkPl01.base = b)
    (s : State) (sp1 rcBase : BitVec 64) (r : Nat) (hr : r < 24)
    (st0 st1 : KeccakState) (F : SepProp)
    (hpc : s.pc = b + 0x02e4#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp1)
    (hsp_align : s.spAligned = true)
    (hx9 : s.readReg64 .x9 = rcBase + BitVec.ofNat 64 (8 * r))
    (hregs : P1RhoPiRegs s st0 st1) :
    let st0' := keccakF1600Round st0 (keccakRcAt r)
    let st1' := keccakF1600Round st1 (keccakRcAt r)
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x03e8#64) s
      (P1ThetaSpill sp1 st0 st1 ∗ ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F))
      (fun sf Q =>
        P1Scalars s sf ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.pstate = s.pstate ∧
        P1RoundRegs sf st0' st1' ∧
        ∃ s16' s32' s48' s64' s80' s96' s112' s128',
          Q ⊢ Spill11 sp1 s16' s32' s48' s64' s80' s96' s112' s128'
            (keccak2Lane st0' st1' 7) (keccak2Lane st0' st1' 8) (keccak2Lane st0' st1' 14) ∗
            ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  intro st0' st1'
  rcases hregs with ⟨hv0, hv3, hv6, hv7, hv8, hv9, hv10, hv11, hv12, hv14, hv15, hv16,
    hv17, hv18, hv19, hv20, hv21, hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  have hrc_bound : 8 * r + 8 ≤ mlkemData01Bytes.length := by
    rw [mlkemData01Bytes_length]; omega
  dsimp only [P1ThetaSpill, Spill11, keccak2Lane]
  simp only [extractLsb_lo_append, extractLsb_hi_append]
  wp_steps
  apply step_simdLd1r_2d
  · wp_norm_lhs
  · wp_norm_lhs
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · exact (SepLoad64.of_pointsToBytes_readLE_RO (off := 8 * r)
      (by sep_focus) hrc_bound rfl).congr_val (rfl : _ = keccakRcAt r)
  · wp_norm_lhs
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  refine ⟨⟨Eq.trans (by wp_norm_lhs) hsp.symm,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
      by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_, ?_⟩
  · dsimp only [st0', st1', P1RoundRegs, keccak2Lane]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (
      refine Eq.trans (by wp_norm_lhs) ?_
      simp only [BitVec.or_self, rhopi_6, rhopi_13, rhopi_15, rhopi_22, keccakChi0_fold,
        chi_1 (rc := keccakRcAt r), chi_2 (rc := keccakRcAt r), chi_3 (rc := keccakRcAt r),
        chi_4 (rc := keccakRcAt r), chi_5 (rc := keccakRcAt r), chi_6 (rc := keccakRcAt r),
        chi_9 (rc := keccakRcAt r), chi_10 (rc := keccakRcAt r), chi_11 (rc := keccakRcAt r),
        chi_12 (rc := keccakRcAt r), chi_13 (rc := keccakRcAt r), chi_15 (rc := keccakRcAt r),
        chi_16 (rc := keccakRcAt r), chi_17 (rc := keccakRcAt r), chi_18 (rc := keccakRcAt r),
        chi_19 (rc := keccakRcAt r), chi_20 (rc := keccakRcAt r), chi_21 (rc := keccakRcAt r),
        chi_22 (rc := keccakRcAt r), chi_23 (rc := keccakRcAt r), chi_24 (rc := keccakRcAt r)])
  · refine ⟨keccak2Lane st0 st1 11, keccak2Lane st0 st1 23, keccak2Lane st0 st1 24,
      keccak2Lane st0 st1 13, keccak2Lane st0 st1 19, keccak2Lane st0 st1 18,
      keccak2Lane st0 st1 9,
      (~~~(keccakRhoPi st1 1) &&& keccakRhoPi st1 2) ++
        (~~~(keccakRhoPi st0 1) &&& keccakRhoPi st0 2), ?_⟩
    dsimp only [st0', st1', Spill11, keccak2Lane]
    simp only [extractLsb_lo_append, extractLsb_hi_append,
      chi_7 (rc := keccakRcAt r), chi_8 (rc := keccakRcAt r), chi_14 (rc := keccakRcAt r)]
    sep_entail

private theorem permute1_one_round [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (s : State) (sp1 rcBase : BitVec 64) (r : Nat) (hr : r < 24)
    (st0 st1 : KeccakState)
    (s16 s32 s48 s64 s80 s96 s112 s128 : BitVec 128) (F : SepProp)
    (hpc : s.pc = b + 0x00f8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp1)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (8 * r))
    (hx27 : s.readReg64 .x27 = rcBase)
    (hregs : P1RoundRegs s st0 st1) :
    let st0' := keccakF1600Round st0 (keccakRcAt r)
    let st1' := keccakF1600Round st1 (keccakRcAt r)
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x03e8#64) s
      (Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
        (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F))
      (fun sf Q =>
        P1Scalars s sf ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (8 * (r + 1)) ∧
        sf.pstate = subsPState64 (BitVec.ofNat 64 (8 * (r + 1))) 192#64 ∧
        P1RoundRegs sf st0' st1' ∧
        ∃ s16' s32' s48' s64' s80' s96' s112' s128',
          Q ⊢ Spill11 sp1 s16' s32' s48' s64' s80' s96' s112' s128'
            (keccak2Lane st0' st1' 7) (keccak2Lane st0' st1' 8) (keccak2Lane st0' st1' 14) ∗
            ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  intro st0' st1'
  refine SepWP.seq
    (permute1_theta hb hbase s sp1 rcBase r st0 st1 s16 s32 s48 s64 s80 s96 s112 s128
      ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F) hpc hrun hsp hsp_align hx8 hx27 hregs) ?_
  intro s1 Q1 hpc1 hrun1 ⟨hscal1, hx26_1, hx8_1, hx9_1, hpst1, hth1, hQ1⟩
  refine SepWP.weaken_pre hQ1 <|
    SepWP.seq
      (permute1_rhopi hb hbase s1 sp1 st0 st1 ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F)
        hpc1 hrun1 (hscal1.1.trans hsp) (hscal1.spAligned hsp_align) hth1) ?_
  intro s2 Q2 hpc2 hrun2 ⟨hscal2, hx26_2, hx8_2, hx9_2, hpst2, hrp2, hQ2⟩
  have hscal12 := hscal1.trans hscal2
  refine SepWP.weaken_pre hQ2 <|
    SepWP.mono
      (permute1_chiiota hb hbase s2 sp1 rcBase r hr st0 st1 F
        hpc2 hrun2 (hscal12.1.trans hsp) (hscal12.spAligned hsp_align)
        (hx9_2.trans hx9_1) hrp2) ?_
  intro s3 Q3 _ _ ⟨hscal3, hx26_3, hx8_3, hpst3, hrr3, hsp3⟩
  exact ⟨hscal12.trans hscal3,
    hx26_3.trans (hx26_2.trans hx26_1),
    hx8_3.trans (hx8_2.trans hx8_1),
    hpst3.trans (hpst2.trans hpst1),
    hrr3, hsp3⟩

private theorem permute1_rounds_from [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (sp1 rcBase : BitVec 64) (F : SepProp) (rem : Nat) :
    ∀ (r : Nat), rem = 23 - r → r ≤ 23 →
      ∀ (s : State) (st0 st1 : KeccakState)
        (s16 s32 s48 s64 s80 s96 s112 s128 : BitVec 128),
        s.pc = b + 0x00f8#64 →
        s.status = .Running →
        s.sp = sp1 →
        s.spAligned = true →
        s.readReg64 .x8 = BitVec.ofNat 64 (8 * r) →
        s.readReg64 .x27 = rcBase →
        P1RoundRegs s st0 st1 →
        SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x03ec#64) s
          (Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
            (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗
            ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F))
          (fun sf Q =>
            let out0 := keccakRunFrom r st0
            let out1 := keccakRunFrom r st1
            P1Scalars s sf ∧
            sf.readReg64 .x26 = s.readReg64 .x26 ∧
            P1RoundRegs sf out0 out1 ∧
            ∃ s16' s32' s48' s64' s80' s96' s112' s128',
              Q ⊢ Spill11 sp1 s16' s32' s48' s64' s80' s96' s112' s128'
                (keccak2Lane out0 out1 7) (keccak2Lane out0 out1 8) (keccak2Lane out0 out1 14) ∗
                ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  induction rem with
  | zero =>
    intro r _hrem _hr s st0 st1 s16 s32 s48 s64 s80 s96 s112 s128
      hpc hrun hsp hsp_align hx8 hx27 hregs
    have hr23 : r = 23 := by omega
    subst hr23
    refine SepWP.seq
      (permute1_one_round hb hbase s sp1 rcBase 23 (by decide) st0 st1
        s16 s32 s48 s64 s80 s96 s112 s128 F hpc hrun hsp hsp_align hx8 hx27 hregs) ?_
    intro s3 Q3 hpc3 hrun3 ⟨hscal3, hx26_3, _hx8_3, hpst3, hrr3,
      s16', s32', s48', s64', s80', s96', s112', s128', hQ3⟩
    refine SepWP.weaken_pre hQ3 ?_
    wp_step
    apply SepWP.done
    · wp_norm_lhs
    · cases s3; exact hrun3
    · dsimp only
      rw [keccakRunFrom_step 23 (by decide) st0,
          keccakRunFrom_step 23 (by decide) st1,
          keccakRunFrom_24, keccakRunFrom_24]
      exact ⟨hscal3.setPC _, setPC_readReg64 _ hx26_3, p1RoundRegs_setPC _ hrr3,
        s16', s32', s48', s64', s80', s96', s112', s128', Entails.refl _⟩
  | succ rem ih =>
    intro r _hrem _hr s st0 st1 s16 s32 s48 s64 s80 s96 s112 s128
      hpc hrun hsp hsp_align hx8 hx27 hregs
    have hr_lt : r < 23 := by omega
    refine SepWP.seq
      (permute1_one_round hb hbase s sp1 rcBase r (by omega) st0 st1
        s16 s32 s48 s64 s80 s96 s112 s128 F hpc hrun hsp hsp_align hx8 hx27 hregs) ?_
    intro s3 Q3 hpc3 hrun3 ⟨hscal3, hx26_3, hx8_3, hpst3, hrr3,
      s16', s32', s48', s64', s80', s96', s112', s128', hQ3⟩
    refine SepWP.weaken_pre hQ3 ?_
    wp_step
    wp_if hbr
    · refine SepWP.mono
        (ih (r + 1) (by omega) (by omega) (s3.setPC (b + 0x00f8#64))
          (keccakF1600Round st0 (keccakRcAt r)) (keccakF1600Round st1 (keccakRcAt r))
          s16' s32' s48' s64' s80' s96' s112' s128'
          (setPC_pc s3 _) (setPC_status _ hrun3)
          (setPC_sp _ (hscal3.1.trans hsp)) (setPC_spAligned _ (hscal3.spAligned hsp_align))
          (setPC_readReg64 _ hx8_3) (setPC_readReg64 _ (hscal3.2.2.2.2.2.2.2.2.1.trans hx27))
          (p1RoundRegs_setPC _ hrr3)) ?_
      intro sf Qf _ _ ⟨hscal_ih, hx26_ih, hrr_ih, hsp_ih⟩
      dsimp only at hrr_ih hsp_ih ⊢
      rw [keccakRunFrom_step r (by omega) st0, keccakRunFrom_step r (by omega) st1]
      exact ⟨(hscal3.setPC _).trans hscal_ih, hx26_ih.trans (setPC_readReg64 _ hx26_3), hrr_ih, hsp_ih⟩
    · exfalso
      have hne : BitVec.ofNat 64 (8 * (r + 1)) ≠ 192#64 := cmp192_ne_of_lt (by omega)
      simp [hne] at hbr

/-- Full 24-round `keccak_f1600` loop `[0x00f8 → 0x03ec]` from `(st0, st1)` to
    `(keccakF1600 st0, keccakF1600 st1)`. -/
theorem permute1_rounds [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl01 b) (hbase : blkPl01.base = b)
    (s : State) (sp1 rcBase : BitVec 64) (st0 st1 : KeccakState)
    (s16 s32 s48 s64 s80 s96 s112 s128 : BitVec 128) (F : SepProp)
    (hpc : s.pc = b + 0x00f8#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp1)
    (hsp_align : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx27 : s.readReg64 .x27 = rcBase)
    (hregs : P1RoundRegs s st0 st1) :
    SepWP (blkPC01.rebase b (fun _ => none)) (b + 0x03ec#64) s
      (Spill11 sp1 s16 s32 s48 s64 s80 s96 s112 s128
        (keccak2Lane st0 st1 7) (keccak2Lane st0 st1 8) (keccak2Lane st0 st1 14) ∗
        ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F))
      (fun sf Q =>
        let out0 := keccakF1600 st0
        let out1 := keccakF1600 st1
        P1Scalars s sf ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        P1RoundRegs sf out0 out1 ∧
        ∃ s16' s32' s48' s64' s80' s96' s112' s128',
          Q ⊢ Spill11 sp1 s16' s32' s48' s64' s80' s96' s112' s128'
            (keccak2Lane out0 out1 7) (keccak2Lane out0 out1 8) (keccak2Lane out0 out1 14) ∗
            ((rcBase ↦ᵣ mlkemData01Bytes) ∗ F)) := by
  simpa only [keccakRunFrom_zero] using
    permute1_rounds_from hb hbase sp1 rcBase F 23 0 rfl (by decide) s st0 st1
      s16 s32 s48 s64 s80 s96 s112 s128 hpc hrun hsp hsp_align hx8 hx27 hregs

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31.Permute1
