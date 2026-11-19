/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.Keccak
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 4a (`+0x39f4 → +0x3cec`)

Spills `m'` (`32` B) into `[sp + 8 .. sp + 136)` (`WordRangeMem 32`) and `[sp + 4432 .. sp + 4464)`,
appends `hPk` (`32` B) at `[sp + 4464 .. sp + 4496)`, calls `B00` (`SHA3-512` → `kr` at
`[sp + 4496 .. sp + 4560)`), stages `z ++ ct` (`1120` B) at `[sp + 4560 .. sp + 5680)`, calls `B01`
(`SHAKE-256_32` → `kRej` at `[sp + 25616 .. sp + 25648)`), stores `[sp + 192] = sp + 13392`, and
zeroes `[sp + 12368 .. sp + 18032)` via `B29` (`memset`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4a

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW keccak2_72_6_RW1Spec keccak2_136_31_RW1Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6 (blk00_keccak2_72_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (blk01_keccak2_136_31_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (keccakSponge sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (cells32_entails_memRegion sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem bytesToVecNat
  pointsToBytes_eq_vecRangeMem step_ldpQ128 step_stpQ128 step_strQ128
  vecRangeMem_congr vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (blk28_memcpy_04 exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  ByteRangeMem SepStore32.wordRange SepStore8.byteRange WordRangeMem byteRangeMem_congr
  byteRangeMem_eq_pointsToBytes msgSlotIdx msgWordFn wordRangeMem_congr)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x39f4 → 0x3ce8]
end

theorem blk00_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 0)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_72_6_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk00_keccak2_72_6_RW1_ok
theorem blk01_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk01_keccak2_136_31_RW1_ok
theorem blk29_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk29_memset_ok

private theorem shake256List_len (n : Nat) (bs : List (BitVec 8)) :
    (shake256List n bs).length = n := by
  simp [shake256List, keccakSponge]

private theorem replicate_entails_memRegion (a : BitVec 64) (n : Nat) :
    (a ↦ₛ List.replicate n 0#8) ⊢ memRegion a n := by
  have h := pointsToBytes_entails_memRegion a (List.replicate n 0#8)
  rwa [List.length_replicate] at h

attribute [local irreducible] blkPC04 sha3_512List shake256List List.replicate
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0
@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

abbrev offSeg4Start : BitVec 64 := BitVec.ofNat 64 14836
abbrev off3b14 : BitVec 64 := BitVec.ofNat 64 15124
abbrev off3c28 : BitVec 64 := BitVec.ofNat 64 15400
abbrev off3c84 : BitVec 64 := BitVec.ofNat 64 15492
abbrev off3cc4 : BitVec 64 := BitVec.ofNat 64 15556
abbrev offSeg4aEnd : BitVec 64 := BitVec.ofNat 64 15596

/-! ## 1. Local Step Macros & `seg4a_prep1` (`+0x39f4 → +0x3b14`) -/

@[simp, arm64_norm, wp_norm] private theorem truncate8_zext32 (v : BitVec 8) :
    ((v.zeroExtend 64).truncate 32).truncate 8 = v := by bv_bits
@[simp, arm64_norm, wp_norm] private theorem truncate32_zext64_zext32 (v : BitVec 8) :
    (v.zeroExtend 64).truncate 32 = v.zeroExtend 32 := by bv_bits

local macro "step_ldrb_m " sp:term:arg hrun:term:arg hsp:term:arg k:num : tactic => `(tactic|
  refine SepWP.step_ldr8 (pc := _) (wb := none) (ea := $sp + 20704#64 + BitVec.ofNat 64 $k)
    (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hsp:term]; try (clear * -; bv_omega))
    (SepLoad8.of_pointsToBytes rfl (off := $k) (by omega) rfl) (by wp_norm_lhs) ?_)

local macro "step_strb_m " sp:term:arg hrun:term:arg hsp:term:arg k:num : tactic => `(tactic|
  refine SepWP.step_str8 (pc := _) (wb := none) (ea := $sp + 4432#64 + BitVec.ofNat 64 $k)
    (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hsp:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.byteRange (k := $k) (by decide) rfl))))
    (by wp_norm_lhs) fun _ => ?_)

local macro "step_stp32_m " sp:term:arg hrun:term:arg hsp:term:arg hsp_chk:term:arg s1:num s2:num : tactic => `(tactic|
  refine SepWP.step_stp32 (pc := _) (wb := none)
    (ea := $sp + 8#64 + BitVec.ofNat 64 (4 * $s1))
    (ea2 := $sp + 8#64 + BitVec.ofNat 64 (4 * $s2))
    (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hsp:term, $hsp_chk:term])
    (by simp [evalAddrMode, $hsp:term]; try (clear * -; bv_omega)) (by clear * -; bv_omega)
    (by wp_norm_lhs) (by wp_norm_lhs)
    (SepStore32.right (SepStore32.left
      (SepStore32.wordRange (k := $s1) (by decide) rfl)))
    (SepStore32.right (SepStore32.left
      (SepStore32.wordRange (k := $s2) (by decide) rfl)))
    (by wp_norm_lhs) fun _ => ?_)

local macro "step_str32_m " sp:term:arg hrun:term:arg hsp:term:arg hsp_chk:term:arg s1:num : tactic => `(tactic|
  refine SepWP.step_str32 (pc := _) (wb := none)
    (ea := $sp + 8#64 + BitVec.ofNat 64 (4 * $s1))
    (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hsp:term, $hsp_chk:term])
    (by simp [evalAddrMode, $hsp:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore32.right (SepStore32.left
      (SepStore32.wordRange (k := $s1) (by decide) rfl)))
    (by wp_norm_lhs) fun _ => ?_)

theorem seg4a_prep1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (_hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (m' hPk : List (BitVec 8))
    (fw : Nat → BitVec 32) (fb : Nat → BitVec 8) (Rest : SepProp)
    (hm' : m'.length = 32)
    (hpc : s.pc = b + offSeg4Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3b14) s
      (((sp + 20704#64) ↦ₛ m') ∗ WordRangeMem 32 (sp + 8#64) fw ∗
        ByteRangeMem 32 (sp + 4432#64) fb ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
        VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = sp + 22400#64 ∧ s1.readReg64 .x1 = sp + 5680#64 ∧
        s1.readReg64 .x2 = sp + 11856#64 ∧ s1.readReg64 .x10 = sp + 19120#64 ∧
        s1.readReg64 .x20 = sp + 5680#64 ∧ s1.readReg64 .x21 = sp + 11856#64 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧ s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x8 = (m'.getD 16 0#8).zeroExtend 64 ∧
        s1.readReg64 .x12 = (m'.getD 17 0#8).zeroExtend 64 ∧
        s1.readVReg128 0#5 = bytesToVecNat hPk 0 ∧ s1.readVReg128 1#5 = bytesToVecNat hPk 1 ∧
        (∃ (fw1 : Nat → BitVec 32) (fb1 : Nat → BitVec 8),
          (∀ j, j < 16 → fw1 j = msgWordFn m' j) ∧ (∀ j, j < 16 → fb1 j = m'.getD j 0#8) ∧
          (P1 ⊢ ((sp + 20704#64) ↦ₛ m') ∗ WordRangeMem 32 (sp + 8#64) fw1 ∗
            ByteRangeMem 32 (sp + 4432#64) fb1 ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
            VecRangeMem 2 (dkA + 2336#64) (bytesToVecNat hPk) ∗ Rest))) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  wp_steps 6
  step_ldrb_m sp hrun hsp 0; step_ldrb_m sp hrun hsp 1; wp_step
  refine step_ldpQ128 (pc := _) (wb := none) (ea := dkA + 2336#64) (ea16 := dkA + 2336#64 + 16#64)
    (v1 := bytesToVecNat hPk 0) (v2 := bytesToVecNat hPk 1) (by wp_norm_lhs) (by simp [hrun])
    (by wp_norm_lhs) rfl (by simp [evalAddrMode]) rfl
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right
      (SepLoad128.left (SepLoad128.vecRange (k := 0) (by decide) (by clear * -; bv_omega)))))))
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.right
      (SepLoad128.left (SepLoad128.vecRange (k := 1) (by decide) (by clear * -; bv_omega)))))))
    (by wp_norm_lhs) ?_
  step_ldrb_m sp hrun hsp 2; step_stp32_m sp hrun hsp hsp_chk 0 1; wp_steps 2
  step_strb_m sp hrun hsp 0; step_ldrb_m sp hrun hsp 3; wp_step; step_strb_m sp hrun hsp 1
  wp_step; step_ldrb_m sp hrun hsp 4; step_stp32_m sp hrun hsp hsp_chk 2 3; wp_steps 2
  step_strb_m sp hrun hsp 2; step_ldrb_m sp hrun hsp 5; wp_step; step_strb_m sp hrun hsp 3
  wp_step; step_ldrb_m sp hrun hsp 6; step_stp32_m sp hrun hsp hsp_chk 4 5; wp_steps 2
  step_strb_m sp hrun hsp 4; step_ldrb_m sp hrun hsp 7; wp_step; step_strb_m sp hrun hsp 5
  wp_step; step_ldrb_m sp hrun hsp 8; step_stp32_m sp hrun hsp hsp_chk 6 7; wp_step
  step_strb_m sp hrun hsp 6; step_ldrb_m sp hrun hsp 9; wp_step; step_strb_m sp hrun hsp 7
  wp_step; step_ldrb_m sp hrun hsp 10; step_stp32_m sp hrun hsp hsp_chk 8 9; step_strb_m sp hrun hsp 8
  step_ldrb_m sp hrun hsp 11; wp_step; step_strb_m sp hrun hsp 9; wp_step; step_ldrb_m sp hrun hsp 12
  step_stp32_m sp hrun hsp hsp_chk 10 11; step_strb_m sp hrun hsp 10
  step_ldrb_m sp hrun hsp 13; wp_step; step_strb_m sp hrun hsp 11; wp_step; step_ldrb_m sp hrun hsp 14
  step_stp32_m sp hrun hsp hsp_chk 12 13; step_strb_m sp hrun hsp 12
  step_ldrb_m sp hrun hsp 15; wp_step; step_strb_m sp hrun hsp 13; wp_step; step_ldrb_m sp hrun hsp 16
  step_stp32_m sp hrun hsp hsp_chk 14 15; step_strb_m sp hrun hsp 14
  step_ldrb_m sp hrun hsp 17; wp_step; step_strb_m sp hrun hsp 15
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨_, _, fun j hj => ?_, fun j hj => ?_, Entails.refl _⟩⟩
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
      j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [msgWordFn, msgSlotIdx]
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
      j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp

/-! ## 2. `seg4a_prep2` (`+0x3b14 → +0x3c28`) -/

local macro "step_ldrb_x10 " sp:term:arg hrun:term:arg hx10:term:arg k:num : tactic => `(tactic|
  refine SepWP.step_ldr8 (pc := _) (wb := none) (ea := $sp + 20704#64 + BitVec.ofNat 64 $k)
    (by wp_norm_lhs) (by simp [$hrun:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx10:term]; try (clear * -; bv_omega))
    (SepLoad8.of_pointsToBytes rfl (off := $k) (by omega) rfl) (by wp_norm_lhs) ?_)

theorem seg4a_prep2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (_hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (m' hPk : List (BitVec 8))
    (fw1 : Nat → BitVec 32) (fb1 : Nat → BitVec 8) (fh fz : Nat → BitVec 128)
    (v0 v1 v2 v3 : BitVec 64) (Rest : SepProp)
    (hm' : m'.length = 32) (hhPk : hPk.length = 32)
    (hpc : s.pc = b + off3b14) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 22400#64) (hx1 : s.readReg64 .x1 = sp + 5680#64)
    (hx2 : s.readReg64 .x2 = sp + 11856#64) (hx10 : s.readReg64 .x10 = sp + 19120#64)
    (hx20 : s.readReg64 .x20 = sp + 5680#64) (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hw8 : s.readReg64 .x8 = (m'.getD 16 0#8).zeroExtend 64)
    (hw12 : s.readReg64 .x12 = (m'.getD 17 0#8).zeroExtend 64)
    (hq0 : s.readVReg128 0#5 = bytesToVecNat hPk 0)
    (hq1 : s.readVReg128 1#5 = bytesToVecNat hPk 1)
    (hfw1 : ∀ j, j < 16 → fw1 j = msgWordFn m' j)
    (hfb1 : ∀ j, j < 16 → fb1 j = m'.getD j 0#8) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3c28) s
      (((sp + 20704#64) ↦ₛ m') ∗ WordRangeMem 32 (sp + 8#64) fw1 ∗
        ByteRangeMem 32 (sp + 4432#64) fb1 ∗ VecRangeMem 2 (sp + 4464#64) fh ∗
        VecRangeMem 4 (sp + 5680#64) fz ∗
        ((sp + 22400#64) ↦₆₄ v0) ∗ ((sp + 22408#64) ↦₆₄ v1) ∗
        ((sp + 22416#64) ↦₆₄ v2) ∗ ((sp + 22424#64) ↦₆₄ v3) ∗ Rest)
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x0 = sp + 22400#64 ∧ s2.readReg64 .x1 = sp + 5680#64 ∧
        s2.readReg64 .x2 = sp + 11856#64 ∧ s2.readReg64 .x20 = sp + 5680#64 ∧
        s2.readReg64 .x21 = sp + 11856#64 ∧ s2.readReg64 .x23 = s.readReg64 .x23 ∧
        s2.readReg64 .x26 = s.readReg64 .x26 ∧ s2.readReg64 .x28 = s.readReg64 .x28 ∧
        s2.readReg64 .fp = s.readReg64 .fp ∧
        (P2 ⊢ Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64)
            (m' ++ hPk).length (m' ++ hPk).length ∗
          ((sp + 4432#64) ↦ₛ (m' ++ hPk)) ∗
          memRegion (sp + 5680#64) 64 ∗
          ((sp + 20704#64) ↦ₛ m') ∗
          WordRangeMem 32 (sp + 8#64) (msgWordFn m') ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  wp_step
  step_ldrb_x10 sp hrun hx10 18
  refine SepWP.step_stp32 (pc := _) (wb := none)
    (ea := sp + 8#64 + BitVec.ofNat 64 (4 * 16)) (ea2 := sp + 8#64 + BitVec.ofNat 64 (4 * 17))
    (v1 := (m'.getD 17 0#8).zeroExtend 32) (v2 := (m'.getD 16 0#8).zeroExtend 32)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by clear * -; bv_omega)
    (by simp [State.readReg32, hw12]) (by simp [State.readReg32, hw8])
    (SepStore32.right (SepStore32.left (SepStore32.wordRange (k := 16) (by decide) rfl)))
    (SepStore32.right (SepStore32.left (SepStore32.wordRange (k := 17) (by decide) rfl)))
    (by wp_norm_lhs) fun _ => ?_
  refine SepWP.step_str8 (pc := _) (wb := none) (ea := sp + 4432#64 + BitVec.ofNat 64 16)
    (val := m'.getD 16 0#8)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode])
    (by simp [State.readReg32, hw8])
    (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.byteRange (k := 16) (by decide) rfl))))
    (by wp_norm_lhs) fun _ => ?_
  step_ldrb_x10 sp hrun hx10 19; wp_step
  refine SepWP.step_str8 (pc := _) (wb := none) (ea := sp + 4432#64 + BitVec.ofNat 64 17)
    (val := m'.getD 17 0#8)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode])
    (by simp [State.readReg32, hw12])
    (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.byteRange (k := 17) (by decide) rfl))))
    (by wp_norm_lhs) fun _ => ?_
  wp_step; step_ldrb_x10 sp hrun hx10 20
  step_stp32_m sp hrun hsp hsp_chk 18 19; step_strb_m sp hrun hsp 18
  step_ldrb_x10 sp hrun hx10 21; wp_step; step_strb_m sp hrun hsp 19; wp_step
  step_ldrb_x10 sp hrun hx10 22; step_stp32_m sp hrun hsp hsp_chk 20 21; step_strb_m sp hrun hsp 20
  step_ldrb_x10 sp hrun hx10 23; wp_step; step_strb_m sp hrun hsp 21; wp_step
  step_ldrb_x10 sp hrun hx10 24; step_stp32_m sp hrun hsp hsp_chk 22 23; step_strb_m sp hrun hsp 22
  step_ldrb_x10 sp hrun hx10 25; wp_step; step_strb_m sp hrun hsp 23; wp_step
  step_ldrb_x10 sp hrun hx10 26; step_stp32_m sp hrun hsp hsp_chk 24 25; step_strb_m sp hrun hsp 24
  step_ldrb_x10 sp hrun hx10 27; wp_step; step_strb_m sp hrun hsp 25; wp_step
  step_ldrb_x10 sp hrun hx10 28; step_stp32_m sp hrun hsp hsp_chk 27 28; step_strb_m sp hrun hsp 26
  wp_step; step_strb_m sp hrun hsp 27; wp_step
  step_ldrb_x10 sp hrun hx10 29; step_str32_m sp hrun hsp hsp_chk 31; step_strb_m sp hrun hsp 28
  wp_steps 3
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 4464#64) (val := bytesToVecNat hPk 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp [hq0])
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 0) (by decide) (by clear * -; bv_omega))))))
    (by wp_norm_lhs) fun _ => ?_
  wp_steps 4
  step_ldrb_x10 sp hrun hx10 30; wp_step; step_ldrb_x10 sp hrun hx10 31
  wp_step; step_strb_m sp hrun hsp 29; wp_step
  step_stp32_m sp hrun hsp hsp_chk 29 30; step_strb_m sp hrun hsp 30; wp_step
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 4464#64 + 16#64) (val := bytesToVecNat hPk 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp [hq1])
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 1) (by decide) (by clear * -; bv_omega))))))
    (by wp_norm_lhs) fun _ => ?_
  step_str32_m sp hrun hsp hsp_chk 26; step_strb_m sp hrun hsp 31
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 5680#64 + 48#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 3) (by decide) (by clear * -; bv_omega)))))))
    (by wp_norm_lhs) fun _ => ?_
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 5680#64 + 32#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 2) (by decide) (by clear * -; bv_omega)))))))
    (by wp_norm_lhs) fun _ => ?_
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 5680#64 + 16#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 1) (by decide) (by clear * -; bv_omega)))))))
    (by wp_norm_lhs) fun _ => ?_
  refine step_strQ128 (pc := _) (wb := none) (ea := sp + 5680#64) (val := 0#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.vecRange (k := 0) (by decide) (by clear * -; bv_omega)))))))
    (by wp_norm_lhs) fun _ => ?_
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [hx0], by simp [hx1], by simp [hx2], by simp [hx20], by simp [hx21],
      by simp, by simp, by simp, by simp, ?_⟩
  rw [wordRangeMem_congr (g := msgWordFn m') (fun j hj => by
      by_cases hj16 : j < 16
      · simp (discharger := omega) only [Function.update_of_ne]
        exact hfw1 j hj16
      · have hj_hi : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨
            j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
        rcases hj_hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [msgWordFn, msgSlotIdx]),
    byteRangeMem_congr (g := fun j => m'.getD j 0#8) (fun j hj => by
      by_cases hj16 : j < 16
      · simp (discharger := omega) only [Function.update_of_ne]
        exact hfb1 j hj16
      · have hj_hi : j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨
            j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
        rcases hj_hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
    ← hm', byteRangeMem_eq_pointsToBytes m' (sp + 4432#64),
    vecRangeMem_congr (n := 2) (g := bytesToVecNat hPk) (fun j hj => by
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl <;> simp),
    ← pointsToBytes_eq_vecRangeMem 2 (sp + 4464#64) hhPk]
  have hmh : ((sp + 4432#64) ↦ₛ m') ∗ ((sp + 4464#64) ↦ₛ hPk) = ((sp + 4432#64) ↦ₛ (m' ++ hPk)) := by
    rw [pointsToBytes_append, hm', show sp + 4432#64 + BitVec.ofNat 64 32 = sp + 4464#64 by bv_omega]
  have hsl : Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64)
      (m' ++ hPk).length (m' ++ hPk).length =
      ((sp + 22400#64) ↦₆₄ (sp + 4432#64)) ∗ ((sp + 22408#64) ↦₆₄ 64#64) ∗
      ((sp + 22416#64) ↦₆₄ (sp + 4432#64)) ∗ ((sp + 22424#64) ↦₆₄ 64#64) := by
    simp [Keccak2SlicesRW, hm', hhPk]
  rw [hsl]
  refine entails_sub (vecRangeMem_entails_memRegion 4 (sp + 5680#64) _) (by sep_frame) ?_
  rw [← hmh]
  sep_frame

private theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0; let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1; rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem vec4_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    let v0 := bytesToVecNat bs 0; let v1 := bytesToVecNat bs 1
    let v2 := bytesToVecNat bs 2; let v3 := bytesToVecNat bs 3
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64) ∗
      ((ptr + 32#64) ↦₆₄ v2.extractLsb' 0 64) ∗ ((ptr + 40#64) ↦₆₄ v2.extractLsb' 64 64) ∗
      ((ptr + 48#64) ↦₆₄ v3.extractLsb' 0 64) ∗ ((ptr + 56#64) ↦₆₄ v3.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1 v2 v3; rw [pointsToBytes_eq_vecRangeMem 4 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, v2, v3, Nat.zero_add]
  simp only [show (ptr + 16#64) + 8#64 = ptr + 24#64 by bv_omega,
    show (ptr + 16#64) + 16#64 = ptr + 32#64 by bv_omega,
    show (ptr + 32#64) + 8#64 = ptr + 40#64 by bv_omega,
    show (ptr + 32#64) + 16#64 = ptr + 48#64 by bv_omega,
    show (ptr + 48#64) + 8#64 = ptr + 56#64 by bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

attribute [local irreducible] bytesToVecNat

@[simp, arm64_norm, wp_norm] private abbrev off3c58 : BitVec 64 := BitVec.ofNat 64 15448
private abbrev off3c5c : BitVec 64 := BitVec.ofNat 64 15452
private abbrev off3cc8 : BitVec 64 := BitVec.ofNat 64 15560

/-! ## 2. `B00` (`SHA3-512`), `B01` (`SHAKE-256_32`), & Zeroing (`+0x3c28 → +0x3cec`) -/

private theorem seg4a_b00_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (msg : List (BitVec 8)) (Rest : SepProp)
    (hmsg : msg.length = 64)
    (hpc : s.pc = b + off3c28) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 22400#64) (hx1 : s.readReg64 .x1 = sp + 5680#64)
    (hx2 : s.readReg64 .x2 = sp + 11856#64) (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3c58) s
      (Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64) msg.length msg.length ∗
        ((sp + 4432#64) ↦ₛ msg) ∗ memRegion (sp + 4496#64) 64 ∗ memRegion (sp + 5680#64) 64 ∗
        memRegion (sp + 11856#64) 1120 ∗ stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 11888#64 ∧ (sm.readReg32 .x1).truncate 8 = 0#8 ∧
        (sm.readReg64 .x2).toNat = 1088 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ ((sp + 4496#64) ↦ₛ sha3_512List msg) ∗ memRegion (sp + 4432#64) 64 ∗
          memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 32 ∗
          memRegion (sp + 11888#64) 1088 ∗ memRegion (sp + 22400#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have hmsg_lt : msg.length < 72 := by omega
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  nth_rw 1 [memRegion_split' (b := sp + 4496#64) (b' := sp + 4528#64) (n := 32) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  nth_rw 1 [memRegion_split' (b := sp + 11856#64) (b' := sp + 11920#64) (n := 64) (k := (1056 : Nat)) rfl (by bv_omega) (by decide)]
  nth_rw 1 [stackAt_shrink sp 1136 720 (by decide)]
  wp_step
  have hro1 : MlKemRoOk mlkemMpl
      ((s.writeReg64 .lr (blkPl04.base + BitVec.ofNat 64 15404)).setPC (mlkemMpl.base 0)).mem := hro
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk00_04 blkPl04.base)
    (sp + 22400#64, sp + 4432#64, sp + 5680#64, sp + 11856#64, msg)
  apply SepWP.done (by assumption) (by assumption)
  intro hcl_c1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hsp_al1 : sf.spAligned = true := spAligned_of_sp_eq hsp_al hsp hsp1
  have hx20_1 : sf.readReg64 .x20 = s.readReg64 .x20 := ‹_›
  have hx21_1 : sf.readReg64 .x21 = sp + 11856#64 := Eq.trans ‹_› hx21
  have hx23_1 : sf.readReg64 .x23 = s.readReg64 .x23 := ‹_›
  have hx26_1 : sf.readReg64 .x26 = s.readReg64 .x26 := ‹_›
  have hx28_1 : sf.readReg64 .x28 = s.readReg64 .x28 := ‹_›
  have hfp_1 : sf.readReg64 .fp = s.readReg64 .fp := hcs_sf
  set kr := sha3_512List msg
  have hkr : kr.length = 64 := sha3_512List_length msg
  have ho1_m : ((sp + 11856#64) ↦ₛ kr) ∗ memRegion (sp + 11920#64) 1056 ⊢
      memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 1088 := by
    have h1 : ((sp + 11856#64) ↦ₛ kr) ⊢ memRegion (sp + 11856#64) 64 := by
      simpa [hkr] using pointsToBytes_entails_memRegion (sp + 11856#64) kr
    refine Entails.trans (sepConj_mono_left h1) ?_
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11888#64) (b' := sp + 11920#64) (n := 32) (k := (1056 : Nat)) rfl (by bv_omega) (by decide)]
    sep_frame
  have hsl : Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64) msg.length msg.length ⊢
      memRegion (sp + 22400#64) 32 := by
    unfold Keccak2SlicesRW; exact cells32_entails_memRegion (sp + 22400#64) _ _ _ _
  have hm_m : ((sp + 4432#64) ↦ₛ msg) ⊢ memRegion (sp + 4432#64) 64 := by
    simpa [hmsg] using pointsToBytes_entails_memRegion (sp + 4432#64) msg
  refine SepWP.weaken_pre (P' :=
      memRegion (sp + 4496#64) 32 ∗ memRegion (sp + 4528#64) 32 ∗ ((sp + 5680#64) ↦ₛ kr) ∗
      (memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 11888#64) 1088 ∗
        memRegion (sp + 22400#64) 32 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub ho1_m (by sep_frame)
      (entails_sub hsl (by sep_frame) (entails_sub hm_m (by sep_frame) (by rw [hsp]; sep_frame)))) ?_
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4496#64)); intro d0 d1 d2 d3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4528#64)); intro d4 d5 d6 d7
  have hkr5 := vec4_cells_eq_bytes (sp + 5680#64) hkr
  simp only [show sp + 5680#64 + 8#64 = sp + 5688#64 by bv_omega, show sp + 5680#64 + 16#64 = sp + 5696#64 by bv_omega,
    show sp + 5680#64 + 24#64 = sp + 5704#64 by bv_omega, show sp + 5680#64 + 32#64 = sp + 5712#64 by bv_omega,
    show sp + 5680#64 + 40#64 = sp + 5720#64 by bv_omega, show sp + 5680#64 + 48#64 = sp + 5728#64 by bv_omega,
    show sp + 5680#64 + 56#64 = sp + 5736#64 by bv_omega] at hkr5
  rw [← hkr5]
  simp only [show sp + 4496#64 + 8#64 = sp + 4504#64 by bv_omega, show sp + 4496#64 + 16#64 = sp + 4512#64 by bv_omega,
    show sp + 4496#64 + 24#64 = sp + 4520#64 by bv_omega, show sp + 4528#64 + 8#64 = sp + 4536#64 by bv_omega,
    show sp + 4528#64 + 16#64 = sp + 4544#64 by bv_omega, show sp + 4528#64 + 24#64 = sp + 4552#64 by bv_omega]
  refine MultiPlacedLib.seq_codeLoaded (mid := blkPl04.base + off3c58) hcl_c1 ?_
  wp_steps 11
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf]) fun hcl_m1 =>
    SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
      ⟨hcl_m1, by simp [hsp1], spAligned_of_sp_eq hsp_al hsp (by simp [hsp1]),
        by simp, by simp [State.readReg32], by simp,
        by simp [hx20_1], by simp [hx23_1], by simp [hx26_1], by simp [hx28_1], by simp [hfp_1], ?_⟩
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  simp only [htrunc]
  have hkr4 := vec4_cells_eq_bytes (sp + 4496#64) hkr
  simp only [show sp + 4496#64 + 8#64 = sp + 4504#64 by bv_omega, show sp + 4496#64 + 16#64 = sp + 4512#64 by bv_omega,
    show sp + 4496#64 + 24#64 = sp + 4520#64 by bv_omega, show sp + 4496#64 + 32#64 = sp + 4528#64 by bv_omega,
    show sp + 4496#64 + 40#64 = sp + 4536#64 by bv_omega, show sp + 4496#64 + 48#64 = sp + 4544#64 by bv_omega,
    show sp + 4496#64 + 56#64 = sp + 4552#64 by bv_omega] at hkr4
  have ho0_m : ((sp + 5680#64) ↦ₛ kr) ⊢ memRegion (sp + 5680#64) 64 := by
    simpa [hkr] using pointsToBytes_entails_memRegion (sp + 5680#64) kr
  rw [hkr5]
  conv_rhs => rw [← hkr4]
  exact entails_sub ho0_m (by sep_frame) (by sep_frame)

private theorem seg4a_zero_11888 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off3c58) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 11888#64)
    (hx1 : truncate 8 (s.readReg32 .x1) = 0#8)
    (hx2 : (s.readReg64 .x2).toNat = 1088)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3c5c) s
      (memRegion (sp + 11888#64) 1088 ∗ Rest)
      (fun sf Pf =>
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ memRegion (sp + 11888#64) 1088 ∗ Rest)) := by
  subst hbase
  wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk29_04 blkPl04.base) (sp + 11888#64, 0#8, 1088)
  apply SepWP.done (by assumption) (by assumption)
  intro hcl_c2
  have hsp2 : sf.sp = sp := hsp_sf.trans hsp
  refine SepWP.done hpc_sf hrun_sf
    ⟨hcl_c2, hsp2, spAligned_of_sp_eq hsp_al hsp hsp2, ‹_›, ‹_›, ‹_›, ‹_›, hcs_sf, ?_⟩
  exact entails_sub (replicate_entails_memRegion (sp + 11888#64) 1088) (by sep_frame) (by sep_frame)

private theorem seg4a_copy_zct [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp zPtr : BitVec 64) (z ct : List (BitVec 8)) (Rest : SepProp)
    (hz : z.length = 32) (_hct : ct.length = 1088)
    (hpc : s.pc = b + off3c5c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3c84) s
      (memRegion (sp + 4560#64) 32 ∗ memRegion (sp + 4592#64) 1088 ∗
        ((sp + 1856#64) ↦₆₄ zPtr) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = sp + 4560#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 4560#64) ↦ₛ (z ++ ct)) ∗ ((sp + 1856#64) ↦₆₄ zPtr) ∗
          ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4560#64)); intro z0 z1 z2 z3
  have hzPtr2 := vec2_cells_eq_bytes zPtr hz
  dsimp only at hzPtr2
  rw [← hzPtr2]
  try simp only [show sp + 4560#64 + 8#64 = sp + 4568#64 by bv_omega,
    show sp + 4560#64 + 16#64 = sp + 4576#64 by bv_omega,
    show sp + 4560#64 + 24#64 = sp + 4584#64 by bv_omega]
  refine MultiPlacedLib.seq_codeLoaded (mid := blkPl04.base + BitVec.ofNat 64 15488) hcl ?_
  wp_steps 9
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) fun _ => ?_
  wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 4592#64, sp + 3344#64, ct)
  apply SepWP.done (by assumption) (by assumption)
  intro _
  have hsp3 : sf.sp = sp := hsp_sf.trans (by simp [hsp])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp3, spAligned_of_sp_eq hsp_al hsp hsp3,
      Eq.trans ‹_› (by simp), Eq.trans ‹_› (by simp), Eq.trans ‹_› (by simp),
      Eq.trans ‹_› (by simp), Eq.trans ‹_› (by simp), Eq.trans hcs_sf (by simp), ?_⟩
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  simp only [htrunc]
  have hz2 := vec2_cells_eq_bytes (sp + 4560#64) hz
  dsimp only at hz2
  simp only [show sp + 4560#64 + 8#64 = sp + 4568#64 by bv_omega,
    show sp + 4560#64 + 16#64 = sp + 4576#64 by bv_omega, show sp + 4560#64 + 24#64 = sp + 4584#64 by bv_omega] at hz2
  have hzct : ((sp + 4560#64) ↦ₛ z) ∗ ((sp + 4592#64) ↦ₛ ct) = ((sp + 4560#64) ↦ₛ (z ++ ct)) := by
    rw [pointsToBytes_append, hz, show sp + 4560#64 + BitVec.ofNat 64 32 = sp + 4592#64 by bv_omega]
  rw [← hzct, ← hz2]
  sep_frame

theorem seg4a_hashes_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp zPtr : BitVec 64) (msg z ct : List (BitVec 8)) (Rest : SepProp)
    (hmsg : msg.length = 64) (hz : z.length = 32) (hct : ct.length = 1088)
    (hpc : s.pc = b + off3c28) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 22400#64) (hx1 : s.readReg64 .x1 = sp + 5680#64)
    (hx2 : s.readReg64 .x2 = sp + 11856#64) (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3c84) s
      (Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64) msg.length msg.length ∗
        ((sp + 4432#64) ↦ₛ msg) ∗ memRegion (sp + 4496#64) 1184 ∗ memRegion (sp + 5680#64) 64 ∗
        memRegion (sp + 11856#64) 1120 ∗ ((sp + 1856#64) ↦₆₄ zPtr) ∗
        ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗ stackAt sp 1136 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧ s3.readReg64 .x20 = s.readReg64 .x20 ∧
        s3.readReg64 .x21 = sp + 4560#64 ∧ s3.readReg64 .x23 = s.readReg64 .x23 ∧
        s3.readReg64 .x26 = s.readReg64 .x26 ∧ s3.readReg64 .x28 = s.readReg64 .x28 ∧
        s3.readReg64 .fp = s.readReg64 .fp ∧
        (P3 ⊢ ((sp + 4496#64) ↦ₛ sha3_512List msg) ∗ ((sp + 4560#64) ↦ₛ (z ++ ct)) ∗
          memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 5680#64) 64 ∗
          memRegion (sp + 11856#64) 1120 ∗ memRegion (sp + 22400#64) 32 ∗
          ((sp + 1856#64) ↦₆₄ zPtr) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗
          stackAt sp 1136 ∗ Rest)) := by
  have h4496 : memRegion (sp + 4496#64) 1184 =
      memRegion (sp + 4496#64) 64 ∗ memRegion (sp + 4560#64) 32 ∗ memRegion (sp + 4592#64) 1088 := by
    rw [memRegion_split' (b := sp + 4496#64) (b' := sp + 4560#64) (n := 64) (k := (1120 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4560#64) (b' := sp + 4592#64) (n := 32) (k := (1088 : Nat)) rfl (by bv_omega) (by decide)]
  have hpre : Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64) msg.length msg.length ∗
      ((sp + 4432#64) ↦ₛ msg) ∗ memRegion (sp + 4496#64) 1184 ∗ memRegion (sp + 5680#64) 64 ∗
      memRegion (sp + 11856#64) 1120 ∗ ((sp + 1856#64) ↦₆₄ zPtr) ∗
      ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗ stackAt sp 1136 ∗ Rest ⊢
      Keccak2SlicesRW (sp + 22400#64) (sp + 4432#64) (sp + 4432#64) msg.length msg.length ∗
      ((sp + 4432#64) ↦ₛ msg) ∗ memRegion (sp + 4496#64) 64 ∗ memRegion (sp + 5680#64) 64 ∗
      memRegion (sp + 11856#64) 1120 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 4560#64) 32 ∗ memRegion (sp + 4592#64) 1088 ∗
        ((sp + 1856#64) ↦₆₄ zPtr) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗ Rest) := by
    rw [h4496]; sep_frame
  refine SepWP.weaken_pre hpre (SepWP.seq
    (seg4a_b00_copy hb hbase s sp msg _ hmsg hpc hrun hsp hsp_al hx0 hx1 hx2 hx21 hcl hro) ?_)
  rintro sm Pm hpcm hrunm ⟨hclm, hspm, hspAm, hx0m, hx1m, hx2m, hx20m, hx23m, hx26m, hx28m, hfpm, hPm⟩
  refine SepWP.weaken_pre (Entails.trans hPm (show _ ⊢
      memRegion (sp + 11888#64) 1088 ∗
      (memRegion (sp + 4560#64) 32 ∗ memRegion (sp + 4592#64) 1088 ∗
        ((sp + 1856#64) ↦₆₄ zPtr) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗
        ((sp + 4496#64) ↦ₛ sha3_512List msg) ∗ memRegion (sp + 4432#64) 64 ∗
        memRegion (sp + 5680#64) 64 ∗ memRegion (sp + 11856#64) 32 ∗
        memRegion (sp + 22400#64) 32 ∗ stackAt sp 1136 ∗ Rest) by sep_frame))
    (SepWP.seq (seg4a_zero_11888 hb hbase sm sp _ hpcm hrunm hspm hspAm hx0m hx1m hx2m hclm) ?_)
  rintro s2 P2 hpc2 hrun2 ⟨hcl2, hsp2, hspA2, hx20_2, hx23_2, hx26_2, hx28_2, hfp_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
      memRegion (sp + 4560#64) 32 ∗ memRegion (sp + 4592#64) 1088 ∗
      ((sp + 1856#64) ↦₆₄ zPtr) ∗ ((sp + 3344#64) ↦ₛ ct) ∗ (zPtr ↦ₛ z) ∗
      (memRegion (sp + 11888#64) 1088 ∗ ((sp + 4496#64) ↦ₛ sha3_512List msg) ∗
        memRegion (sp + 4432#64) 64 ∗ memRegion (sp + 5680#64) 64 ∗
        memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 22400#64) 32 ∗ stackAt sp 1136 ∗ Rest) by sep_frame))
    (SepWP.mono (seg4a_copy_zct hb hbase s2 sp zPtr z ct _ hz hct hpc2 hrun2 hsp2 hspA2 hcl2) ?_)
  rintro s3 P3 _ _ ⟨hsp3, hspA3, hx20_3, hx21_3, hx23_3, hx26_3, hx28_3, hfp_3, hP3⟩
  refine ⟨hsp3, hspA3, hx20_3.trans (hx20_2.trans hx20m), hx21_3,
    hx23_3.trans (hx23_2.trans hx23m), hx26_3.trans (hx26_2.trans hx26m),
    hx28_3.trans (hx28_2.trans hx28m), hfp_3.trans (hfp_2.trans hfpm),
    Entails.trans hP3 ?_⟩
  rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (1088 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame

theorem seg4a_prep_b01 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (zct : List (BitVec 8)) (Rest : SepProp)
    (hzct : zct.length = 1120)
    (hpc : s.pc = b + off3c84) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = sp + 4560#64)
    (hfp : s.readReg64 .fp = sp + 25728#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3cc4) s
      (memRegion (sp + 11856#64) 32 ∗ memRegion (sp + 25616#64) 32 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x0 = sp + 11856#64 ∧ s3.readReg64 .x1 = sp + 25616#64 ∧
        s3.readReg64 .x2 = 32#64 ∧ s3.readReg64 .x3 = sp + 5680#64 ∧
        s3.readReg64 .x4 = 32#64 ∧ s3.readReg64 .x20 = s.readReg64 .x20 ∧
        s3.readReg64 .x21 = sp + 11856#64 ∧ s3.readReg64 .x23 = s.readReg64 .x23 ∧
        s3.readReg64 .x26 = s.readReg64 .x26 ∧ s3.readReg64 .x28 = s.readReg64 .x28 ∧
        s3.readReg64 .fp = sp + 25728#64 ∧
        (P3 ⊢ Keccak2SlicesRW (sp + 11856#64) (sp + 4560#64) (sp + 4560#64) zct.length zct.length ∗
          memRegion (sp + 25616#64) 32 ∗ Rest)) := by
  subst hbase
  sep_frame_apply (sepWP_elim_region32 (a := sp + 11856#64)); intro c0 c1 c2 c3
  apply SepWP.of_memRegion_vecRangeMem 2 (sp + 25616#64) (hf := by sep_focus); intro fk
  wp_steps 12
  refine step_stpQ128 (pc := _) (wb := none) (ea := sp + 25616#64) (ea16 := sp + 25616#64 + 16#64)
    (v1 := 0#128) (v2 := 0#128) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hfp]) rfl (by simp) (by simp)
    (SepStore128.left (SepStore128.vecRange (k := 0) (by decide) (by clear * -; bv_omega)))
    (SepStore128.left (SepStore128.vecRange (k := 1) (by decide) (by clear * -; bv_omega)))
    (by wp_norm_lhs) fun _ => ?_
  wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hsp_al hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp [hfp], ?_⟩
  have hsl : Keccak2SlicesRW (sp + 11856#64) (sp + 4560#64) (sp + 4560#64) zct.length zct.length =
      ((sp + 11856#64) ↦₆₄ (sp + 4560#64)) ∗ ((sp + 11856#64 + 8#64) ↦₆₄ 1120#64) ∗
      ((sp + 11856#64 + 16#64) ↦₆₄ (sp + 4560#64)) ∗ ((sp + 11856#64 + 24#64) ↦₆₄ 1120#64) := by
    simp [Keccak2SlicesRW, hzct]
  rw [hsl]
  exact entails_sub (vecRangeMem_entails_memRegion 2 (sp + 25616#64) _) (by sep_frame) (by sep_frame)

theorem seg4a_call_b01 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (zct : List (BitVec 8)) (Rest : SepProp)
    (hzct : zct.length = 1120)
    (hpc : s.pc = b + off3cc4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_al : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 11856#64) (hx1 : s.readReg64 .x1 = sp + 25616#64)
    (hx2 : s.readReg64 .x2 = 32#64) (hx3 : s.readReg64 .x3 = sp + 5680#64)
    (hx4 : s.readReg64 .x4 = 32#64) (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg4aEnd) s
      (Keccak2SlicesRW (sp + 11856#64) (sp + 4560#64) (sp + 4560#64) zct.length zct.length ∗
        ((sp + 4560#64) ↦ₛ zct) ∗ memRegion (sp + 25616#64) 32 ∗ memRegion (sp + 5680#64) 32 ∗
        memRegion (sp + 192#64) 8 ∗ memRegion (sp + 12368#64) 5664 ∗ stackAt sp 1136 ∗ Rest)
      (fun s4 P4 =>
        s4.sp = sp ∧ s4.spAligned = true ∧ s4.readReg64 .x20 = s.readReg64 .x20 ∧
        s4.readReg64 .x23 = s.readReg64 .x23 ∧ s4.readReg64 .x26 = s.readReg64 .x26 ∧
        s4.readReg64 .x28 = s.readReg64 .x28 ∧ s4.readReg64 .fp = s.readReg64 .fp ∧
        (P4 ⊢ ((sp + 192#64) ↦₆₄ (sp + 13392#64)) ∗ ((sp + 25616#64) ↦ₛ shake256List 32 zct) ∗
          memRegion (sp + 4560#64) 1152 ∗ memRegion (sp + 11856#64) 32 ∗
          memRegion (sp + 12368#64) 5664 ∗ stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have hzct_lt : zct.length < 2 ^ 32 := by omega
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hsp_al
  nth_rw 1 [memRegion_split' (b := sp + 12368#64) (b' := sp + 18000#64) (n := 5632) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 192#64)); intro c192
  sep_frame_apply (sepWP_elim_region32 (a := sp + 18000#64)); intro fz0 fz1 fz2 fz3
  wp_step
  have hro1 : MlKemRoOk mlkemMpl
      ((s.writeReg64 .lr (blkPl04.base + BitVec.ofNat 64 15560)).setPC (mlkemMpl.base 1)).mem := hro
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk01_04 blkPl04.base)
    (sp + 11856#64, sp + 4560#64, sp + 25616#64, sp + 5680#64, (32 : Nat), zct)
  apply SepWP.done (by assumption) (by assumption)
  intro hcl_c1
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hsp_al1 : sf.spAligned = true := spAligned_of_sp_eq hsp_al hsp hsp1
  have hx20_1 : sf.readReg64 .x20 = s.readReg64 .x20 := ‹_›
  have hx21_1 : sf.readReg64 .x21 = sp + 11856#64 := Eq.trans ‹_› hx21
  have hx23_1 : sf.readReg64 .x23 = s.readReg64 .x23 := ‹_›
  have hx26_1 : sf.readReg64 .x26 = s.readReg64 .x26 := ‹_›
  have hx28_1 : sf.readReg64 .x28 = s.readReg64 .x28 := ‹_›
  have hfp_1 : sf.readReg64 .fp = s.readReg64 .fp := hcs_sf
  try simp only [show sp + 18000#64 + 8#64 = sp + 18008#64 by bv_omega,
    show sp + 18000#64 + 16#64 = sp + 18016#64 by bv_omega, show sp + 18000#64 + 24#64 = sp + 18024#64 by bv_omega]
  refine MultiPlacedLib.seq_codeLoaded (mid := blkPl04.base + BitVec.ofNat 64 15592) ‹_› ?_
  wp_steps 8
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf]) fun hcl_m1 => ?_
  wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk29_04 blkPl04.base) (sp + 12368#64, 0#8, (5632 : Nat))
  apply SepWP.done (by assumption) (by assumption)
  intro hcl_c2
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans (by simp [hsp1])
  refine SepWP.done hpc_sf_1 hrun_sf_1
    ⟨hsp2, spAligned_of_sp_eq hsp_al hsp hsp2,
      Eq.trans ‹_› (by simp [hx20_1]),
      Eq.trans ‹_› (by simp [hx23_1]),
      Eq.trans ‹_› (by simp [hx26_1]),
      Eq.trans ‹_› (by simp [hx28_1]),
      Eq.trans hcs_sf_1 (by simp [hfp_1]), ?_⟩
  rw [memRegion_split' (b := sp + 4560#64) (b' := sp + 5680#64) (n := 1120) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12368#64) (b' := sp + 18000#64) (n := 5632) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  have hsl : Keccak2SlicesRW (sp + 11856#64) (sp + 4560#64) (sp + 4560#64) zct.length zct.length ⊢
      memRegion (sp + 11856#64) 32 := by
    unfold Keccak2SlicesRW; exact cells32_entails_memRegion (sp + 11856#64) _ _ _ _
  have hzct_m : ((sp + 4560#64) ↦ₛ zct) ⊢ memRegion (sp + 4560#64) 1120 := by
    simpa [hzct] using pointsToBytes_entails_memRegion (sp + 4560#64) zct
  have ho1_m : ((sp + 5680#64) ↦ₛ shake256List 32 zct) ⊢ memRegion (sp + 5680#64) 32 := by
    simpa [shake256List_len] using pointsToBytes_entails_memRegion (sp + 5680#64) (shake256List 32 zct)
  have hm5632 : ((sp + 12368#64) ↦ₛ List.replicate 5632 0#8) ⊢ memRegion (sp + 12368#64) 5632 :=
    replicate_entails_memRegion (sp + 12368#64) 5632
  have hm32 : ((sp + 18000#64) ↦₆₄ 0#64) ∗ ((sp + 18008#64) ↦₆₄ 0#64) ∗
      ((sp + 18016#64) ↦₆₄ 0#64) ∗ ((sp + 18024#64) ↦₆₄ 0#64) ⊢ memRegion (sp + 18000#64) 32 := by
    simpa [show sp + 18000#64 + 8#64 = sp + 18008#64 by bv_omega,
      show sp + 18000#64 + 16#64 = sp + 18016#64 by bv_omega,
      show sp + 18000#64 + 24#64 = sp + 18024#64 by bv_omega] using
      cells32_entails_memRegion (sp + 18000#64) 0#64 0#64 0#64 0#64
  exact entails_sub hsl (by sep_frame)
    (entails_sub hzct_m (by sep_frame)
      (entails_sub ho1_m (by sep_frame)
        (entails_sub hm5632 (by sep_frame)
          (entails_sub hm32 (by sep_frame) (by rw [hsp]; sep_frame)))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4a
