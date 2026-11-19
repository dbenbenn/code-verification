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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5Epi

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 Entry Ops and `rHat` SWAR `cbd2`

Proves `seg6_entry_ops` (`+0x76a8 → +0x7718`) and `seg6_cbd2_rhat_loop` (`+0x7ad4 → +0x7c04`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl
  resolve_blk28 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (
  blk28_memcpy_ok blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sampleNtt shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  PublicKeyStateAt cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq
  pkStateBytes pkStateBytes_length publicKeyStateAt_eq_pointsToBytes sepWP_elim_byte
  setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64 step_bCond_not_taken step_bCond_taken
  truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8 vec2_bytesToVecNat_eq
  vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06
  [0x76ac → 0x7714, 0x7ad4 → 0x7c00]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

private theorem blk28_memcpy_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk28_memcpy_ok

private theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC06 sampleNtt shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 ubfx2_w32_norm truncate32_zext64 setWidth32_shr_zext64

/-! ## 1. Entry `memcpy` & `memset` Operations (`+0x76a8 → +0x7718`) -/

@[simp, arm64_norm, wp_norm] abbrev off76a8 : BitVec 64 := BitVec.ofNat 64 30376
@[simp, arm64_norm, wp_norm] abbrev off76cc : BitVec 64 := BitVec.ofNat 64 30412
@[simp, arm64_norm, wp_norm] abbrev off76e0 : BitVec 64 := BitVec.ofNat 64 30432
@[simp, arm64_norm, wp_norm] abbrev off7718 : BitVec 64 := BitVec.ofNat 64 30488

private theorem vecRangeBytes_zero : ∀ n : Nat,
    vecRangeBytes n (fun _ => 0#128) = List.replicate (16 * n) (0#8)
  | 0 => rfl
  | n + 1 => by
    rw [vecRangeBytes, vecRangeBytes_zero n, show 16 * (n + 1) = 16 + 16 * n by omega,
      List.replicate_add]
    rfl

private theorem hz4_26320 (sp : BitVec 64) :
    ((sp + 26320#64) ↦ₛ List.replicate 2048 0#8) =
      PolyMem (sp + 26320#64) (fun _ => 0#128) ∗
      PolyMem (sp + 26832#64) (fun _ => 0#128) ∗
      PolyMem (sp + 27344#64) (fun _ => 0#128) ∗
      PolyMem (sp + 27856#64) (fun _ => 0#128) := by
  have hrep : List.replicate 2048 (0#8) =
      vecRangeBytes 32 (fun _ => 0#128) ++
      (vecRangeBytes 32 (fun _ => 0#128) ++
       (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128))) := by
    rw [vecRangeBytes_zero 32, show (2048 : Nat) = 512 + (512 + (512 + 512)) from rfl,
      List.replicate_add, List.replicate_add, List.replicate_add]
  unfold PolyMem
  rw [hrep, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    vecRangeBytes_length,
    ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
    ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
  simp only [
    show sp + 26320#64 + BitVec.ofNat 64 (16 * 32) = sp + 26832#64 by bv_omega,
    show sp + 26832#64 + BitVec.ofNat 64 (16 * 32) = sp + 27344#64 by bv_omega,
    show sp + 27344#64 + BitVec.ofNat 64 (16 * 32) = sp + 27856#64 by bv_omega]

section
attribute [local irreducible] PolyMem PublicKeyStateAt

theorem seg6_entry_ops [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (pk hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + off76a8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let coins := hashed.drop 32
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off7718) s
      (((sp + 2496#64) ↦ₛ hashed) ∗
       memRegion (sp + 4160#64) 10272 ∗
       PublicKeyStateAt (sp + 14432#64) pk ∗
       memRegion (sp + 24704#64) 1568 ∗
       memRegion (sp + 26272#64) 33 ∗
       memRegion (sp + 26320#64) 2048 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x21 = sp + 14432#64 ∧
        sm.readReg64 .x22 = sp + 26320#64 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗
          PublicKeyStateAt (sp + 4160#64) pk ∗
          memRegion (sp + 14432#64) 10272 ∗
          memRegion (sp + 24704#64) 1568 ∗
          ((sp + 26272#64) ↦ₛ coins) ∗
          ((sp + 26304#64) ↦₈ 0#8) ∗
          PolyMem (sp + 26320#64) (fun _ => 0#128) ∗
          PolyMem (sp + 26832#64) (fun _ => 0#128) ∗
          PolyMem (sp + 27344#64) (fun _ => 0#128) ∗
          PolyMem (sp + 27856#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins
  subst hbase
  have htake_len : (hashed.take 32).length = 32 := by simp [hh]
  have hcoins_len : coins.length = 32 := by simp [coins, hh]
  have hh_split : ((sp + 2496#64) ↦ₛ hashed) =
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗ ((sp + 2528#64) ↦ₛ coins) := by
    conv_lhs => rw [← List.take_append_drop 32 hashed]
    rw [pointsToBytes_append, htake_len,
      show sp + 2496#64 + BitVec.ofNat 64 32 = sp + 2528#64 by bv_omega]
  have hpks_len := pkStateBytes_length pk
  rw [publicKeyStateAt_eq_pointsToBytes (sp + 14432#64) pk]
  have hc1 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off76cc) s
      (((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 4160#64) 10272 ∗
        ((sp + 14432#64) ↦ₛ pkStateBytes pk) ∗ memRegion (sp + 24704#64) 1568 ∗
        memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26320#64) 2048 ∗
        stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        mlkemMultiLib.CodeLoaded mlkemMpl s1.mem ∧ s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧ s1.readReg64 .x21 = sp + 14432#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        (P1 ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
          memRegion (sp + 14432#64) 10272 ∗ memRegion (sp + 24704#64) 1568 ∗
          memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26320#64) 2048 ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [← hpks_len]
    wp_steps 9
    refine seq_codeLoaded_lr hcl ?_
    wp_call (blk28_memcpy_06 blkPl06.base) (sp + 4160#64, sp + 14432#64, pkStateBytes pk)
    apply SepWP.done (by assumption) (by assumption); intro hcl_c1
    have hsp_sf : sf.sp = sp := by simp [*]
    refine SepWP.done ‹_› ‹_›
      ⟨hcl_c1, hsp_sf, spAligned_of_sp_eq hspA hsp hsp_sf,
        by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
    rw [← publicKeyStateAt_eq_pointsToBytes (sp + 4160#64) pk]
    have hsrc : ((sp + 14432#64) ↦ₛ pkStateBytes pk) ⊢ memRegion (sp + 14432#64) 10272 := by
      have h := pointsToBytes_entails_memRegion (sp + 14432#64) (pkStateBytes pk)
      rwa [hpks_len] at h
    exact entails_sub hsrc (by sep_frame) (by sep_frame)
  refine SepWP.seq hc1 ?_
  rintro s1 P1 hpc1 hrun1 ⟨hcl1, hsp1, hspA1, hx19_1, hx21_1, hx25_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc2 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off76e0) s1
      (((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
        memRegion (sp + 14432#64) 10272 ∗ memRegion (sp + 24704#64) 1568 ∗
        memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26320#64) 2048 ∗
        stackAt sp 1136 ∗ Rest)
      (fun s2 P2 =>
        mlkemMultiLib.CodeLoaded mlkemMpl s2.mem ∧ s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x21 = sp + 14432#64 ∧
        s2.readReg64 .x25 = s.readReg64 .x25 ∧ s2.readReg64 .fp = s.readReg64 .fp ∧
        (P2 ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
          memRegion (sp + 14432#64) 10272 ∗ memRegion (sp + 24704#64) 1568 ∗
          memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26320#64) 2048 ∗
          stackAt sp 1136 ∗ Rest)) := by
    wp_steps 5
    refine seq_codeLoaded_lr hcl1 ?_
    wp_call (blk29_memset_06 blkPl06.base) (sp + 24704#64, 0#8, 1568)
    apply SepWP.done (by assumption) (by assumption); intro hcl_c2
    have hsp_sf : sf.sp = sp := by simp [*]
    refine SepWP.done ‹_› ‹_›
      ⟨hcl_c2, hsp_sf, spAligned_of_sp_eq hspA1 hsp1 hsp_sf,
        by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
    have hm1568 : ((sp + 24704#64) ↦ₛ List.replicate 1568 0#8) ⊢
        memRegion (sp + 24704#64) 1568 := by
      simpa only [List.length_replicate] using
        pointsToBytes_entails_memRegion (sp + 24704#64) (List.replicate 1568 0#8)
    exact entails_sub hm1568 (by sep_frame) (by sep_frame)
  refine SepWP.seq hc2 ?_
  rintro s2 P2 hpc2 hrun2 ⟨hcl2, hsp2, hspA2, hx19_2, hx21_2, hx25_2, hfp2, hP2⟩
  have hc3 : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 30484) s2 P2
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x0 = sp + 26320#64 ∧ s3.readReg64 .x1 = 0#64 ∧ s3.readReg64 .x2 = 2048#64 ∧
        s3.readReg64 .x19 = 0x55555555#64 ∧ s3.readReg64 .x21 = sp + 14432#64 ∧
        s3.readReg64 .x22 = sp + 26320#64 ∧ s3.readReg64 .x25 = s.readReg64 .x25 ∧
        s3.readReg64 .fp = s.readReg64 .fp ∧
        (P3 ⊢ ((sp + 2496#64) ↦ₛ hashed) ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
          memRegion (sp + 14432#64) 10272 ∗ memRegion (sp + 24704#64) 1568 ∗
          ((sp + 26272#64) ↦ₛ coins) ∗ ((sp + 26304#64) ↦₈ 0#8) ∗
          memRegion (sp + 26320#64) 2048 ∗ stackAt sp 1136 ∗ Rest)) := by
    refine SepWP.weaken_pre hP2 ?_
    rw [memRegion_split' (b := sp + 26272#64) (b' := sp + 26288#64) (n := 16) (k := (17 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 26288#64) (b' := sp + 26304#64) (n := 16) (k := (1 : Nat))
          rfl (by bv_omega) (by decide)]
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 26272#64) (by decide) (by sep_focus); intro vc0
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 26288#64) (by decide) (by sep_focus); intro vc1
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    sep_frame_apply (sepWP_elim_byte (a := sp + 26304#64)); intro b0
    rw [hh_split, ← vec2_bytesToVecNat_eq (sp + 2528#64) hcoins_len]
    have hal_sp2 : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp2] using hspA2
    wp_steps 3
    refine step_ldpQ128 (wb := none) (ea := sp + 2528#64) (ea16 := sp + 2528#64 + 16#64)
      (v1 := bytesToVecNat coins 0) (v2 := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun2]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode]) rfl
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl)))))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.right (SepLoad128.vec128At rfl)))))))
      (by wp_norm_lhs) ?_
    wp_steps 6
    refine step_strQ128 (wb := none) (ea := sp + 26272#64) (val := bytesToVecNat coins 0)
      (by wp_norm_lhs) (by simp [hrun2]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp2, hal_sp2])
      (by simp [evalAddrMode, hsp2]) (by wp_norm_lhs)
      (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) fun _ => ?_
    try rw [setPC_setMem_collapse]
    wp_step
    refine step_strQ128 (wb := none) (ea := sp + 26288#64) (val := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun2]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp2, hal_sp2])
      (by simp [evalAddrMode, hsp2]) (by wp_norm_lhs)
      (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) fun _ => ?_
    try rw [setPC_setMem_collapse]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun2])
      ⟨by simp [hsp2], spAligned_of_sp_eq hspA2 hsp2 (by simp [hsp2]),
        by simp, by simp, by simp, by simp [hx19_2], by simp [hx21_2],
        by simp, by simp [hx25_2], by simp [hfp2], ?_⟩
    rw [vec2_bytesToVecNat_eq (sp + 2528#64) hcoins_len, ← hh_split]
    have hc26272 : Vec128At (sp + 26272#64) (bytesToVecNat coins 0) ∗
        Vec128At (sp + 26288#64) (bytesToVecNat coins 1) = ((sp + 26272#64) ↦ₛ coins) := by
      simpa [show sp + 26272#64 + 16#64 = sp + 26288#64 by bv_omega] using
        vec2_bytesToVecNat_eq (sp + 26272#64) hcoins_len
    exact entails_sub (Entails.of_eq hc26272) (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ _)
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl2 hc3 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hcl3, hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx19_3, hx21_3, hx22_3, hx25_3, hfp3, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  wp_step
  refine seq_codeLoaded_lr hcl3 ?_
  wp_call (blk29_memset_06 blkPl06.base) (sp + 26320#64, 0#8, 2048)
  apply SepWP.done (by assumption) (by assumption); intro _hcl_c4
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done ‹_› ‹_›
    ⟨hsp_sf, spAligned_of_sp_eq hspA3 hsp3 hsp_sf,
      by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], ?_⟩
  rw [hz4_26320 sp]
  sep_frame

end

/-! ## 2. `rHat` Scratch Zero & SWAR `cbd2` Loop (`+0x7ad4 → +0x7c04`) -/

@[simp, arm64_norm, wp_norm] abbrev offRhatCbdStart : BitVec 64 := BitVec.ofNat 64 31444
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdBody  : BitVec 64 := BitVec.ofNat 64 31588
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdBr    : BitVec 64 := BitVec.ofNat 64 31744
@[simp, arm64_norm, wp_norm] abbrev offRhatCbdEnd   : BitVec 64 := BitVec.ofNat 64 31748

local macro "step_strQ14432 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg6_cbd2_rhat_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offRhatCbdBody) s
      (memRegion (sp + 14432#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x6 = 0#64 ∧ s1.readReg64 .x7 = s.readReg64 .x7 ∧
        s1.readReg64 .x8 = s.readReg64 .x7 ∧ s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x10 ∧
        s1.readReg64 .x12 = s.readReg64 .x12 ∧ s1.readReg64 .x13 = s.readReg64 .x13 ∧
        s1.readReg64 .x14 = s.readReg64 .x14 ∧ s1.readReg64 .x15 = s.readReg64 .x15 ∧
        s1.readReg64 .x16 = s.readReg64 .x16 ∧ s1.readReg64 .x17 = s.readReg64 .x17 ∧
        s1.readReg64 .x18 = s.readReg64 .x18 ∧ s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 14432#64) 512 ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 14432#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 14432#64) f = PolyMem (sp + 14432#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ14432 31; step_strQ14432 30; step_strQ14432 29; step_strQ14432 28
  step_strQ14432 27; step_strQ14432 26; step_strQ14432 25; step_strQ14432 24
  step_strQ14432 23; step_strQ14432 22; step_strQ14432 21; step_strQ14432 20
  step_strQ14432 19; step_strQ14432 18; step_strQ14432 17; step_strQ14432 16
  step_strQ14432 15; step_strQ14432 14; step_strQ14432 13; step_strQ14432 12
  step_strQ14432 11; step_strQ14432 10; step_strQ14432 9;  step_strQ14432 8
  step_strQ14432 7;  step_strQ14432 6;  step_strQ14432 5;  step_strQ14432 4
  step_strQ14432 3;  step_strQ14432 2;  step_strQ14432 1;  step_strQ14432 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_cbd_strh " cellPtr:ident hx21Id:term:arg hx6Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx21Id:term, $hx6Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg6_cbd2_rhat_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offRhatCbdBody) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if k < 31 then b + offRhatCbdBody else b + offRhatCbdEnd) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x6 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x7 = s.readReg64 .x7 ∧
        s'.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x21 = dstPtr ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest)) := by
  subst hbase
  obtain ⟨Fk, hsplit, hupd⟩ := vecRangeMem_focus hk dstPtr f
  let cellPtr := dstPtr + BitVec.ofNat 64 (16 * k)
  let w := readU32LE prf k
  rw [hsplit, vec128At_eq_halfRangeMem8 cellPtr (f k),
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗
        (HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗ Fk) ∗ Rest =
      HalfRangeMem 8 cellPtr (fun j => lane16 (f k) ⟨j % 8, Nat.mod_lt _ (by decide)⟩) ∗
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest by
      simp only [sepConj_assoc]; rw [sepConj_left_comm (WordRangeMem 32 prfPtr (readU32LE prf))]]
  refine SepWP.step_ldur32 (wb := none) (ea := prfPtr + BitVec.ofNat 64 (4 * k)) (v := w)
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_cbd_strh cellPtr hx21 hx6 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx6 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx6 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx6 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx21 hx6 6 (cbd2CoeffFromWord w 6)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  have hmem_eq : ∀ hFin : Nat → BitVec 16,
      (∀ j (hj : j < 8), hFin j = cbd2CoeffFromWord w ⟨j, hj⟩) →
      HalfRangeMem 8 cellPtr hFin ∗ WordRangeMem 32 prfPtr (readU32LE prf) ∗ Fk ∗ Rest =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗
          VecRangeMem 32 dstPtr (Function.update f k (polyVecNat (neonCbd2Poly16 prf) k)) ∗ Rest := by
    intro hFin hhFin
    rw [halfRangeMem8_cbd2_eq cellPtr prf k hk hFin hhFin,
      sepConj_left_comm (Vec128At cellPtr _), ← sepConj_assoc (Vec128At cellPtr _) Fk Rest,
      hupd]
  by_cases hk31 : k < 31
  · simp only [hk31, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl06.base + offRhatCbdBody)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offRhatCbdBr, offRhatCbdBody]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega, by simp,
        by simp; clear * -; bv_omega, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx21], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl06.base + offRhatCbdEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offRhatCbdBr, offRhatCbdEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp,
        by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx21], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩


private theorem seg6_cbd2_rhat_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offRhatCbdBody else b + offRhatCbdEnd) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x6 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offRhatCbdEnd) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
          s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
          s'.readReg64 .x7 = s.readReg64 .x7 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
          s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
          s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
          s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x21 = dstPtr ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx21
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hx19, hx21, rfl, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx6 hx8 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + offRhatCbdBody else b + offRhatCbdEnd) =
        (if k + 1 < 32 then b + offRhatCbdBody else b + offRhatCbdEnd) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (seg6_cbd2_rhat_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx6 hx8 hx19 hx21)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hr2, hr3, hr4, hr5, hx6_1, hr7, hx8_1,
        hr9, hr10, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hx21_1, hr22, hfp1, hv3_1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (ih (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx6_1 hx8_1 hx19_1 hx21_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, gx21, g22, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2
        ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g2.trans hr2, g3.trans hr3,
          g4.trans hr4, g5.trans hr5, g7.trans hr7, g9.trans hr9, g10.trans hr10,
          g12.trans hr12, g13.trans hr13, g14.trans hr14, g15.trans hr15, g16.trans hr16,
          g17.trans hr17, g18.trans hr18, gx19, gx21, g22.trans hr22, gfp.trans hfp1,
          gv3.trans hv3_1, hP2⟩

theorem seg6_cbd2_rhat_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + offRhatCbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx7 : s.readReg64 .x7 = prfPtr + 1#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offRhatCbdEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 14432#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x7 = prfPtr + 1#64 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x21 = sp + 14432#64 ∧ s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 14432#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 14432#64) 512 ∗ Rest =
      memRegion (sp + 14432#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (seg6_cbd2_rhat_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, hx6_1, r7, hx8_1,
      r9, r10, r12, r13, r14, r15, r16, r17, r18, r19, r21, r22, rfp, rv3, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    apply SepWP.of_memRegion_vecRangeMem 32 (sp + 14432#64) (hf := by sep_focus); intro f
    rw [show VecRangeMem 32 (sp + 14432#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
      WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 14432#64) f ∗ Rest by
      rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 14432#64) f), sepConj_assoc]]
    refine SepWP.seq
      (seg6_cbd2_rhat_steps hb hbase sp prfPtr (sp + 14432#64) prf Rest 32 0 rfl s1 f
        (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx6_1
        (by simp [hx8_1, hx7]) (r19.trans hx19) (r21.trans hx21)) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
      g16, g17, g18, gx19, gx21, g22, gfp, gv3, hP2⟩
    exact SepWP.done hpc2 hrun2
      ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g2.trans r2, g3.trans r3,
        g4.trans r4, g5.trans r5, g7.trans (r7.trans hx7), g9.trans r9, g10.trans r10,
        g12.trans r12, g13.trans r13, g14.trans r14, g15.trans r15, g16.trans r16,
        g17.trans r17, g18.trans r18, gx19, gx21, g22.trans r22, gfp.trans rfp,
        gv3.trans rv3, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd
