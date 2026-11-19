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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 6a (`+0x7134 .. +0x7604`)

Entry `memset`s (`c'` and `rHat[0..2]`), `B01` PRF (`prf0..2`), 24-vector `Fwd2` zeta spill into
`Spill13`/`Spill6`/`Spill21`, and reusable 32-iteration SWAR `cbd2` loop (`+0x74d4 → +0x7604`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_blk29 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec keccak2_136_31_RW2Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Spill13 Spill13Mem Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat pointsToBytes_eq_vecRangeMem spill13Mem_ofFn
  step_ldpQ128 step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdDup_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq eight_16_eq_vec128At_cbd2 exec_simdMovi_2d_0
  halfRangeMem8_cbd2_eq orr_1_of_aligned16 sepWP_elim_byte setMem_setMem setPC_setMem_setPC
  setWidth32_shr_zext64 shake256List_length stage_prf33_eq step_bCond_not_taken step_bCond_taken
  truncate32_zext64 ubfx2_w32 ubfx2_w32_norm vec128At_eq_eight_16 vec128At_eq_halfRangeMem8
  vec2_bytesToVecNat_eq vecRangeBytes_zero vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepStore128.spill21 SepStore128.spill6 Spill21 Spill21Mem Spill6 Spill6Mem
  spill21Mem_ofFn spill6Mem_ofFn)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange halfRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x7134 → 0x7604]
end
theorem blk01_rw2_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW2Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk01_keccak2_136_31_RW2_ok

theorem blk01_rw1_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk01_keccak2_136_31_RW1_ok

theorem blk29_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk29_memset_ok

@[simp, arm64_norm, wp_norm]
theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC04 shake256List dup8x16
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 exec_simdDup_8h
  ubfx2_w32 ubfx2_w32_norm truncate32_zext64 setWidth32_shr_zext64

@[simp, arm64_norm, wp_norm] abbrev offSeg6Start    : BitVec 64 := BitVec.ofNat 64 28980
@[simp, arm64_norm, wp_norm] abbrev off7184         : BitVec 64 := BitVec.ofNat 64 29060
@[simp, arm64_norm, wp_norm] abbrev off726c         : BitVec 64 := BitVec.ofNat 64 29292
@[simp, arm64_norm, wp_norm] abbrev off72a8         : BitVec 64 := BitVec.ofNat 64 29352
@[simp, arm64_norm, wp_norm] abbrev offSeg6CbdStart : BitVec 64 := BitVec.ofNat 64 29908
@[simp, arm64_norm, wp_norm] abbrev offSeg6CbdBody  : BitVec 64 := BitVec.ofNat 64 30052
@[simp, arm64_norm, wp_norm] abbrev offSeg6CbdBr    : BitVec 64 := BitVec.ofNat 64 30208
@[simp, arm64_norm, wp_norm] abbrev offSeg6CbdEnd   : BitVec 64 := BitVec.ofNat 64 30212

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  exact cells32_entails_memRegion sPtr _ _ _ _

theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

/-! ## 1. `Seg6` Entry `memset`s (`+0x7134 → +0x7184`) -/

theorem seg6_memset_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let coins := hashed.drop 32
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off7184) s
      (((sp + 4496#64) ↦ₛ hashed) ∗
       memRegion (sp + 18032#64) 1088 ∗
       memRegion (sp + 19120#64) 33 ∗
       memRegion (sp + 19168#64) 1536 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 11856#64 ∧
        sm.readReg64 .x21 = sp + 19168#64 ∧
        (Pm ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
          memRegion (sp + 18032#64) 1088 ∗
          ((sp + 19120#64) ↦ₛ coins) ∗
          ((sp + 19152#64) ↦₈ 0#8) ∗
          PolyMem (sp + 19168#64) (fun _ => 0#128) ∗
          PolyMem (sp + 19680#64) (fun _ => 0#128) ∗
          PolyMem (sp + 20192#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro coins
  have _ : b = blkPl04.base := hb
  subst hbase
  have htake_len : (hashed.take 32).length = 32 := by simp [hh]
  have hcoins_len : coins.length = 32 := by simp [coins, hh]
  have hh_split : ((sp + 4496#64) ↦ₛ hashed) =
      ((sp + 4496#64) ↦ₛ hashed.take 32) ∗ ((sp + 4528#64) ↦ₛ coins) := by
    conv_lhs => rw [← List.take_append_drop 32 hashed]
    rw [pointsToBytes_append, htake_len,
      show sp + 4496#64 + BitVec.ofNat 64 32 = sp + 4528#64 by bv_omega]
  have hstep1 : SepWP (blkPC04.rebase blkPl04.base (fun _ => none))
      (blkPl04.base + BitVec.ofNat 64 29000) s
      (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 18032#64) 1088 ∗
        memRegion (sp + 19120#64) 33 ∗ memRegion (sp + 19168#64) 1536 ∗
        stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        s1.readReg64 .x20 = sp + 11856#64 ∧
        (P1 ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
          memRegion (sp + 18032#64) 1088 ∗
          memRegion (sp + 19120#64) 33 ∗
          memRegion (sp + 19168#64) 1536 ∗
          stackAt sp 1136 ∗ Rest)) := by
    wp_steps 5
    apply seq_codeLoaded_lr ‹_›
    wp_call (blk29_04 blkPl04.base) (sp + 18032#64, 0#8, (1088 : Nat))
    apply SepWP.done (by assumption) (by assumption); intro _
    refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
        ‹_›, Eq.trans ‹_› hx19, Eq.trans ‹_› hx20, ?_⟩
    have hm1088 : ((sp + 18032#64) ↦ₛ List.replicate 1088 0#8) ⊢
        memRegion (sp + 18032#64) 1088 := by
      simpa only [List.length_replicate] using
        pointsToBytes_entails_memRegion (sp + 18032#64) (List.replicate 1088 0#8)
    exact entails_sub hm1088 (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm =>
        mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧
          sm.sp = sp ∧ sm.spAligned = true ∧
          sm.readReg64 .fp = s.readReg64 .fp ∧
          sm.readReg64 .x19 = 0x55555555#64 ∧
          sm.readReg64 .x20 = sp + 11856#64 ∧
          (Pm ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
            memRegion (sp + 18032#64) 1088 ∗
            memRegion (sp + 19120#64) 33 ∗
            memRegion (sp + 19168#64) 1536 ∗
            stackAt sp 1136 ∗ Rest))
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl hstep1 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hcl1, hsp1, hspA1, hfp1, hx19_1, hx20_1, hP1⟩
  have hstep2 : SepWP (blkPC04.rebase blkPl04.base (fun _ => none))
      (blkPl04.base + BitVec.ofNat 64 29056) s1 P1
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .fp = s.readReg64 .fp ∧
        s2.readReg64 .x0 = sp + 19168#64 ∧
        s2.readReg64 .x1 = 0#64 ∧
        s2.readReg64 .x2 = 1536#64 ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧
        s2.readReg64 .x20 = sp + 11856#64 ∧
        s2.readReg64 .x21 = sp + 19168#64 ∧
        (P2 ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
          memRegion (sp + 18032#64) 1088 ∗
          ((sp + 19120#64) ↦ₛ coins) ∗
          ((sp + 19152#64) ↦₈ 0#8) ∗
          memRegion (sp + 19168#64) 1536 ∗
          stackAt sp 1136 ∗ Rest)) := by
    have _ := hpc1
    refine SepWP.weaken_pre hP1 ?_
    rw [memRegion_split' (b := sp + 19120#64) (b' := sp + 19136#64) (n := 16) (k := (17 : Nat))
          rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 19136#64) (b' := sp + 19152#64) (n := 16) (k := (1 : Nat))
          rfl (by bv_omega) (by decide)]
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 19120#64) (by decide) (by sep_focus); intro vc0
    apply SepWP.of_memRegion_vecRangeMem 1 (sp + 19136#64) (by decide) (by sep_focus); intro vc1
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    sep_frame_apply (sepWP_elim_byte (a := sp + 19152#64)); intro b0
    rw [hh_split, ← vec2_bytesToVecNat_eq (sp + 4528#64) hcoins_len]
    wp_steps 6
    refine step_ldpQ128 (wb := none) (ea := sp + 4528#64) (ea16 := sp + 4528#64 + 16#64)
      (v1 := bytesToVecNat coins 0) (v2 := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode]) rfl
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl)))))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.right
        (SepLoad128.left (SepLoad128.right (SepLoad128.right (SepLoad128.vec128At rfl)))))))
      (by wp_norm_lhs) ?_
    wp_steps 5
    have hal_sp1 : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp1] using hspA1
    refine step_strQ128 (wb := none) (ea := sp + 19120#64) (val := bytesToVecNat coins 0)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp1, hal_sp1])
      (by simp [evalAddrMode, hsp1]) rfl
      (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) fun _ => ?_
    try rw [setPC_setMem_collapse]
    refine step_strQ128 (wb := none) (ea := sp + 19136#64) (val := bytesToVecNat coins 1)
      (by wp_norm_lhs) (by simp [hrun1]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp1, hal_sp1])
      (by simp [evalAddrMode, hsp1]) rfl
      (SepStore128.right (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) fun _ => ?_
    simp only [setMem_setMem]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
      ⟨by simp [hsp1], spAligned_of_sp_eq hspA1 hsp1 (by simp [hsp1]),
        by simp [hfp1], by simp, by simp, by simp, by simp [hx19_1], by simp [hx20_1], by simp, ?_⟩
    rw [vec2_bytesToVecNat_eq (sp + 4528#64) hcoins_len, ← hh_split]
    have hc19120 : Vec128At (sp + 19120#64) (bytesToVecNat coins 0) ∗
        Vec128At (sp + 19136#64) (bytesToVecNat coins 1) = ((sp + 19120#64) ↦ₛ coins) := by
      simpa [show sp + 19120#64 + 16#64 = sp + 19136#64 by bv_omega] using
        vec2_bytesToVecNat_eq (sp + 19120#64) hcoins_len
    exact entails_sub (Entails.of_eq hc19120) (by sep_frame) (by sep_frame)
  refine SepWP.seq
    (SepWP.mono_frozen (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ _)
      (Φ := mlkemMultiLib.CodeLoaded mlkemMpl)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl1 hstep2 (fun _ _ _ _ hc hp => ⟨hc, hp⟩)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hcl2, hsp2, hspA2, hfp2, hx0_2, hx1_2, hx2_2, hx19_2, hx20_2, hx21_2, hP2⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s2.mem := hcl2
  have _ := hpc2
  refine SepWP.weaken_pre hP2 ?_
  wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk29_04 blkPl04.base) (sp + 19168#64, 0#8, (1536 : Nat))
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp2, spAligned_of_sp_eq hspA2 hsp2 (hsp_sf.trans hsp2),
      Eq.trans ‹_› hfp2, Eq.trans ‹_› hx19_2, Eq.trans ‹_› hx20_2, Eq.trans ‹_› hx21_2, ?_⟩
  have hz3 : ((sp + 19168#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 19168#64) (fun _ => 0#128) ∗
      PolyMem (sp + 19680#64) (fun _ => 0#128) ∗
      PolyMem (sp + 20192#64) (fun _ => 0#128) := by
    have hrep : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, show (1536 : Nat) = 512 + (512 + 512) from rfl,
        List.replicate_add, List.replicate_add]
    rw [hrep, pointsToBytes_append, pointsToBytes_append,
      vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp [PolyMem,
      show sp + 19168#64 + BitVec.ofNat 64 (16 * 32) = sp + 19680#64 by bv_omega,
      show sp + 19680#64 + BitVec.ofNat 64 (16 * 32) = sp + 20192#64 by bv_omega]
  rw [hz3]
  sep_frame

/-! ## 2. `Seg6` PRF Calls (`+0x7184 → +0x72a8`) -/

@[simp, arm64_norm, wp_norm] private abbrev off7268 : BitVec 64 := BitVec.ofNat 64 29288

local macro "step_strQ_oct8 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.oct8 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  (try rw [setPC_setMem_setPC]); (try rw [setMem_setMem]); (try rw [setPC_setMem_collapse])))

local macro "step_dead_zero8 " spTerm:term:arg baseOff:num : tactic => `(tactic| (
  apply SepWP.of_memRegion_vecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) (by decide) (by sep_focus)
  intro zf
  rw [show VecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) zf =
        PolyOctMem ($spTerm + BitVec.ofNat 64 $baseOff) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; step_strQ_oct8 5; step_strQ_oct8 4;
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0))

local syntax "find_load128" : tactic
local macro_rules
  | `(tactic| find_load128) => `(tactic| first
      | (with_reducible apply SepLoad128.vec128At; with_reducible rfl)
      | (with_reducible apply SepLoad128.left; find_load128)
      | (with_reducible apply SepLoad128.right; find_load128))

local syntax "find_store128" : tactic
local macro_rules
  | `(tactic| find_store128) => `(tactic| first
      | (with_reducible apply SepStore128.vec128At; with_reducible rfl)
      | (with_reducible apply SepStore128.left; find_store128)
      | (with_reducible apply SepStore128.right; find_store128))

section

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off7184) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off7268) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 32 ∗
       memRegion (sp + 20704#64) 128 ∗
       memRegion (sp + 24448#64) 128 ∗
       memRegion (sp + 24976#64) 99 ∗
       memRegion (sp + 25296#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x0 = sp + 11856#64 ∧
        sm.readReg64 .x1 = sp + 25296#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 24448#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = 33#64 ∧
        sm.readReg64 .x23 = sp + 25042#64 ∧
        (Pm ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 11856#64) (sp + 24976#64) (sp + 25009#64) 33 33 ∗
          ((sp + 24976#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 25009#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 25042#64) ↦ₛ (coins ++ [2#8])) ∗
          memRegion (sp + 20704#64) 128 ∗
          memRegion (sp + 24448#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 19120#64) hc]
  have h99 : memRegion (sp + 24976#64) 99 =
      memRegion (sp + 24976#64) 16 ∗ memRegion (sp + 24992#64) 16 ∗ memRegion (sp + 25008#64) 1 ∗
      memRegion (sp + 25009#64) 16 ∗ memRegion (sp + 25025#64) 16 ∗ memRegion (sp + 25041#64) 1 ∗
      memRegion (sp + 25042#64) 16 ∗ memRegion (sp + 25058#64) 16 ∗ memRegion (sp + 25074#64) 1 := by
    rw [memRegion_split' (b' := sp + 24992#64) (n := 16) (k := (83 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25008#64) (n := 16) (k := (67 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25009#64) (n := 1)  (k := (66 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25025#64) (n := 16) (k := (50 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25041#64) (n := 16) (k := (34 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25042#64) (n := 1)  (k := (33 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25058#64) (n := 16) (k := (17 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 25074#64) (n := 16) (k := (1 : Nat))  rfl (by bv_omega) (by decide)]
  rw [h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 24976#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 24992#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 25009#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 25025#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 25042#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 25058#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 25008#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 25041#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 25074#64)); intro c2
  sep_frame_apply (sepWP_elim_region32 (a := sp + 11856#64)); intro k0 k1 k2 k3
  simp only [show sp + 11856#64 + 8#64 = sp + 11864#64 by bv_omega,
    show sp + 11856#64 + 16#64 = sp + 11872#64 by bv_omega,
    show sp + 11856#64 + 24#64 = sp + 11880#64 by bv_omega]
  refine step_ldrQ128 (wb := none) (ea := sp + 19120#64) (v := bytesToVecNat coins 0)
    hpc hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 3
  refine step_ldrQ128 (wb := none) (ea := (sp + 19120#64) + 16#64) (v := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 24976#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 25009#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 25042#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 25025#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 25058#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 3
  refine step_strQ128 (wb := none) (ea := sp + 24992#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  step_dead_zero8 sp 25296
  step_dead_zero8 sp 24448
  step_dead_zero8 sp 20704
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 24976#64) 0#8 hc,
      ← stage_prf33_eq (sp + 25009#64) 1#8 hc,
      ← stage_prf33_eq (sp + 25042#64) 2#8 hc]
  unfold Keccak2SlicesRW
  simp only [show sp + 24976#64 + 16#64 = sp + 24992#64 by bv_omega,
    show sp + 24976#64 + 32#64 = sp + 25008#64 by bv_omega,
    show sp + 25009#64 + 16#64 = sp + 25025#64 by bv_omega,
    show sp + 25009#64 + 32#64 = sp + 25041#64 by bv_omega,
    show sp + 25042#64 + 16#64 = sp + 25058#64 by bv_omega,
    show sp + 25042#64 + 32#64 = sp + 25074#64 by bv_omega,
    show sp + 11856#64 + 8#64 = sp + 11864#64 by bv_omega,
    show sp + 11856#64 + 16#64 = sp + 11872#64 by bv_omega,
    show sp + 11856#64 + 24#64 = sp + 11880#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 25296#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 24448#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 20704#64) _) (by sep_frame) (by sep_frame)))

private theorem seg6_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp p2 : BitVec 64) {l2 : Nat} (hl2 : l2 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off726c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = 33#64) (hx23 : s.readReg64 .x23 = p2) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + BitVec.ofNat 64 29348) s
      (memRegion (sp + 22400#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x0 = sp + 22400#64 ∧ sm.readReg64 .x1 = sp + 20704#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 11856#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp + 22400#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 22400#64) p2 p2 l2 l2 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 22400#64)); intro d0 d1 d2 d3
  simp only [show sp + 22400#64 + 8#64 = sp + 22408#64 by bv_omega,
    show sp + 22400#64 + 16#64 = sp + 22416#64 by bv_omega,
    show sp + 22400#64 + 24#64 = sp + 22424#64 by bv_omega]
  wp_steps 14
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hl2, show sp + 22400#64 + 8#64 = sp + 22408#64 by bv_omega,
    show sp + 22400#64 + 16#64 = sp + 22416#64 by bv_omega,
    show sp + 22400#64 + 24#64 = sp + 22424#64 by bv_omega]
  sep_frame

end
set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem seg6_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off7184) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hx21 : s.readReg64 .x21 = sp + 19168#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off72a8) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 128 ∗
       memRegion (sp + 20704#64) 128 ∗
       memRegion (sp + 22400#64) 32 ∗
       memRegion (sp + 24448#64) 128 ∗
       memRegion (sp + 24976#64) 99 ∗
       memRegion (sp + 25296#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧
        sf.readReg64 .x21 = sp + 19168#64 ∧
        sf.readReg64 .x22 = sp + 22400#64 ∧
        (Pf ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 128 ∗
          ((sp + 20704#64) ↦ₛ shake256List 128 (coins ++ [2#8])) ∗
          memRegion (sp + 22400#64) 32 ∗
          ((sp + 24448#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          memRegion (sp + 24976#64) 99 ∗
          ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 32 ∗
      memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 24448#64) 128 ∗
      memRegion (sp + 24976#64) 99 ∗ memRegion (sp + 25296#64) 128 ∗
      (memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 11888#64) 96 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6_prf_stage hb rfl s sp coins _ hc hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc0_len : (coins ++ [0#8]).length = 33 := by simp [hc]
  have hc1_len : (coins ++ [1#8]).length = 33 := by simp [hc]
  have hc2_len : (coins ++ [2#8]).length = 33 := by simp [hc]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC04.rebase blkPl04.base (fun _ => none))
      (blkPl04.base + off726c) s1
      (((sp + 19120#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 11856#64) (sp + 24976#64) (sp + 25009#64) 33 33 ∗
        ((sp + 24976#64) ↦ₛ (coins ++ [0#8])) ∗
        ((sp + 25009#64) ↦ₛ (coins ++ [1#8])) ∗
        ((sp + 25042#64) ↦ₛ (coins ++ [2#8])) ∗
        memRegion (sp + 20704#64) 128 ∗
        memRegion (sp + 24448#64) 128 ∗
        memRegion (sp + 25296#64) 128 ∗
        (memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 11888#64) 96 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .fp = s.readReg64 .fp ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 11856#64 ∧
        s2.readReg64 .x21 = sp + 19168#64 ∧ s2.readReg64 .x22 = 33#64 ∧
        s2.readReg64 .x23 = sp + 25042#64 ∧
        (P2 ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 128 ∗
          memRegion (sp + 20704#64) 128 ∗
          memRegion (sp + 22400#64) 32 ∗
          ((sp + 24448#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          ((sp + 24976#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 25009#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 25042#64) ↦ₛ (coins ++ [2#8])) ∗
          ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [show Keccak2SlicesRW (sp + 11856#64) (sp + 24976#64) (sp + 25009#64) 33 33 =
          Keccak2SlicesRW (sp + 11856#64) (sp + 24976#64) (sp + 25009#64)
            (coins ++ [0#8]).length (coins ++ [1#8]).length from by rw [hc0_len, hc1_len]]
    wp_step
    have hro1 : MlKemRoOk mlkemMpl
        ((s1.writeReg64 .lr (blkPl04.base + off726c)).setPC (mlkemMpl.base 1)).mem := hro1
    apply seq_codeLoaded_lr ‹_›
    wp_call (blk01_rw2_04 blkPl04.base)
      (⟨sp + 11856#64, sp + 24976#64, sp + 25009#64, sp + 25296#64, sp + 24448#64,
        (128 : Nat), coins ++ [0#8], coins ++ [1#8]⟩ : Keccak2ShakeArgs)
    apply SepWP.done (by assumption) (by assumption); intro _
    refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› hfp1,
        Eq.trans ‹_› (hx19_1.trans hx19), Eq.trans ‹_› (hx20_1.trans hx20),
        Eq.trans ‹_› (hx21_1.trans hx21), Eq.trans ‹_› hx22_1, Eq.trans ‹_› hx23_1, ?_⟩
    rw [hsp1]
    have hk11856 : Keccak2SlicesRW (sp + 11856#64) (sp + 24976#64) (sp + 25009#64)
          (coins ++ [0#8]).length (coins ++ [1#8]).length ∗
        memRegion (sp + 11888#64) 96 ⊢ memRegion (sp + 11856#64) 128 := by
      rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (96 : Nat))
            rfl (by clear * -; bv_omega) (by decide)]
      exact sepConj_mono (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (Entails.refl _)
    exact entails_sub hk11856 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 22400#64) 32 ∗ (((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 20704#64) 128 ∗
      ((sp + 24448#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
      ((sp + 24976#64) ↦ₛ (coins ++ [0#8])) ∗ ((sp + 25009#64) ↦ₛ (coins ++ [1#8])) ∗
      ((sp + 25042#64) ↦ₛ (coins ++ [2#8])) ∗
      ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_prf_stage2 hb rfl s2 sp (sp + 25042#64) hc2_len _ hpc2 hrun2 hsp2 hspA2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_step
  have hro3 : MlKemRoOk mlkemMpl
      ((s3.writeReg64 .lr (blkPl04.base + off72a8)).setPC (mlkemMpl.base 1)).mem := hro3
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk01_rw1_04 blkPl04.base)
    (sp + 22400#64, sp + 25042#64, sp + 20704#64, sp + 11856#64, (128 : Nat), coins ++ [2#8])
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› (hfp3.trans hfp2),
      Eq.trans ‹_› (hx19_3.trans hx19_2), Eq.trans ‹_› (hx20_3.trans hx20_2),
      Eq.trans ‹_› (hx21_3.trans hx21_2), Eq.trans ‹_› hx22_3, ?_⟩
  rw [hsp3]
  have hm11856 : ((sp + 11856#64) ↦ₛ shake256List 128 (coins ++ [2#8])) ⊢
      memRegion (sp + 11856#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 11856#64) (shake256List 128 (coins ++ [2#8]))
  have hm99 : ((sp + 24976#64) ↦ₛ (coins ++ [0#8])) ∗
      ((sp + 25009#64) ↦ₛ (coins ++ [1#8])) ∗
      ((sp + 25042#64) ↦ₛ (coins ++ [2#8])) ⊢ memRegion (sp + 24976#64) 99 := by
    rw [memRegion_split' (b' := sp + 25009#64) (n := 33) (k := (66 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 25042#64) (n := 33) (k := (33 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by simpa [hc0_len] using pointsToBytes_entails_memRegion (sp + 24976#64) (coins ++ [0#8]))
      (sepConj_mono
        (by simpa [hc1_len] using pointsToBytes_entails_memRegion (sp + 25009#64) (coins ++ [1#8]))
        (by simpa [hc2_len] using pointsToBytes_entails_memRegion (sp + 25042#64) (coins ++ [2#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm11856 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))

/-! ## 3. Copy `prf0..2` & Spill 24 `Fwd2` Zeta Vectors (`+0x72a8 → +0x74d4`) -/

@[simp, arm64_norm, wp_norm] private abbrev off73b8 : BitVec 64 := BitVec.ofNat 64 29624

local macro "ldr_p0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 25296#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 24448#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 20704#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "str_d0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22400#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22528#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))
local macro "str_d2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22656#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_sp13 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1616#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.spill13 (k := $k) (by decide) rfl (by dsimp only [Spill13.set])))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_sp6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1824#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.right (SepStore128.left
        (SepStore128.spill6 (k := $k) (by decide) rfl (by dsimp only [Spill6.set]))))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_sp21 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1920#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right
      (SepStore128.right (SepStore128.right (SepStore128.left
        (SepStore128.spill21 (k := $k) (by decide) rfl (by dsimp only [Spill21.set])))))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

@[expose] def fwd2Spill13 : Spill13 :=
  ⟨dup8x16 0xd43e#16, dup8x16 0xfa3e#16, dup8x16 0x054e#16, dup8x16 0xfb4e#16,
   dup8x16 0x29c2#16, dup8x16 0x03c2#16, dup8x16 0xc2b6#16, dup8x16 0xf129#16,
   dup8x16 0x0629#16, dup8x16 0x6c6e#16, dup8x16 0x026e#16, dup8x16 0xae55#16,
   dup8x16 0xbeca#16⟩

@[expose] def fwd2Spill6 : Spill6 :=
  ⟨dup8x16 0x6e1f#16, dup8x16 0x011f#16, dup8x16 0xcf8e#16, dup8x16 0x058e#16,
   dup8x16 0x34d5#16, dup8x16 0x05d5#16⟩

@[expose] def setFwd2Spill21 (t : Spill21) : Spill21 :=
  { t with
    s0 := dup8x16 0x0313#16, s1 := dup8x16 0xfa13#16, s2 := dup8x16 0x3999#16,
    s3 := dup8x16 0xfe99#16, s4 := dup8x16 0xf9c0#16 }
private def midD1 (p1 d1 : Oct8) : Oct8 :=
  ⟨p1.o0, d1.o1, p1.o2, d1.o3, p1.o4, p1.o5, p1.o6, d1.o7⟩

private def midD2 (p2 d2 : Oct8) : Oct8 :=
  ⟨d2.o0, p2.o1, p2.o2, d2.o3, d2.o4, d2.o5, p2.o6, d2.o7⟩

theorem aligned16_add22400 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 22400#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 22400#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg6_copy_zetas_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d0 d1 d2 : Oct8)
    (t13 : Spill13) (t6 : Spill6) (t21 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + off72a8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hx21 : s.readReg64 .x21 = sp + 19168#64)
    (hx22 : s.readReg64 .x22 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off73b8) s
      (Oct8Mem (sp + 25296#64) p0 ∗ Oct8Mem (sp + 24448#64) p1 ∗ Oct8Mem (sp + 20704#64) p2 ∗
       Oct8Mem (sp + 22400#64) d0 ∗ Oct8Mem (sp + 22528#64) d1 ∗ Oct8Mem (sp + 22656#64) d2 ∗
       Spill13Mem (sp + 1616#64) t13 ∗ Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) t21 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x5 = 0#64 ∧ sm.readReg64 .x7 = sp + 22401#64 ∧
        sm.readReg64 .x8 = 0xcf8e#64 ∧ sm.readReg64 .x9 = sp + 19184#64 ∧
        sm.readReg64 .x10 = 16#64 ∧ sm.readReg64 .x11 = 0x058e#64 ∧
        sm.readReg64 .x12 = 0xfb4e#64 ∧ sm.readReg64 .x13 = 0x47fa#64 ∧
        sm.readReg64 .x14 = 0x019b#64 ∧ sm.readReg64 .x15 = 0x229b#64 ∧
        sm.readReg64 .x16 = 0x6833#64 ∧ sm.readReg64 .x17 = 0xf9dd#64 ∧
        sm.readReg64 .x18 = 0xc0dd#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 11856#64 ∧ sm.readReg64 .x21 = sp + 19168#64 ∧
        sm.readReg64 .x22 = sp + 22400#64 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readVReg128 0#5 = dup8x16 0x34d5#16 ∧ sm.readVReg128 1#5 = p1.o7 ∧
        sm.readVReg128 2#5 = p2.o3 ∧ sm.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        sm.readVReg128 4#5 = dup8x16 0x05d5#16 ∧
        Pm = (Oct8Mem (sp + 25296#64) p0 ∗ Oct8Mem (sp + 24448#64) p1 ∗ Oct8Mem (sp + 20704#64) p2 ∗
          Oct8Mem (sp + 22400#64) p0 ∗ Oct8Mem (sp + 22528#64) (midD1 p1 d1) ∗
          Oct8Mem (sp + 22656#64) (midD2 p2 d2) ∗ Spill13Mem (sp + 1616#64) t13 ∗
          Spill6Mem (sp + 1824#64) t6 ∗ Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p0 4 hrun hsp hsp_chk; ldr_p0 7 hrun hsp hsp_chk; wp_steps 2
  ldr_p0 5 hrun hsp hsp_chk; wp_step; str_d0 4 hrun hsp hsp_chk
  ldr_p0 6 hrun hsp hsp_chk; wp_step; str_d0 7 hrun hsp hsp_chk; wp_steps 2
  str_d0 6 hrun hsp hsp_chk; ldr_p0 0 hrun hsp hsp_chk; wp_step
  str_sp21 1 hrun hsp hsp_chk; ldr_p2 1 hrun hsp hsp_chk; wp_step
  str_d0 0 hrun hsp hsp_chk; ldr_p0 2 hrun hsp hsp_chk; wp_step
  str_sp21 4 hrun hsp hsp_chk; wp_steps 2; str_d0 2 hrun hsp hsp_chk
  ldr_p1 4 hrun hsp hsp_chk; wp_step; str_d2 1 hrun hsp hsp_chk; wp_steps 2
  str_d1 4 hrun hsp hsp_chk; ldr_p1 6 hrun hsp hsp_chk; wp_step
  str_sp21 3 hrun hsp hsp_chk; wp_steps 2; str_d1 6 hrun hsp hsp_chk
  ldr_p1 0 hrun hsp hsp_chk; wp_steps 2; str_d0 5 hrun hsp hsp_chk
  ldr_p0 1 hrun hsp hsp_chk; str_d1 0 hrun hsp hsp_chk; ldr_p1 2 hrun hsp hsp_chk
  wp_steps 2; str_d0 1 hrun hsp hsp_chk; ldr_p0 3 hrun hsp hsp_chk
  str_d1 2 hrun hsp hsp_chk; ldr_p2 2 hrun hsp hsp_chk; wp_step
  str_sp21 0 hrun hsp hsp_chk; wp_steps 2; str_d2 2 hrun hsp hsp_chk
  ldr_p2 6 hrun hsp hsp_chk; wp_step; str_d0 3 hrun hsp hsp_chk
  ldr_p1 5 hrun hsp hsp_chk; wp_step; str_d2 6 hrun hsp hsp_chk; wp_steps 2
  str_d1 5 hrun hsp hsp_chk; ldr_p1 7 hrun hsp hsp_chk; wp_step
  str_sp21 2 hrun hsp hsp_chk; ldr_p2 3 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp [orr_1_of_aligned16 _ (aligned16_add22400 sp hsp_chk)],
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp [hx19],
      by simp [hx20], by simp [hx21], by simp [hx22], by simp,
      by simp, by simp [Oct8.get], by simp [Oct8.get], by simp, by simp,
      by dsimp [Oct8.get, midD1, midD2, setFwd2Spill21]; rfl⟩
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg6_copy_zetas_b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (_hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d1 d2 : Oct8)
    (t13 : Spill13) (t6 : Spill6) (t21 : Spill21) (Rest : SepProp)
    (hpc : s.pc = b + off73b8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx5 : s.readReg64 .x5 = 0#64) (hx7 : s.readReg64 .x7 = sp + 22401#64)
    (hx8 : s.readReg64 .x8 = 0xcf8e#64) (hx9 : s.readReg64 .x9 = sp + 19184#64)
    (hx10 : s.readReg64 .x10 = 16#64) (hx11 : s.readReg64 .x11 = 0x058e#64)
    (hx12 : s.readReg64 .x12 = 0xfb4e#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64) (hx21 : s.readReg64 .x21 = sp + 19168#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 0x34d5#16) (hv1 : s.readVReg128 1#5 = p1.o7)
    (hv2 : s.readVReg128 2#5 = p2.o3) (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hv4 : s.readVReg128 4#5 = dup8x16 0x05d5#16) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdStart) s
      (Oct8Mem (sp + 25296#64) p0 ∗ Oct8Mem (sp + 24448#64) p1 ∗ Oct8Mem (sp + 20704#64) p2 ∗
       Oct8Mem (sp + 22400#64) p0 ∗ Oct8Mem (sp + 22528#64) (midD1 p1 d1) ∗
       Oct8Mem (sp + 22656#64) (midD2 p2 d2) ∗
       Spill13Mem (sp + 1616#64) t13 ∗ Spill6Mem (sp + 1824#64) t6 ∗
       Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 22401#64 ∧
        sf.readReg64 .x9 = sp + 19184#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧ sf.readReg64 .x21 = sp + 19168#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        Pf = (Oct8Mem (sp + 25296#64) p0 ∗ Oct8Mem (sp + 24448#64) p1 ∗ Oct8Mem (sp + 20704#64) p2 ∗
          Oct8Mem (sp + 22400#64) p0 ∗ Oct8Mem (sp + 22528#64) p1 ∗ Oct8Mem (sp + 22656#64) p2 ∗
          Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
          Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗ Rest)) := by
  subst _hbase
  have _ : MlKemBase blkPl04 blkPl04.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  cases p1; cases p2; cases t13; cases t6
  wp_step; str_sp6 4 hrun hsp hsp_chk; wp_steps 2
  str_d1 7 hrun hsp hsp_chk; ldr_p1 1 hrun hsp hsp_chk
  str_d2 3 hrun hsp hsp_chk; ldr_p2 7 hrun hsp hsp_chk; wp_step
  str_sp6 3 hrun hsp hsp_chk; wp_steps 2; str_d1 1 hrun hsp hsp_chk; ldr_p1 3 hrun hsp hsp_chk
  wp_step; str_sp6 5 hrun hsp hsp_chk; ldr_p2 5 hrun hsp hsp_chk; str_sp6 2 hrun hsp hsp_chk
  wp_steps 2; str_d1 3 hrun hsp hsp_chk; ldr_p2 0 hrun hsp hsp_chk; wp_step
  str_d2 7 hrun hsp hsp_chk; str_sp6 1 hrun hsp hsp_chk; wp_steps 2
  str_d2 0 hrun hsp hsp_chk; ldr_p2 4 hrun hsp hsp_chk; str_d2 5 hrun hsp hsp_chk
  str_sp6 0 hrun hsp hsp_chk; wp_steps 2; str_d2 4 hrun hsp hsp_chk; str_sp13 12 hrun hsp hsp_chk
  wp_steps 2; str_sp13 11 hrun hsp hsp_chk; wp_steps 2; str_sp13 10 hrun hsp hsp_chk
  wp_steps 2; str_sp13 9 hrun hsp hsp_chk; wp_steps 2; str_sp13 8 hrun hsp hsp_chk
  wp_steps 2; str_sp13 7 hrun hsp hsp_chk; wp_steps 2; str_sp13 6 hrun hsp hsp_chk
  wp_steps 2; str_sp13 5 hrun hsp hsp_chk; wp_steps 2; str_sp13 4 hrun hsp hsp_chk
  wp_steps 2; str_sp13 3 hrun hsp hsp_chk; wp_step; str_sp13 2 hrun hsp hsp_chk
  wp_step; str_sp13 1 hrun hsp hsp_chk; wp_steps 2; str_sp13 0 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp [ro00Sym], by simp,
      by simp [ro00Sym], by simp,
      by simp [hx5], by simp [hx7], by simp [hx9], by simp [hx10],
      by simp, by simp [hx13], by simp [hx14], by simp [hx15],
      by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx19],
      by simp [hx20], by simp [hx21], by simp, by simp [hv3],
      by simp [Oct8.get, midD1, midD2, fwd2Spill13, fwd2Spill6]⟩
theorem seg6_copy_and_zetas [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (prf0 prf1 prf2 : List (BitVec 8)) (Rest : SepProp)
    (h0 : prf0.length = 128) (h1 : prf1.length = 128) (h2 : prf2.length = 128)
    (hpc : s.pc = b + off72a8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hx21 : s.readReg64 .x21 = sp + 19168#64)
    (hx22 : s.readReg64 .x22 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdStart) s
      (((sp + 25296#64) ↦ₛ prf0) ∗ ((sp + 24448#64) ↦ₛ prf1) ∗ ((sp + 20704#64) ↦ₛ prf2) ∗
       memRegion (sp + 22400#64) 384 ∗ memRegion (sp + 1616#64) 640 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 22401#64 ∧
        sf.readReg64 .x9 = sp + 19184#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧ sf.readReg64 .x21 = sp + 19168#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        ∃ t21 : Spill21,
          (Pf ⊢ ((sp + 22400#64) ↦ₛ prf0) ∗ ((sp + 22528#64) ↦ₛ prf1) ∗ ((sp + 22656#64) ↦ₛ prf2) ∗
            Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
            Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗
            memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 24448#64) 128 ∗
            memRegion (sp + 25296#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 25296#64) h0,
      pointsToBytes128_eq_oct8Mem (sp + 24448#64) h1,
      pointsToBytes128_eq_oct8Mem (sp + 20704#64) h2,
      memRegion_split' (b := sp + 22400#64) (b' := sp + 22528#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22528#64) (b' := sp + 22656#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1616#64) (b' := sp + 1824#64) (n := 208) (k := (432 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 1824#64) (b' := sp + 1920#64) (n := 96) (k := (336 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22400#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22528#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22656#64) (hf := by sep_focus); intro fd2
  apply SepWP.of_memRegion_vecRangeMem 13 (sp + 1616#64) (hf := by sep_focus); intro f13
  apply SepWP.of_memRegion_vecRangeMem 6 (sp + 1824#64) (hf := by sep_focus); intro f6
  apply SepWP.of_memRegion_vecRangeMem 21 (sp + 1920#64) (hf := by sep_focus); intro f21
  rw [show VecRangeMem 8 (sp + 22400#64) fd0 = Oct8Mem (sp + 22400#64) (Oct8.ofFn fd0) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 22528#64) fd1 = Oct8Mem (sp + 22528#64) (Oct8.ofFn fd1) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 22656#64) fd2 = Oct8Mem (sp + 22656#64) (Oct8.ofFn fd2) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 13 (sp + 1616#64) f13 = Spill13Mem (sp + 1616#64) (Spill13.ofFn f13) from (spill13Mem_ofFn _ _).symm,
      show VecRangeMem 6 (sp + 1824#64) f6 = Spill6Mem (sp + 1824#64) (Spill6.ofFn f6) from (spill6Mem_ofFn _ _).symm,
      show VecRangeMem 21 (sp + 1920#64) f21 = Spill21Mem (sp + 1920#64) (Spill21.ofFn f21) from (spill21Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 25296#64) (Oct8.ofFn (bytesToVecNat prf0)) ∗
      Oct8Mem (sp + 24448#64) (Oct8.ofFn (bytesToVecNat prf1)) ∗
      Oct8Mem (sp + 20704#64) (Oct8.ofFn (bytesToVecNat prf2)) ∗
      Oct8Mem (sp + 22400#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 22528#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 22656#64) (Oct8.ofFn fd2) ∗
      Spill13Mem (sp + 1616#64) (Spill13.ofFn f13) ∗
      Spill6Mem (sp + 1824#64) (Spill6.ofFn f6) ∗
      Spill21Mem (sp + 1920#64) (Spill21.ofFn f21) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (seg6_copy_zetas_a hb hbase s sp _ _ _ _ _ _ _ _ _ Rest hpc hrun hsp hspA hx19 hx20 hx21 hx22)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hx5m, hx7m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m,
      hx14m, hx15m, hx16m, hx17m, hx18m, hx19m, hx20m, hx21m, _, hfpm, hv0m, hv1m, hv2m, hv3m, hv4m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (seg6_copy_zetas_b hb hbase sm sp _ _ _ _ _ _ _ _ Rest hpcm hrunm hspm hspAm
        hx5m hx7m hx8m hx9m hx10m hx11m hx12m hx13m hx14m hx15m hx16m hx17m hx18m
        hx19m hx20m hx21m hv0m hv1m hv2m hv3m hv4m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, hfpf, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf.trans hfpm,
      r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, rv3, Spill21.ofFn f21, ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 22400#64) h0,
      ← pointsToBytes128_eq_oct8Mem (sp + 22528#64) h1,
      ← pointsToBytes128_eq_oct8Mem (sp + 22656#64) h2]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 25296#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 24448#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 20704#64) _) (by sep_frame) (by sep_frame)))
theorem seg6_prf_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdStart) s
      (((sp + 4496#64) ↦ₛ hashed) ∗
       memRegion (sp + 1616#64) 640 ∗
       memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
       memRegion (sp + 19120#64) 33 ∗ memRegion (sp + 19168#64) 1536 ∗
       memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 22400#64) 384 ∗
       memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
       memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 22401#64 ∧
        sf.readReg64 .x9 = sp + 19184#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 11856#64 ∧ sf.readReg64 .x21 = sp + 19168#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t21 : Spill21,
          (Pf ⊢ ((sp + 4496#64) ↦ₛ hashed) ∗
            Spill13Mem (sp + 1616#64) fwd2Spill13 ∗ Spill6Mem (sp + 1824#64) fwd2Spill6 ∗
            Spill21Mem (sp + 1920#64) (setFwd2Spill21 t21) ∗
            memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 18032#64) 1088 ∗
            ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
            PolyMem (sp + 19168#64) (fun _ => 0#128) ∗
            PolyMem (sp + 19680#64) (fun _ => 0#128) ∗
            PolyMem (sp + 20192#64) (fun _ => 0#128) ∗
            memRegion (sp + 20704#64) 128 ∗
            ((sp + 22400#64) ↦ₛ prf0) ∗ ((sp + 22528#64) ↦ₛ prf1) ∗ ((sp + 22656#64) ↦ₛ prf2) ∗
            memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
            memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2
  have hc_len : coins.length = 32 := by simp [coins, hh]
  refine SepWP.weaken_pre
    (P' := ((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 18032#64) 1088 ∗
      memRegion (sp + 19120#64) 33 ∗ memRegion (sp + 19168#64) 1536 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1616#64) 640 ∗ memRegion (sp + 11856#64) 512 ∗
        memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 22400#64) 384 ∗
        memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
        memRegion (sp + 25296#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6_memset_a hb hbase s sp hashed _ hh hpc hrun hsp hspA hx19 hx20 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx21_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (352 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 128 ∗
      memRegion (sp + 20704#64) 128 ∗ memRegion (sp + 22400#64) 32 ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 99 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 1616#64) 640 ∗
        memRegion (sp + 11984#64) 384 ∗ memRegion (sp + 18032#64) 1088 ∗
        ((sp + 19152#64) ↦₈ 0#8) ∗
        PolyMem (sp + 19168#64) (fun _ => 0#128) ∗
        PolyMem (sp + 19680#64) (fun _ => 0#128) ∗
        PolyMem (sp + 20192#64) (fun _ => 0#128) ∗
        memRegion (sp + 22432#64) 352 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6_prf_calls hb hbase s1 sp coins _ hc_len hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm384 : memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 22432#64) 352 =
      memRegion (sp + 22400#64) 384 :=
    (memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (352 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have hm512 : memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 11984#64) 384 =
      memRegion (sp + 11856#64) 512 :=
    (memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 25296#64) ↦ₛ prf0) ∗ ((sp + 24448#64) ↦ₛ prf1) ∗ ((sp + 20704#64) ↦ₛ prf2) ∗
      memRegion (sp + 22400#64) 384 ∗ memRegion (sp + 1616#64) 640 ∗
      (((sp + 4496#64) ↦ₛ hashed) ∗ memRegion (sp + 11856#64) 512 ∗
        memRegion (sp + 18032#64) 1088 ∗ ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 0#8) ∗
        PolyMem (sp + 19168#64) (fun _ => 0#128) ∗ PolyMem (sp + 19680#64) (fun _ => 0#128) ∗
        PolyMem (sp + 20192#64) (fun _ => 0#128) ∗ memRegion (sp + 24976#64) 99 ∗
        stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm384) (by sep_frame)
      (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame))) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_copy_and_zetas hb hbase s2 sp prf0 prf1 prf2 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hfpf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13,
    r14, r15, r16, r17, r18, r19, r20, r21, rv3, t21, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, hfpf.trans (hfp2.trans hfp1),
      r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, rv3, hclf, hrof, t21, Entails.trans hPf (by sep_frame)⟩
/-! ## 4. `Seg6` Scratch Zero & SWAR `cbd2` Loop (`+0x74d4 → +0x7604`) -/

local macro "step_strQ11856 " k:num : tactic => `(tactic| (
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

private theorem seg6_cbd2_zero [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdBody) s
      (memRegion (sp + 11856#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x5 + 1#64 ∧ s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x6 = 0#64 ∧ s1.readReg64 .x7 = s.readReg64 .x7 ∧
        s1.readReg64 .x8 = s.readReg64 .x7 ∧ s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x10 ∧ s1.readReg64 .x12 = s.readReg64 .x12 ∧
        s1.readReg64 .x13 = s.readReg64 .x13 ∧ s1.readReg64 .x14 = s.readReg64 .x14 ∧
        s1.readReg64 .x15 = s.readReg64 .x15 ∧ s1.readReg64 .x16 = s.readReg64 .x16 ∧
        s1.readReg64 .x17 = s.readReg64 .x17 ∧ s1.readReg64 .x18 = s.readReg64 .x18 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧ s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 11856#64) 512 ∗ Rest)) := by
  have _ : b = blkPl04.base := hb
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 11856#64) f = PolyMem (sp + 11856#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ11856 31; step_strQ11856 30; step_strQ11856 29; step_strQ11856 28
  step_strQ11856 27; step_strQ11856 26; step_strQ11856 25; step_strQ11856 24
  step_strQ11856 23; step_strQ11856 22; step_strQ11856 21; step_strQ11856 20
  step_strQ11856 19; step_strQ11856 18; step_strQ11856 17; step_strQ11856 16
  step_strQ11856 15; step_strQ11856 14; step_strQ11856 13; step_strQ11856 12
  step_strQ11856 11; step_strQ11856 10; step_strQ11856 9;  step_strQ11856 8
  step_strQ11856 7;  step_strQ11856 6;  step_strQ11856 5;  step_strQ11856 4
  step_strQ11856 3;  step_strQ11856 2;  step_strQ11856 1;  step_strQ11856 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩
local macro "step_cbd_strh " cellPtr:ident hx20Id:term:arg hx6Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx20Id:term, $hx6Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg6_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6CbdBody) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if k < 31 then b + offSeg6CbdBody else b + offSeg6CbdEnd) s
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
        s'.readReg64 .x20 = dstPtr ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
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
  step_cbd_strh cellPtr hx20 hx6 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx6 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx6 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx6 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx20 hx6 6 (cbd2CoeffFromWord w 6)
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
    refine step_bCond_taken (dst := blkPl04.base + offSeg6CbdBody)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offSeg6CbdBr, offSeg6CbdBody]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega, by simp,
        by simp; clear * -; bv_omega, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl04.base + offSeg6CbdEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg6CbdBr, offSeg6CbdEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
private theorem seg6_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offSeg6CbdBody else b + offSeg6CbdEnd) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x6 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdEnd) s
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
          s'.readReg64 .x20 = dstPtr ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx20
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, hx19, hx20, rfl, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx6 hx8 hx19 hx20
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + offSeg6CbdBody else b + offSeg6CbdEnd) =
        (if k + 1 < 32 then b + offSeg6CbdBody else b + offSeg6CbdEnd) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (seg6_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx6 hx8 hx19 hx20)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hr2, hr3, hr4, hr5, hx6_1, hr7, hx8_1,
        hr9, hr10, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hx20_1, hr21, hfp1, hv3_1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (ih (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx6_1 hx8_1 hx19_1 hx20_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g2.trans hr2, g3.trans hr3,
        g4.trans hr4, g5.trans hr5, g7.trans hr7, g9.trans hr9, g10.trans hr10,
        g12.trans hr12, g13.trans hr13, g14.trans hr14, g15.trans hr15, g16.trans hr16,
        g17.trans hr17, g18.trans hr18, gx19, gx20, g21.trans hr21, gfp.trans hfp1,
        gv3.trans hv3_1, hP2⟩
theorem seg6_cbd2_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + offSeg6CbdStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx7 : s.readReg64 .x7 = prfPtr + 1#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6CbdEnd) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 11856#64) 512 ∗ Rest)
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
        s'.readReg64 .x20 = sp + 11856#64 ∧ s'.readReg64 .x21 = s.readReg64 .x21 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 11856#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 11856#64) 512 ∗ Rest =
      memRegion (sp + 11856#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (seg6_cbd2_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, hx6_1, r7, hx8_1,
      r9, r10, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, rfp, rv3, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) rfl fun f => by
      rw [show VecRangeMem 32 (sp + 11856#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 11856#64) f ∗ Rest by
        rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 11856#64) f), sepConj_assoc]]
      refine SepWP.seq
        (seg6_cbd2_steps hb hbase sp prfPtr (sp + 11856#64) prf Rest 32 0 rfl s1 f
          (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx6_1
          (by simp [hx8_1, hx7]) (r19.trans hx19) (r20.trans hx20)) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g7, g9, g10, g12, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g2.trans r2, g3.trans r3,
        g4.trans r4, g5.trans r5, g7.trans (r7.trans hx7), g9.trans r9, g10.trans r10,
        g12.trans r12, g13.trans r13, g14.trans r14, g15.trans r15, g16.trans r16,
        g17.trans r17, g18.trans r18, gx19, gx20, g21.trans r21, gfp.trans rfp,
        gv3.trans rv3, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a
