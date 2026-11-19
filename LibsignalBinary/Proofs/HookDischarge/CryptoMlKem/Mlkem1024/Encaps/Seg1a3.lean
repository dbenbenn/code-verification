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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2

/-!
# `kyber_encapsulate` (`B07`) — Segment 1a3 (`+0x0228 .. +0x02c0`)

1. `seg1a3_hash_g` (`+0x0228 → +0x0280`): stages `hPk` after `m` at `sp + 2432` and invokes `B00`
   (`keccak2::<72, 6>`) to compute `(kBar, r) = sha3_512List (m ++ hPk)`.
2. `seg1a3_copy_memset` (`+0x0280 → +0x02c0`): copies `(kBar, r)` (`64` B) to `sp + 2496`,
   zeroes `[sp + 23072 .. sp + 23104)`, and invokes `B29` (`memset`) on `[sp + 12832 .. sp + 23072)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a3

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW
  keccak2_72_6_RW1Spec
  mlkemMemsetSpec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_72_6 (
  blk00_keccak2_72_6_RW1_ok
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128
  SepStore128
  SepWP.of_memRegion_vecRangeMem
  Vec128At
  VecRangeMem
  bytesToVecNat
  pointsToBytes_eq_vecRangeMem
  step_ldpQ128
  step_ldrQ128
  step_strQ128
  vecRangeBytes
  vecRangeMem_entails_memRegion
  vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_region32
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq
  blk07_tree_size
  blkLib07
  blkPC07
  blkPl07
  blkPlaceable07
  blkTree07
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  sha3_512List_len
  stackAt_1136_split_720
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x0228 → 0x02bc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

private theorem blk00_rw1_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 0)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_72_6_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk00_keccak2_72_6_RW1_ok

private theorem blk29_memset_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC07 sha3_512List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

/-! ## 1. Vector Range & Zero-Block Helpers -/

private theorem vec2_bytesToVecNat_eq (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    Vec128At ptr (bytesToVecNat bs 0) ∗ Vec128At (ptr + 16#64) (bytesToVecNat bs 1) =
      (ptr ↦ₛ bs) := by
  have hv := pointsToBytes_eq_vecRangeMem 2 ptr h
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  exact hv.symm

private theorem vec4_bytesToVecNat_eq (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    Vec128At ptr (bytesToVecNat bs 0) ∗
      (Vec128At (ptr + 16#64) (bytesToVecNat bs 1) ∗
        (Vec128At (ptr + 16#64 + 16#64) (bytesToVecNat bs 2) ∗
          Vec128At (ptr + 16#64 + 16#64 + 16#64) (bytesToVecNat bs 3))) =
      (ptr ↦ₛ bs) := by
  have hv := pointsToBytes_eq_vecRangeMem 4 ptr h
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  exact hv.symm

private theorem vec2_zero_eq_replicate32 (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗ Vec128At (ptr + 16#64) 0#128 =
      (ptr ↦ₛ List.replicate 32 0#8) := by
  have hv := vecRangeMem_eq_pointsToBytes 2 ptr (fun _ => 0#128)
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  have hb : vecRangeBytes 2 (fun _ => 0#128) = List.replicate 32 0#8 := rfl
  rwa [hb] at hv

private theorem vec4_zero_entails_memRegion64 (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗
      (Vec128At (ptr + 16#64) 0#128 ∗
        (Vec128At (ptr + 16#64 + 16#64) 0#128 ∗
          Vec128At (ptr + 16#64 + 16#64 + 16#64) 0#128)) ⊢
      memRegion ptr 64 := by
  simpa [VecRangeMem, sepConj_emp] using vecRangeMem_entails_memRegion 4 ptr (fun _ => 0#128)
/-! ## 2. `B00` (`(kBar, r) = sha3_512List (m ++ hPk)`) (`+0x0228 → +0x0280`) -/

theorem seg1a3_hash_g [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (m hPk : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hhPk : hPk.length = 32)
    (hpc : s.pc = b + 0x0228#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx20 : s.readReg64 .x20 = pkA)
    (hx21 : s.readReg64 .x21 = pkA + 384#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 2560#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0280#64) s
      (stackAt sp 1136 ∗ ((sp + 2432#64) ↦ₛ m) ∗ memRegion (sp + 2464#64) 32 ∗
        memRegion (sp + 2560#64) 64 ∗ memRegion (sp + 12832#64) 64 ∗
        memRegion (sp + 28848#64) 32 ∗ ((sp + 32896#64) ↦ₛ hPk) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = pkA + 384#64 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = pkA + 384#64 ∧
        sf.readReg64 .x22 = sp + 26768#64 ∧
        sf.readReg64 .x23 = sp + 2560#64 ∧
        sf.readReg64 .x24 = sp + 27032#64 ∧
        sf.readReg64 .x26 = sp + 12832#64 ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 2432#64) 64 ∗
          ((sp + 2560#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
          memRegion (sp + 12832#64) 64 ∗
          memRegion (sp + 28848#64) 32 ∗ memRegion (sp + 32896#64) 32 ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 636#64) s
      (stackAt sp 1136 ∗ ((sp + 2432#64) ↦ₛ m) ∗ memRegion (sp + 2464#64) 32 ∗
        memRegion (sp + 2560#64) 64 ∗ memRegion (sp + 12832#64) 64 ∗
        memRegion (sp + 28848#64) 32 ∗ ((sp + 32896#64) ↦ₛ hPk) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 28848#64 ∧
        sm.readReg64 .x1 = sp + 2560#64 ∧
        sm.readReg64 .x2 = sp + 12832#64 ∧
        sm.readReg64 .x19 = pkA + 384#64 ∧
        sm.readReg64 .x20 = pkA ∧
        sm.readReg64 .x21 = pkA + 384#64 ∧
        sm.readReg64 .x22 = sp + 26768#64 ∧
        sm.readReg64 .x23 = sp + 2560#64 ∧
        sm.readReg64 .x24 = sp + 27032#64 ∧
        sm.readReg64 .x26 = sp + 12832#64 ∧
        sm.readReg64 .fp = sp + 33008#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 28848#64) (sp + 2432#64) (sp + 2432#64)
            (m ++ hPk).length (m ++ hPk).length ∗
          ((sp + 2432#64) ↦ₛ (m ++ hPk)) ∗
          memRegion (sp + 2560#64) 64 ∗ memRegion (sp + 12832#64) 64 ∗
          stackAt sp 720 ∗
          (memRegion (sp - 1136#64) 416 ∗ memRegion (sp + 32896#64) 32 ∗ Rest))) := by
    rw [stackAt_1136_split_720 sp, ← vec2_bytesToVecNat_eq (sp + 32896#64) hhPk]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 28848#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 2464#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f24 => ?_
    refine SepWP.of_memRegion_vecRangeMem 4 (sp + 2560#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f25 => ?_
    dsimp only [VecRangeMem]
    simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 2560#64) (f25 0) ∗
        (Vec128At (sp + 2560#64 + 16#64) (f25 1) ∗
          (Vec128At (sp + 2560#64 + 16#64 + 16#64) (f25 2) ∗
            Vec128At (sp + 2560#64 + 16#64 + 16#64 + 16#64) (f25 3)))) ∗
      (Vec128At (sp + 2464#64) (f24 0) ∗ Vec128At (sp + 2464#64 + 16#64) (f24 1)) ∗
      (Vec128At (sp + 32896#64) (bytesToVecNat hPk 0) ∗
        Vec128At (sp + 32896#64 + 16#64) (bytesToVecNat hPk 1)) ∗
      (sp + 28848#64) ↦₆₄ s0_c ∗ ((sp + 28848#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 28848#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 28848#64 + 24#64) ↦₆₄ s3_c) ∗
      memRegion (sp - 1136#64) 416 ∗ stackAt sp 720 ∗ ((sp + 2432#64) ↦ₛ m) ∗
      memRegion (sp + 12832#64) 64 ∗ Rest by sep_frame) ?_
    have ha32_16 : sp + 32896#64 + 16#64 = sp + 32912#64 := by clear * -; bv_omega
    have ha24_16 : sp + 2464#64 + 16#64 = sp + 2480#64 := by clear * -; bv_omega
    have ha25_16 : sp + 2560#64 + 16#64 = sp + 2576#64 := by clear * -; bv_omega
    have ha25_32 : sp + 2560#64 + 16#64 + 16#64 = sp + 2592#64 := by clear * -; bv_omega
    have ha25_48 : sp + 2560#64 + 16#64 + 16#64 + 16#64 = sp + 2608#64 := by clear * -; bv_omega
    refine step_ldpQ128 (wb := none) (ea := sp + 32896#64) (ea16 := sp + 32912#64)
      (v1 := bytesToVecNat hPk 0) (v2 := bytesToVecNat hPk 1)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp]) ha32_16
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.vec128At ha32_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 7
    refine step_strQ128 (wb := none) (ea := sp + 2464#64) (val := bytesToVecNat hPk 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 2480#64) (val := bytesToVecNat hPk 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha24_16))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 3
    refine step_strQ128 (wb := none) (ea := sp + 2608#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.right
        (SepStore128.vec128At ha25_48)))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2592#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.left
        (SepStore128.vec128At ha25_32)))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2576#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.left
        (SepStore128.vec128At ha25_16))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2560#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec4_zero_entails_memRegion64 (sp + 2560#64))) ?_
    wp_steps 2
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp,
        by simp [hx19], by simp [hx20], by simp [hx21],
        by simp [hx22], by simp [hx23], by simp [hx24],
        by simp, by simp [hfp], ?_⟩
    have hm_len : (m ++ hPk).length = 64 := by simp [hm, hhPk]
    have hcat : ((sp + 2432#64) ↦ₛ (m ++ hPk)) =
        ((sp + 2432#64) ↦ₛ m) ∗ ((sp + 2464#64) ↦ₛ hPk) := by
      rw [pointsToBytes_append, hm]
      have ha : sp + 2432#64 + BitVec.ofNat 64 32 = sp + 2464#64 := by clear * -; bv_omega
      rw [ha]
    have hhPk_reg : ((sp + 32896#64) ↦ₛ hPk) ⊢ memRegion (sp + 32896#64) 32 := by
      rw [← hhPk]; exact pointsToBytes_entails_memRegion _ _
    rw [hm_len, hcat, vec2_bytesToVecNat_eq (sp + 2464#64) hhPk,
      vec2_bytesToVecNat_eq (sp + 32896#64) hhPk]
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 2560#64) 64 ∗
      ((sp + 2464#64) ↦ₛ hPk) ∗ memRegion (sp + 32896#64) 32 ∗
      ((sp + 28848#64) ↦₆₄ (sp + 2432#64)) ∗ ((sp + 28856#64) ↦₆₄ 64#64) ∗
      ((sp + 28864#64) ↦₆₄ (sp + 2432#64)) ∗ ((sp + 28872#64) ↦₆₄ 64#64) ∗
      memRegion (sp - 1136#64) 416 ∗ stackAt sp 720 ∗ ((sp + 2432#64) ↦ₛ m) ∗
      memRegion (sp + 12832#64) 64 ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhPk_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : (m ++ hPk).length < 72 := by simp [hm, hhPk]
  wp_call (blk00_rw1_07 blkPl07.base) (sp + 28848#64, sp + 2432#64, sp + 2560#64, sp + 12832#64, m ++ hPk)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 28848#64) (sp + 2432#64) (sp + 2432#64)
    (m ++ hPk).length (m ++ hPk).length
  have hin_reg : ((sp + 2432#64) ↦ₛ (m ++ hPk)) ⊢ memRegion (sp + 2432#64) 64 := by
    have hl : (m ++ hPk).length = 64 := by simp [hm, hhPk]
    have h := pointsToBytes_entails_memRegion (sp + 2432#64) (m ++ hPk)
    rwa [hl] at h
  have hout1_reg : ((sp + 12832#64) ↦ₛ sha3_512List (m ++ hPk)) ⊢ memRegion (sp + 12832#64) 64 := by
    have h := pointsToBytes_entails_memRegion (sp + 12832#64) (sha3_512List (m ++ hPk))
    rwa [sha3_512List_len (m ++ hPk)] at h
  rw [hspm, stackAt_1136_split_720 sp]
  refine Entails.trans (Q := memRegion (sp + 28848#64) 32 ∗
    memRegion (sp + 2432#64) 64 ∗ ((sp + 2560#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
    memRegion (sp + 12832#64) 64 ∗ stackAt sp 720 ∗
    (memRegion (sp - 1136#64) 416 ∗ memRegion (sp + 32896#64) 32 ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono hin_reg
    (sepConj_mono_right (sepConj_mono hout1_reg (Entails.refl _))))
/-! ## 3. Copy `(kBar, r)` to `sp + 2496` & `B29` (`memset` `10240` B) (`+0x0280 → +0x02c0`) -/

theorem seg1a3_copy_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (kr : List (BitVec 8)) (Rest : SepProp)
    (hkr : kr.length = 64)
    (hpc : s.pc = b + 0x0280#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx20 : s.readReg64 .x20 = pkA)
    (hx21 : s.readReg64 .x21 = pkA + 384#64)
    (hx22 : s.readReg64 .x22 = sp + 26768#64)
    (hx23 : s.readReg64 .x23 = sp + 2560#64)
    (hx24 : s.readReg64 .x24 = sp + 27032#64)
    (hx26 : s.readReg64 .x26 = sp + 12832#64)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x02c0#64) s
      (memRegion (sp + 2496#64) 64 ∗ ((sp + 2560#64) ↦ₛ kr) ∗
        memRegion (sp + 12832#64) 10240 ∗ memRegion (sp + 23072#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = pkA + 384#64 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = pkA + 384#64 ∧
        sf.readReg64 .x22 = sp + 26768#64 ∧
        sf.readReg64 .x23 = sp + 2560#64 ∧
        sf.readReg64 .x24 = sp + 27032#64 ∧
        sf.readReg64 .x26 = sp + 12832#64 ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ ((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 2560#64) 64 ∗
          memRegion (sp + 12832#64) 8192 ∗ memRegion (sp + 21024#64) 2048 ∗
          ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none)) (blkPl07.base + 700#64) s
      (memRegion (sp + 2496#64) 64 ∗ ((sp + 2560#64) ↦ₛ kr) ∗
        memRegion (sp + 12832#64) 10240 ∗ memRegion (sp + 23072#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 12832#64 ∧
        (sm.readReg32 .x1).truncate 8 = 0#8 ∧
        (sm.readReg64 .x2).toNat = 10240 ∧
        sm.readReg64 .x19 = pkA + 384#64 ∧
        sm.readReg64 .x20 = pkA ∧
        sm.readReg64 .x21 = pkA + 384#64 ∧
        sm.readReg64 .x22 = sp + 26768#64 ∧
        sm.readReg64 .x23 = sp + 2560#64 ∧
        sm.readReg64 .x24 = sp + 27032#64 ∧
        sm.readReg64 .x26 = sp + 12832#64 ∧
        sm.readReg64 .fp = sp + 33008#64 ∧
        (Pm ⊢ memRegion (sp + 12832#64) 10240 ∗
          (((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 2560#64) 64 ∗
            ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗ Rest))) := by
    rw [← vec4_bytesToVecNat_eq (sp + 2560#64) hkr]
    refine SepWP.of_memRegion_vecRangeMem 4 (sp + 2496#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f24 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 23072#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f23 => ?_
    dsimp only [VecRangeMem]
    simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 23072#64) (f23 0) ∗ Vec128At (sp + 23072#64 + 16#64) (f23 1)) ∗
      (Vec128At (sp + 2496#64) (f24 0) ∗
        (Vec128At (sp + 2496#64 + 16#64) (f24 1) ∗
          (Vec128At (sp + 2496#64 + 16#64 + 16#64) (f24 2) ∗
            Vec128At (sp + 2496#64 + 16#64 + 16#64 + 16#64) (f24 3)))) ∗
      (Vec128At (sp + 2560#64) (bytesToVecNat kr 0) ∗
        (Vec128At (sp + 2560#64 + 16#64) (bytesToVecNat kr 1) ∗
          (Vec128At (sp + 2560#64 + 16#64 + 16#64) (bytesToVecNat kr 2) ∗
            Vec128At (sp + 2560#64 + 16#64 + 16#64 + 16#64) (bytesToVecNat kr 3)))) ∗
      memRegion (sp + 12832#64) 10240 ∗ Rest by sep_frame) ?_
    have ha23_16 : sp + 23072#64 + 16#64 = sp + 23088#64 := by clear * -; bv_omega
    have ha24_16 : sp + 2496#64 + 16#64 = sp + 2512#64 := by clear * -; bv_omega
    have ha24_32 : sp + 2496#64 + 16#64 + 16#64 = sp + 2528#64 := by clear * -; bv_omega
    have ha24_48 : sp + 2496#64 + 16#64 + 16#64 + 16#64 = sp + 2544#64 := by clear * -; bv_omega
    have ha25_16 : sp + 2560#64 + 16#64 = sp + 2576#64 := by clear * -; bv_omega
    have ha25_32 : sp + 2560#64 + 16#64 + 16#64 = sp + 2592#64 := by clear * -; bv_omega
    have ha25_48 : sp + 2560#64 + 16#64 + 16#64 + 16#64 = sp + 2608#64 := by clear * -; bv_omega
    refine step_ldrQ128 (wb := none) (ea := sp + 2560#64) (v := bytesToVecNat kr 0)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (by wp_norm_lhs) ?_
    refine step_ldrQ128 (wb := none) (ea := sp + 2576#64) (v := bytesToVecNat kr 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.left (SepLoad128.vec128At ha25_16))))))
      (by wp_norm_lhs) ?_
    wp_steps 1
    refine step_ldrQ128 (wb := none) (ea := sp + 2608#64) (v := bytesToVecNat kr 3)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.right (SepLoad128.right (SepLoad128.vec128At ha25_48)))))))
      (by wp_norm_lhs) ?_
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 2496#64) (val := bytesToVecNat kr 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_ldrQ128 (wb := none) (ea := sp + 2592#64) (v := bytesToVecNat kr 2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right
        (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At ha25_32)))))))
      (by wp_norm_lhs) ?_
    wp_steps 1
    refine step_strQ128 (wb := none) (ea := sp + 2512#64) (val := bytesToVecNat kr 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right
        (SepStore128.left (SepStore128.vec128At ha24_16)))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2528#64) (val := bytesToVecNat kr 2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right
        (SepStore128.right (SepStore128.left (SepStore128.vec128At ha24_32))))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 1
    refine step_strQ128 (wb := none) (ea := sp + 2544#64) (val := bytesToVecNat kr 3)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right
        (SepStore128.right (SepStore128.right (SepStore128.vec128At ha24_48))))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 23088#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha23_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 23072#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp [State.readReg32], by simp,
        by simp [hx19], by simp [hx20], by simp [hx21],
        by simp [hx22], by simp [hx23], by simp [hx24],
        by simp [hx26], by simp [hfp], ?_⟩
    rw [vec2_zero_eq_replicate32 (sp + 23072#64),
      vec4_bytesToVecNat_eq (sp + 2496#64) hkr,
      vec4_bytesToVecNat_eq (sp + 2560#64) hkr]
    have h25_reg : ((sp + 2560#64) ↦ₛ kr) ⊢ memRegion (sp + 2560#64) 64 := by
      have h := pointsToBytes_entails_memRegion (sp + 2560#64) kr
      rwa [hkr] at h
    refine Entails.trans (Q := ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗
      ((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 2560#64) 64 ∗
      memRegion (sp + 12832#64) 10240 ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h25_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx21_m, hx22_m, hx23_m, hx24_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  wp_call (blk29_memset_07 blkPl07.base) (sp + 12832#64, 0#8, 10240)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have h10240 : ((sp + 12832#64) ↦ₛ List.replicate 10240 0#8) ⊢
      memRegion (sp + 12832#64) 8192 ∗ memRegion (sp + 21024#64) 2048 := by
    rw [← memRegion_split' (b := sp + 12832#64) (b' := sp + 21024#64)
      (n := (8192 : Nat)) (k := (2048 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    have h := pointsToBytes_entails_memRegion (sp + 12832#64) (List.replicate 10240 0#8)
    rwa [List.length_replicate] at h
  refine Entails.trans (Q := (memRegion (sp + 12832#64) 8192 ∗ memRegion (sp + 21024#64) 2048) ∗
    (((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 2560#64) 64 ∗
      ((sp + 23072#64) ↦ₛ List.replicate 32 0#8) ∗ Rest))
    (sepConj_mono_left h10240) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a3
