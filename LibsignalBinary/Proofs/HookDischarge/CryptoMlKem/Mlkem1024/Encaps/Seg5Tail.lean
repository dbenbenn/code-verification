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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2

/-!
# `kyber_encapsulate` (`B07`) — Segment 5 Tail & Epilogue (`+0x9ed4 .. +0x9fe0` `ret`)

Proves the two `1568`-byte `B28` `memcpy` calls copying `ct = c₁ ++ c₂` to `sp + 28848` and `ret`,
`B02` (`keccak2::<136, 6>`, `H(ct)`), `B01` (`keccak2::<136, 31>`, `SHAKE-256(k̄ ‖ H(ct))`),
writing `ss` (`32` B) to `ret + 1568`, and restoring `SavedFrame07` + `ret`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Tail

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_256List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat pointsToBytes_eq_vecRangeMem step_ldpQ128 step_ldrQ128 step_stpQ128
  step_strQ128 vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_region32 spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  SavedFrame07 blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07
  blkTree07 savedFrame07_entails_memRegion160)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  blk02_rw1_07 sha3_256List_len shake256List_len stackAt_1136_split_1040)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2 (blk01_rw1_07)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Compress (offSeg5Tail)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x9ed4 → 0x9fe0]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm]
theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]
end Simp
open scoped Simp

private theorem blk28_memcpy_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC07 sha3_256List shake256List
attribute [local wp_norm ↓ high] Simp.exec_simdMovi_2d_0

private theorem vec2_bytesToVecNat_eq (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    Vec128At ptr (bytesToVecNat bs 0) ∗ Vec128At (ptr + 16#64) (bytesToVecNat bs 1) =
      (ptr ↦ₛ bs) := by
  have hv := pointsToBytes_eq_vecRangeMem 2 ptr h
  dsimp only [VecRangeMem] at hv
  simp only [sepConj_emp] at hv
  exact hv.symm

private theorem vec2_zero_entails_memRegion32 (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗ Vec128At (ptr + 16#64) 0#128 ⊢ memRegion ptr 32 := by
  simpa [VecRangeMem, sepConj_emp] using vecRangeMem_entails_memRegion 2 ptr (fun _ => 0#128)

/-! ## 1. `B28` `memcpy` Pair (`+0x9ed4 → +0x9f10`) -/

private theorem seg5_tail_memcpy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp ret : BitVec 64) (ct : List (BitVec 8)) (Rest : SepProp)
    (hct : ct.length = 1568)
    (hpc : s.pc = b + offSeg5Tail) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 40720) s
      (((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 23104#64) ↦ₛ ct) ∗
        memRegion (sp + 28848#64) 1568 ∗ memRegion ret 1568 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 1568#64 ∧
        sf.readReg64 .x20 = sp + 28848#64 ∧
        sf.readReg64 .x21 = ret ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ memRegion (sp + 8#64) 8 ∗ memRegion (sp + 23104#64) 1568 ∗
          ((sp + 28848#64) ↦ₛ ct) ∗ (ret ↦ₛ ct) ∗ Rest)) := by
  subst hbase
  have hpc' : s.pc = blkPl07.base + BitVec.ofNat 64 40660 := hpc
  have hlt64 : ct.length < 2 ^ 64 := by rw [hct]; decide
  have hc1 : SepWP (blkPC07.rebase blkPl07.base (fun _ => none))
      (blkPl07.base + BitVec.ofNat 64 40696) s
      (((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 23104#64) ↦ₛ ct) ∗
        memRegion (sp + 28848#64) 1568 ∗ memRegion ret 1568 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 1568#64 ∧
        s1.readReg64 .x20 = sp + 28848#64 ∧
        s1.readReg64 .fp = sp + 33008#64 ∧
        (P1 ⊢ ((sp + 8#64) ↦₆₄ ret) ∗ memRegion (sp + 23104#64) 1568 ∗
          ((sp + 28848#64) ↦ₛ ct) ∗ memRegion ret 1568 ∗ Rest)) := by
    wp_steps 8
    refine SepWP.weaken_pre (show _ ⊢ memRegion (sp + 28848#64) ct.length ∗ ((sp + 23104#64) ↦ₛ ct) ∗
        (((sp + 8#64) ↦₆₄ ret) ∗ memRegion ret 1568 ∗ Rest) by rw [hct]; sep_frame) ?_
    wp_call (blk28_memcpy_07 blkPl07.base) (sp + 28848#64, sp + 23104#64, ct)
    have hsp1 : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption)
      ⟨hsp1, spAligned_of_chk hsp1 hsp_chk, by simp [*], by simp [*], by simp [*], ?_⟩
    have h23 : ((sp + 23104#64) ↦ₛ ct) ⊢ memRegion (sp + 23104#64) 1568 := by
      simpa only [hct] using pointsToBytes_entails_memRegion (sp + 23104#64) ct
    exact Entails.trans (sepConj_mono_right (sepConj_mono_left h23)) (by sep_frame)
  refine sepWP_seq_env hcl hro hc1 ?_
  rintro s1 P1 hpc1 hrun1 _ _ ⟨hsp1, hspA1, hx19_1, hx20_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  wp_steps 5
  refine SepWP.weaken_pre (show _ ⊢ memRegion ret ct.length ∗ ((sp + 28848#64) ↦ₛ ct) ∗
      (((sp + 8#64) ↦₆₄ ret) ∗ memRegion (sp + 23104#64) 1568 ∗ Rest) by rw [hct]; sep_frame) ?_
  wp_call (blk28_memcpy_07 blkPl07.base) (ret, sp + 28848#64, ct)
  have hsp2 : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp2, spAligned_of_chk hsp2 hsp_chk, by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have h8 : ((sp + 8#64) ↦₆₄ ret) ⊢ memRegion (sp + 8#64) 8 := pointsTo64_entails_memRegion _ _
  exact Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h8))) (by sep_frame)

/-! ## 2. `B02` `H(ct) = sha3_256List ct` (`+0x9f10 → +0x9f4c`) -/

private theorem seg5_tail_hash_ct [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp ret : BitVec 64) (kBar ct : List (BitVec 8)) (Rest : SepProp)
    (hkBar : kBar.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + BitVec.ofNat 64 40720) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = 1568#64)
    (hx20 : s.readReg64 .x20 = sp + 28848#64)
    (hx21 : s.readReg64 .x21 = ret)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 40780) s
      (stackAt sp 1136 ∗ ((sp + 2496#64) ↦ₛ kBar) ∗ memRegion (sp + 2560#64) 32 ∗
        memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 26768#64) 32 ∗
        ((sp + 28848#64) ↦ₛ ct) ∗ memRegion (sp + 32864#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x21 = ret ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 2496#64) 32 ∗ memRegion (sp + 2560#64) 32 ∗
          ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 26768#64) 32 ∗
          memRegion (sp + 28848#64) 1568 ∗ ((sp + 32864#64) ↦ₛ sha3_256List ct) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hfp_sub : (sp + 33008#64) + 0xffffffffffffff70#64 = sp + 32864#64 := by clear * -; bv_omega
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none))
      (blkPl07.base + BitVec.ofNat 64 40776) s
      (stackAt sp 1136 ∗ ((sp + 2496#64) ↦ₛ kBar) ∗ memRegion (sp + 2560#64) 32 ∗
        memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 26768#64) 32 ∗
        ((sp + 28848#64) ↦ₛ ct) ∗ memRegion (sp + 32864#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 2560#64 ∧ sm.readReg64 .x1 = sp + 32864#64 ∧
        sm.readReg64 .x2 = sp + 26768#64 ∧ sm.readReg64 .x21 = ret ∧
        sm.readReg64 .fp = sp + 33008#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 2560#64) (sp + 28848#64) (sp + 28848#64) ct.length ct.length ∗
          ((sp + 28848#64) ↦ₛ ct) ∗ memRegion (sp + 32864#64) 32 ∗ memRegion (sp + 26768#64) 32 ∗
          stackAt sp 1040 ∗
          (memRegion (sp - 1136#64) 96 ∗ memRegion (sp + 2496#64) 32 ∗
            ((sp + 12832#64) ↦ₛ kBar) ∗ Rest))) := by
    rw [stackAt_1136_split_1040 sp, ← vec2_bytesToVecNat_eq (sp + 2496#64) hkBar]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 2560#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 12832#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f12 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 32864#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f32 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 32864#64) (f32 0) ∗ Vec128At (sp + 32864#64 + 16#64) (f32 1)) ∗
      (Vec128At (sp + 12832#64) (f12 0) ∗ Vec128At (sp + 12832#64 + 16#64) (f12 1)) ∗
      (Vec128At (sp + 2496#64) (bytesToVecNat kBar 0) ∗
        Vec128At (sp + 2496#64 + 16#64) (bytesToVecNat kBar 1)) ∗
      (sp + 2560#64) ↦₆₄ s0_c ∗ ((sp + 2560#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 2560#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 2560#64 + 24#64) ↦₆₄ s3_c) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 26768#64) 32 ∗
      ((sp + 28848#64) ↦ₛ ct) ∗ Rest by sep_frame) ?_
    have ha24_16 : sp + 2496#64 + 16#64 = sp + 2512#64 := by clear * -; bv_omega
    have ha12_16 : sp + 12832#64 + 16#64 = sp + 12848#64 := by clear * -; bv_omega
    have ha32_16 : sp + 32864#64 + 16#64 = sp + 32880#64 := by clear * -; bv_omega
    wp_steps 1
    refine step_ldrQ128 (wb := none) (ea := sp + 2496#64) (v := bytesToVecNat kBar 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (by wp_norm_lhs) ?_
    refine step_ldrQ128 (wb := none) (ea := sp + 2512#64) (v := bytesToVecNat kBar 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha24_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 4
    refine step_strQ128 (wb := none) (ea := sp + 12832#64) (val := bytesToVecNat kBar 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 12848#64) (val := bytesToVecNat kBar 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha12_16))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_stpQ128 (wb := none) (ea := sp + 32864#64) (ea16 := sp + 32880#64)
      (v1 := 0#128) (v2 := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp, hfp_sub]) ha32_16 (by simp) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha32_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 32864#64))) ?_
    wp_steps 4
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp,
        by simp [hx21], by simp [hfp], ?_⟩
    rw [hct, vec2_bytesToVecNat_eq (sp + 12832#64) hkBar,
      vec2_bytesToVecNat_eq (sp + 2496#64) hkBar]
    have hk_reg : ((sp + 2496#64) ↦ₛ kBar) ⊢ memRegion (sp + 2496#64) 32 := by
      simpa only [hkBar] using pointsToBytes_entails_memRegion (sp + 2496#64) kBar
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 32864#64) 32 ∗
      ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 2496#64) 32 ∗
      ((sp + 2560#64) ↦₆₄ (sp + 28848#64)) ∗ ((sp + 2568#64) ↦₆₄ 1568#64) ∗
      ((sp + 2576#64) ↦₆₄ (sp + 28848#64)) ∗ ((sp + 2584#64) ↦₆₄ 1568#64) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 26768#64) 32 ∗
      ((sp + 28848#64) ↦ₛ ct) ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hk_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx21_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : ct.length < 2 ^ 32 := by rw [hct]; decide
  wp_call (blk02_rw1_07 blkPl07.base) (sp + 2560#64, sp + 28848#64, sp + 32864#64, sp + 26768#64, ct)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 2560#64) (sp + 28848#64) (sp + 28848#64)
    ct.length ct.length
  have hct_reg : ((sp + 28848#64) ↦ₛ ct) ⊢ memRegion (sp + 28848#64) 1568 := by
    simpa only [hct] using pointsToBytes_entails_memRegion (sp + 28848#64) ct
  have hout1 : ((sp + 26768#64) ↦ₛ sha3_256List ct) ⊢ memRegion (sp + 26768#64) 32 := by
    simpa only [sha3_256List_len ct] using pointsToBytes_entails_memRegion (sp + 26768#64) (sha3_256List ct)
  rw [hspm, stackAt_1136_split_1040 sp]
  refine Entails.trans (Q := memRegion (sp + 2560#64) 32 ∗
    memRegion (sp + 28848#64) 1568 ∗ ((sp + 32864#64) ↦ₛ sha3_256List ct) ∗
    memRegion (sp + 26768#64) 32 ∗ stackAt sp 1040 ∗
    (memRegion (sp - 1136#64) 96 ∗ memRegion (sp + 2496#64) 32 ∗
      ((sp + 12832#64) ↦ₛ kBar) ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono hct_reg
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

/-! ## 3. `B01` `ss = shake256List 32 (kBar ++ hCt)` (`+0x9f4c → +0x9fa0`) -/

private theorem seg5_tail_kdf [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp ret : BitVec 64) (kBar hCt : List (BitVec 8)) (Rest : SepProp)
    (hkBar : kBar.length = 32) (hhCt : hCt.length = 32)
    (hpc : s.pc = b + BitVec.ofNat 64 40780) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx21 : s.readReg64 .x21 = ret)
    (hfp : s.readReg64 .fp = sp + 33008#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 40864) s
      (stackAt sp 1136 ∗ memRegion (sp + 2560#64) 32 ∗
        ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 12864#64) 32 ∗
        memRegion (sp + 26768#64) 32 ∗ memRegion (sp + 32704#64) 32 ∗
        ((sp + 32864#64) ↦ₛ hCt) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x21 = ret ∧
        sf.readReg64 .fp = sp + 33008#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 2560#64) 32 ∗
          memRegion (sp + 12832#64) 64 ∗ memRegion (sp + 26768#64) 32 ∗
          ((sp + 32704#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ∗
          memRegion (sp + 32864#64) 32 ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hfp_sub : (sp + 33008#64) + 0xffffffffffffff70#64 = sp + 32864#64 := by clear * -; bv_omega
  have hprep : SepWP (blkPC07.rebase blkPl07.base (fun _ => none))
      (blkPl07.base + BitVec.ofNat 64 40860) s
      (stackAt sp 1136 ∗ memRegion (sp + 2560#64) 32 ∗
        ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 12864#64) 32 ∗
        memRegion (sp + 26768#64) 32 ∗ memRegion (sp + 32704#64) 32 ∗
        ((sp + 32864#64) ↦ₛ hCt) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 2560#64 ∧ sm.readReg64 .x1 = sp + 32704#64 ∧
        sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 .x3 = sp + 26768#64 ∧
        sm.readReg64 .x4 = 32#64 ∧ sm.readReg64 .x21 = ret ∧
        sm.readReg64 .fp = sp + 33008#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 2560#64) (sp + 12832#64) (sp + 12832#64)
            (kBar ++ hCt).length (kBar ++ hCt).length ∗
          ((sp + 12832#64) ↦ₛ (kBar ++ hCt)) ∗
          memRegion (sp + 32704#64) 32 ∗ memRegion (sp + 26768#64) 32 ∗
          stackAt sp 1136 ∗ (memRegion (sp + 32864#64) 32 ∗ Rest))) := by
    rw [← vec2_bytesToVecNat_eq (sp + 32864#64) hhCt]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 2560#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 12864#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f12 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 32704#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f32 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 32704#64) (f32 0) ∗ Vec128At (sp + 32704#64 + 16#64) (f32 1)) ∗
      (Vec128At (sp + 12864#64) (f12 0) ∗ Vec128At (sp + 12864#64 + 16#64) (f12 1)) ∗
      (Vec128At (sp + 32864#64) (bytesToVecNat hCt 0) ∗
        Vec128At (sp + 32864#64 + 16#64) (bytesToVecNat hCt 1)) ∗
      (sp + 2560#64) ↦₆₄ s0_c ∗ ((sp + 2560#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 2560#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 2560#64 + 24#64) ↦₆₄ s3_c) ∗
      stackAt sp 1136 ∗ ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 26768#64) 32 ∗ Rest
      by sep_frame) ?_
    have ha12_16 : sp + 12864#64 + 16#64 = sp + 12880#64 := by clear * -; bv_omega
    have ha32_16 : sp + 32704#64 + 16#64 = sp + 32720#64 := by clear * -; bv_omega
    have ha328_16 : sp + 32864#64 + 16#64 = sp + 32880#64 := by clear * -; bv_omega
    refine step_ldpQ128 (wb := none) (ea := sp + 32864#64) (ea16 := sp + 32880#64)
      (v1 := bytesToVecNat hCt 0) (v2 := bytesToVecNat hCt 1)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp, hfp_sub]) ha328_16
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha328_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 7
    refine step_strQ128 (wb := none) (ea := sp + 12864#64) (val := bytesToVecNat hCt 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 4
    refine step_strQ128 (wb := none) (ea := sp + 12880#64) (val := bytesToVecNat hCt 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha12_16))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 32704#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 32720#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha32_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 32704#64))) ?_
    wp_steps 2
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp, by simp, by simp,
        by simp [hx21], by simp [hfp], ?_⟩
    have hm_len : (kBar ++ hCt).length = 64 := by simp [hkBar, hhCt]
    have hcat : ((sp + 12832#64) ↦ₛ (kBar ++ hCt)) =
        ((sp + 12832#64) ↦ₛ kBar) ∗ ((sp + 12864#64) ↦ₛ hCt) := by
      rw [pointsToBytes_append, hkBar]
      have ha : sp + 12832#64 + BitVec.ofNat 64 32 = sp + 12864#64 := by clear * -; bv_omega
      rw [ha]
    have hhCt_reg : ((sp + 32864#64) ↦ₛ hCt) ⊢ memRegion (sp + 32864#64) 32 := by
      simpa only [hhCt] using pointsToBytes_entails_memRegion (sp + 32864#64) hCt
    rw [hm_len, hcat, vec2_bytesToVecNat_eq (sp + 12864#64) hhCt,
      vec2_bytesToVecNat_eq (sp + 32864#64) hhCt]
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 32704#64) 32 ∗
      ((sp + 12864#64) ↦ₛ hCt) ∗ memRegion (sp + 32864#64) 32 ∗
      ((sp + 2560#64) ↦₆₄ (sp + 12832#64)) ∗ ((sp + 2568#64) ↦₆₄ 64#64) ∗
      ((sp + 2576#64) ↦₆₄ (sp + 12832#64)) ∗ ((sp + 2584#64) ↦₆₄ 64#64) ∗
      stackAt sp 1136 ∗ ((sp + 12832#64) ↦ₛ kBar) ∗ memRegion (sp + 26768#64) 32 ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhCt_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx21_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : (kBar ++ hCt).length < 2 ^ 32 := by simp [hkBar, hhCt]
  have houtLen : (32 : Nat) = 32 ∨ (32 : Nat) = 128 := Or.inl rfl
  wp_call (blk01_rw1_07 blkPl07.base) (sp + 2560#64, sp + 12832#64, sp + 32704#64, sp + 26768#64, 32, kBar ++ hCt)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 2560#64) (sp + 12832#64) (sp + 12832#64)
    (kBar ++ hCt).length (kBar ++ hCt).length
  have hin_reg : ((sp + 12832#64) ↦ₛ (kBar ++ hCt)) ⊢ memRegion (sp + 12832#64) 64 := by
    have hl : (kBar ++ hCt).length = 64 := by simp [hkBar, hhCt]
    simpa only [hl] using pointsToBytes_entails_memRegion (sp + 12832#64) (kBar ++ hCt)
  have hout1 : ((sp + 26768#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ⊢ memRegion (sp + 26768#64) 32 := by
    simpa only [shake256List_len 32 (kBar ++ hCt)] using
      pointsToBytes_entails_memRegion (sp + 26768#64) (shake256List 32 (kBar ++ hCt))
  rw [hspm]
  refine Entails.trans (Q := memRegion (sp + 2560#64) 32 ∗
    memRegion (sp + 12832#64) 64 ∗ ((sp + 32704#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ∗
    memRegion (sp + 26768#64) 32 ∗ stackAt sp 1136 ∗ (memRegion (sp + 32864#64) 32 ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono hin_reg
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

/-! ## 4. Write `ss` (`+0x9fa0 → +0x9fb0`) & Epilogue (`+0x9fb0 → +0x9fe0` `ret`) -/

private theorem seg5_tail_write_ss [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp ret : BitVec 64) (ss : List (BitVec 8)) (Rest : SepProp)
    (hss : ss.length = 32)
    (hpc : s.pc = b + BitVec.ofNat 64 40864) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = ret) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + BitVec.ofNat 64 40880) s
      (((sp + 32704#64) ↦ₛ ss) ∗ memRegion (ret + 1568#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧
        (Pf ⊢ memRegion (sp + 32704#64) 32 ∗ ((ret + 1568#64) ↦ₛ ss) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  rw [← vec2_bytesToVecNat_eq (sp + 32704#64) hss]
  refine SepWP.of_memRegion_vecRangeMem 2 (ret + 1568#64) (by decide)
    (sepProp_ext (by sep_frame) (by sep_frame)) fun fr => ?_
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  refine SepWP.weaken_pre (show _ ⊢
    (Vec128At (ret + 1568#64) (fr 0) ∗ Vec128At (ret + 1568#64 + 16#64) (fr 1)) ∗
    (Vec128At (sp + 32704#64) (bytesToVecNat ss 0) ∗
      Vec128At (sp + 32704#64 + 16#64) (bytesToVecNat ss 1)) ∗ Rest by sep_frame) ?_
  have ha32_16 : sp + 32704#64 + 16#64 = sp + 32720#64 := by clear * -; bv_omega
  have haret_16 : ret + 1568#64 + 16#64 = ret + 1584#64 := by clear * -; bv_omega
  refine step_ldrQ128 (wb := none) (ea := sp + 32704#64) (v := bytesToVecNat ss 0)
    hpc hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl))))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := sp + 32720#64) (v := bytesToVecNat ss 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha32_16))))
    (by wp_norm_lhs) ?_
  refine step_strQ128 (wb := none) (ea := ret + 1568#64) (val := bytesToVecNat ss 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode, hx21]) (by simp)
    (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  intro _
  refine step_strQ128 (wb := none) (ea := ret + 1584#64) (val := bytesToVecNat ss 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
    (by simp [evalAddrMode, hx21]) (by simp)
    (SepStore128.left (SepStore128.right (SepStore128.vec128At haret_16)))
    (by wp_norm_lhs) ?_
  intro _
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) ⟨by simp [hsp], ?_⟩
  rw [vec2_bytesToVecNat_eq (ret + 1568#64) hss, vec2_bytesToVecNat_eq (sp + 32704#64) hss]
  have hss_reg : ((sp + 32704#64) ↦ₛ ss) ⊢ memRegion (sp + 32704#64) 32 := by
    simpa only [hss] using pointsToBytes_entails_memRegion (sp + 32704#64) ss
  exact Entails.trans (sepConj_mono_right (sepConj_mono_left hss_reg)) (by sep_frame)

private theorem calleeSavedVRegs_eq_of_readVReg128 (s0 sf : State)
    (h : ∀ r : Fin 8, sf.readVReg128 (BitVec.ofNat 5 (8 + r.val)) =
      ((s0.readVReg128 (BitVec.ofNat 5 (8 + r.val))).truncate 64).zeroExtend 128) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  have htr (v : BitVec 128) : ((v.truncate 64).zeroExtend 128).truncate 64 = v.truncate 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
  have hr (i : Fin 8) :
      (sf.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 =
        (s0.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 := by
    rw [h i, htr]
  exact Prod.ext (hr 0) (Prod.ext (hr 1) (Prod.ext (hr 2) (Prod.ext (hr 3)
    (Prod.ext (hr 4) (Prod.ext (hr 5) (Prod.ext (hr 6) (hr 7)))))))

private theorem seg5_tail_epilogue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 s : State) (Rest : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + BitVec.ofNat 64 40880) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 33104#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame07 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  subst hbase
  dsimp only [SavedFrame07]
  have hsp160 : (s0.sp - 33104#64) + 32768#64 + 176#64 = s0.sp - 160#64 := by clear * -; bv_omega
  have hsp160_al : ((((s0.sp - 33104#64) + 32768#64 + 176#64) &&& 15#64) == 0#64) = true := by
    rw [hsp160]; exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega), ?_⟩,
    sepConj_mono_left (savedFrame07_entails_memRegion160 s0.sp s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

/-! ## 5. Top-Level `Seg5Tail` Contract (`+0x9ed4 → ret`) -/

theorem seg5_tail_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s0 s : State) (ret : BitVec 64) (hashed ct : List (BitVec 8)) (Rest : SepProp)
    (hhashed : hashed.length = 64) (hct : ct.length = 1568)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + offSeg5Tail) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 33104#64)
    (hsp_chk : ((s0.sp - 33104#64) &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = (s0.sp - 33104#64) + 33008#64) :
    let sp := s0.sp - 33104#64
    let ss := shake256List 32 (hashed.take 32 ++ sha3_256List ct)
    SepWP (blkPC07.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackAt sp 1136 ∗ ((sp + 8#64) ↦₆₄ ret) ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
        memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 64 ∗
        ((sp + 23104#64) ↦ₛ ct) ∗ memRegion (sp + 26768#64) 32 ∗
        memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 32704#64) 32 ∗
        memRegion (sp + 32864#64) 32 ∗ SavedFrame07 s0.sp s0 ∗
        memRegion ret 1600 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ ct) ∗ ((ret + 1568#64) ↦ₛ ss) ∗
          stackAt sp 1136 ∗ memRegion (sp + 8#64) 8 ∗ memRegion (sp + 2496#64) 64 ∗
          memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 12832#64) 64 ∗
          memRegion (sp + 23104#64) 1568 ∗ memRegion (sp + 26768#64) 32 ∗
          memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 32704#64) 32 ∗
          memRegion (sp + 32864#64) 32 ∗ memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  intro sp ss
  have hret_split : memRegion ret 1600 = memRegion ret 1568 ∗ memRegion (ret + 1568#64) 32 :=
    memRegion_split' (b := ret) (b' := ret + 1568#64) (n := (1568 : Nat)) (k := 32)
      rfl rfl (by decide)
  have h12832_split : memRegion (sp + 12832#64) 64 =
      memRegion (sp + 12832#64) 32 ∗ memRegion (sp + 12864#64) 32 :=
    memRegion_split' (b := sp + 12832#64) (b' := sp + 12864#64) (n := 32) (k := 32)
      rfl (by clear * -; bv_omega) (by decide)
  have hhashed_split : ((sp + 2496#64) ↦ₛ hashed) =
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗ ((sp + 2528#64) ↦ₛ hashed.drop 32) := by
    have hp := pointsToBytes_take_drop (sp + 2496#64) 32 hashed (by omega)
    have ha : sp + 2496#64 + BitVec.ofNat 64 32 = sp + 2528#64 := by clear * -; bv_omega
    rwa [ha] at hp
  have hkBar : (hashed.take 32).length = 32 := by simp [hhashed]
  have hrCoins : (hashed.drop 32).length = 32 := by simp [hhashed]
  rw [hret_split, h12832_split, hhashed_split]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro (seg5_tail_memcpy hb hbase s sp ret ct _ hct hpc hrun hsp hsp_chk hcl hro hfp) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, _, hx19_1, hx20_1, hx21_1, hfp1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
    (sepWP_seq_env hcl1 hro1
      (seg5_tail_hash_ct hb hbase s1 sp ret (hashed.take 32) ct _ hkBar hct
        hpc1 hrun1 hsp1 hsp_chk hcl1 hro1 hx19_1 hx20_1 hx21_1 hfp1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, _, hx21_2, hfp2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2
      (seg5_tail_kdf hb hbase s2 sp ret (hashed.take 32) (sha3_256List ct) _ hkBar (sha3_256List_len ct)
        hpc2 hrun2 hsp2 hsp_chk hcl2 hro2 hx21_2 hfp2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, _, hx21_3, _, hP3⟩
  have hss : ss.length = 32 := shake256List_len 32 _
  refine SepWP.weaken_pre (Entails.trans hP3 (by dsimp only [ss]; sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg5_tail_write_ss hb hbase s3 sp ret ss _ hss hpc3 hrun3 hsp3 hsp_chk hx21_3) ?_)
  rintro s4 P4 hpc4 hrun4 _ _ ⟨hsp4, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (by sep_frame))
    (SepWP.mono
      (seg5_tail_epilogue hb hbase s0 s4 _ (by simpa [State.spAligned] using hsp0) hpc4 hrun4 hsp4) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have h2528 : ((sp + 2528#64) ↦ₛ hashed.drop 32) ⊢ memRegion (sp + 2528#64) 32 := by
    simpa only [hrCoins] using pointsToBytes_entails_memRegion (sp + 2528#64) (hashed.drop 32)
  have h2496_join : memRegion (sp + 2496#64) 64 =
      memRegion (sp + 2496#64) 32 ∗ memRegion (sp + 2528#64) 32 :=
    memRegion_split' (b := sp + 2496#64) (b' := sp + 2528#64) (n := 32) (k := 32)
      rfl (by clear * -; bv_omega) (by decide)
  rw [h2496_join]
  refine Entails.trans (Q := memRegion (s0.sp - 160#64) 160 ∗ memRegion (sp + 32704#64) 32 ∗
      ((ret + 1568#64) ↦ₛ ss) ∗ stackAt sp 1136 ∗ memRegion (sp + 2560#64) 32 ∗
      memRegion (sp + 12832#64) 64 ∗ memRegion (sp + 26768#64) 32 ∗
      memRegion (sp + 32864#64) 32 ∗ memRegion (sp + 2496#64) 32 ∗
      memRegion (sp + 28848#64) 1568 ∗ memRegion (sp + 8#64) 8 ∗
      memRegion (sp + 23104#64) 1568 ∗ (ret ↦ₛ ct) ∗
      memRegion (sp + 2528#64) 32 ∗ Rest) ?_ (by sep_frame)
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left h2528)))))))))))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Tail
