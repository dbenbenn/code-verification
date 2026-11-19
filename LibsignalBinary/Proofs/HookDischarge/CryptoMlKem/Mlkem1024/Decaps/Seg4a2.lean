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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2

/-!
# `kyber_decapsulate` (`B06`) — Segment 4a2 (`+0x3b78 .. +0x3c38`)

Copies `(kBar', r') = sha3_512List (m' ++ hPk)` to `[sp + 2496 .. sp + 2560)`, stages `z ++ ct`
(`1600` B) at `[sp + 2560 .. sp + 4160)`, calls `B01` (`keccak2::<136, 31>`) to compute
`kRejPre = shake256List 32 (z ++ ct)` at `[sp + 34432 .. sp + 34464)`, zeroes
`[sp + 24672 .. sp + 24704)` (`32` B) and `[sp + 14432 .. sp + 24672)` (`10240` B), and composes
`seg4a_ok` (`+0x39c4 → +0x3c38`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW keccak2_136_31_RW1Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat pointsToBytes_eq_vecRangeMem step_ldpQ128 step_ldrQ128 step_strQ128
  vecRangeBytes vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (
  SpilledDecapsWords off39c4 off3b78 seg4a1_ok vec2_bytesToVecNat_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  sha3_512List_len shake256List_len)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x3b78 → 0x3c34]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

theorem blk01_rw1_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk01_keccak2_136_31_RW1_ok

theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC06 sha3_512List shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] private abbrev off3ba4 : BitVec 64 := 15268#64
@[simp, arm64_norm, wp_norm] private abbrev off3ba8 : BitVec 64 := 15272#64
@[simp, arm64_norm, wp_norm] private abbrev off3bc8 : BitVec 64 := 15304#64
@[simp, arm64_norm, wp_norm] private abbrev off3bcc : BitVec 64 := 15308#64
@[simp, arm64_norm, wp_norm] private abbrev off3c14 : BitVec 64 := 15380#64
@[simp, arm64_norm, wp_norm] private abbrev off3c18 : BitVec 64 := 15384#64
@[simp, arm64_norm, wp_norm] private abbrev off3c34 : BitVec 64 := 15412#64
@[simp, arm64_norm, wp_norm] abbrev off3c38 : BitVec 64 := 15416#64

/-! ## 1. Vector Range & Zero-Block Helpers -/

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
    Vec128At ptr 0#128 ∗ Vec128At (ptr + 16#64) 0#128 = (ptr ↦ₛ List.replicate 32 0#8) := by
  have hv := vecRangeMem_eq_pointsToBytes 2 ptr (fun _ => 0#128)
  dsimp only [VecRangeMem] at hv; simp only [sepConj_emp] at hv
  have hb : vecRangeBytes 2 (fun _ => 0#128) = List.replicate 32 0#8 := rfl
  rwa [hb] at hv

private theorem vec2_zero_entails_memRegion32 (ptr : BitVec 64) :
    Vec128At ptr 0#128 ∗ Vec128At (ptr + 16#64) 0#128 ⊢ memRegion ptr 32 := by
  simpa [VecRangeMem, sepConj_emp] using vecRangeMem_entails_memRegion 2 ptr (fun _ => 0#128)

/-! ## 2. Copy `(kBar', r')` to `sp + 2496` & `B29` (`memset` `1568` B) (`+0x3b78 → +0x3ba8`) -/

private theorem seg4a2_copy_kr [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (kr : List (BitVec 8)) (Rest : SepProp)
    (hkr : kr.length = 64) (hpc : s.pc = b + off3b78) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 14432#64) (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3ba8) s
      (memRegion (sp + 2496#64) 64 ∗ ((sp + 4160#64) ↦ₛ kr) ∗
        memRegion (sp + 14464#64) 1568 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x23 = ctA ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 4160#64) 64 ∗
          memRegion (sp + 14464#64) 1568 ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp (by simpa [State.spAligned, hsp] using hspA)
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off3ba4) s
      (memRegion (sp + 2496#64) 64 ∗ ((sp + 4160#64) ↦ₛ kr) ∗
        memRegion (sp + 14464#64) 1568 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 14464#64 ∧ (sm.readReg32 .x1).truncate 8 = 0#8 ∧
        (sm.readReg64 .x2).toNat = 1568 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x23 = ctA ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ memRegion (sp + 14464#64) 1568 ∗
          (((sp + 2496#64) ↦ₛ kr) ∗ memRegion (sp + 4160#64) 64 ∗ Rest))) := by
    rw [← vec4_bytesToVecNat_eq (sp + 4160#64) hkr]
    refine SepWP.of_memRegion_vecRangeMem 4 (sp + 2496#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f24 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    have ha24_16 : sp + 2496#64 + 16#64 = sp + 2512#64 := by clear * -; bv_omega
    have ha24_32 : sp + 2496#64 + 16#64 + 16#64 = sp + 2528#64 := by clear * -; bv_omega
    have ha24_48 : sp + 2496#64 + 16#64 + 16#64 + 16#64 = sp + 2544#64 := by clear * -; bv_omega
    have ha41_16 : sp + 4160#64 + 16#64 = sp + 4176#64 := by clear * -; bv_omega
    have ha41_32 : sp + 4160#64 + 16#64 + 16#64 = sp + 4192#64 := by clear * -; bv_omega
    have ha41_48 : sp + 4160#64 + 16#64 + 16#64 + 16#64 = sp + 4208#64 := by clear * -; bv_omega
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 2496#64) (f24 0) ∗ (Vec128At (sp + 2496#64 + 16#64) (f24 1) ∗
        (Vec128At (sp + 2496#64 + 16#64 + 16#64) (f24 2) ∗
          Vec128At (sp + 2496#64 + 16#64 + 16#64 + 16#64) (f24 3)))) ∗
      (Vec128At (sp + 4160#64) (bytesToVecNat kr 0) ∗
        (Vec128At (sp + 4160#64 + 16#64) (bytesToVecNat kr 1) ∗
          (Vec128At (sp + 4160#64 + 16#64 + 16#64) (bytesToVecNat kr 2) ∗
            Vec128At (sp + 4160#64 + 16#64 + 16#64 + 16#64) (bytesToVecNat kr 3)))) ∗
      memRegion (sp + 14464#64) 1568 ∗ Rest by sep_frame) ?_
    refine step_ldrQ128 (wb := none) (ea := sp + 4160#64) (v := bytesToVecNat kr 0)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))) (by wp_norm_lhs) ?_
    refine step_ldrQ128 (wb := none) (ea := sp + 4176#64) (v := bytesToVecNat kr 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At ha41_16))))) (by wp_norm_lhs) ?_
    wp_steps 1
    refine step_ldrQ128 (wb := none) (ea := sp + 4208#64) (v := bytesToVecNat kr 3)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.vec128At ha41_48)))))) (by wp_norm_lhs) ?_
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 2496#64) (val := bytesToVecNat kr 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp) (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))) (by wp_norm_lhs) ?_
    intro _
    refine step_ldrQ128 (wb := none) (ea := sp + 4192#64) (v := bytesToVecNat kr 2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At ha41_32)))))) (by wp_norm_lhs) ?_
    refine step_strQ128 (wb := none) (ea := sp + 2512#64) (val := bytesToVecNat kr 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.left (SepStore128.vec128At ha24_16)))) (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2528#64) (val := bytesToVecNat kr 2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.vec128At ha24_32))))) (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2544#64) (val := bytesToVecNat kr 3)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.vec128At ha24_48))))) (by wp_norm_lhs) ?_
    intro _
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp, by simp [State.readReg32], by simp,
        by simp, by simp [hx23], by simp, by simp, by simp, ?_⟩
    rw [vec4_bytesToVecNat_eq (sp + 2496#64) hkr, vec4_bytesToVecNat_eq (sp + 4160#64) hkr]
    have h41_reg : ((sp + 4160#64) ↦ₛ kr) ⊢ memRegion (sp + 4160#64) 64 := by
      have h := pointsToBytes_entails_memRegion (sp + 4160#64) kr; rwa [hkr] at h
    exact entails_sub h41_reg (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx23_m, hx25_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : 1568 < 2 ^ 64 := by decide
  wp_call (blk29_memset_06 blkPl06.base) (sp + 14464#64, 0#8, 1568)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, by simpa [State.spAligned, hsp_sf, ← hsp] using hspA,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have h14_reg : ((sp + 14464#64) ↦ₛ List.replicate 1568 0#8) ⊢ memRegion (sp + 14464#64) 1568 := by
    have h := pointsToBytes_entails_memRegion (sp + 14464#64) (List.replicate 1568 0#8)
    rwa [List.length_replicate] at h
  exact entails_sub h14_reg (by sep_frame) (by sep_frame)

/-! ## 3. Stage `z ++ ct` (`1600` B) at `sp + 2560` (`+0x3ba8 → +0x3bcc`) -/

private theorem seg4a2_stage_z_ct [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (z ct : List (BitVec 8)) (Rest : SepProp)
    (hz : z.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + off3ba8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3bcc) s
      (((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2560#64) 1600 ∗
        ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = sp + 2560#64 ∧
        sf.readReg64 .x23 = ctA ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
          ((sp + 2560#64) ↦ₛ (z ++ ct)) ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp (by simpa [State.spAligned, hsp] using hspA)
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off3bc8) s
      (((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2560#64) 1600 ∗
        ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 2592#64 ∧ sm.readReg64 .x1 = ctA ∧
        (sm.readReg64 .x2).toNat = ct.length ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = sp + 2560#64 ∧
        sm.readReg64 .x23 = ctA ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ memRegion (sp + 2592#64) ct.length ∗ (ctA ↦ₛ ct) ∗
          (((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ ((sp + 2560#64) ↦ₛ z) ∗
            ((skA + 3136#64) ↦ₛ z) ∗ Rest))) := by
    have hsplit : memRegion (sp + 2560#64) 1600 =
        memRegion (sp + 2560#64) 32 ∗ memRegion (sp + 2592#64) 1568 :=
      memRegion_split' (b := sp + 2560#64) (b' := sp + 2592#64) (n := 32) (k := (1568 : Nat))
        rfl (by clear * -; bv_omega) (by decide)
    rw [hsplit, ← vec2_bytesToVecNat_eq (skA + 3136#64) hz]
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 2560#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f25 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    have ha_z : skA + 3136#64 + 16#64 = skA + 3152#64 := by clear * -; bv_omega
    have ha25 : sp + 2560#64 + 16#64 = sp + 2576#64 := by clear * -; bv_omega
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 2560#64) (f25 0) ∗ Vec128At (sp + 2560#64 + 16#64) (f25 1)) ∗
      (Vec128At (skA + 3136#64) (bytesToVecNat z 0) ∗
        Vec128At (skA + 3136#64 + 16#64) (bytesToVecNat z 1)) ∗
      (((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2592#64) 1568 ∗
        (ctA ↦ₛ ct) ∗ Rest) by sep_frame) ?_
    wp_steps 5
    refine step_ldpQ128 (wb := none) (ea := skA + 3136#64) (ea16 := skA + 3152#64)
      (v1 := bytesToVecNat z 0) (v2 := bytesToVecNat z 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode]) ha_z
      (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl))))
      (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha_z))))
      (by wp_norm_lhs) ?_
    refine step_strQ128 (wb := none) (ea := sp + 2560#64) (val := bytesToVecNat z 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 2576#64) (val := bytesToVecNat z 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha25)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hspA,
        by simp, by simp, by simp [hct], by simp, by simp,
        by simp [hx23], by simp, by simp, by simp, ?_⟩
    rw [vec2_bytesToVecNat_eq (sp + 2560#64) hz, vec2_bytesToVecNat_eq (skA + 3136#64) hz, hct]
    sep_frame
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx20_m, hx23_m, hx25_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : ct.length < 2 ^ 64 := by rw [hct]; decide
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 2592#64, ctA, ct)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, by simpa [State.spAligned, hsp_sf, ← hsp] using hspA,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hcat : ((sp + 2560#64) ↦ₛ (z ++ ct)) =
      ((sp + 2560#64) ↦ₛ z) ∗ ((sp + 2592#64) ↦ₛ ct) := by
    rw [pointsToBytes_append, hz, show sp + 2560#64 + BitVec.ofNat 64 32 = sp + 2592#64 by clear * -; bv_omega]
  rw [hcat]; sep_frame

/-! ## 4. `B01` (`kRejPre = shake256List 32 (z ++ ct)`) (`+0x3bcc → +0x3c18`) -/

private theorem seg4a2_hash_krej [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (zct : List (BitVec 8)) (Rest : SepProp)
    (hzct : zct.length = 1600) (hpc : s.pc = b + off3bcc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 2560#64) (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3c18) s
      (stackAt sp 1136 ∗ ((sp + 2560#64) ↦ₛ zct) ∗ memRegion (sp + 4160#64) 32 ∗
        memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x22 = sp + 14432#64 ∧
        sf.readReg64 .x23 = ctA ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ ((sp + 2560#64) ↦ₛ zct) ∗ memRegion (sp + 4160#64) 32 ∗
          memRegion (sp + 14432#64) 32 ∗ ((sp + 34432#64) ↦ₛ shake256List 32 zct) ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_eq : s.sp &&& 15#64 = 0#64 := beq_iff_eq.mp (by simpa [State.spAligned] using hspA)
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off3c14) s
      (stackAt s.sp 1136 ∗ ((s.sp + 2560#64) ↦ₛ zct) ∗ memRegion (s.sp + 4160#64) 32 ∗
        memRegion (s.sp + 14432#64) 32 ∗ memRegion (s.sp + 34432#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = s.sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = s.sp + 14432#64 ∧ sm.readReg64 .x1 = s.sp + 34432#64 ∧
        sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 .x3 = s.sp + 4160#64 ∧ sm.readReg64 .x4 = 32#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = s.sp + 14432#64 ∧
        sm.readReg64 .x23 = ctA ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Keccak2SlicesRW (s.sp + 14432#64) (s.sp + 2560#64) (s.sp + 2560#64) zct.length zct.length ∗
          ((s.sp + 2560#64) ↦ₛ zct) ∗ memRegion (s.sp + 34432#64) 32 ∗
          memRegion (s.sp + 4160#64) 32 ∗ stackAt s.sp 1136 ∗ Rest)) := by
    sep_frame_apply (sepWP_elim_region32 (a := s.sp + 14432#64)); intro c0 c1 c2 c3
    refine SepWP.of_memRegion_vecRangeMem 2 (s.sp + 34432#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f34 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    have ha34 : s.sp + 34432#64 + 16#64 = s.sp + 34448#64 := by clear * -; bv_omega
    refine SepWP.weaken_pre (show _ ⊢
      (((s.sp + 14432#64) ↦₆₄ c0) ∗ ((s.sp + 14432#64 + 8#64) ↦₆₄ c1) ∗
        ((s.sp + 14432#64 + 16#64) ↦₆₄ c2) ∗ ((s.sp + 14432#64 + 24#64) ↦₆₄ c3)) ∗
      (Vec128At (s.sp + 34432#64) (f34 0) ∗ Vec128At (s.sp + 34432#64 + 16#64) (f34 1)) ∗
      stackAt s.sp 1136 ∗ ((s.sp + 2560#64) ↦ₛ zct) ∗ memRegion (s.sp + 4160#64) 32 ∗ Rest
      by sep_frame) ?_
    wp_steps 12
    refine step_strQ128 (wb := none) (ea := s.sp + 34432#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 1
    refine step_strQ128 (wb := none) (ea := s.sp + 34448#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha34))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 3
    refine SepWP.weaken_pre (entails_sub (vec2_zero_entails_memRegion32 (s.sp + 34432#64)) (by sep_frame) (by sep_frame)) ?_
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp [hx23], by simp, by simp, by simp, ?_⟩
    rw [hzct]; unfold Keccak2SlicesRW; simp only [BitVec.add_assoc]; sep_frame
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : zct.length < 2 ^ 32 := by rw [hzct]; decide
  have hout : (32 : Nat) = 32 ∨ (32 : Nat) = 128 := Or.inl rfl
  wp_call (blk01_rw1_06 blkPl06.base) (s.sp + 14432#64, s.sp + 2560#64, s.sp + 34432#64, s.sp + 4160#64, 32, zct)
  have hsp_sf : sf.sp = s.sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, by simpa [State.spAligned, hsp_sf] using hspA,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (s.sp + 14432#64) (s.sp + 2560#64) (s.sp + 2560#64)
    zct.length zct.length
  have hout1_reg : ((s.sp + 4160#64) ↦ₛ shake256List 32 zct) ⊢ memRegion (s.sp + 4160#64) 32 := by
    have h := pointsToBytes_entails_memRegion (s.sp + 4160#64) (shake256List 32 zct)
    rwa [shake256List_len 32 zct] at h
  rw [hspm]
  exact entails_sub hslices (by sep_frame) (entails_sub hout1_reg (by sep_frame) (by sep_frame))

/-! ## 5. Zero `aTrans` Region (`+0x3c18 → +0x3c38`) & Composed `seg4a_ok` (`+0x39c4 → +0x3c38`) -/

private theorem seg4a2_zero_atrans [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off3c18) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3c38) s
      (memRegion (sp + 14432#64) 10240 ∗ memRegion (sp + 24672#64) 32 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = ctA ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 22624#64) 2048 ∗
          ((sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗ Rest)) := by
  subst hbase; subst hsp
  have hsp_eq : s.sp &&& 15#64 = 0#64 := beq_iff_eq.mp (by simpa [State.spAligned] using hspA)
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none)) (blkPl06.base + off3c34) s
      (memRegion (s.sp + 14432#64) 10240 ∗ memRegion (s.sp + 24672#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = s.sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = s.sp + 14432#64 ∧ (sm.readReg32 .x1).truncate 8 = 0#8 ∧
        (sm.readReg64 .x2).toNat = 10240 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = ctA ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ memRegion (s.sp + 14432#64) 10240 ∗
          (((s.sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗ Rest))) := by
    refine SepWP.of_memRegion_vecRangeMem 2 (s.sp + 24672#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f24 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    have ha24 : s.sp + 24672#64 + 16#64 = s.sp + 24688#64 := by clear * -; bv_omega
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (s.sp + 24672#64) (f24 0) ∗ Vec128At (s.sp + 24672#64 + 16#64) (f24 1)) ∗
      (memRegion (s.sp + 14432#64) 10240 ∗ Rest) by sep_frame) ?_
    wp_steps 5
    refine step_strQ128 (wb := none) (ea := s.sp + 24688#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha24))) (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := s.sp + 24672#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_eq])
      (by simp [evalAddrMode]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))) (by wp_norm_lhs) ?_
    intro _
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp, by simpa [State.spAligned] using hspA,
        by simp, by simp [State.readReg32], by simp, by simp, by simp,
        by simp [hx23], by simp, by simp, by simp, ?_⟩
    rw [vec2_zero_eq_replicate32 (s.sp + 24672#64)]; sep_frame
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx22_m, hx23_m, hx25_m, hx26_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : 10240 < 2 ^ 64 := by decide
  wp_call (blk29_memset_06 blkPl06.base) (s.sp + 14432#64, 0#8, 10240)
  have hsp_sf : sf.sp = s.sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, by simpa [State.spAligned, hsp_sf] using hspA,
      by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have h10240 : ((s.sp + 14432#64) ↦ₛ List.replicate 10240 0#8) ⊢
      memRegion (s.sp + 14432#64) 8192 ∗ memRegion (s.sp + 22624#64) 2048 := by
    rw [← memRegion_split' (b := s.sp + 14432#64) (b' := s.sp + 22624#64) (n := 8192) (k := (2048 : Nat))
      rfl (by clear * -; bv_omega) (by decide)]
    have h := pointsToBytes_entails_memRegion (s.sp + 14432#64) (List.replicate 10240 0#8)
    rwa [List.length_replicate] at h
  exact entails_sub h10240 (by sep_frame) (by sep_frame)

/-- Segment 4a (`+0x39c4 → +0x3c38`): spills `SpilledDecapsWords sp m` to `[sp + 0 .. sp + 128)`,
    computes `(kBar', r') = sha3_512List (m ++ hPk)` at `[sp + 2496 .. sp + 2560)` and
    `kRejPre = shake256List 32 (z ++ ct)` at `[sp + 34432 .. sp + 34464)`, and zeroes
    `[sp + 14432 .. sp + 24704)`. -/
theorem seg4a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (m hPk z ct : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hhPk : hPk.length = 32) (hz : z.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + off39c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3c38) s
      (stackAt sp 1136 ∗ memRegion sp 128 ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
        ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2432#64) 1792 ∗
        memRegion (sp + 14432#64) 10272 ∗ ((sp + 28368#64) ↦ₛ m) ∗
        memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
        ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 4160#64 ∧ sf.readReg64 .x22 = sp + 14432#64 ∧
        sf.readReg64 .x23 = ctA ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗
          ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
          memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
          memRegion (sp + 2560#64) 1664 ∗ memRegion (sp + 14432#64) 8192 ∗
          memRegion (sp + 22624#64) 2048 ∗ ((sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗
          memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 32 ∗
          ((sp + 34432#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
          ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)) := by
  have h24 : memRegion (sp + 2432#64) 1792 =
      memRegion (sp + 2432#64) 64 ∗ memRegion (sp + 2496#64) 64 ∗
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 64 := by
    rw [memRegion_split' (b := sp + 2432#64) (b' := sp + 2496#64) (n := 64) (k := (1728 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 2496#64) (b' := sp + 2560#64) (n := 64) (k := (1664 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 2560#64) (b' := sp + 4160#64) (n := 1600) (k := (64 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have h14 : memRegion (sp + 14432#64) 10272 =
      memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 14496#64) 1536 ∗
      memRegion (sp + 16032#64) 8640 ∗ memRegion (sp + 24672#64) 32 := by
    rw [memRegion_split' (b := sp + 14432#64) (b' := sp + 14496#64) (n := 64) (k := (10208 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 14496#64) (b' := sp + 16032#64) (n := 1536) (k := (8672 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 16032#64) (b' := sp + 24672#64) (n := 8640) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  rw [h24, h14]
  refine SepWP.weaken_pre (show _ ⊢
    stackAt sp 1136 ∗ memRegion sp 128 ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
    memRegion (sp + 2432#64) 64 ∗ memRegion (sp + 4160#64) 64 ∗
    memRegion (sp + 14432#64) 64 ∗ ((sp + 28368#64) ↦ₛ m) ∗
    memRegion (sp + 30448#64) 32 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
    (((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2496#64) 64 ∗
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 14496#64) 1536 ∗
      memRegion (sp + 16032#64) 8640 ∗ memRegion (sp + 24672#64) 32 ∗
      memRegion (sp + 34432#64) 32 ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4a1_ok hb hbase s sp skA ctA m hPk _ hm hhPk hpc hrun hsp hspA hcl hro hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hx23_1, hx25_1, hx26_1, hfp_1, hP1⟩
  have h14_64 : memRegion (sp + 14432#64) 64 =
      memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 14464#64) 32 :=
    memRegion_split' (b := sp + 14432#64) (b' := sp + 14464#64) (n := 32) (k := (32 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have h14_1568 : memRegion (sp + 14464#64) 32 ∗ memRegion (sp + 14496#64) 1536 =
      memRegion (sp + 14464#64) 1568 :=
    (memRegion_split' (b := sp + 14464#64) (b' := sp + 14496#64) (n := 32) (k := (1536 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
    memRegion (sp + 2496#64) 64 ∗ ((sp + 4160#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
    memRegion (sp + 14464#64) 1568 ∗
    (stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2432#64) 64 ∗
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 14432#64) 32 ∗
      memRegion (sp + 16032#64) 8640 ∗ memRegion (sp + 24672#64) 32 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 32 ∗
      memRegion (sp + 34432#64) 32 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
      ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest) by
      rw [h14_64, ← h14_1568]; sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg4a2_copy_kr hb hbase s1 sp ctA (sha3_512List (m ++ hPk)) _
      (sha3_512List_len _) hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx20_1 hx23_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx23_2, hx25_2, hx26_2, hfp_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
    ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2560#64) 1600 ∗
    ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗
    (stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
      memRegion (sp + 4160#64) 64 ∗ memRegion (sp + 14432#64) 32 ∗
      memRegion (sp + 14464#64) 1568 ∗ memRegion (sp + 16032#64) 8640 ∗
      memRegion (sp + 24672#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
      ((skA + 3104#64) ↦ₛ hPk) ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg4a2_stage_z_ct hb hbase s2 sp skA ctA z ct _ hz hct hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx19_3, hx20_3, hx23_3, hx25_3, hx26_3, hfp_3, hP3⟩
  have h41_64 : memRegion (sp + 4160#64) 64 =
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 4192#64) 32 :=
    memRegion_split' (b := sp + 4160#64) (b' := sp + 4192#64) (n := 32) (k := (32 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢
    stackAt sp 1136 ∗ ((sp + 2560#64) ↦ₛ (z ++ ct)) ∗ memRegion (sp + 4160#64) 32 ∗
    memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
    (SpilledDecapsWords sp m ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2432#64) 64 ∗
      ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗ memRegion (sp + 4192#64) 32 ∗
      memRegion (sp + 14464#64) 1568 ∗ memRegion (sp + 16032#64) 8640 ∗
      memRegion (sp + 24672#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 30448#64) 32 ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
      ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest) by rw [h41_64]; sep_frame)) ?_
  refine sepWP_seq_env hcl3 hro3
    (seg4a2_hash_krej hb hbase s3 sp ctA (z ++ ct) _ (by simp [hz, hct])
      hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx20_3 hx23_3) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hx19_4, hx22_4, hx23_4, hx25_4, hx26_4, hfp_4, hP4⟩
  have h14_full : memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 14464#64) 1568 ∗
      memRegion (sp + 16032#64) 8640 = memRegion (sp + 14432#64) 10240 := by
    rw [memRegion_split' (b := sp + 14432#64) (b' := sp + 14464#64) (n := 32) (k := (10208 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 14464#64) (b' := sp + 16032#64) (n := 1568) (k := (8640 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  refine SepWP.weaken_pre (Entails.trans hP4 (show _ ⊢
    memRegion (sp + 14432#64) 10240 ∗ memRegion (sp + 24672#64) 32 ∗
    (stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
      ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2432#64) 64 ∗
      ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗ ((sp + 2560#64) ↦ₛ (z ++ ct)) ∗
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 4192#64) 32 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 32 ∗
      ((sp + 34432#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
      ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)
    by rw [← h14_full]; sep_frame)) ?_
  refine SepWP.mono
    (seg4a2_zero_atrans hb hbase s4 sp ctA _ hpc4 hrun4 hsp4 hspA4 hcl4 hro4 hx23_4) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx19_f, hx22_f, hx23_f, hx25_f, hx26_f, hfp_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    hx19_f.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1))),
    hx22_f.trans hx22_4, hx23_f,
    hx25_f.trans (hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))),
    hx26_f.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1))),
    hfp_f.trans (hfp_4.trans (hfp_3.trans (hfp_2.trans hfp_1))),
    Entails.trans hPf ?_⟩
  have hzct_reg : ((sp + 2560#64) ↦ₛ (z ++ ct)) ⊢ memRegion (sp + 2560#64) 1600 := by
    have h := pointsToBytes_entails_memRegion (sp + 2560#64) (z ++ ct)
    rwa [show (z ++ ct).length = 1600 by simp [hz, hct]] at h
  have h25_1664 : memRegion (sp + 2560#64) 1664 =
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 4192#64) 32 := by
    rw [memRegion_split' (b := sp + 2560#64) (b' := sp + 4160#64) (n := 1600) (k := (64 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 4160#64) (b' := sp + 4192#64) (n := 32) (k := (32 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  rw [h25_1664]
  exact entails_sub hzct_reg (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2
