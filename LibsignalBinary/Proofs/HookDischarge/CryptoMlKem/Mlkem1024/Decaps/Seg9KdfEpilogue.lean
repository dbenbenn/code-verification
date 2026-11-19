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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2

/-!
# `kyber_decapsulate` (`B06`) — Segment 9 Outer KDF, FO Select & Epilogue (`+0xd89c .. +0xda1c`)

Proves the Round-3 Kyber outer KDF pairs (`B02` `SHA3-256` + `B01` `SHAKE-256`) for both
`ssRej = SHAKE-256(kRejPre ‖ H(ct))` and `ssGood = SHAKE-256(k̄' ‖ H(ct))`, the constant-time
selection `B16` (`compare_ciphertexts_select_shared_secret_in_constant_time`) writing
`kyber1024Decaps sk ct` to `ret`, and callee-saved frame restoration + `ret`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg9KdfEpilogue

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2SlicesRW keccak2_136_6_RW1Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  indCpaDecrypt indCpaEncryptWith kyber1024Decaps kyber1024DecapsWith sampleNtt
  sha3_256List sha3_512List shake256List toByteVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6 (
  blk02_keccak2_136_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs (
  CtCompareSelectArgs mlkemCompareSelectRWSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps (blk16_compare_select_RW_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env toByteVec_toList_of_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  bytesToVecNat pointsToBytes_eq_vecRangeMem step_ldpQ128 step_ldrQ128 step_stpQ128
  step_strQ128 vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_region32 spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  sha3_256List_len sha3_512List_len shake256List_len stackAt_1136_split_1040)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a2 (
  keccak2SlicesRW_entails_memRegion32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  SavedFrame06 blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06
  blkTree06 savedFrame06_entails_memRegion160)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2 (blk01_rw1_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5 (offSeg9Start)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xd89c → 0xda1c]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm]
theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

@[scoped simp, arm64_norm, wp_norm]
theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]
end Simp
open scoped Simp

private theorem blk02_rw1_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 2)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_6_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk02_keccak2_136_6_RW1_ok

private theorem blk16_rw_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 16)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemCompareSelectRWSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk16_compare_select_RW_ok

attribute [local irreducible] blkPC06 sha3_256List shake256List
attribute [local wp_norm ↓ high] Simp.exec_simdMovi_2d_0

/-! ## 1. Pure `kyber1024Decaps` Selection Equivalence & Vector Helpers -/

theorem decaps_select_eq_kyber1024Decaps {sk ct : List (BitVec 8)} (hct : ct.length = 1568) :
    let m' := indCpaDecrypt 4 11 5 (sk.take 1536) ct
    let kr := sha3_512List (m' ++ (sk.drop 3104).take 32)
    let kRejPre := shake256List 32 ((sk.drop 3136).take 32 ++ ct)
    let ct' := (indCpaEncryptWith sampleNtt 4 11 5 ((sk.drop 1536).take 1568) m' (kr.drop 32)).1 ++
      (indCpaEncryptWith sampleNtt 4 11 5 ((sk.drop 1536).take 1568) m' (kr.drop 32)).2.1
    let hCt := sha3_256List ct
    (if ct == ct' then shake256List 32 (kr.take 32 ++ hCt)
     else shake256List 32 (kRejPre ++ hCt)) = kyber1024Decaps sk ct := by
  dsimp only
  have hlen : (kyber1024DecapsWith sampleNtt sk ct).length = 32 := by
    unfold kyber1024DecapsWith; dsimp only; split <;> exact shake256List_len 32 _
  rw [kyber1024Decaps, toByteVec_toList_of_length hlen]
  unfold kyber1024DecapsWith; dsimp only
  have hct_take : ct.take 1568 = ct := List.take_of_length_le (Nat.le_of_eq hct)
  rw [hct_take]
  have hkr : ((sha3_512List (indCpaDecrypt 4 11 5 (sk.take 1536) ct ++ (sk.drop 3104).take 32)).drop 32).take 32 =
      (sha3_512List (indCpaDecrypt 4 11 5 (sk.take 1536) ct ++ (sk.drop 3104).take 32)).drop 32 := by
    apply List.take_of_length_le
    have hl := sha3_512List_len (indCpaDecrypt 4 11 5 (sk.take 1536) ct ++ (sk.drop 3104).take 32)
    simp [hl]
  rw [hkr]

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

/-! ## 2. Rejection KDF Pair (`+0xd89c → +0xd934`): `B02` `H(ct)` + `B01` `ssRej` -/

private theorem seg9_hash_ct1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (kRejPre ct : List (BitVec 8)) (Rest : SepProp)
    (hkRej : kRejPre.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + offSeg9Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = 1568#64) (hx22 : s.readReg64 .x22 = ctA)
    (hfp : s.readReg64 .fp = sp + 34736#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 55516) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ ((sp + 34432#64) ↦ₛ kRejPre) ∗
        memRegion (sp + 34592#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 1568#64 ∧ sf.readReg64 .x22 = ctA ∧
        sf.readReg64 .fp = sp + 34736#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
          ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 28368#64) 32 ∗
          memRegion (sp + 34432#64) 32 ∗ ((sp + 34592#64) ↦ₛ sha3_256List ct) ∗
          (ctA ↦ₛ ct) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hpc' : s.pc = blkPl06.base + BitVec.ofNat 64 55452 := hpc
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 55512) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ ((sp + 34432#64) ↦ₛ kRejPre) ∗
        memRegion (sp + 34592#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4160#64 ∧ sm.readReg64 .x1 = sp + 34592#64 ∧
        sm.readReg64 .x2 = sp + 28368#64 ∧ sm.readReg64 .x19 = 1568#64 ∧
        sm.readReg64 .x22 = ctA ∧ sm.readReg64 .fp = sp + 34736#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 4160#64) ctA ctA ct.length ct.length ∗
          (ctA ↦ₛ ct) ∗ memRegion (sp + 34592#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
          stackAt sp 1040 ∗
          (memRegion (sp - 1136#64) 96 ∗ ((sp + 14432#64) ↦ₛ kRejPre) ∗
            memRegion (sp + 34432#64) 32 ∗ Rest))) := by
    rw [stackAt_1136_split_1040 sp, ← vec2_bytesToVecNat_eq (sp + 34432#64) hkRej]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 4160#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 14432#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f14 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 34592#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f34 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 34592#64) (f34 0) ∗ Vec128At (sp + 34592#64 + 16#64) (f34 1)) ∗
      (Vec128At (sp + 14432#64) (f14 0) ∗ Vec128At (sp + 14432#64 + 16#64) (f14 1)) ∗
      (Vec128At (sp + 34432#64) (bytesToVecNat kRejPre 0) ∗
        Vec128At (sp + 34432#64 + 16#64) (bytesToVecNat kRejPre 1)) ∗
      (sp + 4160#64) ↦₆₄ s0_c ∗ ((sp + 4160#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 4160#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 4160#64 + 24#64) ↦₆₄ s3_c) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 28368#64) 32 ∗
      (ctA ↦ₛ ct) ∗ Rest by sep_frame) ?_
    have ha344_16 : sp + 34432#64 + 16#64 = sp + 34448#64 := by clear * -; bv_omega
    have ha144_16 : sp + 14432#64 + 16#64 = sp + 14448#64 := by clear * -; bv_omega
    have ha345_16 : sp + 34592#64 + 16#64 = sp + 34608#64 := by clear * -; bv_omega
    wp_steps 1
    refine step_ldrQ128 (wb := none) (ea := sp + 34432#64) (v := bytesToVecNat kRejPre 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (by wp_norm_lhs) ?_
    refine step_ldrQ128 (wb := none) (ea := sp + 34448#64) (v := bytesToVecNat kRejPre 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp])
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha344_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 5
    refine step_strQ128 (wb := none) (ea := sp + 14432#64) (val := bytesToVecNat kRejPre 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 14448#64) (val := bytesToVecNat kRejPre 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha144_16))))
      (by wp_norm_lhs) ?_
    intro _
    refine step_stpQ128 (wb := none) (ea := sp + 34592#64) (ea16 := sp + 34608#64)
      (v1 := 0#128) (v2 := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp]) ha345_16 (by simp) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha345_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 34592#64))) ?_
    wp_steps 4
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp,
        by simp [hx19], by simp [hx22], by simp [hfp], ?_⟩
    rw [hct, vec2_bytesToVecNat_eq (sp + 14432#64) hkRej,
      vec2_bytesToVecNat_eq (sp + 34432#64) hkRej]
    have hk_reg : ((sp + 34432#64) ↦ₛ kRejPre) ⊢ memRegion (sp + 34432#64) 32 := by
      simpa only [hkRej] using pointsToBytes_entails_memRegion (sp + 34432#64) kRejPre
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 34592#64) 32 ∗
      ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 34432#64) 32 ∗
      ((sp + 4160#64) ↦₆₄ ctA) ∗ ((sp + 4168#64) ↦₆₄ 1568#64) ∗
      ((sp + 4176#64) ↦₆₄ ctA) ∗ ((sp + 4184#64) ↦₆₄ 1568#64) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 28368#64) 32 ∗
      (ctA ↦ₛ ct) ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hk_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx19_m, hx22_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : ct.length < 2 ^ 32 := by rw [hct]; decide
  wp_call (blk02_rw1_06 blkPl06.base) (sp + 4160#64, ctA, sp + 34592#64, sp + 28368#64, ct)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 4160#64) ctA ctA ct.length ct.length
  have hout1 : ((sp + 28368#64) ↦ₛ sha3_256List ct) ⊢ memRegion (sp + 28368#64) 32 := by
    simpa only [sha3_256List_len ct] using pointsToBytes_entails_memRegion (sp + 28368#64) (sha3_256List ct)
  rw [hspm, stackAt_1136_split_1040 sp]
  refine Entails.trans (Q := memRegion (sp + 4160#64) 32 ∗
    (ctA ↦ₛ ct) ∗ ((sp + 34592#64) ↦ₛ sha3_256List ct) ∗
    memRegion (sp + 28368#64) 32 ∗ stackAt sp 1040 ∗
    (memRegion (sp - 1136#64) 96 ∗ ((sp + 14432#64) ↦ₛ kRejPre) ∗
      memRegion (sp + 34432#64) 32 ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

private theorem seg9_kdf_rej [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (kRejPre hCt : List (BitVec 8)) (Rest : SepProp)
    (hkRej : kRejPre.length = 32) (hhCt : hCt.length = 32)
    (hpc : s.pc = b + BitVec.ofNat 64 55516) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = 1568#64) (hx22 : s.readReg64 .x22 = ctA)
    (hfp : s.readReg64 .fp = sp + 34736#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 55604) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
        ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 14464#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 34368#64) 32 ∗
        ((sp + 34592#64) ↦ₛ hCt) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 1568#64 ∧ sf.readReg64 .x20 = sp + 14432#64 ∧
        sf.readReg64 .x21 = 64#64 ∧ sf.readReg64 .x22 = ctA ∧
        sf.readReg64 .fp = sp + 34736#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
          memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 28368#64) 32 ∗
          ((sp + 34368#64) ↦ₛ shake256List 32 (kRejPre ++ hCt)) ∗
          memRegion (sp + 34592#64) 32 ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 55600) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
        ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 14464#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 34368#64) 32 ∗
        ((sp + 34592#64) ↦ₛ hCt) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4160#64 ∧ sm.readReg64 .x1 = sp + 34368#64 ∧
        sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 .x3 = sp + 28368#64 ∧
        sm.readReg64 .x4 = 32#64 ∧ sm.readReg64 .x19 = 1568#64 ∧
        sm.readReg64 .x20 = sp + 14432#64 ∧ sm.readReg64 .x21 = 64#64 ∧
        sm.readReg64 .x22 = ctA ∧ sm.readReg64 .fp = sp + 34736#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 4160#64) (sp + 14432#64) (sp + 14432#64)
            (kRejPre ++ hCt).length (kRejPre ++ hCt).length ∗
          ((sp + 14432#64) ↦ₛ (kRejPre ++ hCt)) ∗
          memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
          stackAt sp 1136 ∗ (memRegion (sp + 34592#64) 32 ∗ Rest))) := by
    rw [← vec2_bytesToVecNat_eq (sp + 34592#64) hhCt]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 4160#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 14464#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f14 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 34368#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f34 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 34368#64) (f34 0) ∗ Vec128At (sp + 34368#64 + 16#64) (f34 1)) ∗
      (Vec128At (sp + 14464#64) (f14 0) ∗ Vec128At (sp + 14464#64 + 16#64) (f14 1)) ∗
      (Vec128At (sp + 34592#64) (bytesToVecNat hCt 0) ∗
        Vec128At (sp + 34592#64 + 16#64) (bytesToVecNat hCt 1)) ∗
      (sp + 4160#64) ↦₆₄ s0_c ∗ ((sp + 4160#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 4160#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 4160#64 + 24#64) ↦₆₄ s3_c) ∗
      stackAt sp 1136 ∗ ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 28368#64) 32 ∗ Rest
      by sep_frame) ?_
    have ha144_16 : sp + 14464#64 + 16#64 = sp + 14480#64 := by clear * -; bv_omega
    have ha343_16 : sp + 34368#64 + 16#64 = sp + 34384#64 := by clear * -; bv_omega
    have ha345_16 : sp + 34592#64 + 16#64 = sp + 34608#64 := by clear * -; bv_omega
    refine step_ldpQ128 (wb := none) (ea := sp + 34592#64) (ea16 := sp + 34608#64)
      (v1 := bytesToVecNat hCt 0) (v2 := bytesToVecNat hCt 1)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp]) ha345_16
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha345_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 7
    refine step_strQ128 (wb := none) (ea := sp + 14464#64) (val := bytesToVecNat hCt 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 5
    refine step_strQ128 (wb := none) (ea := sp + 14480#64) (val := bytesToVecNat hCt 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha144_16))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 1
    refine step_strQ128 (wb := none) (ea := sp + 34368#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 34384#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha343_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 34368#64))) ?_
    wp_steps 3
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp, by simp, by simp,
        by simp [hx19], by simp, by simp, by simp [hx22], by simp [hfp], ?_⟩
    have hm_len : (kRejPre ++ hCt).length = 64 := by simp [hkRej, hhCt]
    have hcat : ((sp + 14432#64) ↦ₛ (kRejPre ++ hCt)) =
        ((sp + 14432#64) ↦ₛ kRejPre) ∗ ((sp + 14464#64) ↦ₛ hCt) := by
      rw [pointsToBytes_append, hkRej]
      have ha : sp + 14432#64 + BitVec.ofNat 64 32 = sp + 14464#64 := by clear * -; bv_omega
      rw [ha]
    have hhCt_reg : ((sp + 34592#64) ↦ₛ hCt) ⊢ memRegion (sp + 34592#64) 32 := by
      simpa only [hhCt] using pointsToBytes_entails_memRegion (sp + 34592#64) hCt
    rw [hm_len, hcat, vec2_bytesToVecNat_eq (sp + 14464#64) hhCt,
      vec2_bytesToVecNat_eq (sp + 34592#64) hhCt]
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 34368#64) 32 ∗
      ((sp + 14464#64) ↦ₛ hCt) ∗ memRegion (sp + 34592#64) 32 ∗
      ((sp + 4160#64) ↦₆₄ (sp + 14432#64)) ∗ ((sp + 4168#64) ↦₆₄ 64#64) ∗
      ((sp + 4176#64) ↦₆₄ (sp + 14432#64)) ∗ ((sp + 4184#64) ↦₆₄ 64#64) ∗
      stackAt sp 1136 ∗ ((sp + 14432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 28368#64) 32 ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhCt_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx19_m, hx20_m, hx21_m, hx22_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : (kRejPre ++ hCt).length < 2 ^ 32 := by simp [hkRej, hhCt]
  have houtLen : (32 : Nat) = 32 ∨ (32 : Nat) = 128 := Or.inl rfl
  wp_call (blk01_rw1_06 blkPl06.base)
    (sp + 4160#64, sp + 14432#64, sp + 34368#64, sp + 28368#64, 32, kRejPre ++ hCt)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 4160#64) (sp + 14432#64) (sp + 14432#64)
    (kRejPre ++ hCt).length (kRejPre ++ hCt).length
  have hin_reg : ((sp + 14432#64) ↦ₛ (kRejPre ++ hCt)) ⊢ memRegion (sp + 14432#64) 64 := by
    have hl : (kRejPre ++ hCt).length = 64 := by simp [hkRej, hhCt]
    simpa only [hl] using pointsToBytes_entails_memRegion (sp + 14432#64) (kRejPre ++ hCt)
  have hout1 : ((sp + 28368#64) ↦ₛ shake256List 32 (kRejPre ++ hCt)) ⊢ memRegion (sp + 28368#64) 32 := by
    simpa only [shake256List_len 32 (kRejPre ++ hCt)] using
      pointsToBytes_entails_memRegion (sp + 28368#64) (shake256List 32 (kRejPre ++ hCt))
  rw [hspm]
  refine Entails.trans (Q := memRegion (sp + 4160#64) 32 ∗
    memRegion (sp + 14432#64) 64 ∗ ((sp + 34368#64) ↦ₛ shake256List 32 (kRejPre ++ hCt)) ∗
    memRegion (sp + 28368#64) 32 ∗ stackAt sp 1136 ∗ (memRegion (sp + 34592#64) 32 ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono hin_reg
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

/-! ## 3. Good KDF Pair (`+0xd934 → +0xd9c0`): `B02` `H(ct)` + `B01` `ssGood` -/

private theorem seg9_hash_ct2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (kBar ct : List (BitVec 8)) (Rest : SepProp)
    (hkBar : kBar.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + BitVec.ofNat 64 55604) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = 1568#64) (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hx21 : s.readReg64 .x21 = 64#64) (hx22 : s.readReg64 .x22 = ctA)
    (hfp : s.readReg64 .fp = sp + 34736#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 55668) s
      (stackAt sp 1136 ∗ ((sp + 2496#64) ↦ₛ kBar) ∗ memRegion (sp + 4160#64) 32 ∗
        memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
        memRegion (sp + 34624#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 14432#64 ∧ sf.readReg64 .x21 = 64#64 ∧
        sf.readReg64 .x22 = ctA ∧ sf.readReg64 .fp = sp + 34736#64 ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 2496#64) 32 ∗ memRegion (sp + 4160#64) 32 ∗
          ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 28368#64) 32 ∗
          ((sp + 34624#64) ↦ₛ sha3_256List ct) ∗ (ctA ↦ₛ ct) ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 55664) s
      (stackAt sp 1136 ∗ ((sp + 2496#64) ↦ₛ kBar) ∗ memRegion (sp + 4160#64) 32 ∗
        memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
        memRegion (sp + 34624#64) 32 ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4160#64 ∧ sm.readReg64 .x1 = sp + 34624#64 ∧
        sm.readReg64 .x2 = sp + 28368#64 ∧ sm.readReg64 .x20 = sp + 14432#64 ∧
        sm.readReg64 .x21 = 64#64 ∧ sm.readReg64 .x22 = ctA ∧ sm.readReg64 .fp = sp + 34736#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 4160#64) ctA ctA ct.length ct.length ∗
          (ctA ↦ₛ ct) ∗ memRegion (sp + 34624#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
          stackAt sp 1040 ∗
          (memRegion (sp - 1136#64) 96 ∗ memRegion (sp + 2496#64) 32 ∗
            ((sp + 14432#64) ↦ₛ kBar) ∗ Rest))) := by
    rw [stackAt_1136_split_1040 sp, ← vec2_bytesToVecNat_eq (sp + 2496#64) hkBar]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 4160#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 14432#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f14 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 34624#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f34 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 34624#64) (f34 0) ∗ Vec128At (sp + 34624#64 + 16#64) (f34 1)) ∗
      (Vec128At (sp + 14432#64) (f14 0) ∗ Vec128At (sp + 14432#64 + 16#64) (f14 1)) ∗
      (Vec128At (sp + 2496#64) (bytesToVecNat kBar 0) ∗
        Vec128At (sp + 2496#64 + 16#64) (bytesToVecNat kBar 1)) ∗
      (sp + 4160#64) ↦₆₄ s0_c ∗ ((sp + 4160#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 4160#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 4160#64 + 24#64) ↦₆₄ s3_c) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 28368#64) 32 ∗
      (ctA ↦ₛ ct) ∗ Rest by sep_frame) ?_
    have ha24_16 : sp + 2496#64 + 16#64 = sp + 2512#64 := by clear * -; bv_omega
    have ha144_16 : sp + 14432#64 + 16#64 = sp + 14448#64 := by clear * -; bv_omega
    have ha346_16 : sp + 34624#64 + 16#64 = sp + 34640#64 := by clear * -; bv_omega
    refine step_ldrQ128 (wb := none) (ea := sp + 2496#64) (v := bytesToVecNat kBar 0)
      hpc hrun (by wp_norm_lhs)
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
    refine step_strQ128 (wb := none) (ea := sp + 14432#64) (val := bytesToVecNat kBar 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 14448#64) (val := bytesToVecNat kBar 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha144_16))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_stpQ128 (wb := none) (ea := sp + 34624#64) (ea16 := sp + 34640#64)
      (v1 := 0#128) (v2 := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp]) ha346_16 (by simp) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha346_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 34624#64))) ?_
    wp_steps 2
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp,
        by simp [hx20], by simp [hx21], by simp [hx22], by simp [hfp], ?_⟩
    rw [hct, vec2_bytesToVecNat_eq (sp + 14432#64) hkBar,
      vec2_bytesToVecNat_eq (sp + 2496#64) hkBar]
    have hk_reg : ((sp + 2496#64) ↦ₛ kBar) ⊢ memRegion (sp + 2496#64) 32 := by
      simpa only [hkBar] using pointsToBytes_entails_memRegion (sp + 2496#64) kBar
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 34624#64) 32 ∗
      ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 2496#64) 32 ∗
      ((sp + 4160#64) ↦₆₄ ctA) ∗ ((sp + 4168#64) ↦₆₄ 1568#64) ∗
      ((sp + 4176#64) ↦₆₄ ctA) ∗ ((sp + 4184#64) ↦₆₄ 1568#64) ∗
      memRegion (sp - 1136#64) 96 ∗ stackAt sp 1040 ∗ memRegion (sp + 28368#64) 32 ∗
      (ctA ↦ₛ ct) ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hk_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _ ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx20_m, hx21_m, hx22_m, hfpm, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : ct.length < 2 ^ 32 := by rw [hct]; decide
  wp_call (blk02_rw1_06 blkPl06.base) (sp + 4160#64, ctA, sp + 34624#64, sp + 28368#64, ct)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 4160#64) ctA ctA ct.length ct.length
  have hout1 : ((sp + 28368#64) ↦ₛ sha3_256List ct) ⊢ memRegion (sp + 28368#64) 32 := by
    simpa only [sha3_256List_len ct] using pointsToBytes_entails_memRegion (sp + 28368#64) (sha3_256List ct)
  rw [hspm, stackAt_1136_split_1040 sp]
  refine Entails.trans (Q := memRegion (sp + 4160#64) 32 ∗
    (ctA ↦ₛ ct) ∗ ((sp + 34624#64) ↦ₛ sha3_256List ct) ∗
    memRegion (sp + 28368#64) 32 ∗ stackAt sp 1040 ∗
    (memRegion (sp - 1136#64) 96 ∗ memRegion (sp + 2496#64) 32 ∗
      ((sp + 14432#64) ↦ₛ kBar) ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

private theorem seg9_kdf_good [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (kBar hCt : List (BitVec 8)) (Rest : SepProp)
    (hkBar : kBar.length = 32) (hhCt : hCt.length = 32)
    (hpc : s.pc = b + BitVec.ofNat 64 55668) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 14432#64) (hx21 : s.readReg64 .x21 = 64#64)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = sp + 34736#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 55744) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
        ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 14464#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
        ((sp + 34624#64) ↦ₛ hCt) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x22 = ctA ∧
        (Pf ⊢ stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
          memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 28368#64) 32 ∗
          ((sp + 34400#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ∗
          memRegion (sp + 34624#64) 32 ∗ Rest)) := by
  subst hbase
  have hsp_eq : sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_chk
  have hprep : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + BitVec.ofNat 64 55740) s
      (stackAt sp 1136 ∗ memRegion (sp + 4160#64) 32 ∗
        ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 14464#64) 32 ∗
        memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
        ((sp + 34624#64) ↦ₛ hCt) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4160#64 ∧ sm.readReg64 .x1 = sp + 34400#64 ∧
        sm.readReg64 .x2 = 32#64 ∧ sm.readReg64 .x3 = sp + 28368#64 ∧
        sm.readReg64 .x4 = 32#64 ∧ sm.readReg64 .x22 = ctA ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 4160#64) (sp + 14432#64) (sp + 14432#64)
            (kBar ++ hCt).length (kBar ++ hCt).length ∗
          ((sp + 14432#64) ↦ₛ (kBar ++ hCt)) ∗
          memRegion (sp + 34400#64) 32 ∗ memRegion (sp + 28368#64) 32 ∗
          stackAt sp 1136 ∗ (memRegion (sp + 34624#64) 32 ∗ Rest))) := by
    rw [← vec2_bytesToVecNat_eq (sp + 34624#64) hhCt]
    sep_frame_apply (sepWP_elim_region32 (a := sp + 4160#64)); intro s0_c s1_c s2_c s3_c
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 14464#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f14 => ?_
    refine SepWP.of_memRegion_vecRangeMem 2 (sp + 34400#64) (by decide)
      (sepProp_ext (by sep_frame) (by sep_frame)) fun f34 => ?_
    dsimp only [VecRangeMem]; simp only [sepConj_emp]
    refine SepWP.weaken_pre (show _ ⊢
      (Vec128At (sp + 34400#64) (f34 0) ∗ Vec128At (sp + 34400#64 + 16#64) (f34 1)) ∗
      (Vec128At (sp + 14464#64) (f14 0) ∗ Vec128At (sp + 14464#64 + 16#64) (f14 1)) ∗
      (Vec128At (sp + 34624#64) (bytesToVecNat hCt 0) ∗
        Vec128At (sp + 34624#64 + 16#64) (bytesToVecNat hCt 1)) ∗
      (sp + 4160#64) ↦₆₄ s0_c ∗ ((sp + 4160#64 + 8#64) ↦₆₄ s1_c) ∗
      ((sp + 4160#64 + 16#64) ↦₆₄ s2_c) ∗ ((sp + 4160#64 + 24#64) ↦₆₄ s3_c) ∗
      stackAt sp 1136 ∗ ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 28368#64) 32 ∗ Rest
      by sep_frame) ?_
    have ha144_16 : sp + 14464#64 + 16#64 = sp + 14480#64 := by clear * -; bv_omega
    have ha344_16 : sp + 34400#64 + 16#64 = sp + 34416#64 := by clear * -; bv_omega
    have ha346_16 : sp + 34624#64 + 16#64 = sp + 34640#64 := by clear * -; bv_omega
    refine step_ldpQ128 (wb := none) (ea := sp + 34624#64) (ea16 := sp + 34640#64)
      (v1 := bytesToVecNat hCt 0) (v2 := bytesToVecNat hCt 1)
      hpc hrun (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg])
      (by simp [evalAddrMode, hfp]) ha346_16
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))))
      (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At ha346_16)))))
      (by wp_norm_lhs) ?_
    wp_steps 7
    refine step_strQ128 (wb := none) (ea := sp + 14464#64) (val := bytesToVecNat hCt 0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 14480#64) (val := bytesToVecNat hCt 1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.right (SepStore128.left (SepStore128.right (SepStore128.vec128At ha144_16))))
      (by wp_norm_lhs) ?_
    intro _
    wp_steps 2
    refine step_strQ128 (wb := none) (ea := sp + 34400#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.left (SepStore128.vec128At rfl)))
      (by wp_norm_lhs) ?_
    intro _
    refine step_strQ128 (wb := none) (ea := sp + 34416#64) (val := 0#128)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_eq])
      (by simp [evalAddrMode, hsp]) (by simp)
      (SepStore128.left (SepStore128.right (SepStore128.vec128At ha344_16)))
      (by wp_norm_lhs) ?_
    intro _
    refine SepWP.weaken_pre (sepConj_mono_left (vec2_zero_entails_memRegion32 (sp + 34400#64))) ?_
    wp_steps 2
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_chk (by simp [hsp]) hsp_chk,
        by simp, by simp, by simp, by simp, by simp, by simp [hx22], ?_⟩
    have hm_len : (kBar ++ hCt).length = 64 := by simp [hkBar, hhCt]
    have hcat : ((sp + 14432#64) ↦ₛ (kBar ++ hCt)) =
        ((sp + 14432#64) ↦ₛ kBar) ∗ ((sp + 14464#64) ↦ₛ hCt) := by
      rw [pointsToBytes_append, hkBar]
      have ha : sp + 14432#64 + BitVec.ofNat 64 32 = sp + 14464#64 := by clear * -; bv_omega
      rw [ha]
    have hhCt_reg : ((sp + 34624#64) ↦ₛ hCt) ⊢ memRegion (sp + 34624#64) 32 := by
      simpa only [hhCt] using pointsToBytes_entails_memRegion (sp + 34624#64) hCt
    rw [hm_len, hcat, vec2_bytesToVecNat_eq (sp + 14464#64) hhCt,
      vec2_bytesToVecNat_eq (sp + 34624#64) hhCt]
    unfold Keccak2SlicesRW
    simp only [BitVec.add_assoc]
    refine Entails.trans (Q := memRegion (sp + 34400#64) 32 ∗
      ((sp + 14464#64) ↦ₛ hCt) ∗ memRegion (sp + 34624#64) 32 ∗
      ((sp + 4160#64) ↦₆₄ (sp + 14432#64)) ∗ ((sp + 4168#64) ↦₆₄ 64#64) ∗
      ((sp + 4176#64) ↦₆₄ (sp + 14432#64)) ∗ ((sp + 4184#64) ↦₆₄ 64#64) ∗
      stackAt sp 1136 ∗ ((sp + 14432#64) ↦ₛ kBar) ∗ memRegion (sp + 28368#64) 32 ∗ Rest) ?_ (by sep_frame)
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hhCt_reg))
  refine sepWP_seq_env hcl hro hprep ?_
  rintro sm Pm hpcm hrunm _ _
    ⟨hspm, hspAm, hx0_m, hx1_m, hx2_m, hx3_m, hx4_m, hx22_m, hPm⟩
  refine SepWP.weaken_pre hPm ?_
  have hlt : (kBar ++ hCt).length < 2 ^ 32 := by simp [hkBar, hhCt]
  have houtLen : (32 : Nat) = 32 ∨ (32 : Nat) = 128 := Or.inl rfl
  wp_call (blk01_rw1_06 blkPl06.base)
    (sp + 4160#64, sp + 14432#64, sp + 34400#64, sp + 28368#64, 32, kBar ++ hCt)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], ?_⟩
  have hslices := keccak2SlicesRW_entails_memRegion32 (sp + 4160#64) (sp + 14432#64) (sp + 14432#64)
    (kBar ++ hCt).length (kBar ++ hCt).length
  have hin_reg : ((sp + 14432#64) ↦ₛ (kBar ++ hCt)) ⊢ memRegion (sp + 14432#64) 64 := by
    have hl : (kBar ++ hCt).length = 64 := by simp [hkBar, hhCt]
    simpa only [hl] using pointsToBytes_entails_memRegion (sp + 14432#64) (kBar ++ hCt)
  have hout1 : ((sp + 28368#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ⊢ memRegion (sp + 28368#64) 32 := by
    simpa only [shake256List_len 32 (kBar ++ hCt)] using
      pointsToBytes_entails_memRegion (sp + 28368#64) (shake256List 32 (kBar ++ hCt))
  rw [hspm]
  refine Entails.trans (Q := memRegion (sp + 4160#64) 32 ∗
    memRegion (sp + 14432#64) 64 ∗ ((sp + 34400#64) ↦ₛ shake256List 32 (kBar ++ hCt)) ∗
    memRegion (sp + 28368#64) 32 ∗ stackAt sp 1136 ∗ (memRegion (sp + 34624#64) 32 ∗ Rest)) ?_ (by sep_frame)
  exact sepConj_mono hslices (sepConj_mono hin_reg
    (sepConj_mono_right (sepConj_mono hout1 (Entails.refl _))))

/-! ## 4. FO Selection (`B16`, `+0xd9c0 → +0xd9ec`) & Epilogue (`+0xd9ec → ret`) -/

private theorem seg9_b16 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (hbase : blkPl06.base = b) (s : State) (sp ret ctA : BitVec 64)
    (ct ct' ssGood ssRej : List (BitVec 8)) (Rest : SepProp)
    (hct : ct.length = 1568) (hct' : ct'.length = 1568)
    (hssGood : ssGood.length = 32) (hssRej : ssRej.length = 32)
    (hpc : s.pc = b + BitVec.ofNat 64 55744) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx22 : s.readReg64 .x22 = ctA)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 55788) s
      (((sp + 128#64) ↦₆₄ ret) ∗ (ctA ↦ₛ ct) ∗ ((sp + 30448#64) ↦ₛ ct') ∗
        ((sp + 34400#64) ↦ₛ ssGood) ∗ ((sp + 34368#64) ↦ₛ ssRej) ∗
        stackAt sp 1136 ∗ memRegion ret 32 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        Pf = ((ret ↦ₛ (if ct == ct' then ssGood else ssRej)) ∗
          ((sp + 128#64) ↦₆₄ ret) ∗ (ctA ↦ₛ ct) ∗ ((sp + 30448#64) ↦ₛ ct') ∗
          ((sp + 34400#64) ↦ₛ ssGood) ∗ ((sp + 34368#64) ↦ₛ ssRej) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [stackAt_shrink sp 1136 112 (by decide) (by decide)]
  wp_steps 10
  wp_call (blk16_rw_06 blkPl06.base)
    ({ outPtr := ret, lhsCtPtr := ctA, rhsCtPtr := sp + 30448#64,
       lhsSsPtr := sp + 34400#64, rhsSsPtr := sp + 34368#64,
       lhsCt := ct, rhsCt := ct', lhsSs := ssGood, rhsSs := ssRej } : CtCompareSelectArgs)
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by simp [*]) ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, ?_⟩
  rw [← stackAt_shrink sp 1136 112 (by decide) (by decide)]
  exact sepProp_ext (by sep_frame) (by sep_frame)

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

private theorem seg9_epilogue [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (hbase : blkPl06.base = b) (s0 s : State) (Rest : SepProp)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + BitVec.ofNat 64 55788) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 34832#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame06 s0.sp s0 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  subst hbase
  dsimp only [SavedFrame06]
  have hsp160 : (s0.sp - 34832#64) + 32768#64 + 1904#64 = s0.sp - 160#64 := by clear * -; bv_omega
  have hsp160_al : ((((s0.sp - 34832#64) + 32768#64 + 1904#64) &&& 15#64) == 0#64) = true := by
    rw [hsp160]; exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
  rw [sepPost_apply]
  refine ⟨⟨Eq.trans (by wp_norm_lhs) (by clear * -; bv_omega), ?_⟩,
    sepConj_mono_left (savedFrame06_entails_memRegion160 s0.sp s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

/-! ## 5. Composed Segment 9 (`+0xd89c → ret`) -/

private theorem split_14432_32 (sp : BitVec 64) :
    memRegion (sp + 14432#64) 64 = memRegion (sp + 14432#64) 32 ∗ memRegion (sp + 14464#64) 32 := by
  simpa using memRegion_split' (b := sp + 14432#64) (b' := sp + 14464#64) (n := 32) (k := (32 : Nat))
    rfl (by bv_omega) (by decide)

/-- Full Segment 9 (`+0xd89c → ret`): rejection & good KDF pairs (`B02` + `B01`), `B16` FO
    constant-time selection, and callee-saved frame restoration + `ret`. -/
theorem seg9_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 s : State) (ret ctA : BitVec 64)
    (kBar kRejPre ct ct' : List (BitVec 8)) (Rest : SepProp)
    (hkBar : kBar.length = 32) (hkRej : kRejPre.length = 32)
    (hct : ct.length = 1568) (hct' : ct'.length = 1568)
    (hsp0 : s0.spAligned = true)
    (hpc : s.pc = b + offSeg9Start) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 34832#64) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1568#64) (hx22 : s.readReg64 .x22 = ctA)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let sp := s0.sp - 34832#64
    let hCt := sha3_256List ct
    let ssGood := shake256List 32 (kBar ++ hCt)
    let ssRej := shake256List 32 (kRejPre ++ hCt)
    SepWP (blkPC06.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (stackAt sp 1136 ∗ ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 2496#64) ↦ₛ kBar) ∗
        memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 64 ∗
        memRegion (sp + 28368#64) 32 ∗ ((sp + 30448#64) ↦ₛ ct') ∗
        memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
        ((sp + 34432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 34592#64) 32 ∗
        memRegion (sp + 34624#64) 32 ∗ SavedFrame06 s0.sp s0 ∗
        (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ Rest)
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((ret ↦ₛ (if ct == ct' then ssGood else ssRej)) ∗ (ctA ↦ₛ ct) ∗
          memRegion (sp + 128#64) 8 ∗ memRegion (sp + 2496#64) 32 ∗
          memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 64 ∗
          memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 1568 ∗
          memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
          memRegion (sp + 34432#64) 32 ∗ memRegion (sp + 34592#64) 32 ∗
          memRegion (sp + 34624#64) 32 ∗ stackAt sp 1136 ∗
          memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  intro sp hCt ssGood ssRej
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by unfold State.spAligned at hspA; rwa [hsp] at hspA
  have hfp' : s.readReg64 .fp = sp + 34736#64 := by
    rw [hfp]; dsimp only [sp]; clear * -; bv_omega
  have hhCt : hCt.length = 32 := sha3_256List_len ct
  have hssGood : ssGood.length = 32 := shake256List_len 32 (kBar ++ hCt)
  have hssRej : ssRej.length = 32 := shake256List_len 32 (kRejPre ++ hCt)
  refine SepWP.weaken_pre (by rw [split_14432_32 sp]; sep_frame)
    (sepWP_seq_env hcl hro
      (seg9_hash_ct1 hb hbase s sp ctA kRejPre ct _ hkRej hct hpc hrun hsp hsp_chk hcl hro
        hx19 hx22 hfp') ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, _, hx19_1, hx22_1, hfp1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
    (sepWP_seq_env hcl1 hro1
      (seg9_kdf_rej hb hbase s1 sp ctA kRejPre hCt _ hkRej hhCt hpc1 hrun1 hsp1 hsp_chk hcl1 hro1
        hx19_1 hx22_1 hfp1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, _, hx19_2, hx20_2, hx21_2, hx22_2, hfp2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by rw [split_14432_32 sp]; sep_frame))
    (sepWP_seq_env hcl2 hro2
      (seg9_hash_ct2 hb hbase s2 sp ctA kBar ct _ hkBar hct hpc2 hrun2 hsp2 hsp_chk hcl2 hro2
        hx19_2 hx20_2 hx21_2 hx22_2 hfp2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, _, hx20_3, hx21_3, hx22_3, hfp3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg9_kdf_good hb hbase s3 sp ctA kBar hCt _ hkBar hhCt hpc3 hrun3 hsp3 hsp_chk hcl3 hro3
        hx20_3 hx21_3 hx22_3 hfp3) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, _, hx22_4, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (by sep_frame))
    (sepWP_seq_env hcl4 hro4
      (seg9_b16 hb hbase s4 sp ret ctA ct ct' ssGood ssRej _ hct hct' hssGood hssRej
        hpc4 hrun4 hsp4 hsp_chk hx22_4 hcl4) ?_)
  rintro s5 _ hpc5 hrun5 _ _ ⟨hsp5, _, rfl⟩
  refine SepWP.weaken_pre (by sep_frame)
    (SepWP.mono (seg9_epilogue hb hbase s0 s5 _ (by simpa [State.spAligned] using hsp0) hpc5 hrun5 hsp5) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have h128 : ((sp + 128#64) ↦₆₄ ret) ⊢ memRegion (sp + 128#64) 8 := pointsTo64_entails_memRegion _ _
  have h30448 : ((sp + 30448#64) ↦ₛ ct') ⊢ memRegion (sp + 30448#64) 1568 := by
    simpa only [hct'] using pointsToBytes_entails_memRegion (sp + 30448#64) ct'
  have h34400 : ((sp + 34400#64) ↦ₛ ssGood) ⊢ memRegion (sp + 34400#64) 32 := by
    simpa only [hssGood] using pointsToBytes_entails_memRegion (sp + 34400#64) ssGood
  have h34368 : ((sp + 34368#64) ↦ₛ ssRej) ⊢ memRegion (sp + 34368#64) 32 := by
    simpa only [hssRej] using pointsToBytes_entails_memRegion (sp + 34368#64) ssRej
  have hsub := sepConj_mono h128 (sepConj_mono h30448 (sepConj_mono h34400 h34368))
  exact Entails.trans (by sep_frame) (Entails.trans (sepConj_mono_left hsub) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg9KdfEpilogue
