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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1

/-!
# `kyber_decapsulate` (`B06`) — Segment 4b Part 2 (`+0x3e80 .. +0x40f0`) and Composed `seg4_ok`

Steps modular NEON `deserialize_12` Loops `2` and `3` (`tHat[2]`, `tHat[3]`), `B28` (`memcpy`)
copies to `[sp + 23648 .. sp + 24672)`, `rho` load into `v0, v1`, and composes `seg4_ok`
(`+0x39c4 → +0x40f0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmhs8h simdTbl16b simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 (
  loadVec12 neonDeserialize12Mod8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At polyVecNat
  step_ldrQ128 step_stpQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  applySimdResult_ok evalSimdModImmExt_bic_8h_0xf0_lsl8 evalSimdModImmExt_mvni_4s_3_msl16
  exec_simdDup_8h exec_simdTbl_16b_1 exec_simdUshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (
  SpilledDecapsWords off39c4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a2 (seg4a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b1 (
  off3c38 off3e80 seg4b_copy0_zero1 seg4b_copy1 seg4b_init_zero0 seg4b_loop0 seg4b_loop1)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdAdd_8h_svc exec_simdCmhs_8h_svc exec_simdMovi_2d_0
  neonDeserialize12Mod8h_loadVec12_eq pkEk0 pkEk0_len pkEk1 pkEk1_len pkEk2 pkEk2_len
  pkEk3 pkEk3_len pkRho pkRho_len pk_pointsTo_split rhoW rho_pointsTo_eq_vec128
  sp_add_26768_or_11 sp_add_28848_or_11 step_deser12_simd12_gen step_ld1S2_load
  step_ldrD64_raw tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1 (
  SepStore128.polyMem polyMem_congr trunc16_3329 update2_prefix)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x3e80 → 0x40ec]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible]
  blkPC06 dup8x16 polyVecNat tHatModPoly16 loadVec12 neonDeserialize12Mod8h
  simdTbl16b simdUshl8h simdCmhs8h simdAdd8h SpilledDecapsWords sha3_512List shake256List

attribute [local wp_norm ↓ high]
  applySimdResult_ok evalSimdModImmExt_mvni_4s_3_msl16 evalSimdModImmExt_bic_8h_0xf0_lsl8
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdMovi_2d_0 exec_simdDup_8h trunc16_3329
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdCmhs_8h_svc exec_simdAdd_8h_svc

@[simp, arm64_norm, wp_norm] private abbrev off3f1c : BitVec 64 := 16156#64
@[simp, arm64_norm, wp_norm] private abbrev off3f7c : BitVec 64 := 16252#64
@[simp, arm64_norm, wp_norm] private abbrev off403c : BitVec 64 := 16444#64
@[simp, arm64_norm, wp_norm] private abbrev off409c : BitVec 64 := 16540#64
@[simp, arm64_norm, wp_norm] abbrev off40f0 : BitVec 64 := 16624#64

private theorem le_512_pow64 : 512 ≤ 2 ^ 64 := by decide

local macro "step_dead_strQ512 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128_region
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by wp_norm_lhs)
    (off := 16 * $k) (total := 512) (by decide) le_512_pow64
    (by simp [$hspId:term]; try (clear * -; bv_omega)) ?_
  intro _
  try rw [setPC_setMem_collapse]))

local macro "step_dead_zero32 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  step_dead_strQ512 31 $hrunId $hspId $hchkId; step_dead_strQ512 30 $hrunId $hspId $hchkId; step_dead_strQ512 29 $hrunId $hspId $hchkId; step_dead_strQ512 28 $hrunId $hspId $hchkId;
  step_dead_strQ512 27 $hrunId $hspId $hchkId; step_dead_strQ512 26 $hrunId $hspId $hchkId; step_dead_strQ512 25 $hrunId $hspId $hchkId; step_dead_strQ512 24 $hrunId $hspId $hchkId;
  step_dead_strQ512 23 $hrunId $hspId $hchkId; step_dead_strQ512 22 $hrunId $hspId $hchkId; step_dead_strQ512 21 $hrunId $hspId $hchkId; step_dead_strQ512 20 $hrunId $hspId $hchkId;
  step_dead_strQ512 19 $hrunId $hspId $hchkId; step_dead_strQ512 18 $hrunId $hspId $hchkId; step_dead_strQ512 17 $hrunId $hspId $hchkId; step_dead_strQ512 16 $hrunId $hspId $hchkId;
  step_dead_strQ512 15 $hrunId $hspId $hchkId; step_dead_strQ512 14 $hrunId $hspId $hchkId; step_dead_strQ512 13 $hrunId $hspId $hchkId; step_dead_strQ512 12 $hrunId $hspId $hchkId;
  step_dead_strQ512 11 $hrunId $hspId $hchkId; step_dead_strQ512 10 $hrunId $hspId $hchkId; step_dead_strQ512 9 $hrunId $hspId $hchkId; step_dead_strQ512 8 $hrunId $hspId $hchkId;
  step_dead_strQ512 7 $hrunId $hspId $hchkId; step_dead_strQ512 6 $hrunId $hspId $hchkId; step_dead_strQ512 5 $hrunId $hspId $hchkId; step_dead_strQ512 4 $hrunId $hspId $hchkId;
  step_dead_strQ512 3 $hrunId $hspId $hchkId; step_dead_strQ512 2 $hrunId $hspId $hchkId; step_dead_strQ512 1 $hrunId $hspId $hchkId; step_dead_strQ512 0 $hrunId $hspId $hchkId))

local macro "prove_deser12_mod_loop " bId:term:arg _src:ident dst:ident bs:ident hbs:ident
    p0:num rn0:term:arg rn1:term:arg vsh:term:arg vq:term:arg srcReg:term:arg : tactic => `(tactic| (
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih =>
    intro k hkrem s f hpc hrun hspA hx_src hx8 hx_dst hv_sh hv_q hv6 hf
    have hk16 : k < 16 := by omega
    refine step_ldrD64_raw $bId $p0 ($p0 + 4) 2#5 (.Offset $srcReg 0#64) (24 * k)
      hpc hrun (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_src]) (by omega) rfl ?_
    refine step_ldrD64_raw $bId ($p0 + 4) ($p0 + 8) 3#5 (.UnscaledOffset $srcReg 12#64) (24 * k + 12)
      rfl (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_src]; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 3
    refine step_ld1S2_load $bId ($p0 + 20) ($p0 + 24) $rn0 2#5 (24 * k)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [hx_src]; clear * -; bv_omega) (by simp) (by omega) rfl ?_
    refine step_ld1S2_load $bId ($p0 + 24) ($p0 + 28) $rn1 3#5 (24 * k + 12)
      rfl (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [hx_src]; clear * -; bv_omega) (by simp) (by omega) rfl ?_
    wp_steps 3
    refine step_deser12_simd12_gen $bId ($p0 + 40) $vsh $vq
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by wp_norm_lhs) (by simp [hrun])
      (by simp [hv_sh]) (by simp [hv_q]) (by simp [hv6])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    have hv2_eq : neonDeserialize12Mod8h (loadVec12 $bs (24 * k)) =
        polyVecNat (tHatModPoly16 $bs) (2 * k) := by
      simpa [show 12 * (2 * k) = 24 * k by omega] using
        neonDeserialize12Mod8h_loadVec12_eq $hbs (2 * k) (by omega)
    have hv3_eq : neonDeserialize12Mod8h (loadVec12 $bs (24 * k + 12)) =
        polyVecNat (tHatModPoly16 $bs) (2 * k + 1) := by
      simpa [show 12 * (2 * k + 1) = 24 * k + 12 by omega] using
        neonDeserialize12Mod8h_loadVec12_eq $hbs (2 * k + 1) (by omega)
    refine step_stpQ128 (pc := $bId + BitVec.ofNat 64 ($p0 + 88)) (wb := none)
      (ea := $dst + BitVec.ofNat 64 (32 * k))
      (ea16 := $dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (tHatModPoly16 $bs) (2 * k))
      (v2 := polyVecNat (tHatModPoly16 $bs) (2 * k + 1))
      rfl (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_dst, hx8]) rfl (by simp [hv2_eq]) (by simp [hv3_eq])
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k) (by omega) (by clear * -; bv_omega))))
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k + 1) (by omega) (by clear * -; bv_omega))))
      (by wp_norm_lhs) ?_
    intro m'
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp [hx8] at hne
      · refine SepWP.mono
          (ih rem' (by omega) (k + 1) (by omega) _ _
            (by wp_norm_lhs) (by first | rfl | simp [hrun])
            (by simpa [State.spAligned] using hspA)
            (by simp [hx_src]; clear * -; bv_omega)
            (by simp [hx8]; clear * -; bv_omega)
            (by simp [hx_dst]) (by simp [hv_sh]) (by simp [hv_q]) (by simp [hv6])
            (update2_prefix hf)) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hv6_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hr1, by simpa using hr2,
          by simpa using hr3, by simpa using hr4, by simpa using hr5, by simpa using hr6,
          by simpa using hr7, hv6_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa [hx8] using hne
        have hlt1 : 32 * k < 2 ^ 64 := by omega
        have hlt2 : 32 * k + 32 < 2 ^ 64 := by omega
        have hnat := congrArg BitVec.toNat hbv
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
            show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt hlt2,
            show (512#64).toNat = 512 from rfl] at hnat
        omega
      subst hk15
      have hf32 : ∀ j, j < 32 →
          Function.update (Function.update f 30 (polyVecNat (tHatModPoly16 $bs) 30))
            31 (polyVecNat (tHatModPoly16 $bs) 31) j = polyVecNat (tHatModPoly16 $bs) j :=
        update2_prefix (k := 15) hf
      refine SepWP.done (by wp_norm_lhs) (by first | rfl | simp [hrun])
        ⟨by simp, by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv6], ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _))

private theorem sp1600_chk {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 1600#64) &&& 15#64 == 0#64) = true := by
  have h1 : (sp + 1600#64) &&& 15#64 = sp &&& 15#64 := by clear * -; bv_bits
  rwa [h1]

private theorem sp_add_30448_or_11 {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 30448#64) ||| 11#64) = sp + 30459#64 := by
  have h0 := sp_add_28848_or_11 (sp1600_chk hsp)
  rwa [show sp + 1600#64 + 28672#64 + 176#64 = sp + 30448#64 by clear * -; bv_omega,
    show sp + 1600#64 + 28859#64 = sp + 30459#64 by clear * -; bv_omega] at h0

private theorem sp_add_28368_or_11 {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 28368#64) ||| 11#64) = sp + 28379#64 := by
  have h0 := sp_add_26768_or_11 (sp1600_chk hsp)
  rwa [show sp + 1600#64 + 24576#64 + 2192#64 = sp + 28368#64 by clear * -; bv_omega,
    show sp + 1600#64 + 26779#64 = sp + 28379#64 by clear * -; bv_omega] at h0

/-! ## 1. Zero 2 + Loop 2 + Copy 2 + Zero 3 (`+0x3e80 → +0x403c`) -/

private theorem seg4b_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b) (s : State) (sp skA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off3e80) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_chk : (sp &&& 15#64 == 0#64) = true) (hx20 : s.readReg64 .x20 = skA + 384#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off3f1c) s
      (memRegion (sp + 4160#64) 512 ∗ Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = skA + 384#64 ∧
        sf.readReg64 .x21 = skA + 2688#64 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧ sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ memRegion (sp + 4160#64) 512 ∗ Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)) := by
  subst hbase
  have ha2688 : skA + 384#64 + 2304#64 = skA + 2688#64 := by clear * -; bv_omega
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_steps 2
  step_dead_zero32 hrun hsp hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], by simp, by simp, by simp [hx20],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, Entails.refl _⟩

private theorem seg4b_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3f1c → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x22 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + off3f7c) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatModPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 16156 Reg.x9 Reg.x10 1#5 0#5 Reg.x19

private theorem seg4b_copy2_zero3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b) (s : State) (sp : BitVec 64)
    (ek2 : List (BitVec 8)) (Rest : SepProp) (hpc : s.pc = b + off3f7c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true) (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off403c) s
      (Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ memRegion (sp + 23648#64) 512 ∗
        PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 ek2)) ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = sp + 4160#64 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧ sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 ek2)) ∗ memRegion (sp + 4160#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp4160 : PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 ek2)) = ((sp + 4160#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp23648 : ((sp + 23648#64) ↦ₛ bs2) =
      PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 ek2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha23648 : sp + 12288#64 + 2144#64 + 9216#64 = sp + 23648#64 := by clear * -; bv_omega
  rw [hp4160]
  wp_steps 9
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 23648#64, sp + 4160#64, bs2)
  rw [hp23648]
  have h512 : ((sp + 4160#64) ↦ₛ bs2) ⊢ memRegion (sp + 4160#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 4160#64) bs2; rwa [hbs2] at h
  have hP_pre : PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 ek2)) ∗
      ((sp + 4160#64) ↦ₛ bs2) ∗
      (Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest) ⊢
      memRegion (sp + 4160#64) 512 ∗
        (Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 ek2)) ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf2, hsp_chk])
    (by simp [evalAddrMode, hsp_sf2])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_step
  step_dead_zero32 hrun_sf hsp_sf2 hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp, by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp, by simp, by simp, by sep_frame⟩

/-! ## 2. Loop 3 + Copy 3 + `rho` Load (`+0x403c → +0x40f0`) -/

private theorem seg4b_loop3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off403c → s.status = .Running → s.spAligned = true →
      s.readReg64 .x21 = src + BitVec.ofNat 64 (24 * k) → s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x19 = dst → s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 → s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + off409c) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧ sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatModPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 16444 Reg.x9 Reg.x10 1#5 0#5 Reg.x21

private theorem seg4b_copy3_rho [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b) (s : State) (sp skA : BitVec 64)
    (ek3 rho : List (BitVec 8)) (Rest : SepProp) (hpc : s.pc = b + off409c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true) (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off40f0) s
      (((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (skA + 3072#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (skA + 3088#64) (rhoW rho 3 ++ rhoW rho 2) ∗ memRegion (sp + 24160#64) 512 ∗
        PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 ek3)) ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x9 = sp + 30459#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = sp + 28379#64 ∧
        sf.readReg64 .x22 = sp + 4160#64 ∧ sf.readReg64 .x23 = sp + 24576#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧ sf.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 0 ∧
        sf.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2 ∧
        (Pf ⊢ ((sp + 2032#64) ↦₆₄ skA) ∗ Vec128At (skA + 3072#64) (rhoW rho 1 ++ rhoW rho 0) ∗
          Vec128At (skA + 3088#64) (rhoW rho 3 ++ rhoW rho 2) ∗
          PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 ek3)) ∗ memRegion (sp + 4160#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs3_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek3)) = bs3
  have hbs3 : bs3.length = 512 := by rw [← hbs3_def, vecRangeBytes_length]
  have hp4160 : PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 ek3)) = ((sp + 4160#64) ↦ₛ bs3) := by
    rw [← hbs3_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp24160 : ((sp + 24160#64) ↦ₛ bs3) =
      PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 ek3)) := by
    rw [← hbs3_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha24160 : sp + 12288#64 + 2144#64 + 9728#64 = sp + 24160#64 := by clear * -; bv_omega
  rw [hp4160]
  wp_steps 9
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 24160#64, sp + 4160#64, bs3)
  rw [hp24160]
  have h512 : ((sp + 4160#64) ↦ₛ bs3) ⊢ memRegion (sp + 4160#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 4160#64) bs3; rwa [hbs3] at h
  have hP_pre : PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 ek3)) ∗
      ((sp + 4160#64) ↦ₛ bs3) ∗
      (((sp + 2032#64) ↦₆₄ skA) ∗
        Vec128At (skA + 3072#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (skA + 3088#64) (rhoW rho 3 ++ rhoW rho 2) ∗ Rest) ⊢
      ((sp + 2032#64) ↦₆₄ skA) ∗
        Vec128At (skA + 3072#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (skA + 3088#64) (rhoW rho 3 ++ rhoW rho 2) ∗
        PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 ek3)) ∗
        memRegion (sp + 4160#64) 512 ∗ Rest :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  wp_steps 6
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode])
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl)))) (by wp_norm_lhs) ?_
  wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp [sp_add_30448_or_11 hsp_chk], by simp [*],
      by simp [sp_add_28368_or_11 hsp_chk], by simp [*],
      by simp, by simp [*], by simp [*], by simp [*],
      by simp, by simp, Entails.refl _⟩

/-! ## 3. Composed `seg4b_ok` (`+0x3c38 → +0x40f0`) & `seg4_ok` (`+0x39c4 → +0x40f0`) -/

private theorem pk_split_sk {skA : BitVec 64} {pk : List (BitVec 8)} (hpk : pk.length = 1568) :
    ((skA + 1536#64) ↦ₛ pk) =
      ((skA + 1536#64) ↦ₛ pkEk0 pk) ∗ ((skA + 1920#64) ↦ₛ pkEk1 pk) ∗
      ((skA + 2304#64) ↦ₛ pkEk2 pk) ∗ ((skA + 2688#64) ↦ₛ pkEk3 pk) ∗
      Vec128At (skA + 3072#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
      Vec128At (skA + 3088#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) := by
  have h := pk_pointsTo_split (pkA := skA + 1536#64) hpk
  rw [rho_pointsTo_eq_vec128 (pkRho_len hpk)] at h
  simpa [BitVec.add_assoc] using h

set_option maxRecDepth 4096 in
private theorem seg4b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA : BitVec 64) (pk : List (BitVec 8)) (Rest : SepProp)
    (hpk : pk.length = 1568)
    (hpc : s.pc = b + off3c38) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = sp + 4160#64)
    (hx22 : s.readReg64 .x22 = sp + 14432#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off40f0) s
      (((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
        Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 22624#64) 2048 ∗
        ((skA + 1536#64) ↦ₛ pk) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = sp + 30459#64 ∧ sf.readReg64 .x20 = sp + 28379#64 ∧
        sf.readReg64 .x22 = sp + 4160#64 ∧ sf.readReg64 .x23 = sp + 24576#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0 ∧
        sf.readVReg128 1#5 = rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2 ∧
        (Pf ⊢ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
          Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
          memRegion (sp + 4160#64) 512 ∗
          PolyMem (sp + 22624#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
          PolyMem (sp + 23136#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
          PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
          PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
          ((skA + 1536#64) ↦ₛ pk) ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have h22 : memRegion (sp + 22624#64) 2048 =
      memRegion (sp + 22624#64) 512 ∗ memRegion (sp + 23136#64) 512 ∗
      memRegion (sp + 23648#64) 512 ∗ memRegion (sp + 24160#64) 512 := by
    rw [memRegion_split' (b := sp + 22624#64) (b' := sp + 23136#64) (n := 512) (k := (1536 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 23136#64) (b' := sp + 23648#64) (n := 512) (k := (1024 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 23648#64) (b' := sp + 24160#64) (n := 512) (k := (512 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  rw [h22, pk_split_sk hpk]
  refine SepWP.weaken_pre (show _ ⊢
    memRegion (sp + 4160#64) 512 ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
    Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg4b_init_zero0 hb hbase s sp skA _ hpc hrun hsp hsp_chk) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1, _, hx25_1, hx26_1, hfp1, hv0_1, hv1_1, hv6_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4160#64) (by decide) rfl fun f0 => ?_
  refine SepWP.weaken_pre (show PolyMem (sp + 4160#64) f0 ∗ _ ⊢
      ((skA + 1536#64) ↦ₛ pkEk0 pk) ∗ PolyMem (sp + 4160#64) f0 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1 (seg4b_loop0 hb (skA + 1536#64) (sp + 4160#64) (pkEk0 pk) _
    (pkEk0_len hpk) 15 0 rfl s1 f0 hpc1 hrun1 hspA1
    (by simp [hx9_1]) (by simp [hx8_1]) (hx19_1.trans hx19) hv0_1 hv1_1 hv6_1 (fun _ hj => by omega)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, _, _, hx20_2, hx21_2, hx22_2, _, hx25_2, hx26_2, hfp2, _, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
    Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
    memRegion (sp + 22624#64) 512 ∗
    PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2 (seg4b_copy0_zero1 hb hbase s2 sp skA (pkEk0 pk) _
    hpc2 hrun2 (hsp2.trans hsp1) hsp_chk hcl2 (hx20_2.trans hx20_1) (hx22_2.trans (hx22_1.trans hx22))) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, _, hx25_3, hx26_3, hfp3, hv0_3, hv1_3, hv6_3, hP3⟩
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢ memRegion (sp + 4160#64) 512 ∗ _ by sep_frame)) ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4160#64) (by decide) rfl fun f1 => ?_
  refine SepWP.weaken_pre (show PolyMem (sp + 4160#64) f1 ∗ _ ⊢
      ((skA + 1920#64) ↦ₛ pkEk1 pk) ∗ PolyMem (sp + 4160#64) f1 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl3 hro3 (seg4b_loop1 hb (skA + 1920#64) (sp + 4160#64) (pkEk1 pk) _
    (pkEk1_len hpk) 15 0 rfl s3 f1 hpc3 hrun3 hspA3
    (by simp [hx21_3, hx21_2, hx21_1]) (by simp [hx8_3]) hx22_3 hv0_3 hv1_3 hv6_3 (fun _ hj => by omega)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, _, hx19_4, hx20_4, _, _, hx25_4, hx26_4, hfp4, _, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (show _ ⊢
    memRegion (sp + 23136#64) 512 ∗
    PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl4 hro4
    (seg4b_copy1 hb hbase s4 sp (pkEk1 pk) _ hpc4 hrun4 (hsp4.trans hsp3) hsp_chk hcl4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, _, hx19_5, hx20_5, hx22_5, _, hx25_5, hx26_5, hfp5, hP5⟩
  refine SepWP.weaken_pre (Entails.trans hP5 (show _ ⊢
    memRegion (sp + 4160#64) 512 ∗
    Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl5 hro5
    (seg4b_zero2 hb hbase s5 sp skA _ hpc5 hrun5 hsp5 hsp_chk (hx20_5.trans (hx20_4.trans hx20_3))) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 hro6
    ⟨hsp6, hspA6, hx8_6, hx19_6, _, hx21_6, hx22_6, _, hx25_6, hx26_6, hfp6, hv0_6, hv1_6, hv6_6, hP6⟩
  refine SepWP.weaken_pre hP6 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4160#64) (by decide) rfl fun f2 => ?_
  refine SepWP.weaken_pre (show PolyMem (sp + 4160#64) f2 ∗ _ ⊢
      ((skA + 2304#64) ↦ₛ pkEk2 pk) ∗ PolyMem (sp + 4160#64) f2 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl6 hro6 (seg4b_loop2 hb (skA + 2304#64) (sp + 4160#64) (pkEk2 pk) _
    (pkEk2_len hpk) 15 0 rfl s6 f2 hpc6 hrun6 hspA6
    (by simp [hx19_6, hx19_5, hx19_4, hx19_3]) (by simp [hx8_6]) (hx22_6.trans hx22_5)
    hv1_6 hv0_6 hv6_6 (fun _ hj => by omega)) ?_
  rintro s7 P7 hpc7 hrun7 hcl7 hro7
    ⟨hsp7, _, _, hx21_7, _, _, hx25_7, hx26_7, hfp7, _, hP7⟩
  refine SepWP.weaken_pre (Entails.trans hP7 (show _ ⊢
    Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
    memRegion (sp + 23648#64) 512 ∗
    PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗ _ by sep_frame)) ?_
  refine sepWP_seq_env hcl7 hro7
    (seg4b_copy2_zero3 hb hbase s7 sp (pkEk2 pk) _ hpc7 hrun7 (hsp7.trans hsp6) hsp_chk hcl7) ?_
  rintro s8 P8 hpc8 hrun8 hcl8 hro8
    ⟨hsp8, hspA8, hx8_8, hx19_8, _, hx21_8, _, hx25_8, hx26_8, hfp8, hv0_8, hv1_8, hv6_8, hP8⟩
  refine SepWP.weaken_pre (Entails.trans hP8 (show _ ⊢ memRegion (sp + 4160#64) 512 ∗ _ by sep_frame)) ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 4160#64) (by decide) rfl fun f3 => ?_
  refine SepWP.weaken_pre (show PolyMem (sp + 4160#64) f3 ∗ _ ⊢
      ((skA + 2688#64) ↦ₛ pkEk3 pk) ∗ PolyMem (sp + 4160#64) f3 ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl8 hro8 (seg4b_loop3 hb (skA + 2688#64) (sp + 4160#64) (pkEk3 pk) _
    (pkEk3_len hpk) 15 0 rfl s8 f3 hpc8 hrun8 hspA8
    (by simp [hx21_8, hx21_7, hx21_6]) (by simp [hx8_8]) hx19_8 hv1_8 hv0_8 hv6_8 (fun _ hj => by omega)) ?_
  rintro s9 P9 hpc9 hrun9 hcl9 hro9
    ⟨hsp9, _, _, _, _, _, hx25_9, hx26_9, hfp9, _, hP9⟩
  refine SepWP.weaken_pre (Entails.trans hP9 (show _ ⊢
    ((sp + 2032#64) ↦₆₄ skA) ∗
    Vec128At (skA + 3072#64) (rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0) ∗
    Vec128At (skA + 3088#64) (rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2) ∗
    memRegion (sp + 24160#64) 512 ∗
    PolyMem (sp + 4160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗ _ by sep_frame)) ?_
  refine SepWP.mono
    (seg4b_copy3_rho hb hbase s9 sp skA (pkEk3 pk) (pkRho pk) _
      hpc9 hrun9 (hsp9.trans hsp8) hsp_chk hcl9) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx9_f, _, hx20_f, hx22_f, hx23_f, hx25_f, hx26_f, hfp_f, hv0_f, hv1_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f,
    by rw [hx25_f, hx25_9, hx25_8, hx25_7, hx25_6, hx25_5, hx25_4, hx25_3, hx25_2, hx25_1],
    by rw [hx26_f, hx26_9, hx26_8, hx26_7, hx26_6, hx26_5, hx26_4, hx26_3, hx26_2, hx26_1],
    by rw [hfp_f, hfp9, hfp8, hfp7, hfp6, hfp5, hfp4, hfp3, hfp2, hfp1],
    hv0_f, hv1_f, Entails.trans hPf (by sep_frame)⟩

set_option maxRecDepth 4096 in
theorem seg4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (m pk hPk z ct : List (BitVec 8)) (Rest : SepProp)
    (hm : m.length = 32) (hpk : pk.length = 1568) (hhPk : hPk.length = 32)
    (hz : z.length = 32) (hct : ct.length = 1568)
    (hpc : s.pc = b + off39c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = ctA) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off40f0) s
      (stackAt sp 1136 ∗ memRegion sp 128 ∗
        ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
        ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
        Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 2432#64) 2240 ∗ memRegion (sp + 14432#64) 10272 ∗
        ((sp + 28368#64) ↦ₛ m) ∗ memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
        ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
        ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = sp + 30459#64 ∧ sf.readReg64 .x20 = sp + 28379#64 ∧
        sf.readReg64 .x22 = sp + 4160#64 ∧ sf.readReg64 .x23 = sp + 24576#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0 ∧
        sf.readVReg128 1#5 = rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2 ∧
        (Pf ⊢ stackAt sp 1136 ∗ SpilledDecapsWords sp m ∗
          ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
          ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
          Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
          memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
          memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 14432#64) 8192 ∗
          PolyMem (sp + 22624#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
          PolyMem (sp + 23136#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
          PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
          PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
          ((sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗
          memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 32 ∗
          ((sp + 34432#64) ↦ₛ shake256List 32 (z ++ ct)) ∗
          ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
          ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ Rest)) := by
  have h24_in : memRegion (sp + 2432#64) 2240 =
      memRegion (sp + 2432#64) 1792 ∗ memRegion (sp + 4224#64) 448 :=
    memRegion_split' (b := sp + 2432#64) (b' := sp + 4224#64) (n := 1792) (k := (448 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have h25_mid : memRegion (sp + 2560#64) 1664 =
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 64 :=
    memRegion_split' (b := sp + 2560#64) (b' := sp + 4160#64) (n := 1600) (k := (64 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  have h41_512 : memRegion (sp + 4160#64) 64 ∗ memRegion (sp + 4224#64) 448 =
      memRegion (sp + 4160#64) 512 :=
    (memRegion_split' (b := sp + 4160#64) (b' := sp + 4224#64) (n := 64) (k := (448 : Nat))
      rfl (by clear * -; bv_omega) (by decide)).symm
  have h25_out : memRegion (sp + 2560#64) 2112 =
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 512 :=
    memRegion_split' (b := sp + 2560#64) (b' := sp + 4160#64) (n := 1600) (k := (512 : Nat))
      rfl (by clear * -; bv_omega) (by decide)
  rw [h24_in]
  refine SepWP.weaken_pre (show _ ⊢
    stackAt sp 1136 ∗ memRegion sp 128 ∗ ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗
    ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2432#64) 1792 ∗
    memRegion (sp + 14432#64) 10272 ∗ ((sp + 28368#64) ↦ₛ m) ∗
    memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
    ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗ _ by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4a_ok hb hbase s sp skA ctA m hPk z ct _ hm hhPk hz hct hpc hrun hsp hspA hcl hro hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx22_1, _, hx25_1, hx26_1, hfp_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢
    ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
    Vec128At (sp + 2048#64) 0x0b0a0a09080707060504040302010100#128 ∗
    memRegion (sp + 4160#64) 512 ∗ memRegion (sp + 22624#64) 2048 ∗
    ((skA + 1536#64) ↦ₛ pk) ∗ _ by rw [h25_mid, ← h41_512]; sep_frame)) ?_
  refine SepWP.mono
    (seg4b_ok hb hbase s1 sp skA pk _ hpk hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx19_1 hx22_1) ?_
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f, hx25_f, hx26_f, hfp_f, hv0_f, hv1_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f,
    hx25_f.trans hx25_1, hx26_f.trans hx26_1, hfp_f.trans hfp_1, hv0_f, hv1_f,
    Entails.trans hPf (by rw [h25_out]; sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2
