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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 4b (`+0x3cec → +0x4058`)

Steps scratch-buffer clears at `[sp + 5680 .. sp + 6192)`, modular NEON `deserialize_12`
Loops `0`, `1`, `2` (`tHat[0..2]`) from `pk = dk[1152..2304]`, `B28` (`memcpy`) copies to
`[sp + 11856 .. sp + 13392)`, and pre-`SampleNTT` setup (`x9 = dkA`, `w10 = 11`, `x23 = sp + 16384`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmhs8h simdTbl16b simdUshl8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 (
  loadVec12 neonDeserialize12Mod8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At polyVecNat
  step_ldrQ128 step_stpQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  applySimdResult_ok evalSimdModImmExt_bic_8h_0xf0_lsl8 evalSimdModImmExt_mvni_4s_3_msl16
  exec_simdDup_8h exec_simdTbl_16b_1 exec_simdUshl_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (
  blk28_memcpy_04 exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  modDeser12_loadVec12_pair modTHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdAdd_8h_svc exec_simdCmhs_8h_svc
  step_deser12_simd12_gen step_ld1S2_load step_ldrD64_raw)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1 (
  SepStore128.polyMem polyMem_congr trunc16_3329 update2_prefix)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x3cec → 0x4054]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible]
  blkPC04 dup8x16 polyVecNat modTHatPoly16
  loadVec12 neonDeserialize12Mod8h
  simdTbl16b simdUshl8h simdCmhs8h simdAdd8h

attribute [local wp_norm ↓ high]
  applySimdResult_ok evalSimdModImmExt_mvni_4s_3_msl16 evalSimdModImmExt_bic_8h_0xf0_lsl8
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdMovi_2d_0 exec_simdDup_8h trunc16_3329
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdCmhs_8h_svc exec_simdAdd_8h_svc

@[simp, arm64_norm, wp_norm] abbrev offSeg4aEnd : BitVec 64 := BitVec.ofNat 64 15596
@[simp, arm64_norm, wp_norm] private abbrev off3d90 : BitVec 64 := BitVec.ofNat 64 15760
@[simp, arm64_norm, wp_norm] private abbrev off3df0 : BitVec 64 := BitVec.ofNat 64 15856
@[simp, arm64_norm, wp_norm] private abbrev off3eac : BitVec 64 := BitVec.ofNat 64 16044
@[simp, arm64_norm, wp_norm] private abbrev off3f0c : BitVec 64 := BitVec.ofNat 64 16140
@[simp, arm64_norm, wp_norm] private abbrev off3fc8 : BitVec 64 := BitVec.ofNat 64 16328
@[simp, arm64_norm, wp_norm] private abbrev off4028 : BitVec 64 := BitVec.ofNat 64 16424
@[simp, arm64_norm, wp_norm] abbrev offSeg4End : BitVec 64 := BitVec.ofNat 64 16472

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

local macro "step_dead_zero28 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  step_dead_strQ512 31 $hrunId $hspId $hchkId; step_dead_strQ512 30 $hrunId $hspId $hchkId;
  step_dead_strQ512 29 $hrunId $hspId $hchkId; step_dead_strQ512 28 $hrunId $hspId $hchkId;
  step_dead_strQ512 27 $hrunId $hspId $hchkId; step_dead_strQ512 26 $hrunId $hspId $hchkId;
  step_dead_strQ512 25 $hrunId $hspId $hchkId; step_dead_strQ512 24 $hrunId $hspId $hchkId;
  step_dead_strQ512 23 $hrunId $hspId $hchkId; step_dead_strQ512 22 $hrunId $hspId $hchkId;
  step_dead_strQ512 21 $hrunId $hspId $hchkId; step_dead_strQ512 20 $hrunId $hspId $hchkId;
  step_dead_strQ512 19 $hrunId $hspId $hchkId; step_dead_strQ512 18 $hrunId $hspId $hchkId;
  step_dead_strQ512 17 $hrunId $hspId $hchkId; step_dead_strQ512 16 $hrunId $hspId $hchkId;
  step_dead_strQ512 15 $hrunId $hspId $hchkId; step_dead_strQ512 14 $hrunId $hspId $hchkId;
  step_dead_strQ512 13 $hrunId $hspId $hchkId; step_dead_strQ512 12 $hrunId $hspId $hchkId;
  step_dead_strQ512 11 $hrunId $hspId $hchkId; step_dead_strQ512 10 $hrunId $hspId $hchkId;
  step_dead_strQ512 9 $hrunId $hspId $hchkId; step_dead_strQ512 8 $hrunId $hspId $hchkId;
  step_dead_strQ512 7 $hrunId $hspId $hchkId; step_dead_strQ512 6 $hrunId $hspId $hchkId;
  step_dead_strQ512 5 $hrunId $hspId $hchkId; step_dead_strQ512 4 $hrunId $hspId $hchkId))

local macro "step_dead_zero4 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  step_dead_strQ512 3 $hrunId $hspId $hchkId; step_dead_strQ512 2 $hrunId $hspId $hchkId;
  step_dead_strQ512 1 $hrunId $hspId $hchkId; step_dead_strQ512 0 $hrunId $hspId $hchkId))

local macro "step_dead_zero32 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  step_dead_zero28 $hrunId $hspId $hchkId; step_dead_zero4 $hrunId $hspId $hchkId))

/-! ## 1. Init + Zero 0 (`+0x3cec → +0x3d90`) -/

private theorem seg4b_init_zero0 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4aEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = sp + 5680#64)
    (hx23 : s.readReg64 .x23 = dkA + 384#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3d90) s
      (memRegion (sp + 5680#64) 512 ∗
        Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = (dkA + 1152#64) + 12#64 ∧
        sf.readReg64 .x20 = sp + 5680#64 ∧
        sf.readReg64 .x21 = dkA + 1536#64 ∧
        sf.readReg64 .x23 = dkA + 384#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = dup8x16 3329#16 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ memRegion (sp + 5680#64) 512 ∗
          Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)) := by
  subst hbase
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 3
  step_dead_zero28 hrun hsp hsp_chk
  simp only [BitVec.add_assoc]
  wp_step
  step_dead_zero4 hrun hsp hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp,
      by simp [hx20], by simp,
      by simp [hx23], by simp, by simp, by simp,
      by simp, by simp, by simp, Entails.refl _⟩

/-! ## 2. Loop 0 (`+0x3d90 → +0x3df0`) & Modular `deserialize_12` Loop Macro -/

private theorem seg4b_loop0 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3d90 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + 12#64 + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x20 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 1#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (modTHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + off3df0) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (modTHatPoly16 bs)) ∗ Rest)) := by
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih =>
    intro k hkrem s f hpc hrun hspA hx_src hx8 hx_dst hv_sh hv_q hv6 hf
    have hk16 : k < 16 := by omega
    refine step_ldrD64_raw b 15760 15764 2#5 _ (24 * k)
      hpc hrun (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_src]; clear * -; bv_omega) (by omega) rfl ?_
    refine step_ldrD64_raw b 15764 15768 3#5 _ (24 * k + 12)
      rfl (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_src]; clear * -; bv_omega) (by omega) rfl ?_
    wp_steps 1
    refine step_ld1S2_load b 15772 15776 Reg.x10 2#5 (24 * k)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp; clear * -; bv_omega) (by simp) (by omega) rfl ?_
    wp_steps 2
    refine step_ld1S2_load b 15784 15788 Reg.x10 3#5 (24 * k + 12)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp; clear * -; bv_omega) (by simp) (by omega) rfl ?_
    wp_steps 3
    refine step_deser12_simd12_gen b 15800 0#5 1#5
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by wp_norm_lhs) (by simp [hrun])
      (by simp [hv_sh]) (by simp [hv_q]) (by simp [hv6])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    obtain ⟨hv2_eq, hv3_eq⟩ := modDeser12_loadVec12_pair hbs k hk16
    refine step_stpQ128 (pc := b + BitVec.ofNat 64 15848) (wb := none)
      (ea := dst + BitVec.ofNat 64 (32 * k))
      (ea16 := dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (modTHatPoly16 bs) (2 * k))
      (v2 := polyVecNat (modTHatPoly16 bs) (2 * k + 1))
      rfl (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode]) rfl (by simp [hv2_eq]) (by simp [hv3_eq])
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
        subst hk15; simp at hne
      · refine SepWP.mono
          (ih rem' (by omega) (k + 1) (by omega) _ _
            (by wp_norm_lhs) (by first | rfl | simp [hrun])
            (by simpa [State.spAligned] using hspA)
            (by simp; clear * -; bv_omega)
            (by simp; clear * -; bv_omega)
            (by simp [hx_dst]) (by simp [hv_sh]) (by simp [hv_q]) (by simp [hv6])
            (update2_prefix hf)) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hr1, hr2, hr3, hr4, hr5, hr6, hv6_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hr1, by simpa using hr2,
          by simpa using hr3, by simpa using hr4, by simpa using hr5, by simpa using hr6,
          hv6_f, hPf⟩
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
          Function.update (Function.update f 30 (polyVecNat (modTHatPoly16 bs) 30))
            31 (polyVecNat (modTHatPoly16 bs) 31) j = polyVecNat (modTHatPoly16 bs) j :=
        update2_prefix (k := 15) hf
      refine SepWP.done (by wp_norm_lhs) (by first | rfl | simp [hrun])
        ⟨by simp, by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv6], ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _

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
    obtain ⟨hv2_eq, hv3_eq⟩ := modDeser12_loadVec12_pair $hbs k hk16
    refine step_stpQ128 (pc := $bId + BitVec.ofNat 64 ($p0 + 88)) (wb := none)
      (ea := $dst + BitVec.ofNat 64 (32 * k))
      (ea16 := $dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (modTHatPoly16 $bs) (2 * k))
      (v2 := polyVecNat (modTHatPoly16 $bs) (2 * k + 1))
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
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hr1, hr2, hr3, hr4, hr5, hr6, hv6_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hr1, by simpa using hr2,
          by simpa using hr3, by simpa using hr4, by simpa using hr5, by simpa using hr6,
          hv6_f, hPf⟩
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
          Function.update (Function.update f 30 (polyVecNat (modTHatPoly16 $bs) 30))
            31 (polyVecNat (modTHatPoly16 $bs) 31) j = polyVecNat (modTHatPoly16 $bs) j :=
        update2_prefix (k := 15) hf
      refine SepWP.done (by wp_norm_lhs) (by first | rfl | simp [hrun])
        ⟨by simp, by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv6], ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _))

/-! ## 3. Copy 0 + Zero 1 + Loop 1 (`+0x3df0 → +0x3f0c`) -/

private theorem seg4b_copy0_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (pk0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off3df0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx23 : s.readReg64 .x23 = dkA + 384#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3eac) s
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x20 = dkA + 1920#64 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = sp + 5680#64 ∧
        sf.readReg64 .x23 = dkA + 384#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
          memRegion (sp + 5680#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs0_def : vecRangeBytes 32 (polyVecNat (modTHatPoly16 pk0)) = bs0
  have hbs0 : bs0.length = 512 := by rw [← hbs0_def, vecRangeBytes_length]
  have hp5680 : PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) = ((sp + 5680#64) ↦ₛ bs0) := by
    rw [← hbs0_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp11856 : ((sp + 11856#64) ↦ₛ bs0) =
      PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) := by
    rw [← hbs0_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp5680]
  wp_steps 7
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 11856#64, sp + 5680#64, bs0)
  rw [hp11856]
  have h512 : ((sp + 5680#64) ↦ₛ bs0) ⊢ memRegion (sp + 5680#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 5680#64) bs0; rwa [hbs0] at h
  have hP_pre : PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
      ((sp + 5680#64) ↦ₛ bs0) ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest) ⊢
      memRegion (sp + 5680#64) 512 ∗
        (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans (by simp [hsp])
  have hx21_sf : sf.readReg64 .x21 = s.readReg64 .x21 := Eq.trans ‹_› (by simp)
  have hx22_sf : sf.readReg64 .x22 = sp + 5680#64 := Eq.trans ‹_› (by simp)
  have hx23_sf : sf.readReg64 .x23 = dkA + 384#64 := Eq.trans ‹_› (by simp [hx23])
  have hx26_sf : sf.readReg64 .x26 = s.readReg64 .x26 := Eq.trans ‹_› (by simp)
  have hx28_sf : sf.readReg64 .x28 = s.readReg64 .x28 := Eq.trans ‹_› (by simp)
  have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := Eq.trans hcs_sf (by simp)
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf2, hsp_chk])
    (by simp [evalAddrMode, hsp_sf2])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_steps 2
  step_dead_zero32 hrun_sf hsp_sf2 hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp, by simp,
      by simp [hx21_sf], by simp [hx22_sf], by simp [hx23_sf],
      by simp [hx26_sf], by simp [hx28_sf], by simp [hfp_sf],
      by simp, by simp, by simp, by sep_frame⟩

private theorem seg4b_loop1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3eac → s.status = .Running → s.spAligned = true →
      s.readReg64 .x21 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x22 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (modTHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + off3f0c) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (modTHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 16044 Reg.x9 Reg.x10 1#5 0#5 Reg.x21


/-! ## 4. Copy 1 + Zero 2 + Loop 2 + Copy 2 + Pre-`SampleNTT` Tail (`+0x3f0c → +0x4058`) -/

private theorem seg4b_copy1_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (pk1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off3f0c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off3fc8) s
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 12368#64) 512 ∗
        PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk1)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = sp + 5680#64 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
          memRegion (sp + 5680#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs1_def : vecRangeBytes 32 (polyVecNat (modTHatPoly16 pk1)) = bs1
  have hbs1 : bs1.length = 512 := by rw [← hbs1_def, vecRangeBytes_length]
  have hp5680 : PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk1)) = ((sp + 5680#64) ↦ₛ bs1) := by
    rw [← hbs1_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp12368 : ((sp + 12368#64) ↦ₛ bs1) =
      PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) := by
    rw [← hbs1_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp5680]
  wp_steps 8
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 12368#64, sp + 5680#64, bs1)
  rw [hp12368]
  have h512 : ((sp + 5680#64) ↦ₛ bs1) ⊢ memRegion (sp + 5680#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 5680#64) bs1; rwa [hbs1] at h
  have hP_pre : PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      ((sp + 5680#64) ↦ₛ bs1) ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest) ⊢
      memRegion (sp + 5680#64) 512 ∗
        (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans (by simp [hsp])
  have hx20_sf : sf.readReg64 .x20 = s.readReg64 .x20 := Eq.trans ‹_› (by simp)
  have hx21_sf : sf.readReg64 .x21 = sp + 5680#64 := Eq.trans ‹_› (by simp)
  have hx23_sf : sf.readReg64 .x23 = s.readReg64 .x23 := Eq.trans ‹_› (by simp)
  have hx26_sf : sf.readReg64 .x26 = s.readReg64 .x26 := Eq.trans ‹_› (by simp)
  have hx28_sf : sf.readReg64 .x28 = s.readReg64 .x28 := Eq.trans ‹_› (by simp)
  have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := Eq.trans hcs_sf (by simp)
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf2, hsp_chk])
    (by simp [evalAddrMode, hsp_sf2])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_step
  step_dead_zero32 hrun_sf hsp_sf2 hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp, by simp [hx20_sf], by simp [hx21_sf], by simp [hx23_sf],
      by simp [hx26_sf], by simp [hx28_sf], by simp [hfp_sf],
      by simp, by simp, by simp, by sep_frame⟩

private theorem seg4b_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off3fc8 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x20 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (modTHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + off4028) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (modTHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 16328 Reg.x9 Reg.x10 1#5 0#5 Reg.x20

private theorem seg4b_copy2_tail [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (pk2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + off4028) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg4End) s
      (((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 12880#64) 512 ∗
        PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk2)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = dkA ∧
        sf.readReg64 .x10 = 11#64 ∧
        sf.readReg64 .x23 = sp + 16384#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 1872#64) ↦₆₄ dkA) ∗
          PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
          memRegion (sp + 5680#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (modTHatPoly16 pk2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp5680 : PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk2)) = ((sp + 5680#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp12880 : ((sp + 12880#64) ↦ₛ bs2) =
      PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp5680]
  wp_steps 8
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 12880#64, sp + 5680#64, bs2)
  rw [hp12880]
  have h512 : ((sp + 5680#64) ↦ₛ bs2) ⊢ memRegion (sp + 5680#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 5680#64) bs2; rwa [hbs2] at h
  have hP_pre : PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      ((sp + 5680#64) ↦ₛ bs2) ∗ (((sp + 1872#64) ↦₆₄ dkA) ∗ Rest) ⊢
      ((sp + 1872#64) ↦₆₄ dkA) ∗
        (PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
          memRegion (sp + 5680#64) 512 ∗ Rest) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans (by simp [hsp])
  have hx26_sf : sf.readReg64 .x26 = s.readReg64 .x26 := Eq.trans ‹_› (by simp)
  have hx27_sf : sf.readReg64 .x27 = sp + 5680#64 := Eq.trans ‹_› (by simp)
  have hx28_sf : sf.readReg64 .x28 = s.readReg64 .x28 := Eq.trans ‹_› (by simp)
  have hfp_sf : sf.readReg64 .fp = s.readReg64 .fp := Eq.trans hcs_sf (by simp)
  wp_steps 3
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp, by simp, by simp,
      by simp [hx26_sf], by simp [hx27_sf], by simp [hx28_sf], by simp [hfp_sf],
      by sep_frame⟩

private theorem sepWP_seq_cl {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post1 post2 : State → SepProp → Prop} [MlKemPlacement]
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      mlkemMultiLib.CodeLoaded mlkemMpl sm.mem → post1 sm Pm → SepWP prog target sm Pm post2) :
    SepWP prog target s P post2 :=
  SepWP.seq
    (SepWP.mono_frozen
      (post' := fun sm Pm => mlkemMultiLib.CodeLoaded mlkemMpl sm.mem ∧ post1 sm Pm)
      (Φ := fun m => mlkemMultiLib.CodeLoaded mlkemMpl m)
      (fun _ _ hc hkf => hc.of_keepsFrozen hkf) hcl h1
      (fun _ _ _ _ hc hp1 => ⟨hc, hp1⟩))
    (fun sm Pm hpc hrun ⟨hc, hp1⟩ => h2 sm Pm hpc hrun hc hp1)

/-! ## 5. Composed `seg4b_ok` (`+0x3cec → +0x4058`) -/

theorem seg4b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (pk0 pk1 pk2 : List (BitVec 8)) (Rest : SepProp)
    (hpk0 : pk0.length = 384) (hpk1 : pk1.length = 384) (hpk2 : pk2.length = 384)
    (hpc : s.pc = b + offSeg4aEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = sp + 5680#64)
    (hx23 : s.readReg64 .x23 = dkA + 384#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg4End) s
      (((sp + 1872#64) ↦₆₄ dkA) ∗
        Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 5680#64) 512 ∗
        memRegion (sp + 11856#64) 1536 ∗
        ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = dkA ∧ sf.readReg64 .x10 = 11#64 ∧
        sf.readReg64 .x23 = sp + 16384#64 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 1872#64) ↦₆₄ dkA) ∗
          Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
          memRegion (sp + 5680#64) 512 ∗
          PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
          PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
          PolyMem (sp + 12880#64) (polyVecNat (modTHatPoly16 pk2)) ∗
          ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have h11856 : memRegion (sp + 11856#64) 1536 =
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 512 ∗ memRegion (sp + 12880#64) 512 := by
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12368#64) (b' := sp + 12880#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  rw [h11856]
  refine SepWP.weaken_pre (show _ ⊢
      memRegion (sp + 5680#64) 512 ∗ Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
      (((sp + 1872#64) ↦₆₄ dkA) ∗ memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 512 ∗
        memRegion (sp + 12880#64) 512 ∗ ((dkA + 1152#64) ↦ₛ pk0) ∗
        ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by sep_frame) ?_
  refine sepWP_seq_cl hcl (seg4b_init_zero0 hb hbase s sp dkA _ hpc hrun hsp hsp_chk hx20 hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx20_1, hx21_1, hx23_1, hx26_1, hx28_1, hfp1, hv0_1, hv1_1, hv6_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 5680#64) (by decide) (sepProp_ext (by sep_frame) (by sep_frame)) fun f0 => ?_
  refine SepWP.weaken_pre (show _ ⊢ ((dkA + 1152#64) ↦ₛ pk0) ∗ PolyMem (sp + 5680#64) f0 ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 12368#64) 512 ∗ memRegion (sp + 12880#64) 512 ∗
        ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by dsimp only [PolyMem]; sep_frame) ?_
  refine sepWP_seq_cl hcl1 (seg4b_loop0 hb (dkA + 1152#64) (sp + 5680#64) pk0 _ hpk0 15 0 rfl s1 f0
    hpc1 hrun1 hspA1 (by simpa [BitVec.add_zero] using hx9_1) (by simpa using hx8_1) hx20_1 hv0_1 hv1_1 hv6_1 (by intro _ hj; omega)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 ⟨hsp2, hspA2, _, hx21_2, hx23_2, hx26_2, hx28_2, hfp2, _, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢
      Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ memRegion (sp + 11856#64) 512 ∗
      PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk0)) ∗ (((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 12368#64) 512 ∗ memRegion (sp + 12880#64) 512 ∗ ((dkA + 1152#64) ↦ₛ pk0) ∗
        ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_cl hcl2 (seg4b_copy0_zero1 hb hbase s2 sp dkA pk0 _ hpc2 hrun2 (hsp2.trans hsp1) hsp_chk hcl2 (hx23_2.trans hx23_1)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 ⟨hsp3, hspA3, hx8_3, hx20_3, hx21_3, hx22_3, hx23_3, hx26_3, hx28_3, hfp3, hv0_3, hv1_3, hv6_3, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 5680#64) (by decide) (sepProp_ext (by sep_frame) (by sep_frame)) fun f1 => ?_
  refine SepWP.weaken_pre (show _ ⊢ ((dkA + 1536#64) ↦ₛ pk1) ∗ PolyMem (sp + 5680#64) f1 ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 12368#64) 512 ∗ memRegion (sp + 12880#64) 512 ∗ ((dkA + 1152#64) ↦ₛ pk0) ∗
        ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by dsimp only [PolyMem]; sep_frame) ?_
  refine sepWP_seq_cl hcl3 (seg4b_loop1 hb (dkA + 1536#64) (sp + 5680#64) pk1 _ hpk1 15 0 rfl s3 f1
    hpc3 hrun3 hspA3 (by simpa [BitVec.add_zero] using hx21_3.trans (hx21_2.trans hx21_1)) (by simpa using hx8_3) hx22_3 hv1_3 hv0_3 hv6_3 (by intro _ hj; omega)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 ⟨hsp4, _, hx20_4, _, hx23_4, hx26_4, hx28_4, hfp4, _, hP4⟩
  refine SepWP.weaken_pre (Entails.trans hP4 (show _ ⊢
      Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗ memRegion (sp + 12368#64) 512 ∗
      PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk1)) ∗
      (PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 12880#64) 512 ∗ ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗
        ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_cl hcl4 (seg4b_copy1_zero2 hb hbase s4 sp pk1 _ hpc4 hrun4 (hsp4.trans hsp3) hsp_chk hcl4) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 ⟨hsp5, hspA5, hx8_5, hx20_5, hx21_5, _, hx26_5, hx28_5, hfp5, hv0_5, hv1_5, hv6_5, hP5⟩
  refine SepWP.weaken_pre hP5 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 5680#64) (by decide) (sepProp_ext (by sep_frame) (by sep_frame)) fun f2 => ?_
  refine SepWP.weaken_pre (show _ ⊢ ((dkA + 1920#64) ↦ₛ pk2) ∗ PolyMem (sp + 5680#64) f2 ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗ ((sp + 1872#64) ↦₆₄ dkA) ∗
        memRegion (sp + 12880#64) 512 ∗ ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ Rest) by dsimp only [PolyMem]; sep_frame) ?_
  refine sepWP_seq_cl hcl5 (seg4b_loop2 hb (dkA + 1920#64) (sp + 5680#64) pk2 _ hpk2 15 0 rfl s5 f2
    hpc5 hrun5 hspA5 (by simpa [BitVec.add_zero] using hx20_5.trans (hx20_4.trans hx20_3)) (by simpa using hx8_5) hx21_5 hv1_5 hv0_5 hv6_5 (by intro _ hj; omega)) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 ⟨hsp6, _, _, _, _, hx26_6, hx28_6, hfp6, _, hP6⟩
  refine SepWP.weaken_pre (Entails.trans hP6 (show _ ⊢
      ((sp + 1872#64) ↦₆₄ dkA) ∗ memRegion (sp + 12880#64) 512 ∗
      PolyMem (sp + 5680#64) (polyVecNat (modTHatPoly16 pk2)) ∗
      (Vec128At (sp + 1904#64) 0x0b0a0a09080707060504040302010100#128 ∗
        PolyMem (sp + 11856#64) (polyVecNat (modTHatPoly16 pk0)) ∗
        PolyMem (sp + 12368#64) (polyVecNat (modTHatPoly16 pk1)) ∗
        ((dkA + 1152#64) ↦ₛ pk0) ∗ ((dkA + 1536#64) ↦ₛ pk1) ∗ ((dkA + 1920#64) ↦ₛ pk2) ∗ Rest) by sep_frame)) ?_
  refine SepWP.mono (seg4b_copy2_tail hb hbase s6 sp dkA pk2 _ hpc6 hrun6 (hsp6.trans hsp5) hsp_chk hcl6) ?_
  rintro sf Pf _ _ ⟨hsp7, hspA7, hx9_7, hx10_7, hx23_7, hx26_7, hx27_7, hx28_7, hfp7, hPf⟩
  refine ⟨hsp7, hspA7, hx9_7, hx10_7, hx23_7, ?_, hx27_7, ?_, ?_,
    Entails.trans hPf (by sep_frame)⟩
  · exact hx26_7.trans (hx26_6.trans (hx26_5.trans (hx26_4.trans (hx26_3.trans (hx26_2.trans hx26_1)))))
  · exact hx28_7.trans (hx28_6.trans (hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans hx28_1)))))
  · exact hfp7.trans (hfp6.trans (hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1)))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4b
