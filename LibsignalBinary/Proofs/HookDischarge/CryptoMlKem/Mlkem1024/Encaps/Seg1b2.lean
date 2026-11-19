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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1

/-!
# `kyber_encapsulate` (`B07`) — Segment 1b Part 2 (`+0x04f8 .. +0x0758`)

Steps modular NEON `deserialize_12` Loops `2` and `3` (`tHat[2]`, `tHat[3]`), their `B28`
(`memcpy`) copies to `[sp + 22048 .. sp + 23072)`, and the `32`-byte `rho` load + lane
duplication (`+0x072c → +0x0758`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h
  simdCmhs8h
  simdTbl16b
  simdUshl8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12 (
  loadVec12
  neonDeserialize12Mod8h
  neonDeserialize12ModStep8h
  neonDeserialize12Raw8h
)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.PermuteInlined.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse
  step_strQ128_region
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem
  SepLoad128
  SepStore128
  Vec128At
  polyVecNat
  step_ldrQ128
  step_stpQ128
  vecRangeBytes
  vecRangeBytes_length
  vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  applySimdResult_ok
  evalSimdModImmExt_bic_8h_0xf0_lsl8
  evalSimdModImmExt_mvni_4s_3_msl16
  exec_simdDup_8h
  exec_simdTbl_16b_1
  exec_simdUshl_8h
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  evalSimdModImmExt_bic_8h_13_lsl8
  exec_simdAdd_8h_svc
  exec_simdCmhs_8h_svc
  exec_simdMovi_2d_0
  neonDeserialize12Mod8h_loadVec12_eq
  rhoW
  sp_add_26768_or_11
  sp_add_28848_or_11
  step_deser12_simd12_gen
  step_ld1S2_load
  step_ldrD64_raw
  tHatModPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1 (
  SepStore128.polyMem
  blk28_memcpy_07
  mask_0x0fff_eq_dup
  mask_0xf2ff_eq_dup
  mask_3329_eq_dup
  polyMem_congr
  trunc16_3329
  update2_prefix
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x04f8 → 0x0754]
end

attribute [local irreducible]
  blkPC07 dup8x16 polyVecNat tHatModPoly16
  loadVec12 neonDeserialize12Mod8h
  simdTbl16b simdUshl8h simdCmhs8h simdAdd8h

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_2d_lane0 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b01000#5 0b0000#4 rn rd) s =
      (s.writeVReg128 rd ((s.readVReg128 rn).extractLsb' 0 64 ++
        (s.readVReg128 rn).extractLsb' 0 64)).advancePC := by
  simp [execInstWithSvc, getSimdLane, mapSimdLanes_true_64, mapLanes, laneMask_64]
  apply congrArg State.advancePC; apply congrArg (s.writeVReg128 rd)
  generalize s.readVReg128 rn = x; bv_bits

@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_2d_lane1 {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b11000#5 0b0000#4 rn rd) s =
      (s.writeVReg128 rd ((s.readVReg128 rn).extractLsb' 64 64 ++
        (s.readVReg128 rn).extractLsb' 64 64)).advancePC := by
  simp [execInstWithSvc, getSimdLane, mapSimdLanes_true_64, mapLanes, laneMask_64]
  apply congrArg State.advancePC; apply congrArg (s.writeVReg128 rd)
  generalize s.readVReg128 rn = x; bv_bits

attribute [local wp_norm ↓ high]
  applySimdResult_ok evalSimdModImmExt_mvni_4s_3_msl16 evalSimdModImmExt_bic_8h_0xf0_lsl8
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdMovi_2d_0 exec_simdDup_8h trunc16_3329
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdCmhs_8h_svc exec_simdAdd_8h_svc
  exec_simdDup_2d_lane0 exec_simdDup_2d_lane1

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
  step_dead_strQ512 5 $hrunId $hspId $hchkId; step_dead_strQ512 4 $hrunId $hspId $hchkId;
  step_dead_strQ512 3 $hrunId $hspId $hchkId; step_dead_strQ512 2 $hrunId $hspId $hchkId;
  step_dead_strQ512 1 $hrunId $hspId $hchkId; step_dead_strQ512 0 $hrunId $hspId $hchkId))

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
      (by simp [evalAddrMode, hx_dst, hx8]) rfl
      (by simp [hv2_eq])
      (by simp [hv3_eq])
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

/-! ## 1. Zero 2 + Loop 2 + Copy 2 + Zero 3 + Loop 3 + Copy 3 + Rho Load (`+0x04f8 → +0x0758`) -/

theorem seg1b_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x04f8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = pkA + 384#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0594#64) s
      (memRegion (sp + 2560#64) 512 ∗
        Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = pkA + 1152#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ memRegion (sp + 2560#64) 512 ∗
          Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest)) := by
  subst hbase
  have ha1152 : pkA + 384#64 + 768#64 = pkA + 1152#64 := by clear * -; bv_omega
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_steps 2
  step_dead_zero32 hrun hsp hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, Entails.refl _⟩

theorem seg1b_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0594#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x23 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x05f4#64) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatModPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 0x0594 Reg.x9 Reg.x10 1#5 0#5 Reg.x23

theorem seg1b_copy2_zero3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (ek2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x05f4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x06ac#64) s
      (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
        memRegion (sp + 22048#64) 512 ∗
        PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek2)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = sp + 2560#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 ek2)) ∗
          memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp2560 : PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek2)) = ((sp + 2560#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp22048 : ((sp + 22048#64) ↦ₛ bs2) =
      PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 ek2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha22048 : sp + 12288#64 + 544#64 + 9216#64 = sp + 22048#64 := by clear * -; bv_omega
  rw [hp2560]
  wp_steps 7
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 22048#64, sp + 2560#64, bs2)
  rw [hp22048]
  have h512 : ((sp + 2560#64) ↦ₛ bs2) ⊢ memRegion (sp + 2560#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 2560#64) bs2; rwa [hbs2] at h
  have hP_pre : PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 ek2)) ∗
      ((sp + 2560#64) ↦ₛ bs2) ∗
      (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest) ⊢
      memRegion (sp + 2560#64) 512 ∗
        (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 22048#64) (polyVecNat (tHatModPoly16 ek2)) ∗ Rest) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) ?_; sep_frame
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

theorem seg1b_loop3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x06ac#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x19 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x070c#64) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatModPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 0x06ac Reg.x9 Reg.x10 1#5 0#5 Reg.x19

theorem seg1b_copy3_rho [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (ek3 rho : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x070c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = pkA) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0758#64) s
      (Vec128At (pkA + 1536#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (pkA + 1552#64) (rhoW rho 3 ++ rhoW rho 2) ∗
        memRegion (sp + 22560#64) 512 ∗
        PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek3)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = sp + 28859#64 ∧
        sf.readReg64 .x19 = sp + 2560#64 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 26779#64 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = rhoW rho 1 ++ rhoW rho 1 ∧
        sf.readVReg128 1#5 = rhoW rho 3 ++ rhoW rho 2 ∧
        sf.readVReg128 2#5 = rhoW rho 0 ++ rhoW rho 0 ∧
        (Pf ⊢ Vec128At (pkA + 1536#64) (rhoW rho 1 ++ rhoW rho 0) ∗
          Vec128At (pkA + 1552#64) (rhoW rho 3 ++ rhoW rho 2) ∗
          PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 ek3)) ∗
          memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs3_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek3)) = bs3
  have hbs3 : bs3.length = 512 := by rw [← hbs3_def, vecRangeBytes_length]
  have hp2560 : PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek3)) = ((sp + 2560#64) ↦ₛ bs3) := by
    rw [← hbs3_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp22560 : ((sp + 22560#64) ↦ₛ bs3) =
      PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 ek3)) := by
    rw [← hbs3_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha22560 : sp + 12288#64 + 544#64 + 9728#64 = sp + 22560#64 := by clear * -; bv_omega
  rw [hp2560]
  wp_steps 7
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 22560#64, sp + 2560#64, bs3)
  rw [hp22560]
  have h512 : ((sp + 2560#64) ↦ₛ bs3) ⊢ memRegion (sp + 2560#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 2560#64) bs3; rwa [hbs3] at h
  have hP_pre : PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 ek3)) ∗
      ((sp + 2560#64) ↦ₛ bs3) ∗
      (Vec128At (pkA + 1536#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (pkA + 1552#64) (rhoW rho 3 ++ rhoW rho 2) ∗ Rest) ⊢
      Vec128At (pkA + 1536#64) (rhoW rho 1 ++ rhoW rho 0) ∗
        Vec128At (pkA + 1552#64) (rhoW rho 3 ++ rhoW rho 2) ∗
        PolyMem (sp + 22560#64) (polyVecNat (tHatModPoly16 ek3)) ∗
        memRegion (sp + 2560#64) 512 ∗ Rest := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) ?_; sep_frame
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  have hx20_sf2 : sf.readReg64 .x20 = pkA := by simp [*]
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, hx20_sf2])
    (SepLoad128.left (SepLoad128.vec128At rfl)) (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, hx20_sf2])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_steps 9
  have hor9 : ((sp + 28848#64) ||| 11#64) = sp + 28859#64 := by
    have h0 := sp_add_28848_or_11 hsp_chk; rwa [BitVec.add_assoc] at h0
  have hor23 : ((sp + 26768#64) ||| 11#64) = sp + 26779#64 := by
    have h0 := sp_add_26768_or_11 hsp_chk; rwa [BitVec.add_assoc] at h0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp [hor9],
      by simp [*], by simp [hx20_sf2], by simp [*],
      by simp [hor23],
      by simp [*], by simp [*], by simp [*],
      by simp, by simp, by simp, Entails.refl _⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b2
