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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.Decode12
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `kyber_encapsulate` (`B07`) — Segment 1b Part 1 (`+0x02c0 .. +0x04f8`)

Steps `cst16.3` `.rodata` load, scratch-buffer clears, modular NEON `deserialize_12` Loops `0` and
`1` (`tHat[0]`, `tHat[1]`), and `B28` (`memcpy`) copies to `[sp + 21024 .. sp + 22048)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  fetch_rebase_ldst128Lo12_site
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (
  MlKemRoOk
  cst16_3_vec
  mlkemData05Bytes_length
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse
  step_ldrQ128_ro
  step_strQ128_region
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem
  SepLoad128
  SepStore128
  Vec128At
  polyVecNat
  step_ldrQ128
  step_stpQ128
  step_strQ128
  vecRangeBytes
  vecRangeBytes_length
  vecRangeMem_congr
  vecRangeMem_entails_memRegion
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
  step_deser12_simd12_gen
  step_ld1S2_load
  step_ldrD64_raw
  tHatModPoly16
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x02c0 → 0x04f4]
gen_placed_odd_sites blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x0350 → 0x0354]

@[simp, arm64_norm]
private theorem blkPC07_rebase_ldst128_cst16_3 [MlKemPlacement] (b : BitVec 64)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (blkPC07.rebase b X).fetch (b + BitVec.ofNat 64 852) =
      some (.ldrSimd .Q128 (BitVec.ofNat 5 6)
        (.Offset (.gpr (BitVec.ofNat 5 9))
          (lo12Of (blkPl07.ρ "libcrux_ml_kem:.rodata.cst16.3")))) :=
  fetch_rebase_ldst128Lo12_site
    (lib := blkLib07) (prog := blkPC07) (pl := blkPl07)
    (b := b) (X := X) (off := 852)
    (r := { off := 852, kind := .ldst128Lo12, sym := "libcrux_ml_kem:.rodata.cst16.3" })
    rfl blkPlaceable07 (by decide +kernel) rfl
    (ProofLib.GenPlacedFetches.hookAtOff?_rebase_program (by decide +kernel) 852)
    (ProofLib.GenPlacedFetches.wordAt_of_getQuad? (j := 213) blk07_code_eq blk07_tree_size rfl)
    rfl rfl rfl rfl
    (ProofLib.GenPlacedFetches.target_of_extern_zero rfl (by decide +kernel) rfl)
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

theorem blk28_memcpy_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk28_memcpy_ok

@[simp, arm64_norm, wp_norm]
theorem trunc16_3329 : (3329#64 : BitVec 64).truncate 16 = 3329#16 := rfl

theorem mask_0x0fff_eq_dup : (0x0fff0fff0fff0fff0fff0fff0fff0fff#128) = dup8x16 0x0fff#16 := rfl
theorem mask_0xf2ff_eq_dup : (0xf2fff2fff2fff2fff2fff2fff2fff2ff#128) = dup8x16 0xf2ff#16 := rfl
theorem mask_3329_eq_dup : (0x0d010d010d010d010d010d010d010d01#128) = dup8x16 3329#16 := rfl

attribute [local irreducible]
  blkPC07 dup8x16 polyVecNat tHatModPoly16
  loadVec12 neonDeserialize12Mod8h
  simdTbl16b simdUshl8h simdCmhs8h simdAdd8h

attribute [local wp_norm ↓ high]
  applySimdResult_ok evalSimdModImmExt_mvni_4s_3_msl16 evalSimdModImmExt_bic_8h_0xf0_lsl8
  evalSimdModImmExt_bic_8h_13_lsl8 exec_simdMovi_2d_0 exec_simdDup_8h trunc16_3329
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdCmhs_8h_svc exec_simdAdd_8h_svc

theorem update2_prefix {f g : Nat → BitVec 128} {k : Nat}
    (hf : ∀ j, j < 2 * k → f j = g j) :
    ∀ j, j < 2 * (k + 1) →
      Function.update (Function.update f (2 * k) (g (2 * k))) (2 * k + 1) (g (2 * k + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * k + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * k
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

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

local macro "step_dead_zero30 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
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
  step_dead_strQ512 3 $hrunId $hspId $hchkId; step_dead_strQ512 2 $hrunId $hspId $hchkId))

local macro "step_dead_zero32 " hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  step_dead_zero30 $hrunId $hspId $hchkId;
  step_dead_strQ512 1 $hrunId $hspId $hchkId;
  step_dead_strQ512 0 $hrunId $hspId $hchkId))

/-! ## 1. Modular `deserialize_12` Loop Macro -/

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

/-! ## 2. Init + Zero 0 (`+0x02c0 → +0x0364`) -/

private theorem seg1b_init_pre_ro [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x02c0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = pkA) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0354#64) s
      (memRegion (sp + 2560#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = pageOf (mlkemMpl.ρ "libcrux_ml_kem:.rodata.cst16.3") ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        (Pf ⊢ memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  subst hbase
  wp_steps 5
  step_dead_zero30 hrun hsp hsp_chk
  simp only [BitVec.add_assoc]
  wp_step
  wp_step
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp, by simp, by simp [hx20], by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp, Entails.refl _⟩

theorem seg1b_init_zero0 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x02c0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = pkA) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0364#64) s
      (memRegion (sp + 2560#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = pkA ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = pkA ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = dup8x16 3329#16 ∧
        sf.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  refine sepWP_seq_env hcl hro (seg1b_init_pre_ro hb hbase s sp pkA Rest hpc hrun hsp hsp_chk hx20) ?_
  rintro s1 P1 hpc1 hrun1 _hcl1 hro1
    ⟨hsp1, _hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx26_1, hfp1,
      hv0_1, hv1_1, hP1⟩
  subst hbase
  refine SepWP.weaken_pre hP1 ?_
  refine step_ldrQ128_ro (wb := none) hpc1 hrun1 (by wp_norm_lhs)
    rfl (by simp [evalAddrMode, hx9_1, pageOf_add_lo12Of])
    hro1.cst16_3 mlkemData05Bytes_length cst16_3_vec (by wp_norm_lhs) ?_
  wp_step
  step_dead_strQ512 1 hrun1 hsp1 hsp_chk
  step_dead_strQ512 0 hrun1 hsp1 hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun1])
    ⟨by simp [hsp1], by simp [State.spAligned, hsp1, hsp_chk],
      by simp [hx8_1], by simp, by simp [hx19_1], by simp [hx20_1],
      by simp [hx21_1], by simp [hx22_1], by simp [hx23_1], by simp [hx24_1],
      by simp [hx26_1], by simp [hfp1], by simp [hv0_1], by simp [hv1_1],
      by simp, Entails.refl _⟩

/-! ## 3. Loop 0 + Copy 0 + Zero 1 + Loop 1 + Copy 1 (`+0x0364 → +0x04f8`) -/

theorem seg1b_loop0 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0364#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x23 = dst →
      s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 0#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x03c4#64) s
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
  prove_deser12_mod_loop b src dst bs hbs 0x0364 Reg.x10 Reg.x11 1#5 0#5 Reg.x9

theorem seg1b_copy0_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp pkA : BitVec 64) (v2416 : BitVec 128) (ek0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x03c4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hx19 : s.readReg64 .x19 = pkA + 384#64)
    (hx26 : s.readReg64 .x26 = sp + 12832#64)
    (hv6 : s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x0478#64) s
      (Vec128At (sp + 2416#64) v2416 ∗ memRegion (sp + 21024#64) 512 ∗
        PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek0)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = pkA + 384#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = pkA + 768#64 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = sp + 2560#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = dup8x16 3329#16 ∧
        sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        (Pf ⊢ Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 ek0)) ∗
          memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs0_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek0)) = bs0
  have hbs0 : bs0.length = 512 := by rw [← hbs0_def, vecRangeBytes_length]
  have hp2560 : PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek0)) = ((sp + 2560#64) ↦ₛ bs0) := by
    rw [← hbs0_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp21024 : ((sp + 21024#64) ↦ₛ bs0) =
      PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 ek0)) := by
    rw [← hbs0_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha21024 : sp + 12832#64 + 8192#64 = sp + 21024#64 := by clear * -; bv_omega
  have ha768 : pkA + 384#64 + 384#64 = pkA + 768#64 := by clear * -; bv_omega
  rw [hp2560]
  refine MultiPlacedLib.seq_codeLoaded (mid := blkPl07.base + 984#64) _hcl ?_
  wp_steps 4
  refine step_strQ128 (wb := none) (val := 0x0b0a0a09080707060504040302010100#128)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by simp [hv6])
    (SepStore128.left (SepStore128.vec128At rfl)) (by wp_norm_lhs) ?_
  intro m'
  apply SepWP.done (by wp_norm_lhs) (by simp [hrun])
  intro _hcl2
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 21024#64, sp + 2560#64, bs0)
  rw [hp21024]
  have h512 : ((sp + 2560#64) ↦ₛ bs0) ⊢ memRegion (sp + 2560#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 2560#64) bs0; rwa [hbs0] at h
  have hP_pre : PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 ek0)) ∗
      ((sp + 2560#64) ↦ₛ bs0) ∗
      (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗ Rest) ⊢
      memRegion (sp + 2560#64) 512 ∗
        (Vec128At (sp + 2416#64) 0x0b0a0a09080707060504040302010100#128 ∗
          PolyMem (sp + 21024#64) (polyVecNat (tHatModPoly16 ek0)) ∗ Rest) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) ?_; sep_frame
  refine SepWP.weaken_pre hP_pre ?_
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  wp_steps 4
  refine step_ldrQ128 (wb := none) (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp_sf2, hsp_chk])
    (by simp [evalAddrMode, hsp_sf2])
    (SepLoad128.right (SepLoad128.left (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  wp_steps 2
  step_dead_zero32 hrun_sf hsp_sf2 hsp_chk
  refine SepWP.done (by simp [BitVec.add_assoc]) (by simp [hrun_sf])
    ⟨by simp [hsp_sf2], by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp, by simp, by simp, by sep_frame⟩

theorem seg1b_loop1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0478#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x21 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x26 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 1#5 = dup8x16 3329#16 →
      s.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatModPoly16 bs) j) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x04d8#64) s
        ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf =>
          sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readVReg128 6#5 = 0x0b0a0a09080707060504040302010100#128 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatModPoly16 bs)) ∗ Rest)) := by
  prove_deser12_mod_loop b src dst bs hbs 0x0478 Reg.x9 Reg.x10 0#5 1#5 Reg.x21

theorem seg1b_copy1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (ek1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x04d8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_chk : (sp &&& 15#64 == 0#64) = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + 0x04f8#64) s
      (memRegion (sp + 21536#64) 512 ∗
        PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek1)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = sp + 2560#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 ek1)) ∗
          memRegion (sp + 2560#64) 512 ∗ Rest)) := by
  subst hbase
  generalize hbs1_def : vecRangeBytes 32 (polyVecNat (tHatModPoly16 ek1)) = bs1
  have hbs1 : bs1.length = 512 := by rw [← hbs1_def, vecRangeBytes_length]
  have hp2560 : PolyMem (sp + 2560#64) (polyVecNat (tHatModPoly16 ek1)) = ((sp + 2560#64) ↦ₛ bs1) := by
    rw [← hbs1_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp21536 : ((sp + 21536#64) ↦ₛ bs1) =
      PolyMem (sp + 21536#64) (polyVecNat (tHatModPoly16 ek1)) := by
    rw [← hbs1_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have ha21536 : sp + 12288#64 + 544#64 + 8704#64 = sp + 21536#64 := by clear * -; bv_omega
  rw [hp2560]
  wp_steps 7
  wp_call (blk28_memcpy_07 blkPl07.base) (sp + 21536#64, sp + 2560#64, bs1)
  rw [hp21536]
  have h512 : ((sp + 2560#64) ↦ₛ bs1) ⊢ memRegion (sp + 2560#64) 512 := by
    have h := pointsToBytes_entails_memRegion (sp + 2560#64) bs1; rwa [hbs1] at h
  have hsp_sf2 : sf.sp = sp := hsp_sf.trans hsp
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨hsp_sf2, by simp [State.spAligned, hsp_sf2, hsp_chk],
      by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], by simp [*],
      Entails.trans (sepConj_mono_right (sepConj_mono_left h512)) (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b1
