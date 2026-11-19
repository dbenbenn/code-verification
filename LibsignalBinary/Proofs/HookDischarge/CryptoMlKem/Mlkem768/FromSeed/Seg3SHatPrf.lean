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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow

/-!
# `generate_keypair_compressed` (`B05`): `sHat` PRF, zeta spill, and `cbd2`

1. `sHat_prf_calls` (`+0x3480 → +0x35a4`): saves `sigma` (`32` B) to `[sp + 29440, sp + 29472)`,
   stages `sigma ++ [0/1/2#8]` at `[sp + 29616, sp + 29715)`, and invokes `B01` (`RW2` + `RW1`)
   to compute `prf0..2` at `sp + 29744`, `sp + 29024`, and `sp + 27840`.
2. `sHat_copy_and_zetas` (`+0x35a4 → +0x37c4`): copies `prf0..2` into `[sp + 9984, sp + 10368)`,
   spills 24 `Fwd2` zeta vectors into `SpillSliceMem 40 (sp + 1568#64)`, and initializes `sHat`
   loop registers.
3. `sHat_cbd2_loop` (`+0x37c4 → +0x38f4`): zeroes `[sp + 17376, sp + 17888)` and runs 32 SWAR
   `cbd2` iterations to produce `PolyMem (sp + 17376#64) (polyVecNat (neonCbd2Poly16 prf))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHatPrf

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec keccak2_136_31_RW2Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem Poly32Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn oct8_ofFn_get
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat pointsToBytes_eq_vecRangeMem
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128 vecRangeMem_congr
  vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdDup_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem wordRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SepStore128.spillSlice Spill40 SpillSliceMem SymEnv evalSExpr spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3Sym (seg3SpillConsts)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq
  keccak2SlicesRW_entails_memRegion32 orr_1_of_aligned16 sepWP_elim_byte setMem_setMem
  setPC_setMem_setPC setSpillZetas setWidth32_shr_zext64 shake256List_length stage_prf33_eq
  truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8 vec2_bytesToVecNat_eq
  vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  step_bCond_not_taken step_bCond_taken)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x3480 → 0x38f4]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib05 shake256List dup8x16
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 exec_simdDup_8h

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

@[simp, arm64_norm, wp_norm] abbrev off3480 : BitVec 64 := BitVec.ofNat 64 13440
@[simp, arm64_norm, wp_norm] abbrev off3564 : BitVec 64 := BitVec.ofNat 64 13668
@[simp, arm64_norm, wp_norm] abbrev off3568 : BitVec 64 := BitVec.ofNat 64 13672
@[simp, arm64_norm, wp_norm] abbrev off35a4 : BitVec 64 := BitVec.ofNat 64 13732
@[simp, arm64_norm, wp_norm] abbrev off36b0 : BitVec 64 := BitVec.ofNat 64 14000
@[simp, arm64_norm, wp_norm] abbrev off37c4 : BitVec 64 := BitVec.ofNat 64 14276
@[simp, arm64_norm, wp_norm] abbrev off3854 : BitVec 64 := BitVec.ofNat 64 14420
@[simp, arm64_norm, wp_norm] abbrev off38f0 : BitVec 64 := BitVec.ofNat 64 14576
@[simp, arm64_norm, wp_norm] abbrev off38f4 : BitVec 64 := BitVec.ofNat 64 14580

local syntax "find_load128" : tactic
local macro_rules
  | `(tactic| find_load128) => `(tactic| first
      | (apply SepLoad128.vec128At; with_reducible rfl)
      | (apply SepLoad128.left; find_load128)
      | (apply SepLoad128.right; find_load128))

local syntax "find_store128" : tactic
local macro_rules
  | `(tactic| find_store128) => `(tactic| first
      | (apply SepStore128.vec128At; with_reducible rfl)
      | (apply SepStore128.left; find_store128)
      | (apply SepStore128.right; find_store128))

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
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "step_dead_zero8 " spTerm:term:arg baseOff:num : tactic => `(tactic| (
  apply SepWP.of_memRegion_vecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) (by decide) (by sep_focus)
  intro zf
  rw [show VecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) zf =
        PolyOctMem ($spTerm + BitVec.ofNat 64 $baseOff) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; step_strQ_oct8 5; step_strQ_oct8 4;
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0))

local macro "step_stpQ_fp_oct8 " spTerm:term:arg k1:num k2:num hfpId:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine step_stpQ128 (wb := none)
    (ea := $spTerm + 29744#64 + BitVec.ofNat 64 (16 * $k1))
    (ea16 := $spTerm + 29744#64 + BitVec.ofNat 64 (16 * $k2))
    (v1 := 0#128) (v2 := 0#128)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hfpId:term]; try (clear * -; bv_omega))
    (by clear * -; bv_omega) (by wp_norm_lhs) (by wp_norm_lhs)
    (SepStore128.left (SepStore128.oct8 (k := $k1) (by decide) rfl rfl))
    (SepStore128.left (SepStore128.oct8 (k := $k2) (by decide) rfl (by dsimp only [Oct8.set])))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

/-! ## 1. `sHat` PRF Stage & Calls (`+0x3480 → +0x35a4`) -/

@[simp, arm64_norm, wp_norm] private abbrev off35a0 : BitVec 64 := BitVec.ofNat 64 13728

section
attribute [local irreducible] blkPC05 Vec128At bytesToVecNat

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem sHat_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off3480) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off3564) s
      (((sp + 29408#64) ↦ₛ sigma) ∗
       memRegion (sp + 17376#64) 32 ∗
       memRegion (sp + 27840#64) 128 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29440#64) 32 ∗
       memRegion (sp + 29616#64) 99 ∗
       memRegion (sp + 29744#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = sp + 29984#64 ∧
        sm.readReg64 .x0 = sp + 17376#64 ∧ sm.readReg64 .x1 = sp + 29744#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 29024#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 17376#64 ∧ sm.readReg64 .x21 = 33#64 ∧
        sm.readReg64 .x22 = sp + 29682#64 ∧
        (Pm ⊢ ((sp + 29408#64) ↦ₛ sigma) ∗
          ((sp + 29440#64) ↦ₛ sigma) ∗
          Keccak2SlicesRW (sp + 17376#64) (sp + 29616#64) (sp + 29649#64) 33 33 ∗
          ((sp + 29616#64) ↦ₛ (sigma ++ [0#8])) ∗
          ((sp + 29649#64) ↦ₛ (sigma ++ [1#8])) ∗
          ((sp + 29682#64) ↦ₛ (sigma ++ [2#8])) ∗
          memRegion (sp + 27840#64) 128 ∗
          memRegion (sp + 29024#64) 128 ∗
          memRegion (sp + 29744#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 29408#64) hsig]
  have h32 : memRegion (sp + 29440#64) 32 =
      memRegion (sp + 29440#64) 16 ∗ memRegion (sp + 29456#64) 16 :=
    memRegion_split' (b' := sp + 29456#64) (n := 16) (k := (16 : Nat)) rfl (by bv_omega) (by decide)
  have h99 : memRegion (sp + 29616#64) 99 =
      memRegion (sp + 29616#64) 16 ∗ memRegion (sp + 29632#64) 16 ∗ memRegion (sp + 29648#64) 1 ∗
      memRegion (sp + 29649#64) 16 ∗ memRegion (sp + 29665#64) 16 ∗ memRegion (sp + 29681#64) 1 ∗
      memRegion (sp + 29682#64) 16 ∗ memRegion (sp + 29698#64) 16 ∗ memRegion (sp + 29714#64) 1 := by
    rw [memRegion_split' (b' := sp + 29632#64) (n := 16) (k := (83 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29648#64) (n := 16) (k := (67 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29649#64) (n := 1)  (k := (66 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29665#64) (n := 16) (k := (50 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29681#64) (n := 16) (k := (34 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29682#64) (n := 1)  (k := (33 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29698#64) (n := 16) (k := (17 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 29714#64) (n := 16) (k := (1 : Nat))  rfl (by bv_omega) (by decide)]
  rw [h32, h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29440#64) (by decide) (by sep_focus); intro vs0
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29456#64) (by decide) (by sep_focus); intro vs1
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29616#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29632#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29649#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29665#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29682#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29698#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 29648#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 29681#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 29714#64)); intro c2
  sep_frame_apply (sepWP_elim_region32 (a := sp + 17376#64)); intro k0 k1 k2 k3
  simp only [show sp + 17376#64 + 8#64 = sp + 17384#64 by bv_omega,
    show sp + 17376#64 + 16#64 = sp + 17392#64 by bv_omega,
    show sp + 17376#64 + 24#64 = sp + 17400#64 by bv_omega]
  refine step_ldrQ128 (wb := none) (ea := sp + 29408#64) (v := bytesToVecNat sigma 0)
    hpc hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 3
  refine step_ldrQ128 (wb := none) (ea := (sp + 29408#64) + 16#64) (v := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 29440#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29616#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29649#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29682#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 29665#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 29698#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]
  wp_steps 3
  refine step_strQ128 (wb := none) (ea := sp + 29456#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  try simp only [setMem_setMem]
  refine step_strQ128 (wb := none) (ea := sp + 29632#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  try simp only [setMem_setMem]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 29744#64) (by decide) (by sep_focus)
  intro zf0
  rw [show VecRangeMem 8 (sp + 29744#64) zf0 = PolyOctMem (sp + 29744#64) zf0 from rfl, ← oct8Mem_ofFn]
  step_stpQ_fp_oct8 sp 0 1 hfp hrun
  step_stpQ_fp_oct8 sp 2 3 hfp hrun
  step_stpQ_fp_oct8 sp 4 5 hfp hrun
  step_stpQ_fp_oct8 sp 6 7 hfp hrun
  step_dead_zero8 sp 29024
  step_dead_zero8 sp 27840
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk, by simp [hfp],
      by simp, by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  rw [← show Vec128At (sp + 29440#64) (bytesToVecNat sigma 0) ∗
          Vec128At (sp + 29456#64) (bytesToVecNat sigma 1) = ((sp + 29440#64) ↦ₛ sigma) by
        simpa [show sp + 29440#64 + 16#64 = sp + 29456#64 by bv_omega] using
          vec2_bytesToVecNat_eq (sp + 29440#64) hsig,
      ← stage_prf33_eq (sp + 29616#64) 0#8 hsig,
      ← stage_prf33_eq (sp + 29649#64) 1#8 hsig,
      ← stage_prf33_eq (sp + 29682#64) 2#8 hsig]
  unfold Keccak2SlicesRW
  simp only [show sp + 29616#64 + 16#64 = sp + 29632#64 by bv_omega,
    show sp + 29616#64 + 32#64 = sp + 29648#64 by bv_omega,
    show sp + 29649#64 + 16#64 = sp + 29665#64 by bv_omega,
    show sp + 29649#64 + 32#64 = sp + 29681#64 by bv_omega,
    show sp + 29682#64 + 16#64 = sp + 29698#64 by bv_omega,
    show sp + 29682#64 + 32#64 = sp + 29714#64 by bv_omega,
    show sp + 17376#64 + 8#64 = sp + 17384#64 by bv_omega,
    show sp + 17376#64 + 16#64 = sp + 17392#64 by bv_omega,
    show sp + 17376#64 + 24#64 = sp + 17400#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 29744#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 29024#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 27840#64) _) (by sep_frame) (by sep_frame)))

private theorem sHat_prf_mid [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hc2_len : (sigma ++ [2#8]).length = 33)
    (hpc : s.pc = b + off3568) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = sp + 29682#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off35a0) s
      (memRegion (sp + 9984#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = sp + 29984#64 ∧
        sm.readReg64 .x0 = sp + 9984#64 ∧ sm.readReg64 .x1 = sp + 27840#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 17376#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 17376#64 ∧ sm.readReg64 .x21 = sp + 9984#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 9984#64) (sp + 29682#64) (sp + 29682#64)
          (sigma ++ [2#8]).length (sigma ++ [2#8]).length ∗ Rest)) := by
  subst hbase
  sep_frame_apply (sepWP_elim_region32 (a := sp + 9984#64))
  intro d0 d1 d2 d3
  simp only [show sp + 9984#64 + 8#64 = sp + 9992#64 by bv_omega,
    show sp + 9984#64 + 16#64 = sp + 10000#64 by bv_omega,
    show sp + 9984#64 + 24#64 = sp + 10008#64 by bv_omega]
  wp_steps 14
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp],
      by simp, by simp, by simp,
      by simp, by simp, by simp [hx19], by simp [hx20],
      by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hc2_len,
    show sp + 9984#64 + 8#64 = sp + 9992#64 by bv_omega,
    show sp + 9984#64 + 16#64 = sp + 10000#64 by bv_omega,
    show sp + 9984#64 + 24#64 = sp + 10008#64 by bv_omega]
  sep_frame

end

set_option maxHeartbeats 800000 in
theorem sHat_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off3480) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off35a4) s
      (((sp + 29408#64) ↦ₛ sigma) ∗
       memRegion (sp + 9984#64) 32 ∗
       memRegion (sp + 17376#64) 128 ∗
       memRegion (sp + 27840#64) 128 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29440#64) 32 ∗
       memRegion (sp + 29616#64) 99 ∗
       memRegion (sp + 29744#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 17376#64 ∧
        sf.readReg64 .x21 = sp + 9984#64 ∧
        (Pf ⊢ ((sp + 29408#64) ↦ₛ sigma) ∗
          ((sp + 29440#64) ↦ₛ sigma) ∗
          memRegion (sp + 9984#64) 32 ∗
          memRegion (sp + 17376#64) 128 ∗
          ((sp + 27840#64) ↦ₛ shake256List 128 (sigma ++ [2#8])) ∗
          ((sp + 29024#64) ↦ₛ shake256List 128 (sigma ++ [1#8])) ∗
          memRegion (sp + 29616#64) 99 ∗
          ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 17376#64) (b' := sp + 17408#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 29408#64) ↦ₛ sigma) ∗
      memRegion (sp + 17376#64) 32 ∗ memRegion (sp + 27840#64) 128 ∗
      memRegion (sp + 29024#64) 128 ∗ memRegion (sp + 29440#64) 32 ∗
      memRegion (sp + 29616#64) 99 ∗ memRegion (sp + 29744#64) 128 ∗
      (memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 17408#64) 96 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (sHat_prf_stage hb rfl s sp sigma _ hsig hpc hrun hsp hspA hfp) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc0_len : (sigma ++ [0#8]).length = 33 := by simp [hsig]
  have hc1_len : (sigma ++ [1#8]).length = 33 := by simp [hsig]
  have hc2_len : (sigma ++ [2#8]).length = 33 := by simp [hsig]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC05.rebase blkPl05.base (fun _ => none))
      (blkPl05.base + off3568) s1
      (((sp + 29408#64) ↦ₛ sigma) ∗ ((sp + 29440#64) ↦ₛ sigma) ∗
        Keccak2SlicesRW (sp + 17376#64) (sp + 29616#64) (sp + 29649#64) 33 33 ∗
        ((sp + 29616#64) ↦ₛ (sigma ++ [0#8])) ∗
        ((sp + 29649#64) ↦ₛ (sigma ++ [1#8])) ∗
        ((sp + 29682#64) ↦ₛ (sigma ++ [2#8])) ∗
        memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 29024#64) 128 ∗
        memRegion (sp + 29744#64) 128 ∗
        (memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 17408#64) 96 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧ s2.readReg64 .fp = sp + 29984#64 ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 17376#64 ∧
        s2.readReg64 .x21 = 33#64 ∧ s2.readReg64 .x22 = sp + 29682#64 ∧
        (P2 ⊢ ((sp + 29408#64) ↦ₛ sigma) ∗ ((sp + 29440#64) ↦ₛ sigma) ∗
          memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 17376#64) 128 ∗
          memRegion (sp + 27840#64) 128 ∗
          ((sp + 29024#64) ↦ₛ shake256List 128 (sigma ++ [1#8])) ∗
          ((sp + 29616#64) ↦ₛ (sigma ++ [0#8])) ∗
          ((sp + 29649#64) ↦ₛ (sigma ++ [1#8])) ∗
          ((sp + 29682#64) ↦ₛ (sigma ++ [2#8])) ∗
          ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    have hsl_rw2 : Keccak2SlicesRW (sp + 17376#64) (sp + 29616#64) (sp + 29649#64) 33 33 =
        Keccak2SlicesRW (sp + 17376#64) (sp + 29616#64) (sp + 29649#64)
          (sigma ++ [0#8]).length (sigma ++ [1#8]).length := by rw [hc0_len, hc1_len]
    rw [hsl_rw2]
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk01_keccak2_136_31_RW2_ok
      (⟨sp + 17376#64, sp + 29616#64, sp + 29649#64, sp + 29744#64, sp + 29024#64,
        (128 : Nat), sigma ++ [0#8], sigma ++ [1#8]⟩ : Keccak2ShakeArgs)
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› hfp1, Eq.trans ‹_› hx19_1, Eq.trans ‹_› hx20_1,
        Eq.trans ‹_› hx21_1, Eq.trans ‹_› hx22_1, ?_⟩
    rw [hsp1]
    have hk17376 : Keccak2SlicesRW (sp + 17376#64) (sp + 29616#64) (sp + 29649#64)
          (sigma ++ [0#8]).length (sigma ++ [1#8]).length ∗
        memRegion (sp + 17408#64) 96 ⊢ memRegion (sp + 17376#64) 128 := by
      rw [memRegion_split' (b := sp + 17376#64) (b' := sp + 17408#64) (n := 32) (k := (96 : Nat))
            rfl (by bv_omega) (by decide)]
      exact sepConj_mono (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (Entails.refl _)
    exact entails_sub hk17376 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hP2⟩
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 9984#64) 32 ∗
      (((sp + 29408#64) ↦ₛ sigma) ∗ ((sp + 29440#64) ↦ₛ sigma) ∗
        memRegion (sp + 17376#64) 128 ∗ memRegion (sp + 27840#64) 128 ∗
        ((sp + 29024#64) ↦ₛ shake256List 128 (sigma ++ [1#8])) ∗
        ((sp + 29616#64) ↦ₛ (sigma ++ [0#8])) ∗ ((sp + 29649#64) ↦ₛ (sigma ++ [1#8])) ∗
        ((sp + 29682#64) ↦ₛ (sigma ++ [2#8])) ∗
        ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [0#8])) ∗ stackAt sp 1136 ∗ Rest))
    (Entails.trans hP2 (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (sHat_prf_mid hb rfl s2 sp sigma _ hc2_len hpc2 hrun2 hsp2 hspA2 hfp2 hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk01_keccak2_136_31_RW1_ok
    (sp + 9984#64, sp + 29682#64, sp + 27840#64, sp + 17376#64, (128 : Nat), sigma ++ [2#8])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› hfp3, Eq.trans ‹_› hx19_3, Eq.trans ‹_› hx20_3,
      Eq.trans ‹_› hx21_3, ?_⟩
  rw [hsp3]
  have hm17376 : ((sp + 17376#64) ↦ₛ shake256List 128 (sigma ++ [2#8])) ⊢
      memRegion (sp + 17376#64) 128 := by
    simpa [shake256List_length 128 (sigma ++ [2#8])] using
      pointsToBytes_entails_memRegion (sp + 17376#64) (shake256List 128 (sigma ++ [2#8]))
  have hm99 : ((sp + 29616#64) ↦ₛ (sigma ++ [0#8])) ∗
      ((sp + 29649#64) ↦ₛ (sigma ++ [1#8])) ∗
      ((sp + 29682#64) ↦ₛ (sigma ++ [2#8])) ⊢ memRegion (sp + 29616#64) 99 := by
    rw [memRegion_split' (b := sp + 29616#64) (b' := sp + 29649#64) (n := 33) (k := (66 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29649#64) (b' := sp + 29682#64) (n := 33) (k := (33 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by rw [← hc0_len]; exact pointsToBytes_entails_memRegion (sp + 29616#64) (sigma ++ [0#8]))
      (sepConj_mono
        (by rw [← hc1_len]; exact pointsToBytes_entails_memRegion (sp + 29649#64) (sigma ++ [1#8]))
        (by rw [← hc2_len]; exact pointsToBytes_entails_memRegion (sp + 29682#64) (sigma ++ [2#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm17376 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))

/-! ## 2. Copy `prf0..2` & Spill 24 `Fwd2` Zeta Vectors (`+0x35a4 → +0x37c4`) -/

section
attribute [local irreducible] blkPC05 Vec128At

local macro "ldp_p0 " k1:num k2:num hrunId:term:arg hfpId:term:arg : tactic => `(tactic| (
  refine step_ldpQ128 (wb := none)
    (ea := _ + 29744#64 + BitVec.ofNat 64 (16 * $k1))
    (ea16 := _ + 29744#64 + BitVec.ofNat 64 (16 * $k2))
    (v1 := Oct8.get _ $k1) (v2 := Oct8.get _ $k2)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hfpId:term]; try (clear * -; bv_omega))
    (by clear * -; bv_omega)
    (SepLoad128.left (SepLoad128.oct8 (k := $k1) (by decide) rfl rfl))
    (SepLoad128.left (SepLoad128.oct8 (k := $k2) (by decide) rfl rfl))
    (by wp_norm_lhs) ?_))

local macro "ldr_p1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 29024#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 27840#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "str_d0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 9984#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 10112#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 10240#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_sp " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1568#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.spillSlice (n := 40) (k := $k) (by decide) (by decide) rfl (by dsimp only [Spill40.set])))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private def midSpillZetas (t : Spill40) : Spill40 :=
  { t with
    s19 := dup8x16 0x0313#16, s20 := dup8x16 0xfa13#16,
    s22 := dup8x16 0xfe99#16, s23 := dup8x16 0xf9c0#16 }

private def midD1 (p1 d1 : Oct8) : Oct8 :=
  ⟨p1.o0, d1.o1, p1.o2, d1.o3, p1.o4, p1.o5, p1.o6, p1.o7⟩

private def midD2 (p2 d2 : Oct8) : Oct8 :=
  ⟨d2.o0, p2.o1, p2.o2, d2.o3, d2.o4, d2.o5, d2.o6, d2.o7⟩

private theorem aligned16_add9984 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 9984#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 9984#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
private theorem sHat_copy_zetas_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d0 d1 d2 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off35a4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off36b0) s
      (Oct8Mem (sp + 29744#64) p0 ∗ Oct8Mem (sp + 29024#64) p1 ∗ Oct8Mem (sp + 27840#64) p2 ∗
       Oct8Mem (sp + 9984#64) d0 ∗ Oct8Mem (sp + 10112#64) d1 ∗ Oct8Mem (sp + 10240#64) d2 ∗
       SpillSliceMem 40 (sp + 1568#64) t ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = sp + 29984#64 ∧
        sm.readReg64 .x0 = 0xc0dd#64 ∧ sm.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sm.readReg64 .x2 = 0xf301#64 ∧ sm.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sm.readReg64 .x6 = 0#64 ∧ sm.readReg64 .x8 = 0x34d5#64 ∧
        sm.readReg64 .x9 = 6224#64 ∧ sm.readReg64 .x10 = sp + 2208#64 ∧
        sm.readReg64 .x11 = sp + 8432#64 ∧ sm.readReg64 .x12 = 0x058e#64 ∧
        sm.readReg64 .x13 = 0xfb4e#64 ∧ sm.readReg64 .x14 = 0x47fa#64 ∧
        sm.readReg64 .x15 = 0x019b#64 ∧ sm.readReg64 .x16 = 0x229b#64 ∧
        sm.readReg64 .x17 = 0x6833#64 ∧ sm.readReg64 .x18 = 0xf9dd#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧ sm.readReg64 .x20 = sp + 17376#64 ∧
        sm.readReg64 .x21 = sp + 9985#64 ∧
        sm.readVReg128 0#5 = p2.o6 ∧ sm.readVReg128 1#5 = p1.o1 ∧
        sm.readVReg128 2#5 = dup8x16 0x3999#16 ∧ sm.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        sm.readVReg128 4#5 = dup8x16 0x05d5#16 ∧
        Pm = (Oct8Mem (sp + 29744#64) p0 ∗ Oct8Mem (sp + 29024#64) p1 ∗ Oct8Mem (sp + 27840#64) p2 ∗
          Oct8Mem (sp + 9984#64) p0 ∗ Oct8Mem (sp + 10112#64) (midD1 p1 d1) ∗
          Oct8Mem (sp + 10240#64) (midD2 p2 d2) ∗
          SpillSliceMem 40 (sp + 1568#64) (midSpillZetas t) ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldp_p0 4 5 hrun hfp; wp_steps 7; str_d0 4 hrun hsp hsp_chk
  ldp_p0 6 7 hrun hfp; str_d0 5 hrun hsp hsp_chk; wp_steps 2
  str_sp 20 hrun hsp hsp_chk; ldr_p2 1 hrun hsp hsp_chk; wp_step
  str_d0 6 hrun hsp hsp_chk; ldp_p0 0 1 hrun hfp; str_d0 7 hrun hsp hsp_chk
  wp_steps 2; str_d2 1 hrun hsp hsp_chk; wp_steps 2; str_d0 0 hrun hsp hsp_chk
  wp_steps 2; str_d0 1 hrun hsp hsp_chk; ldp_p0 2 3 hrun hfp
  str_sp 23 hrun hsp hsp_chk; wp_steps 6; str_d0 2 hrun hsp hsp_chk
  ldr_p1 4 hrun hsp hsp_chk; str_sp 22 hrun hsp hsp_chk; wp_steps 2
  str_d1 4 hrun hsp hsp_chk; ldr_p1 6 hrun hsp hsp_chk; wp_steps 2
  str_d0 3 hrun hsp hsp_chk; ldr_p1 5 hrun hsp hsp_chk
  str_d1 6 hrun hsp hsp_chk; ldr_p1 0 hrun hsp hsp_chk; wp_steps 2
  str_d1 5 hrun hsp hsp_chk; ldr_p1 7 hrun hsp hsp_chk
  str_d1 0 hrun hsp hsp_chk; ldr_p1 2 hrun hsp hsp_chk; wp_step
  str_sp 19 hrun hsp hsp_chk; wp_steps 2; str_d1 2 hrun hsp hsp_chk
  ldr_p2 2 hrun hsp hsp_chk; wp_steps 2; str_d1 7 hrun hsp hsp_chk
  ldr_p1 1 hrun hsp hsp_chk; str_d2 2 hrun hsp hsp_chk; ldr_p2 6 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk, by simp [hfp],
      by simp, by simp [ro00Sym],
      by simp, by simp [ro00Sym],
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp [hx19], by simp [hx20],
      by simp [orr_1_of_aligned16 _ (aligned16_add9984 sp hsp_chk)],
      by simp [Oct8.get], by simp [Oct8.get], by simp, by simp, by simp,
      by cases p0; simp [Oct8.get, midD1, midD2, midSpillZetas]⟩

private theorem setSpillZetas_slot (t : Spill40) (env : SymEnv) (i : Nat) (hi : i < 24) :
    (setSpillZetas t).get i = evalSExpr env (seg3SpillConsts.get i) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | rfl | omega

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
private theorem sHat_copy_zetas_b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d1 d2 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off36b0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx0 : s.readReg64 .x0 = 0xc0dd#64) (hx1 : s.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx2 : s.readReg64 .x2 = 0xf301#64) (hx3 : s.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx6 : s.readReg64 .x6 = 0#64) (hx8 : s.readReg64 .x8 = 0x34d5#64)
    (hx9 : s.readReg64 .x9 = 6224#64) (hx10 : s.readReg64 .x10 = sp + 2208#64)
    (hx11 : s.readReg64 .x11 = sp + 8432#64) (hx12 : s.readReg64 .x12 = 0x058e#64)
    (hx13 : s.readReg64 .x13 = 0xfb4e#64) (hx14 : s.readReg64 .x14 = 0x47fa#64)
    (hx15 : s.readReg64 .x15 = 0x019b#64) (hx16 : s.readReg64 .x16 = 0x229b#64)
    (hx17 : s.readReg64 .x17 = 0x6833#64) (hx18 : s.readReg64 .x18 = 0xf9dd#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = sp + 9985#64)
    (hv0 : s.readVReg128 0#5 = p2.o6) (hv1 : s.readVReg128 1#5 = p1.o1)
    (hv2 : s.readVReg128 2#5 = dup8x16 0x3999#16) (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hv4 : s.readVReg128 4#5 = dup8x16 0x05d5#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off37c4) s
      (Oct8Mem (sp + 29744#64) p0 ∗ Oct8Mem (sp + 29024#64) p1 ∗ Oct8Mem (sp + 27840#64) p2 ∗
       Oct8Mem (sp + 9984#64) p0 ∗ Oct8Mem (sp + 10112#64) (midD1 p1 d1) ∗
       Oct8Mem (sp + 10240#64) (midD2 p2 d2) ∗
       SpillSliceMem 40 (sp + 1568#64) (midSpillZetas t) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x0 = 0xc0dd#64 ∧ sf.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x2 = 0xf301#64 ∧ sf.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x4 = 0x4ebf#64 ∧ sf.readReg64 .x6 = 0#64 ∧
        sf.readReg64 .x9 = 6224#64 ∧ sf.readReg64 .x10 = sp + 2208#64 ∧
        sf.readReg64 .x11 = sp + 8432#64 ∧ sf.readReg64 .x13 = 0xf9fa#64 ∧
        sf.readReg64 .x14 = 0x47fa#64 ∧ sf.readReg64 .x15 = 0x019b#64 ∧
        sf.readReg64 .x16 = 0x229b#64 ∧ sf.readReg64 .x17 = 0x6833#64 ∧
        sf.readReg64 .x18 = 0xf9dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 17376#64 ∧ sf.readReg64 .x21 = sp + 9985#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        Pf = (Oct8Mem (sp + 29744#64) p0 ∗ Oct8Mem (sp + 29024#64) p1 ∗ Oct8Mem (sp + 27840#64) p2 ∗
          Oct8Mem (sp + 9984#64) p0 ∗ Oct8Mem (sp + 10112#64) p1 ∗ Oct8Mem (sp + 10240#64) p2 ∗
          SpillSliceMem 40 (sp + 1568#64) (setSpillZetas t) ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_step; str_d1 1 hrun hsp hsp_chk; ldr_p1 3 hrun hsp hsp_chk
  str_d2 6 hrun hsp hsp_chk; wp_steps 2; str_sp 21 hrun hsp hsp_chk
  ldr_p2 3 hrun hsp hsp_chk; str_d1 3 hrun hsp hsp_chk; ldr_p2 0 hrun hsp hsp_chk
  str_sp 17 hrun hsp hsp_chk; wp_steps 2; str_d2 3 hrun hsp hsp_chk
  ldr_p2 7 hrun hsp hsp_chk; str_sp 18 hrun hsp hsp_chk; ldr_p2 5 hrun hsp hsp_chk
  str_sp 16 hrun hsp hsp_chk; wp_steps 2; str_d2 0 hrun hsp hsp_chk
  ldr_p2 4 hrun hsp hsp_chk; str_d2 7 hrun hsp hsp_chk; str_sp 15 hrun hsp hsp_chk
  wp_steps 2; str_d2 5 hrun hsp hsp_chk; str_d2 4 hrun hsp hsp_chk
  str_sp 14 hrun hsp hsp_chk; wp_steps 2; str_sp 13 hrun hsp hsp_chk
  wp_steps 2; str_sp 12 hrun hsp hsp_chk; wp_steps 2; str_sp 11 hrun hsp hsp_chk
  wp_steps 2; str_sp 10 hrun hsp hsp_chk; wp_steps 2; str_sp 9 hrun hsp hsp_chk
  wp_steps 2; str_sp 8 hrun hsp hsp_chk; wp_steps 2; str_sp 7 hrun hsp hsp_chk
  wp_steps 2; str_sp 6 hrun hsp hsp_chk; wp_steps 2; str_sp 5 hrun hsp hsp_chk
  wp_steps 2; str_sp 4 hrun hsp hsp_chk; wp_steps 2; str_sp 3 hrun hsp hsp_chk
  wp_step; str_sp 2 hrun hsp hsp_chk; wp_step; str_sp 1 hrun hsp hsp_chk
  wp_steps 2; str_sp 0 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk, by simp [hfp],
      by simp [hx0], by simp [hx1], by simp [hx2], by simp [hx3],
      by simp, by simp [hx6], by simp [hx9], by simp [hx10],
      by simp [hx11], by simp, by simp [hx14], by simp [hx15],
      by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx19],
      by simp [hx20], by simp [hx21], by simp [hv3],
      by cases p1; cases p2; cases t
         simp [Oct8.get, midD1, midD2, midSpillZetas, setSpillZetas]⟩

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

private theorem spillSliceMem40_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    SpillSliceMem 40 ptr (Spill40.ofFn f) = VecRangeMem 40 ptr f :=
  vecRangeMem_congr fun i hi => spill40_ofFn_get f i hi

theorem sHat_copy_and_zetas [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (prf0 prf1 prf2 : List (BitVec 8)) (Rest : SepProp)
    (h0 : prf0.length = 128) (h1 : prf1.length = 128) (h2 : prf2.length = 128)
    (hpc : s.pc = b + off35a4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off37c4) s
      (((sp + 29744#64) ↦ₛ prf0) ∗ ((sp + 29024#64) ↦ₛ prf1) ∗ ((sp + 27840#64) ↦ₛ prf2) ∗
       memRegion (sp + 9984#64) 384 ∗ memRegion (sp + 1568#64) 640 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x0 = 0xc0dd#64 ∧ sf.readReg64 .x1 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sf.readReg64 .x2 = 0xf301#64 ∧ sf.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        sf.readReg64 .x4 = 0x4ebf#64 ∧ sf.readReg64 .x6 = 0#64 ∧
        sf.readReg64 .x9 = 6224#64 ∧ sf.readReg64 .x10 = sp + 2208#64 ∧
        sf.readReg64 .x11 = sp + 8432#64 ∧ sf.readReg64 .x13 = 0xf9fa#64 ∧
        sf.readReg64 .x14 = 0x47fa#64 ∧ sf.readReg64 .x15 = 0x019b#64 ∧
        sf.readReg64 .x16 = 0x229b#64 ∧ sf.readReg64 .x17 = 0x6833#64 ∧
        sf.readReg64 .x18 = 0xf9dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 17376#64 ∧ sf.readReg64 .x21 = sp + 9985#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        ∃ t : Spill40, (∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 9984#64) ↦ₛ prf0) ∗ ((sp + 10112#64) ↦ₛ prf1) ∗ ((sp + 10240#64) ↦ₛ prf2) ∗
            SpillSliceMem 40 (sp + 1568#64) t ∗
            memRegion (sp + 27840#64) 128 ∗ memRegion (sp + 29024#64) 128 ∗
            memRegion (sp + 29744#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 29744#64) h0,
      pointsToBytes128_eq_oct8Mem (sp + 29024#64) h1,
      pointsToBytes128_eq_oct8Mem (sp + 27840#64) h2,
      memRegion_split' (b := sp + 9984#64) (b' := sp + 10112#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 10112#64) (b' := sp + 10240#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 9984#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 10112#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 10240#64) (hf := by sep_focus); intro fd2
  apply SepWP.of_memRegion_vecRangeMem 40 (sp + 1568#64) (hf := by sep_focus); intro fsp
  rw [show VecRangeMem 8 (sp + 9984#64) fd0 = Oct8Mem (sp + 9984#64) (Oct8.ofFn fd0) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 10112#64) fd1 = Oct8Mem (sp + 10112#64) (Oct8.ofFn fd1) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 10240#64) fd2 = Oct8Mem (sp + 10240#64) (Oct8.ofFn fd2) from
        (oct8Mem_ofFn _ _).symm,
      ← spillSliceMem40_ofFn (sp + 1568#64) fsp]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 29744#64) (Oct8.ofFn (bytesToVecNat prf0)) ∗
      Oct8Mem (sp + 29024#64) (Oct8.ofFn (bytesToVecNat prf1)) ∗
      Oct8Mem (sp + 27840#64) (Oct8.ofFn (bytesToVecNat prf2)) ∗
      Oct8Mem (sp + 9984#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 10112#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 10240#64) (Oct8.ofFn fd2) ∗
      SpillSliceMem 40 (sp + 1568#64) (Spill40.ofFn fsp) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (sHat_copy_zetas_a hb hbase s sp _ _ _ _ _ _ _ Rest hpc hrun hsp hspA hfp hx19 hx20 hx21)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hfpm, hx0m, hx1m, hx2m, hx3m, hx6m, hx8m, hx9m, hx10m,
      hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hx17m, hx18m, hx19m, hx20m, hx21m,
      hv0m, hv1m, hv2m, hv3m, hv4m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (sHat_copy_zetas_b hb hbase sm sp _ _ _ _ _ _ Rest hpcm hrunm hspm hspAm hfpm
        hx0m hx1m hx2m hx3m hx6m hx8m hx9m hx10m hx11m hx12m hx13m hx14m hx15m hx16m hx17m hx18m
        hx19m hx20m hx21m hv0m hv1m hv2m hv3m hv4m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, rfpf, r0, r1, r2, r3, r4, r6, r9, r10, r11, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, rfpf, r0, r1, r2, r3, r4, r6, r9, r10, r11, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, rv3, setSpillZetas (Spill40.ofFn fsp),
      setSpillZetas_slot (Spill40.ofFn fsp), ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 9984#64) h0,
      ← pointsToBytes128_eq_oct8Mem (sp + 10112#64) h1,
      ← pointsToBytes128_eq_oct8Mem (sp + 10240#64) h2]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 29744#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 29024#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 27840#64) _) (by sep_frame) (by sep_frame)))

/-! ## 3. `sHat` `cbd2` Zeroing & 32-Iter SWAR Loop (`+0x37c4 → +0x38f4`) -/

local macro "step_strQ17376 " k:num : tactic => `(tactic| (
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

private theorem sHat_cbd2_zero [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off37c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off3854) s
      (memRegion (sp + 17376#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧
        s1.readReg64 .x5 = s.readReg64 .x6 + 1#64 ∧ s1.readReg64 .x6 = s.readReg64 .x6 ∧
        s1.readReg64 .x7 = 0#64 ∧ s1.readReg64 .x8 = s.readReg64 .x21 ∧
        s1.readReg64 .x9 = s.readReg64 .x9 ∧ s1.readReg64 .x10 = s.readReg64 .x10 ∧
        s1.readReg64 .x11 = s.readReg64 .x11 ∧ s1.readReg64 .x13 = s.readReg64 .x13 ∧
        s1.readReg64 .x14 = s.readReg64 .x14 ∧ s1.readReg64 .x15 = s.readReg64 .x15 ∧
        s1.readReg64 .x16 = s.readReg64 .x16 ∧ s1.readReg64 .x17 = s.readReg64 .x17 ∧
        s1.readReg64 .x18 = s.readReg64 .x18 ∧ s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 17376#64) 512 ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 17376#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 17376#64) f = PolyMem (sp + 17376#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ17376 31; step_strQ17376 30; step_strQ17376 29; step_strQ17376 28
  step_strQ17376 27; step_strQ17376 26; step_strQ17376 25; step_strQ17376 24
  step_strQ17376 23; step_strQ17376 22; step_strQ17376 21; step_strQ17376 20
  step_strQ17376 19; step_strQ17376 18; step_strQ17376 17; step_strQ17376 16
  step_strQ17376 15; step_strQ17376 14; step_strQ17376 13; step_strQ17376 12
  step_strQ17376 11; step_strQ17376 10; step_strQ17376 9;  step_strQ17376 8
  step_strQ17376 7;  step_strQ17376 6;  step_strQ17376 5;  step_strQ17376 4
  step_strQ17376 3;  step_strQ17376 2;  step_strQ17376 1;  step_strQ17376 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_cbd_strh " cellPtr:ident hx20Id:term:arg hx7Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx20Id:term, $hx7Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem sHat_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off3854) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx7 : s.readReg64 .x7 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if k < 31 then b + off3854 else b + off38f4) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
        s'.readReg64 .x6 = s.readReg64 .x6 ∧
        s'.readReg64 .x7 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = s.readReg64 .x11 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
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
  step_cbd_strh cellPtr hx20 hx7 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx7 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx7 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_step
  step_cbd_strh cellPtr hx20 hx7 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx7 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx7 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx20 hx7 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx20 hx7 6 (cbd2CoeffFromWord w 6)
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
    refine step_bCond_taken (dst := blkPl05.base + off3854)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [off38f0, off3854]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp,
        by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl05.base + off38f4)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [off38f0, off38f4]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp,
        by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp,
        by simp [hx19], by simp [hx20], by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem sHat_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + off3854 else b + off38f4) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x7 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + off38f4) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
          s'.readReg64 .x4 = s.readReg64 .x4 ∧ s'.readReg64 .x5 = s.readReg64 .x5 ∧
          s'.readReg64 .x6 = s.readReg64 .x6 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x11 = s.readReg64 .x11 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
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
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, hx19, hx20, rfl, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx7 hx8 hx19 hx20
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + off3854 else b + off38f4) =
        (if k + 1 < 32 then b + off3854 else b + off38f4) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (sHat_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx7 hx8 hx19 hx20)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hr2, hr3, hr4, hr5, hr6, hx7_1, hx8_1,
        hr9, hr10, hr11, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hx20_1, hr21, hfp1, hv3_1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (ih (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx7_1 hx8_1 hx19_1 hx20_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g6, g9, g10, g11, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g2.trans hr2, g3.trans hr3,
        g4.trans hr4, g5.trans hr5, g6.trans hr6, g9.trans hr9, g10.trans hr10,
        g11.trans hr11, g13.trans hr13, g14.trans hr14, g15.trans hr15, g16.trans hr16,
        g17.trans hr17, g18.trans hr18, gx19, gx20, g21.trans hr21, gfp.trans hfp1,
        gv3.trans hv3_1, hP2⟩

theorem sHat_cbd2_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + off37c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 17376#64)
    (hx21 : s.readReg64 .x21 = prfPtr + 1#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off38f4) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 17376#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = s.readReg64 .x2 ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x4 = s.readReg64 .x4 ∧
        s'.readReg64 .x5 = s.readReg64 .x6 + 1#64 ∧ s'.readReg64 .x6 = s.readReg64 .x6 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = s.readReg64 .x11 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = sp + 17376#64 ∧ s'.readReg64 .x21 = prfPtr + 1#64 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 17376#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 17376#64) 512 ∗ Rest =
      memRegion (sp + 17376#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (sHat_cbd2_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, r2, r3, r4, r5, r6, hx7_1, hx8_1,
      r9, r10, r11, r13, r14, r15, r16, r17, r18, r19, r20, r21, rfp, rv3, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.of_memRegion_vecRangeMem 32 (sp + 17376#64) (by decide) rfl fun f => by
      rw [show VecRangeMem 32 (sp + 17376#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 17376#64) f ∗ Rest by
        rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 17376#64) f), sepConj_assoc]]
      refine SepWP.seq
        (sHat_cbd2_steps hb hbase sp prfPtr (sp + 17376#64) prf Rest 32 0 rfl s1 f
          (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx7_1
          (by simp [hx8_1, hx21]) (r19.trans hx19) (r20.trans hx20)) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g2, g3, g4, g5, g6, g9, g10, g11, g13, g14, g15,
        g16, g17, g18, gx19, gx20, g21, gfp, gv3, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g2.trans r2, g3.trans r3,
        g4.trans r4, g5.trans r5, g6.trans r6, g9.trans r9, g10.trans r10,
        g11.trans r11, g13.trans r13, g14.trans r14, g15.trans r15, g16.trans r16,
        g17.trans r17, g18.trans r18, gx19, gx20, g21.trans (r21.trans hx21), gfp.trans rfp,
        gv3.trans rv3, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3SHatPrf
