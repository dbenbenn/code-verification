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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure

/-!
# `generate_keypair_compressed` (`B05`): `eHat` zeroing, PRF calls, and `cbd2`

1. `eHat_memset` (`+0x48cc → +0x48e8`): calls `B29` `memset` (`1536` B at `sp + 17376`) and sets
   `x23 = sp + 17376`.
2. `eHat_prf_calls` (`+0x48e8 → +0x4a04`): reads `sigma` from `sp + 29440`, stages
   `sigma ++ [3/4/5#8]` at `[sp + 29504, sp + 29603)`, and invokes `B01` (`RW2` + `RW1`) to compute
   `prf3..5` at `sp + 29616`, `sp + 29744`, and `sp + 29024`.
3. `eHat_copy_regs` (`+0x4a04 → +0x4afc`): copies `prf3..5` into `[sp + 27840, sp + 28224)` and
   initializes `eHat` loop registers (`x1, x3, x9..x21, x23, x27, x28, x30`).
4. `eHat_cbd2_loop` (`+0x4afc → +0x4c2c`): zeroes `[sp + 9984, sp + 10496)` and runs 32 SWAR
   `cbd2` iterations to produce `PolyMem (sp + 9984#64) (polyVecNat (neonCbd2Poly16 prf))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3EHatPrf

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_blk29 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec keccak2_136_31_RW2Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat pointsToBytes_eq_vecRangeMem
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg1Prologue (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3CbdPure (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq
  keccak2SlicesRW_entails_memRegion32 orr_1_of_aligned16 sepWP_elim_byte setMem_setMem
  setPC_setMem_setPC setWidth32_shr_zext64 shake256List_length stage_prf33_eq
  truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8 vec2_bytesToVecNat_eq
  vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  ro00Sym step_bCond_not_taken step_bCond_taken)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x48cc → 0x4c2c]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkLib05 shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] abbrev off48cc : BitVec 64 := BitVec.ofNat 64 18636
@[simp, arm64_norm, wp_norm] abbrev off48e8 : BitVec 64 := BitVec.ofNat 64 18664
@[simp, arm64_norm, wp_norm] abbrev off49c4 : BitVec 64 := BitVec.ofNat 64 18884
@[simp, arm64_norm, wp_norm] abbrev off49c8 : BitVec 64 := BitVec.ofNat 64 18888
@[simp, arm64_norm, wp_norm] abbrev off4a00 : BitVec 64 := BitVec.ofNat 64 18944
@[simp, arm64_norm, wp_norm] abbrev off4a04 : BitVec 64 := BitVec.ofNat 64 18948
@[simp, arm64_norm, wp_norm] abbrev off4afc : BitVec 64 := BitVec.ofNat 64 19196
@[simp, arm64_norm, wp_norm] abbrev off4b8c : BitVec 64 := BitVec.ofNat 64 19340
@[simp, arm64_norm, wp_norm] abbrev off4c28 : BitVec 64 := BitVec.ofNat 64 19496
@[simp, arm64_norm, wp_norm] abbrev off4c2c : BitVec 64 := BitVec.ofNat 64 19500

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
    · clear * -; bv_omega
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

/-! ## 1. `eHat` Zeroing & PRF Calls (`+0x48cc → +0x4a04`) -/

set_option maxRecDepth 200000 in
theorem eHat_memset [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off48cc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off48e8) s
      (memRegion (sp + 17376#64) 1536 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x23 = sp + 17376#64 ∧
        (Pf ⊢ memRegion (sp + 17376#64) 1536 ∗ Rest)) := by
  subst hbase
  wp_cut_codeLoaded; wp_steps 6; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 17376#64, 0#8, 1536)
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      Eq.trans ‹_› hfp, Eq.trans ‹_› hx19, Eq.trans ‹_› (by simp), ?_⟩
  have hlen : (List.replicate 1536 0#8).length = 1536 := List.length_replicate
  have hz : ((sp + 17376#64) ↦ₛ List.replicate 1536 0#8) ⊢ memRegion (sp + 17376#64) 1536 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (sp + 17376#64) (List.replicate 1536 0#8)
  exact entails_sub hz (by sep_frame) (by sep_frame)

section
attribute [local irreducible] blkPC05 Vec128At bytesToVecNat

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem eHat_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off48e8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx23 : s.readReg64 .x23 = sp + 17376#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off49c4) s
      (((sp + 29440#64) ↦ₛ sigma) ∗
       memRegion (sp + 9984#64) 32 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29504#64) 99 ∗
       memRegion (sp + 29616#64) 128 ∗
       memRegion (sp + 29744#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = sp + 29984#64 ∧
        sm.readReg64 .x0 = sp + 9984#64 ∧ sm.readReg64 .x1 = sp + 29616#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 29744#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = 33#64 ∧ sm.readReg64 .x21 = sp + 9984#64 ∧
        sm.readReg64 .x22 = sp + 29570#64 ∧ sm.readReg64 .x23 = sp + 17376#64 ∧
        (Pm ⊢ ((sp + 29440#64) ↦ₛ sigma) ∗
          Keccak2SlicesRW (sp + 9984#64) (sp + 29504#64) (sp + 29537#64) 33 33 ∗
          ((sp + 29504#64) ↦ₛ (sigma ++ [3#8])) ∗
          ((sp + 29537#64) ↦ₛ (sigma ++ [4#8])) ∗
          ((sp + 29570#64) ↦ₛ (sigma ++ [5#8])) ∗
          memRegion (sp + 29024#64) 128 ∗
          memRegion (sp + 29616#64) 128 ∗
          memRegion (sp + 29744#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 29440#64) hsig]
  have h99 : memRegion (sp + 29504#64) 99 =
      memRegion (sp + 29504#64) 16 ∗ memRegion (sp + 29520#64) 16 ∗ memRegion (sp + 29536#64) 1 ∗
      memRegion (sp + 29537#64) 16 ∗ memRegion (sp + 29553#64) 16 ∗ memRegion (sp + 29569#64) 1 ∗
      memRegion (sp + 29570#64) 16 ∗ memRegion (sp + 29586#64) 16 ∗ memRegion (sp + 29602#64) 1 := by
    rw [memRegion_split' (b' := sp + 29520#64) (n := 16) (k := (83 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29536#64) (n := 16) (k := (67 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29537#64) (n := 1)  (k := (66 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29553#64) (n := 16) (k := (50 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29569#64) (n := 16) (k := (34 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29570#64) (n := 1)  (k := (33 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29586#64) (n := 16) (k := (17 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 29602#64) (n := 16) (k := (1 : Nat))  rfl (by clear * -; bv_omega) (by decide)]
  rw [h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29504#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29520#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29537#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29553#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29570#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 29586#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 29536#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 29569#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 29602#64)); intro c2
  sep_frame_apply (sepWP_elim_region32 (a := sp + 9984#64)); intro k0 k1 k2 k3
  simp only [show sp + 9984#64 + 8#64 = sp + 9992#64 by clear * -; bv_omega,
    show sp + 9984#64 + 16#64 = sp + 10000#64 by clear * -; bv_omega,
    show sp + 9984#64 + 24#64 = sp + 10008#64 by clear * -; bv_omega]
  wp_step
  refine step_ldrQ128 (wb := none) (ea := sp + 29440#64) (v := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := (sp + 29440#64) + 16#64) (v := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 4
  refine step_strQ128 (wb := none) (ea := sp + 29504#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]; wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29537#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]; wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29570#64) (val := bytesToVecNat sigma 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]; wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 29553#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]; wp_step
  refine step_strQ128 (wb := none) (ea := sp + 29586#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  simp only [setMem_setMem]; wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 29520#64) (val := bytesToVecNat sigma 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  try simp only [setMem_setMem]
  step_dead_zero8 sp 29616
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 29744#64) (by decide) (by sep_focus)
  intro zf0
  rw [show VecRangeMem 8 (sp + 29744#64) zf0 = PolyOctMem (sp + 29744#64) zf0 from rfl, ← oct8Mem_ofFn]
  step_stpQ_fp_oct8 sp 0 1 hfp hrun; step_stpQ_fp_oct8 sp 2 3 hfp hrun
  step_stpQ_fp_oct8 sp 4 5 hfp hrun; step_stpQ_fp_oct8 sp 6 7 hfp hrun
  step_dead_zero8 sp 29024
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk, by simp [hfp],
      by simp, by simp, by simp, by simp, by simp,
      by simp [hx19], by simp, by simp, by simp, by simp [hx23], ?_⟩
  rw [← stage_prf33_eq (sp + 29504#64) 3#8 hsig,
      ← stage_prf33_eq (sp + 29537#64) 4#8 hsig,
      ← stage_prf33_eq (sp + 29570#64) 5#8 hsig]
  unfold Keccak2SlicesRW
  simp only [show sp + 29504#64 + 16#64 = sp + 29520#64 by clear * -; bv_omega,
    show sp + 29504#64 + 32#64 = sp + 29536#64 by clear * -; bv_omega,
    show sp + 29537#64 + 16#64 = sp + 29553#64 by clear * -; bv_omega,
    show sp + 29537#64 + 32#64 = sp + 29569#64 by clear * -; bv_omega,
    show sp + 29570#64 + 16#64 = sp + 29586#64 by clear * -; bv_omega,
    show sp + 29570#64 + 32#64 = sp + 29602#64 by clear * -; bv_omega,
    show sp + 9984#64 + 8#64 = sp + 9992#64 by clear * -; bv_omega,
    show sp + 9984#64 + 16#64 = sp + 10000#64 by clear * -; bv_omega,
    show sp + 9984#64 + 24#64 = sp + 10008#64 by clear * -; bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 29616#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 29744#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 29024#64) _) (by sep_frame) (by sep_frame)))

private theorem eHat_prf_mid [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hc5_len : (sigma ++ [5#8]).length = 33)
    (hpc : s.pc = b + off49c8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = 33#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64)
    (hx22 : s.readReg64 .x22 = sp + 29570#64)
    (hx23 : s.readReg64 .x23 = sp + 17376#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4a00) s
      (memRegion (sp + 27840#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧ sm.readReg64 .fp = sp + 29984#64 ∧
        sm.readReg64 .x0 = sp + 27840#64 ∧ sm.readReg64 .x1 = sp + 29024#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 9984#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 27840#64 ∧ sm.readReg64 .x21 = sp + 9984#64 ∧
        sm.readReg64 .x23 = sp + 17376#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 27840#64) (sp + 29570#64) (sp + 29570#64)
          (sigma ++ [5#8]).length (sigma ++ [5#8]).length ∗ Rest)) := by
  subst hbase
  sep_frame_apply (sepWP_elim_region32 (a := sp + 27840#64))
  intro d0 d1 d2 d3
  simp only [show sp + 27840#64 + 8#64 = sp + 27848#64 by clear * -; bv_omega,
    show sp + 27840#64 + 16#64 = sp + 27856#64 by clear * -; bv_omega,
    show sp + 27840#64 + 24#64 = sp + 27864#64 by clear * -; bv_omega]
  wp_steps 14
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp],
      by simp, by simp, by simp,
      by simp, by simp, by simp [hx19], by simp,
      by simp [hx21], by simp [hx23], ?_⟩
  unfold Keccak2SlicesRW
  simp only [hc5_len,
    show sp + 27840#64 + 8#64 = sp + 27848#64 by clear * -; bv_omega,
    show sp + 27840#64 + 16#64 = sp + 27856#64 by clear * -; bv_omega,
    show sp + 27840#64 + 24#64 = sp + 27864#64 by clear * -; bv_omega]
  sep_frame

end

set_option maxHeartbeats 800000 in
theorem eHat_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (sigma : List (BitVec 8)) (Rest : SepProp)
    (hsig : sigma.length = 32)
    (hpc : s.pc = b + off48e8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx23 : s.readReg64 .x23 = sp + 17376#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4a04) s
      (((sp + 29440#64) ↦ₛ sigma) ∗
       memRegion (sp + 9984#64) 128 ∗
       memRegion (sp + 27840#64) 32 ∗
       memRegion (sp + 29024#64) 128 ∗
       memRegion (sp + 29504#64) 99 ∗
       memRegion (sp + 29616#64) 128 ∗
       memRegion (sp + 29744#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 27840#64 ∧
        sf.readReg64 .x21 = sp + 9984#64 ∧
        sf.readReg64 .x23 = sp + 17376#64 ∧
        (Pf ⊢ ((sp + 29440#64) ↦ₛ sigma) ∗
          memRegion (sp + 9984#64) 128 ∗
          memRegion (sp + 27840#64) 32 ∗
          ((sp + 29024#64) ↦ₛ shake256List 128 (sigma ++ [5#8])) ∗
          memRegion (sp + 29504#64) 99 ∗
          ((sp + 29616#64) ↦ₛ shake256List 128 (sigma ++ [3#8])) ∗
          ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 9984#64) (b' := sp + 10016#64) (n := 32) (k := (96 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 29440#64) ↦ₛ sigma) ∗
      memRegion (sp + 9984#64) 32 ∗ memRegion (sp + 29024#64) 128 ∗
      memRegion (sp + 29504#64) 99 ∗ memRegion (sp + 29616#64) 128 ∗
      memRegion (sp + 29744#64) 128 ∗
      (memRegion (sp + 10016#64) 96 ∗ memRegion (sp + 27840#64) 32 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (eHat_prf_stage hb rfl s sp sigma _ hsig hpc hrun hsp hspA hfp hx19 hx23) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc3_len : (sigma ++ [3#8]).length = 33 := by simp [hsig]
  have hc4_len : (sigma ++ [4#8]).length = 33 := by simp [hsig]
  have hc5_len : (sigma ++ [5#8]).length = 33 := by simp [hsig]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC05.rebase blkPl05.base (fun _ => none))
      (blkPl05.base + off49c8) s1
      (((sp + 29440#64) ↦ₛ sigma) ∗
        Keccak2SlicesRW (sp + 9984#64) (sp + 29504#64) (sp + 29537#64) 33 33 ∗
        ((sp + 29504#64) ↦ₛ (sigma ++ [3#8])) ∗
        ((sp + 29537#64) ↦ₛ (sigma ++ [4#8])) ∗
        ((sp + 29570#64) ↦ₛ (sigma ++ [5#8])) ∗
        memRegion (sp + 29024#64) 128 ∗ memRegion (sp + 29616#64) 128 ∗
        memRegion (sp + 29744#64) 128 ∗
        (memRegion (sp + 10016#64) 96 ∗ memRegion (sp + 27840#64) 32 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧ s2.readReg64 .fp = sp + 29984#64 ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = 33#64 ∧
        s2.readReg64 .x21 = sp + 9984#64 ∧ s2.readReg64 .x22 = sp + 29570#64 ∧
        s2.readReg64 .x23 = sp + 17376#64 ∧
        (P2 ⊢ ((sp + 29440#64) ↦ₛ sigma) ∗
          memRegion (sp + 9984#64) 128 ∗ memRegion (sp + 27840#64) 32 ∗
          memRegion (sp + 29024#64) 128 ∗
          ((sp + 29504#64) ↦ₛ (sigma ++ [3#8])) ∗
          ((sp + 29537#64) ↦ₛ (sigma ++ [4#8])) ∗
          ((sp + 29570#64) ↦ₛ (sigma ++ [5#8])) ∗
          ((sp + 29616#64) ↦ₛ shake256List 128 (sigma ++ [3#8])) ∗
          ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    have hsl_rw2 : Keccak2SlicesRW (sp + 9984#64) (sp + 29504#64) (sp + 29537#64) 33 33 =
        Keccak2SlicesRW (sp + 9984#64) (sp + 29504#64) (sp + 29537#64)
          (sigma ++ [3#8]).length (sigma ++ [4#8]).length := by rw [hc3_len, hc4_len]
    rw [hsl_rw2]
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk01_keccak2_136_31_RW2_ok
      (⟨sp + 9984#64, sp + 29504#64, sp + 29537#64, sp + 29616#64, sp + 29744#64,
        (128 : Nat), sigma ++ [3#8], sigma ++ [4#8]⟩ : Keccak2ShakeArgs)
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› hfp1, Eq.trans ‹_› hx19_1, Eq.trans ‹_› hx20_1,
        Eq.trans ‹_› hx21_1, Eq.trans ‹_› hx22_1, Eq.trans ‹_› hx23_1, ?_⟩
    rw [hsp1]
    have hk9984 : Keccak2SlicesRW (sp + 9984#64) (sp + 29504#64) (sp + 29537#64)
          (sigma ++ [3#8]).length (sigma ++ [4#8]).length ∗
        memRegion (sp + 10016#64) 96 ⊢ memRegion (sp + 9984#64) 128 := by
      rw [memRegion_split' (b := sp + 9984#64) (b' := sp + 10016#64) (n := 32) (k := (96 : Nat))
            rfl (by clear * -; bv_omega) (by decide)]
      exact sepConj_mono (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (Entails.refl _)
    exact entails_sub hk9984 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hP2⟩
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 27840#64) 32 ∗
      (((sp + 29440#64) ↦ₛ sigma) ∗ memRegion (sp + 9984#64) 128 ∗
        memRegion (sp + 29024#64) 128 ∗
        ((sp + 29504#64) ↦ₛ (sigma ++ [3#8])) ∗ ((sp + 29537#64) ↦ₛ (sigma ++ [4#8])) ∗
        ((sp + 29570#64) ↦ₛ (sigma ++ [5#8])) ∗
        ((sp + 29616#64) ↦ₛ shake256List 128 (sigma ++ [3#8])) ∗
        ((sp + 29744#64) ↦ₛ shake256List 128 (sigma ++ [4#8])) ∗ stackAt sp 1136 ∗ Rest))
    (Entails.trans hP2 (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (eHat_prf_mid hb rfl s2 sp sigma _ hc5_len hpc2 hrun2 hsp2 hspA2 hfp2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx23_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk01_keccak2_136_31_RW1_ok
    (sp + 27840#64, sp + 29570#64, sp + 29024#64, sp + 9984#64, (128 : Nat), sigma ++ [5#8])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› hfp3, Eq.trans ‹_› hx19_3, Eq.trans ‹_› hx20_3,
      Eq.trans ‹_› hx21_3, Eq.trans ‹_› hx23_3, ?_⟩
  rw [hsp3]
  have hm9984 : ((sp + 9984#64) ↦ₛ shake256List 128 (sigma ++ [5#8])) ⊢
      memRegion (sp + 9984#64) 128 := by
    simpa [shake256List_length 128 (sigma ++ [5#8])] using
      pointsToBytes_entails_memRegion (sp + 9984#64) (shake256List 128 (sigma ++ [5#8]))
  have hm99 : ((sp + 29504#64) ↦ₛ (sigma ++ [3#8])) ∗
      ((sp + 29537#64) ↦ₛ (sigma ++ [4#8])) ∗
      ((sp + 29570#64) ↦ₛ (sigma ++ [5#8])) ⊢ memRegion (sp + 29504#64) 99 := by
    rw [memRegion_split' (b := sp + 29504#64) (b' := sp + 29537#64) (n := 33) (k := (66 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 29537#64) (b' := sp + 29570#64) (n := 33) (k := (33 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by rw [← hc3_len]; exact pointsToBytes_entails_memRegion (sp + 29504#64) (sigma ++ [3#8]))
      (sepConj_mono
        (by rw [← hc4_len]; exact pointsToBytes_entails_memRegion (sp + 29537#64) (sigma ++ [4#8]))
        (by rw [← hc5_len]; exact pointsToBytes_entails_memRegion (sp + 29570#64) (sigma ++ [5#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm9984 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))

/-! ## 2. Copy `prf3..5` & Initialize `eHat` Loop Registers (`+0x4a04 → +0x4afc`) -/

section
attribute [local irreducible] blkPC05 Vec128At

local macro "ldr_p3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 29616#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))
    (by wp_norm_lhs) ?_))

local macro "ldp_p4 " k1:num k2:num hrunId:term:arg hfpId:term:arg : tactic => `(tactic| (
  refine step_ldpQ128 (wb := none)
    (ea := _ + 29744#64 + BitVec.ofNat 64 (16 * $k1))
    (ea16 := _ + 29744#64 + BitVec.ofNat 64 (16 * $k2))
    (v1 := Oct8.get _ $k1) (v2 := Oct8.get _ $k2)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hfpId:term]; try (clear * -; bv_omega))
    (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k1) (by decide) rfl rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k2) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 29024#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "str_d3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 27840#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d4 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 27968#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 28096#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem aligned16_add27840 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 27840#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 27840#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 200000 in
private theorem eHat_copy_oct8 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (p3 p4 p5 d3 d4 d5 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off4a04) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 27840#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64)
    (hx23 : s.readReg64 .x23 = sp + 17376#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4afc) s
      (Oct8Mem (sp + 29616#64) p3 ∗ Oct8Mem (sp + 29744#64) p4 ∗ Oct8Mem (sp + 29024#64) p5 ∗
       Oct8Mem (sp + 27840#64) d3 ∗ Oct8Mem (sp + 27968#64) d4 ∗ Oct8Mem (sp + 28096#64) d5 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x1 = 0#64 ∧ sf.readReg64 .x3 = sp + 27841#64 ∧
        sf.readReg64 .x9 = sp + 17392#64 ∧ sf.readReg64 .x10 = 0x019b#64 ∧
        sf.readReg64 .x11 = 0x229b#64 ∧ sf.readReg64 .x12 = 0x6833#64 ∧
        sf.readReg64 .x13 = 0xf9dd#64 ∧ sf.readReg64 .x14 = 0xc0dd#64 ∧
        sf.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x16 = 0xf301#64 ∧
        sf.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x18 = 0x4ebf#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = 0x47fa#64 ∧
        sf.readReg64 .x21 = sp + 9984#64 ∧ sf.readReg64 .x23 = sp + 17376#64 ∧
        sf.readReg64 .x27 = 0x0260#64 ∧ sf.readReg64 .x28 = 0x2260#64 ∧
        sf.readReg64 .lr = 0xf9fa#64 ∧
        Pf = (Oct8Mem (sp + 29616#64) p3 ∗ Oct8Mem (sp + 29744#64) p4 ∗ Oct8Mem (sp + 29024#64) p5 ∗
          Oct8Mem (sp + 27840#64) p3 ∗ Oct8Mem (sp + 27968#64) p4 ∗ Oct8Mem (sp + 28096#64) p5 ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p3 4 hrun hsp hsp_chk; ldr_p3 5 hrun hsp hsp_chk; wp_step
  ldr_p3 7 hrun hsp hsp_chk; ldr_p5 1 hrun hsp hsp_chk; wp_step
  str_d3 4 hrun hsp hsp_chk; ldr_p3 6 hrun hsp hsp_chk; wp_step
  str_d3 5 hrun hsp hsp_chk; ldr_p3 1 hrun hsp hsp_chk; wp_step
  str_d3 6 hrun hsp hsp_chk; ldr_p3 0 hrun hsp hsp_chk; wp_step
  str_d3 1 hrun hsp hsp_chk; ldr_p3 3 hrun hsp hsp_chk; wp_step
  str_d3 0 hrun hsp hsp_chk; ldr_p3 2 hrun hsp hsp_chk; wp_step
  str_d3 3 hrun hsp hsp_chk; wp_steps 2; str_d3 2 hrun hsp hsp_chk
  ldp_p4 4 5 hrun hfp; str_d3 7 hrun hsp hsp_chk
  ldr_p5 3 hrun hsp hsp_chk; wp_step; str_d5 1 hrun hsp hsp_chk
  ldr_p5 5 hrun hsp hsp_chk; wp_step; str_d4 4 hrun hsp hsp_chk
  wp_steps 3; str_d4 5 hrun hsp hsp_chk; wp_step
  ldp_p4 6 7 hrun hfp; str_d5 3 hrun hsp hsp_chk
  ldr_p5 7 hrun hsp hsp_chk; wp_steps 3
  str_d5 5 hrun hsp hsp_chk; str_d4 6 hrun hsp hsp_chk; str_d4 7 hrun hsp hsp_chk
  ldp_p4 0 1 hrun hfp; str_d5 7 hrun hsp hsp_chk
  str_d4 0 hrun hsp hsp_chk; str_d4 1 hrun hsp hsp_chk
  ldp_p4 2 3 hrun hfp; str_d4 2 hrun hsp hsp_chk
  ldr_p5 2 hrun hsp hsp_chk; str_d4 3 hrun hsp hsp_chk
  ldr_p5 0 hrun hsp hsp_chk; str_d5 2 hrun hsp hsp_chk
  ldr_p5 6 hrun hsp hsp_chk; str_d5 0 hrun hsp hsp_chk
  ldr_p5 4 hrun hsp hsp_chk; str_d5 6 hrun hsp hsp_chk; str_d5 4 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk, by simp [hfp],
      by simp,
      by simp [orr_1_of_aligned16 _ (aligned16_add27840 sp hsp_chk)],
      by simp,
      by simp, by simp, by simp, by simp, by simp,
      by simp [ro00Sym], by simp, by simp [ro00Sym], by simp,
      by simp [hx19], by simp, by simp [hx21], by simp [hx23],
      by simp, by simp, by simp,
      by cases p3; cases p4; cases p5; simp [Oct8.get]⟩

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

theorem eHat_copy_regs [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (prf3 prf4 prf5 : List (BitVec 8)) (Rest : SepProp)
    (h3 : prf3.length = 128) (h4 : prf4.length = 128) (h5 : prf5.length = 128)
    (hpc : s.pc = b + off4a04) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfp : s.readReg64 .fp = sp + 29984#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 27840#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64)
    (hx23 : s.readReg64 .x23 = sp + 17376#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4afc) s
      (((sp + 29616#64) ↦ₛ prf3) ∗ ((sp + 29744#64) ↦ₛ prf4) ∗ ((sp + 29024#64) ↦ₛ prf5) ∗
       memRegion (sp + 27840#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = sp + 29984#64 ∧
        sf.readReg64 .x1 = 0#64 ∧ sf.readReg64 .x3 = sp + 27841#64 ∧
        sf.readReg64 .x9 = sp + 17392#64 ∧ sf.readReg64 .x10 = 0x019b#64 ∧
        sf.readReg64 .x11 = 0x229b#64 ∧ sf.readReg64 .x12 = 0x6833#64 ∧
        sf.readReg64 .x13 = 0xf9dd#64 ∧ sf.readReg64 .x14 = 0xc0dd#64 ∧
        sf.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x16 = 0xf301#64 ∧
        sf.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x18 = 0x4ebf#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = 0x47fa#64 ∧
        sf.readReg64 .x21 = sp + 9984#64 ∧ sf.readReg64 .x23 = sp + 17376#64 ∧
        sf.readReg64 .x27 = 0x0260#64 ∧ sf.readReg64 .x28 = 0x2260#64 ∧
        sf.readReg64 .lr = 0xf9fa#64 ∧
        (Pf ⊢ ((sp + 27840#64) ↦ₛ prf3) ∗ ((sp + 27968#64) ↦ₛ prf4) ∗ ((sp + 28096#64) ↦ₛ prf5) ∗
          memRegion (sp + 29024#64) 128 ∗ memRegion (sp + 29616#64) 128 ∗
          memRegion (sp + 29744#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 29616#64) h3,
      pointsToBytes128_eq_oct8Mem (sp + 29744#64) h4,
      pointsToBytes128_eq_oct8Mem (sp + 29024#64) h5,
      memRegion_split' (b := sp + 27840#64) (b' := sp + 27968#64) (n := 128) (k := (256 : Nat))
        rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 27968#64) (b' := sp + 28096#64) (n := 128) (k := (128 : Nat))
        rfl (by clear * -; bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 27840#64) (hf := by sep_focus); intro fd3
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 27968#64) (hf := by sep_focus); intro fd4
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 28096#64) (hf := by sep_focus); intro fd5
  rw [show VecRangeMem 8 (sp + 27840#64) fd3 = Oct8Mem (sp + 27840#64) (Oct8.ofFn fd3) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 27968#64) fd4 = Oct8Mem (sp + 27968#64) (Oct8.ofFn fd4) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 28096#64) fd5 = Oct8Mem (sp + 28096#64) (Oct8.ofFn fd5) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 29616#64) (Oct8.ofFn (bytesToVecNat prf3)) ∗
      Oct8Mem (sp + 29744#64) (Oct8.ofFn (bytesToVecNat prf4)) ∗
      Oct8Mem (sp + 29024#64) (Oct8.ofFn (bytesToVecNat prf5)) ∗
      Oct8Mem (sp + 27840#64) (Oct8.ofFn fd3) ∗ Oct8Mem (sp + 27968#64) (Oct8.ofFn fd4) ∗
      Oct8Mem (sp + 28096#64) (Oct8.ofFn fd5) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (eHat_copy_oct8 hb hbase s sp _ _ _ _ _ _ Rest hpc hrun hsp hspA hfp hx19 hx20 hx21 hx23) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, rfpf, r1, r3, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r23, r27, r28, rlr, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, rfpf, r1, r3, r9, r10, r11, r12, r13, r14, r15,
    r16, r17, r18, r19, r20, r21, r23, r27, r28, rlr, ?_⟩
  rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 27840#64) h3,
      ← pointsToBytes128_eq_oct8Mem (sp + 27968#64) h4,
      ← pointsToBytes128_eq_oct8Mem (sp + 28096#64) h5]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 29616#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 29744#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 29024#64) _) (by sep_frame) (by sep_frame)))

end

/-! ## 3. `eHat` `cbd2` Zeroing & 32-Iter SWAR Loop (`+0x4afc → +0x4c2c`) -/

section
attribute [local irreducible] blkPC05 Vec128At

local macro "step_strQ9984 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k)
    · decide
    · clear * -; bv_omega
    · rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem eHat_cbd2_zero [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off4afc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4b8c) s
      (memRegion (sp + 9984#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x0 = s.readReg64 .x1 + 1#64 ∧ s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = 0#64 ∧ s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x8 = s.readReg64 .x3 ∧ s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x10 ∧ s1.readReg64 .x11 = s.readReg64 .x11 ∧
        s1.readReg64 .x12 = s.readReg64 .x12 ∧ s1.readReg64 .x13 = s.readReg64 .x13 ∧
        s1.readReg64 .x14 = s.readReg64 .x14 ∧ s1.readReg64 .x15 = s.readReg64 .x15 ∧
        s1.readReg64 .x16 = s.readReg64 .x16 ∧ s1.readReg64 .x17 = s.readReg64 .x17 ∧
        s1.readReg64 .x18 = s.readReg64 .x18 ∧ s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧ s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧ s1.readReg64 .lr = s.readReg64 .lr ∧
        (P1 ⊢ memRegion (sp + 9984#64) 512 ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 4
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 9984#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 9984#64) f = PolyMem (sp + 9984#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ9984 31; step_strQ9984 30; step_strQ9984 29; step_strQ9984 28
  step_strQ9984 27; step_strQ9984 26; step_strQ9984 25; step_strQ9984 24
  step_strQ9984 23; step_strQ9984 22; step_strQ9984 21; step_strQ9984 20
  step_strQ9984 19; step_strQ9984 18; step_strQ9984 17; step_strQ9984 16
  step_strQ9984 15; step_strQ9984 14; step_strQ9984 13; step_strQ9984 12
  step_strQ9984 11; step_strQ9984 10; step_strQ9984 9;  step_strQ9984 8
  step_strQ9984 7;  step_strQ9984 6;  step_strQ9984 5;  step_strQ9984 4
  step_strQ9984 3;  step_strQ9984 2;  step_strQ9984 1;  step_strQ9984 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_cbd_strh " cellPtr:ident hx21Id:term:arg hx2Id:term:arg c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, $hx21Id:term, $hx2Id:term]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem eHat_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off4b8c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (16 * k))
    (hx8 : s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if k < 31 then b + off4b8c else b + off4c2c) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (16 * (k + 1)) ∧ s'.readReg64 .x3 = s.readReg64 .x3 ∧
        s'.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧ s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = s.readReg64 .x11 ∧ s'.readReg64 .x12 = s.readReg64 .x12 ∧
        s'.readReg64 .x13 = s.readReg64 .x13 ∧ s'.readReg64 .x14 = s.readReg64 .x14 ∧
        s'.readReg64 .x15 = s.readReg64 .x15 ∧ s'.readReg64 .x16 = s.readReg64 .x16 ∧
        s'.readReg64 .x17 = s.readReg64 .x17 ∧ s'.readReg64 .x18 = s.readReg64 .x18 ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧ s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = dstPtr ∧ s'.readReg64 .x27 = s.readReg64 .x27 ∧
        s'.readReg64 .x28 = s.readReg64 .x28 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .lr = s.readReg64 .lr ∧
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
  step_cbd_strh cellPtr hx21 hx2 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx2 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx2 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_steps 2
  step_cbd_strh cellPtr hx21 hx2 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 3
  step_cbd_strh cellPtr hx21 hx2 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx2 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_cbd_strh cellPtr hx21 hx2 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_cbd_strh cellPtr hx21 hx2 6 (cbd2CoeffFromWord w 6)
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
    refine step_bCond_taken (dst := blkPl05.base + off4b8c)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [off4c28, off4b8c]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp,
        by simp; clear * -; bv_omega,
        by simp,
        by simp; clear * -; bv_omega,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp [hx19], by simp,
        by simp [hx21], by simp, by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl05.base + off4c2c)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [off4c28, off4c2c]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp, by simp,
        by simp, by simp, by simp, by simp, by simp [hx19], by simp,
        by simp [hx21], by simp, by simp, by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem eHat_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + off4b8c else b + off4c2c) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x2 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x8 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + off4c2c) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x0 = s.readReg64 .x0 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
          s'.readReg64 .x3 = s.readReg64 .x3 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
          s'.readReg64 .x10 = s.readReg64 .x10 ∧ s'.readReg64 .x11 = s.readReg64 .x11 ∧
          s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
          s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
          s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
          s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = s.readReg64 .x20 ∧ s'.readReg64 .x21 = dstPtr ∧
          s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 .lr = s.readReg64 .lr ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx21
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, hx19, rfl, hx21, rfl, rfl, rfl, rfl, by
        dsimp only [PolyMem]; rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx2 hx8 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    have hpc_next : (if k < 31 then b + off4b8c else b + off4c2c) =
        (if k + 1 < 32 then b + off4b8c else b + off4c2c) := by
      by_cases h : k < 31 <;> [simp [h, show k + 1 < 32 by omega]; simp [h, show ¬(k + 1 < 32) by omega]]
    refine SepWP.seq
      (eHat_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest hpc hrun hsp hspA hx2 hx8 hx19 hx21)
      fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hr0, hr1, hx2_1, hr3, hx8_1,
        hr9, hr10, hr11, hr12, hr13, hr14, hr15, hr16, hr17, hr18, hx19_1, hr20, hx21_1,
        hr27, hr28, hfp1, hlr1, hP1⟩ => by
      subst hP1
      rw [hpc_next] at hpc1
      refine SepWP.seq
        (ih (k + 1) (by omega) s1 _
          (fun i hi => by
            by_cases hik : i = k
            · subst hik; exact Function.update_self i _ f
            · rw [Function.update_of_ne hik]; exact hf i (by omega))
          hpc1 hrun1 hsp1 hspA1 hx2_1 hx8_1 hx19_1 hx21_1) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g3, g9, g10, g11, g12, g13, g14, g15,
        g16, g17, g18, gx19, g20, gx21, g27, g28, gfp, glr, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans hr0, g1.trans hr1, g3.trans hr3,
        g9.trans hr9, g10.trans hr10, g11.trans hr11, g12.trans hr12, g13.trans hr13,
        g14.trans hr14, g15.trans hr15, g16.trans hr16, g17.trans hr17, g18.trans hr18,
        gx19, g20.trans hr20, gx21, g27.trans hr27, g28.trans hr28, gfp.trans hfp1,
        glr.trans hlr1, hP2⟩

theorem eHat_cbd2_loop [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl05 b) (hbase : blkPl05.base = b)
    (s : State) (sp prfPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp)
    (hprf : prf.length = 128)
    (hpc : s.pc = b + off4afc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = prfPtr + 1#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 9984#64) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off4c2c) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 9984#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = s.readReg64 .x1 + 1#64 ∧ s'.readReg64 .x1 = s.readReg64 .x1 ∧
        s'.readReg64 .x3 = prfPtr + 1#64 ∧ s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧ s'.readReg64 .x11 = s.readReg64 .x11 ∧
        s'.readReg64 .x12 = s.readReg64 .x12 ∧ s'.readReg64 .x13 = s.readReg64 .x13 ∧
        s'.readReg64 .x14 = s.readReg64 .x14 ∧ s'.readReg64 .x15 = s.readReg64 .x15 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧ s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧ s'.readReg64 .x21 = sp + 9984#64 ∧
        s'.readReg64 .x27 = s.readReg64 .x27 ∧ s'.readReg64 .x28 = s.readReg64 .x28 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ s'.readReg64 .lr = s.readReg64 .lr ∧
        P' = ((prfPtr ↦ₛ prf) ∗ PolyMem (sp + 9984#64) (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf,
    show WordRangeMem 32 prfPtr (readU32LE prf) ∗ memRegion (sp + 9984#64) 512 ∗ Rest =
      memRegion (sp + 9984#64) 512 ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) by
      rw [← sepConj_assoc, sepConj_comm (WordRangeMem 32 prfPtr (readU32LE prf)), sepConj_assoc]]
  refine SepWP.seq (eHat_cbd2_zero hb hbase s sp _ hpc hrun hsp hspA)
    fun s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, r0, r1, hx2_1, r3, hx8_1, r9,
      r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r27, r28, rfp, rlr, hP1⟩ => by
    refine SepWP.weaken_pre hP1 ?_
    refine SepWP.of_memRegion_vecRangeMem 32 (sp + 9984#64) (by decide) rfl fun f => by
      rw [show VecRangeMem 32 (sp + 9984#64) f ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest) =
        WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 9984#64) f ∗ Rest by
        rw [← sepConj_assoc, sepConj_comm (VecRangeMem 32 (sp + 9984#64) f), sepConj_assoc]]
      refine SepWP.seq
        (eHat_cbd2_steps hb hbase sp prfPtr (sp + 9984#64) prf Rest 32 0 rfl s1 f
          (fun _ hi => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx2_1
          (by simp [hx8_1, hx3]) (r19.trans hx19) (r21.trans hx21)) ?_
      rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, g0, g1, g3, g9, g10, g11, g12, g13, g14, g15,
        g16, g17, g18, gx19, g20, gx21, g27, g28, gfp, glr, hP2⟩
      exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, g0.trans r0, g1.trans r1, g3.trans (r3.trans hx3),
        g9.trans r9, g10.trans r10, g11.trans r11, g12.trans r12, g13.trans r13,
        g14.trans r14, g15.trans r15, g16.trans r16, g17.trans r17, g18.trans r18,
        gx19, g20.trans r20, gx21, g27.trans r27, g28.trans r28, gfp.trans rfp,
        glr.trans rlr, by rw [hP2, wordRangeMem32_eq_pointsToBytes prfPtr hprf]⟩

end

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3EHatPrf
