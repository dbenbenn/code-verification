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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 6c (`+0x85d8 .. +0x89f0`)

Zeroes `e1[0..2]` (`1536` B at `sp + 20704`), runs `B01` (`RW2` + `RW1`) for `prf3..5`, copies
`prf3..5` to `[sp + 22400, sp + 22784)`, and runs the 3-iteration `cbd2` loop writing `e1[0..2]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6c

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ mlkemMpl
  resolve_blk01 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (
  cbd2CoeffFromWord neonCbd2Poly16 readU32LE)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (lane16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem Poly32Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At Vec32 VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldrQ128 step_stpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq orr_1_of_aligned16
  sepWP_elim_byte setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64 shake256List_length
  stage_prf33_eq step_bCond_not_taken step_bCond_taken truncate32_zext64 ubfx2_w32_norm
  vec128At_eq_halfRangeMem8 vec2_bytesToVecNat_eq vecRangeBytes_zero vecRangeMem_focus
  wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a (
  blk01_rw1_04 blk01_rw2_04 blk29_04 blkPl04_ρ keccak2SlicesRW_entails_memRegion32
  pointsToBytes128_eq_oct8Mem)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x85d8 → 0x89ec]
end

attribute [local irreducible] blkPC04 shake256List neonCbd2Poly16 polyVecNat
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 ubfx2_w32_norm
  truncate32_zext64 setWidth32_shr_zext64

@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Start : BitVec 64 := BitVec.ofNat 64 34264
@[simp, arm64_norm, wp_norm] abbrev off85f4        : BitVec 64 := BitVec.ofNat 64 34292
@[simp, arm64_norm, wp_norm] abbrev off86e4        : BitVec 64 := BitVec.ofNat 64 34532
@[simp, arm64_norm, wp_norm] abbrev off86e8        : BitVec 64 := BitVec.ofNat 64 34536
@[simp, arm64_norm, wp_norm] abbrev off8720        : BitVec 64 := BitVec.ofNat 64 34592
@[simp, arm64_norm, wp_norm] abbrev off8724        : BitVec 64 := BitVec.ofNat 64 34596
@[simp, arm64_norm, wp_norm] abbrev off877c        : BitVec 64 := BitVec.ofNat 64 34684
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1      : BitVec 64 := BitVec.ofNat 64 34800
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Body  : BitVec 64 := BitVec.ofNat 64 34940
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Br    : BitVec 64 := BitVec.ofNat 64 35096
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Copy  : BitVec 64 := BitVec.ofNat 64 35100
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Out   : BitVec 64 := BitVec.ofNat 64 35308
@[simp, arm64_norm, wp_norm] abbrev offSeg6E2      : BitVec 64 := BitVec.ofNat 64 35312

private theorem aligned16_add22400 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 22400#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 22400#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

/-! ## 1. Zero `e1[0..2]` at `[sp + 20704, sp + 22240)` (`+0x85d8 → +0x85f4`) -/

theorem seg6c_memset_e1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off85f4) s
      (memRegion (sp + 20704#64) 1536 ∗ stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 20704#64 ∧
        (Pm ⊢ PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
          PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
          PolyMem (sp + 21728#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  wp_steps 7
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk29_04 blkPl04.base) (sp + 20704#64, 0#8, (1536 : Nat))
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      ‹_›, Eq.trans ‹_› hx19, Eq.trans ‹_› (by simp), ?_⟩
  have hz3 : ((sp + 20704#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
      PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
      PolyMem (sp + 21728#64) (fun _ => 0#128) := by
    have hrep : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, show (1536 : Nat) = 512 + (512 + 512) from rfl,
        List.replicate_add, List.replicate_add]
    rw [hrep, pointsToBytes_append, pointsToBytes_append, vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp [PolyMem,
      show sp + 20704#64 + BitVec.ofNat 64 (16 * 32) = sp + 21216#64 by clear * -; bv_omega,
      show sp + 21216#64 + BitVec.ofNat 64 (16 * 32) = sp + 21728#64 by clear * -; bv_omega]
  rw [hz3]
  sep_frame

/-! ## 2. `Seg6c` PRF Stage & Calls (`+0x85f4 → +0x8724`) -/

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
  (try rw [setPC_setMem_setPC]); (try rw [setMem_setMem]); (try rw [setPC_setMem_collapse])))

local macro "step_dead_zero8 " spTerm:term:arg baseOff:num : tactic => `(tactic| (
  apply SepWP.of_memRegion_vecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) (by decide) (by sep_focus)
  intro zf
  rw [show VecRangeMem 8 ($spTerm + BitVec.ofNat 64 $baseOff) zf =
        PolyOctMem ($spTerm + BitVec.ofNat 64 $baseOff) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; step_strQ_oct8 5; step_strQ_oct8 4;
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0))

local syntax "find_load128" : tactic
local macro_rules
  | `(tactic| find_load128) => `(tactic| first
      | (with_reducible apply SepLoad128.vec128At; with_reducible rfl)
      | (with_reducible apply SepLoad128.left; find_load128)
      | (with_reducible apply SepLoad128.right; find_load128))

local syntax "find_store128" : tactic
local macro_rules
  | `(tactic| find_store128) => `(tactic| first
      | (with_reducible apply SepStore128.vec128At; with_reducible rfl)
      | (with_reducible apply SepStore128.left; find_store128)
      | (with_reducible apply SepStore128.right; find_store128))

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg6c_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off85f4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off86e4) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 32 ∗
       memRegion (sp + 22240#64) 99 ∗
       memRegion (sp + 24448#64) 128 ∗
       memRegion (sp + 24976#64) 128 ∗
       memRegion (sp + 25296#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x0 = sp + 11856#64 ∧
        sm.readReg64 .x1 = sp + 24976#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 25296#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = sp + 11856#64 ∧
        sm.readReg64 .x22 = 33#64 ∧
        sm.readReg64 .x23 = sp + 22306#64 ∧
        (Pm ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 11856#64) (sp + 22240#64) (sp + 22273#64) 33 33 ∗
          ((sp + 22240#64) ↦ₛ (coins ++ [3#8])) ∗
          ((sp + 22273#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 22306#64) ↦ₛ (coins ++ [5#8])) ∗
          memRegion (sp + 24448#64) 128 ∗
          memRegion (sp + 24976#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 19120#64) hc]
  have h99 : memRegion (sp + 22240#64) 99 =
      memRegion (sp + 22240#64) 16 ∗ memRegion (sp + 22256#64) 16 ∗ memRegion (sp + 22272#64) 1 ∗
      memRegion (sp + 22273#64) 16 ∗ memRegion (sp + 22289#64) 16 ∗ memRegion (sp + 22305#64) 1 ∗
      memRegion (sp + 22306#64) 16 ∗ memRegion (sp + 22322#64) 16 ∗ memRegion (sp + 22338#64) 1 := by
    rw [memRegion_split' (b' := sp + 22256#64) (n := 16) (k := (83 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22272#64) (n := 16) (k := (67 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22273#64) (n := 1)  (k := (66 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22289#64) (n := 16) (k := (50 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22305#64) (n := 16) (k := (34 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22306#64) (n := 1)  (k := (33 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22322#64) (n := 16) (k := (17 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 22338#64) (n := 16) (k := (1 : Nat))  rfl (by bv_omega) (by decide)]
  rw [h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22240#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22256#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22273#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22289#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22306#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 22322#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 22272#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 22305#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 22338#64)); intro c2
  sep_frame_apply (sepWP_elim_region32 (a := sp + 11856#64)); intro k0 k1 k2 k3
  simp only [show sp + 11856#64 + 8#64 = sp + 11864#64 by bv_omega,
    show sp + 11856#64 + 16#64 = sp + 11872#64 by bv_omega,
    show sp + 11856#64 + 24#64 = sp + 11880#64 by bv_omega]
  have _ := hpc
  wp_step
  refine step_ldrQ128 (wb := none) (ea := sp + 19120#64) (v := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := (sp + 19120#64) + 16#64) (v := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 4
  refine step_strQ128 (wb := none) (ea := sp + 22240#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 22273#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 22306#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 22289#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 22322#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 22256#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  step_dead_zero8 sp 24976
  step_dead_zero8 sp 25296
  step_dead_zero8 sp 24448
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 22240#64) 3#8 hc,
      ← stage_prf33_eq (sp + 22273#64) 4#8 hc,
      ← stage_prf33_eq (sp + 22306#64) 5#8 hc]
  unfold Keccak2SlicesRW
  simp only [show sp + 22240#64 + 16#64 = sp + 22256#64 by bv_omega,
    show sp + 22240#64 + 32#64 = sp + 22272#64 by bv_omega,
    show sp + 22273#64 + 16#64 = sp + 22289#64 by bv_omega,
    show sp + 22273#64 + 32#64 = sp + 22305#64 by bv_omega,
    show sp + 22306#64 + 16#64 = sp + 22322#64 by bv_omega,
    show sp + 22306#64 + 32#64 = sp + 22338#64 by bv_omega,
    show sp + 11856#64 + 8#64 = sp + 11864#64 by bv_omega,
    show sp + 11856#64 + 16#64 = sp + 11872#64 by bv_omega,
    show sp + 11856#64 + 24#64 = sp + 11880#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 24976#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 25296#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 24448#64) _) (by sep_frame) (by sep_frame)))

private theorem seg6c_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp p5 : BitVec 64) {l5 : Nat} (hl5 : l5 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off86e8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = 33#64) (hx23 : s.readReg64 .x23 = p5) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8720) s
      (memRegion (sp + 22400#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x0 = sp + 22400#64 ∧ sm.readReg64 .x1 = sp + 24448#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 11856#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp + 22400#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 22400#64) p5 p5 l5 l5 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 22400#64)); intro d0 d1 d2 d3
  simp only [show sp + 22400#64 + 8#64 = sp + 22408#64 by bv_omega,
    show sp + 22400#64 + 16#64 = sp + 22416#64 by bv_omega,
    show sp + 22400#64 + 24#64 = sp + 22424#64 by bv_omega]
  wp_steps 14
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hl5, show sp + 22400#64 + 8#64 = sp + 22408#64 by bv_omega,
    show sp + 22400#64 + 16#64 = sp + 22416#64 by bv_omega,
    show sp + 22400#64 + 24#64 = sp + 22424#64 by bv_omega]
  sep_frame

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem seg6c_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off85f4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8724) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 128 ∗
       memRegion (sp + 22240#64) 99 ∗
       memRegion (sp + 22400#64) 32 ∗
       memRegion (sp + 24448#64) 128 ∗
       memRegion (sp + 24976#64) 128 ∗
       memRegion (sp + 25296#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readReg64 .x22 = sp + 22400#64 ∧
        (Pf ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 128 ∗
          memRegion (sp + 22240#64) 99 ∗
          memRegion (sp + 22400#64) 32 ∗
          ((sp + 24448#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
          ((sp + 24976#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
          ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 32 ∗
      memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 24448#64) 128 ∗
      memRegion (sp + 24976#64) 128 ∗ memRegion (sp + 25296#64) 128 ∗
      (memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 11888#64) 96 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6c_prf_stage hb rfl s sp coins _ hc hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc3_len : (coins ++ [3#8]).length = 33 := by simp [hc]
  have hc4_len : (coins ++ [4#8]).length = 33 := by simp [hc]
  have hc5_len : (coins ++ [5#8]).length = 33 := by simp [hc]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC04.rebase blkPl04.base (fun _ => none))
      (blkPl04.base + off86e8) s1
      (((sp + 19120#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 11856#64) (sp + 22240#64) (sp + 22273#64) 33 33 ∗
        ((sp + 22240#64) ↦ₛ (coins ++ [3#8])) ∗
        ((sp + 22273#64) ↦ₛ (coins ++ [4#8])) ∗
        ((sp + 22306#64) ↦ₛ (coins ++ [5#8])) ∗
        memRegion (sp + 24448#64) 128 ∗
        memRegion (sp + 24976#64) 128 ∗
        memRegion (sp + 25296#64) 128 ∗
        (memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 11888#64) 96 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .fp = s.readReg64 .fp ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 20704#64 ∧
        s2.readReg64 .x21 = sp + 11856#64 ∧ s2.readReg64 .x22 = 33#64 ∧
        s2.readReg64 .x23 = sp + 22306#64 ∧
        (P2 ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 128 ∗
          ((sp + 22240#64) ↦ₛ (coins ++ [3#8])) ∗
          ((sp + 22273#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 22306#64) ↦ₛ (coins ++ [5#8])) ∗
          memRegion (sp + 22400#64) 32 ∗
          memRegion (sp + 24448#64) 128 ∗
          ((sp + 24976#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
          ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [show Keccak2SlicesRW (sp + 11856#64) (sp + 22240#64) (sp + 22273#64) 33 33 =
          Keccak2SlicesRW (sp + 11856#64) (sp + 22240#64) (sp + 22273#64)
            (coins ++ [3#8]).length (coins ++ [4#8]).length from by rw [hc3_len, hc4_len]]
    wp_step
    have hro1 : MlKemRoOk mlkemMpl
        ((s1.writeReg64 .lr (blkPl04.base + off86e8)).setPC (mlkemMpl.base 1)).mem := hro1
    apply seq_codeLoaded_lr ‹_›
    wp_call (blk01_rw2_04 blkPl04.base)
      (⟨sp + 11856#64, sp + 22240#64, sp + 22273#64, sp + 24976#64, sp + 25296#64,
        (128 : Nat), coins ++ [3#8], coins ++ [4#8]⟩ : Keccak2ShakeArgs)
    apply SepWP.done (by assumption) (by assumption); intro _
    refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› hfp1,
        Eq.trans ‹_› (hx19_1.trans hx19), Eq.trans ‹_› (hx20_1.trans hx20),
        Eq.trans ‹_› hx21_1, Eq.trans ‹_› hx22_1, Eq.trans ‹_› hx23_1, ?_⟩
    rw [hsp1]
    have hk11856 : Keccak2SlicesRW (sp + 11856#64) (sp + 22240#64) (sp + 22273#64)
          (coins ++ [3#8]).length (coins ++ [4#8]).length ∗
        memRegion (sp + 11888#64) 96 ⊢ memRegion (sp + 11856#64) 128 := by
      rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11888#64) (n := 32) (k := (96 : Nat))
            rfl (by clear * -; bv_omega) (by decide)]
      exact sepConj_mono (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (Entails.refl _)
    exact entails_sub hk11856 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 22400#64) 32 ∗ (((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 11856#64) 128 ∗ ((sp + 22240#64) ↦ₛ (coins ++ [3#8])) ∗
      ((sp + 22273#64) ↦ₛ (coins ++ [4#8])) ∗ ((sp + 22306#64) ↦ₛ (coins ++ [5#8])) ∗
      memRegion (sp + 24448#64) 128 ∗
      ((sp + 24976#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
      ((sp + 25296#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6c_prf_stage2 hb rfl s2 sp (sp + 22306#64) hc5_len _ hpc2 hrun2 hsp2 hspA2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_step
  have hro3 : MlKemRoOk mlkemMpl
      ((s3.writeReg64 .lr (blkPl04.base + off8724)).setPC (mlkemMpl.base 1)).mem := hro3
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk01_rw1_04 blkPl04.base)
    (sp + 22400#64, sp + 22306#64, sp + 24448#64, sp + 11856#64, (128 : Nat), coins ++ [5#8])
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› (hfp3.trans hfp2),
      Eq.trans ‹_› (hx19_3.trans hx19_2), Eq.trans ‹_› (hx20_3.trans hx20_2),
      Eq.trans ‹_› (hx21_3.trans hx21_2), Eq.trans ‹_› hx22_3, ?_⟩
  rw [hsp3]
  have hm11856 : ((sp + 11856#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ⊢
      memRegion (sp + 11856#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 11856#64) (shake256List 128 (coins ++ [5#8]))
  have hm99 : ((sp + 22240#64) ↦ₛ (coins ++ [3#8])) ∗
      ((sp + 22273#64) ↦ₛ (coins ++ [4#8])) ∗
      ((sp + 22306#64) ↦ₛ (coins ++ [5#8])) ⊢ memRegion (sp + 22240#64) 99 := by
    rw [memRegion_split' (b' := sp + 22273#64) (n := 33) (k := (66 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 22306#64) (n := 33) (k := (33 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by simpa [hc3_len] using pointsToBytes_entails_memRegion (sp + 22240#64) (coins ++ [3#8]))
      (sepConj_mono
        (by simpa [hc4_len] using pointsToBytes_entails_memRegion (sp + 22273#64) (coins ++ [4#8]))
        (by simpa [hc5_len] using pointsToBytes_entails_memRegion (sp + 22306#64) (coins ++ [5#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm11856 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))

/-! ## 3. Copy `prf3..5` to `[sp + 22400, sp + 22784)` (`+0x8724 → +0x87f0`) -/

local macro "ldr_p3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 24976#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p4 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 25296#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 24448#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "str_d0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22400#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22528#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22656#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg6c_copy_prfs_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (p3 p4 p5 d0 d1 d2 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off8724) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hx22 : s.readReg64 .x22 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off877c) s
      (Oct8Mem (sp + 24976#64) p3 ∗ Oct8Mem (sp + 25296#64) p4 ∗ Oct8Mem (sp + 24448#64) p5 ∗
       Oct8Mem (sp + 22400#64) d0 ∗ Oct8Mem (sp + 22528#64) d1 ∗ Oct8Mem (sp + 22656#64) d2 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x8 = 0#64 ∧ sm.readReg64 .x9 = sp + 22401#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧ sm.readReg64 .x20 = sp + 20704#64 ∧
        sm.readReg64 .x21 = sp + 11856#64 ∧
        sm.readVReg128 0#5 = p4.o5 ∧ sm.readVReg128 1#5 = p4.o4 ∧
        sm.readVReg128 2#5 = p4.o6 ∧ sm.readVReg128 3#5 = 0#128 ∧
        Pm = (Oct8Mem (sp + 24976#64) p3 ∗ Oct8Mem (sp + 25296#64) p4 ∗ Oct8Mem (sp + 24448#64) p5 ∗
          Oct8Mem (sp + 22400#64) p3 ∗ Oct8Mem (sp + 22528#64) d1 ∗ Oct8Mem (sp + 22656#64) d2 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  ldr_p3 4 hrun hsp hsp_chk; ldr_p3 5 hrun hsp hsp_chk; wp_step
  ldr_p3 7 hrun hsp hsp_chk; wp_steps 2
  str_d0 4 hrun hsp hsp_chk; ldr_p3 6 hrun hsp hsp_chk
  str_d0 5 hrun hsp hsp_chk; ldr_p3 0 hrun hsp hsp_chk
  str_d0 6 hrun hsp hsp_chk; ldr_p3 1 hrun hsp hsp_chk
  str_d0 7 hrun hsp hsp_chk; ldr_p3 2 hrun hsp hsp_chk
  str_d0 1 hrun hsp hsp_chk; ldr_p3 3 hrun hsp hsp_chk
  str_d0 0 hrun hsp hsp_chk; ldr_p4 4 hrun hsp hsp_chk
  str_d0 3 hrun hsp hsp_chk; ldr_p4 5 hrun hsp hsp_chk
  str_d0 2 hrun hsp hsp_chk; ldr_p4 6 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp [orr_1_of_aligned16 _ (aligned16_add22400 sp hsp_chk)],
      by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [Oct8.get], by simp [Oct8.get], by simp [Oct8.get], by simp,
      by cases p3; cases d0; rfl⟩

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg6c_copy_prfs_b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (p3 p4 p5 d1 d2 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off877c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = sp + 22401#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hv0 : s.readVReg128 0#5 = p4.o5) (hv1 : s.readVReg128 1#5 = p4.o4)
    (hv2 : s.readVReg128 2#5 = p4.o6) (hv3 : s.readVReg128 3#5 = 0#128) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E1) s
      (Oct8Mem (sp + 24976#64) p3 ∗ Oct8Mem (sp + 25296#64) p4 ∗ Oct8Mem (sp + 24448#64) p5 ∗
       Oct8Mem (sp + 22400#64) p3 ∗ Oct8Mem (sp + 22528#64) d1 ∗ Oct8Mem (sp + 22656#64) d2 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 22401#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        Pf = (Oct8Mem (sp + 24976#64) p3 ∗ Oct8Mem (sp + 25296#64) p4 ∗ Oct8Mem (sp + 24448#64) p5 ∗
          Oct8Mem (sp + 22400#64) p3 ∗ Oct8Mem (sp + 22528#64) p4 ∗ Oct8Mem (sp + 22656#64) p5 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  str_d1 5 hrun hsp hsp_chk; ldr_p4 7 hrun hsp hsp_chk
  str_d1 4 hrun hsp hsp_chk; ldr_p4 0 hrun hsp hsp_chk
  str_d1 7 hrun hsp hsp_chk; ldr_p4 1 hrun hsp hsp_chk
  str_d1 6 hrun hsp hsp_chk; ldr_p4 2 hrun hsp hsp_chk
  str_d1 1 hrun hsp hsp_chk; ldr_p4 3 hrun hsp hsp_chk
  str_d1 0 hrun hsp hsp_chk; ldr_p5 3 hrun hsp hsp_chk
  str_d1 3 hrun hsp hsp_chk; ldr_p5 1 hrun hsp hsp_chk
  str_d1 2 hrun hsp hsp_chk; ldr_p5 2 hrun hsp hsp_chk
  str_d2 3 hrun hsp hsp_chk; ldr_p5 0 hrun hsp hsp_chk
  str_d2 1 hrun hsp hsp_chk; ldr_p5 7 hrun hsp hsp_chk
  str_d2 2 hrun hsp hsp_chk; ldr_p5 6 hrun hsp hsp_chk
  str_d2 0 hrun hsp hsp_chk; ldr_p5 4 hrun hsp hsp_chk
  str_d2 7 hrun hsp hsp_chk; ldr_p5 5 hrun hsp hsp_chk
  str_d2 6 hrun hsp hsp_chk; str_d2 5 hrun hsp hsp_chk; str_d2 4 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp [hx8], by simp [hx9], by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hv3], by cases p4; cases p5; cases d1; cases d2; simp [Oct8.get]⟩

theorem seg6c_copy_prfs [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (prf3 prf4 prf5 : List (BitVec 8)) (Rest : SepProp)
    (h3 : prf3.length = 128) (h4 : prf4.length = 128) (h5 : prf5.length = 128)
    (hpc : s.pc = b + off8724) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hx22 : s.readReg64 .x22 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E1) s
      (((sp + 24976#64) ↦ₛ prf3) ∗ ((sp + 25296#64) ↦ₛ prf4) ∗ ((sp + 24448#64) ↦ₛ prf5) ∗
       memRegion (sp + 22400#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 22401#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ ((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
          memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 24976#64) h3,
      pointsToBytes128_eq_oct8Mem (sp + 25296#64) h4,
      pointsToBytes128_eq_oct8Mem (sp + 24448#64) h5,
      memRegion_split' (b := sp + 22400#64) (b' := sp + 22528#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22528#64) (b' := sp + 22656#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22400#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22528#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22656#64) (hf := by sep_focus); intro fd2
  rw [show VecRangeMem 8 (sp + 22400#64) fd0 = Oct8Mem (sp + 22400#64) (Oct8.ofFn fd0) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 22528#64) fd1 = Oct8Mem (sp + 22528#64) (Oct8.ofFn fd1) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 22656#64) fd2 = Oct8Mem (sp + 22656#64) (Oct8.ofFn fd2) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 24976#64) (Oct8.ofFn (bytesToVecNat prf3)) ∗
      Oct8Mem (sp + 25296#64) (Oct8.ofFn (bytesToVecNat prf4)) ∗
      Oct8Mem (sp + 24448#64) (Oct8.ofFn (bytesToVecNat prf5)) ∗
      Oct8Mem (sp + 22400#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 22528#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 22656#64) (Oct8.ofFn fd2) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (seg6c_copy_prfs_a hb hbase s sp _ _ _ _ _ _ Rest hpc hrun hsp hspA hx19 hx20 hx21 hx22)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hfpm, hx8m, hx9m, hx19m, hx20m, hx21m, hv0m, hv1m, hv2m, hv3m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (seg6c_copy_prfs_b hb hbase sm sp _ _ _ _ _ Rest hpcm hrunm hspm hspAm
        hx8m hx9m hx19m hx20m hx21m hv0m hv1m hv2m hv3m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, rf, r8, r9, r19, r20, r21, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, rf.trans hfpm, r8, r9, r19, r20, r21, rv3, ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 22400#64) h3,
      ← pointsToBytes128_eq_oct8Mem (sp + 22528#64) h4,
      ← pointsToBytes128_eq_oct8Mem (sp + 22656#64) h5]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 24976#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 25296#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 24448#64) _) (by sep_frame) (by sep_frame)))

theorem seg6c_prf_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6E1Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E1) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 20704#64) 1536 ∗
       memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 384 ∗
       memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
       memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 22401#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 512 ∗
          PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
          PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
          PolyMem (sp + 21728#64) (fun _ => 0#128) ∗
          memRegion (sp + 22240#64) 99 ∗
          ((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
          memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro prf3 prf4 prf5
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 20704#64) 1536 ∗ stackAt sp 1136 ∗
      (((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 512 ∗
        memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 384 ∗
        memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
        memRegion (sp + 25296#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6c_memset_e1 hb hbase s sp _ hpc hrun hsp hspA hx19 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (352 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 128 ∗
      memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 32 ∗
      memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
      memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 11984#64) 384 ∗ memRegion (sp + 22432#64) 352 ∗
        PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21728#64) (fun _ => 0#128) ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6c_prf_calls hb hbase s1 sp coins _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm512 : memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 11984#64) 384 =
      memRegion (sp + 11856#64) 512 :=
    (memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have hm384 : memRegion (sp + 22400#64) 32 ∗ memRegion (sp + 22432#64) 352 =
      memRegion (sp + 22400#64) 384 :=
    (memRegion_split' (b := sp + 22400#64) (b' := sp + 22432#64) (n := 32) (k := (352 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 24976#64) ↦ₛ prf3) ∗ ((sp + 25296#64) ↦ₛ prf4) ∗ ((sp + 24448#64) ↦ₛ prf5) ∗
      memRegion (sp + 22400#64) 384 ∗
      (((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21728#64) (fun _ => 0#128) ∗
        memRegion (sp + 22240#64) 99 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm512) (by sep_frame)
      (entails_sub (Entails.of_eq hm384) (by sep_frame) (by sep_frame))) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6c_copy_prfs hb hbase s2 sp prf3 prf4 prf5 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, rf, r8, r9, r19, r20, r21, rv3, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, rf.trans (hfp2.trans hfp1), r8, r9, r19, r20, r21, rv3, hclf, hrof,
      Entails.trans hPf (by sep_frame)⟩

/-! ## 4. 3-Iteration `e1[0..2]` `cbd2` Loop (`+0x87f0 → +0x89f0`) -/

local macro "step_strQ11856 " k:num : tactic => `(tactic| (
  apply step_strQ128 (wb := none)
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

private theorem seg6c_e1_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E1Body) s
      (memRegion (sp + 11856#64) 512 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x8 = s.readReg64 .x8 ∧
        s1.readReg64 .x9 = s.readReg64 .x9 ∧
        s1.readReg64 .x10 = s.readReg64 .x8 + 1#64 ∧
        s1.readReg64 .x11 = 0#64 ∧
        s1.readReg64 .x12 = s.readReg64 .x9 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (P1 ⊢ memRegion (sp + 11856#64) 512 ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_steps 3
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) rfl
  intro f
  rw [show VecRangeMem 32 (sp + 11856#64) f = PolyMem (sp + 11856#64) f from rfl, ← poly32Mem_ofFn]
  step_strQ11856 31; step_strQ11856 30; step_strQ11856 29; step_strQ11856 28
  step_strQ11856 27; step_strQ11856 26; step_strQ11856 25; step_strQ11856 24
  step_strQ11856 23; step_strQ11856 22; step_strQ11856 21; step_strQ11856 20
  step_strQ11856 19; step_strQ11856 18; step_strQ11856 17; step_strQ11856 16
  step_strQ11856 15; step_strQ11856 14; step_strQ11856 13; step_strQ11856 12
  step_strQ11856 11; step_strQ11856 10; step_strQ11856 9;  step_strQ11856 8
  step_strQ11856 7;  step_strQ11856 6;  step_strQ11856 5;  step_strQ11856 4
  step_strQ11856 3;  step_strQ11856 2;  step_strQ11856 1;  step_strQ11856 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp,
      sepConj_mono_left (poly32Mem_entails_memRegion _ _)⟩

local macro "step_e1_strh " cellPtr:ident c:num
    valTerm:term:arg valPrf:term:arg hrunId:term:arg : tactic => `(tactic| (
  refine SepWP.step_str16 (wb := none)
    (ea := $cellPtr + BitVec.ofNat 64 (2 * $c)) (val := $valTerm)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; first | rfl | (dsimp only [$cellPtr:ident]; clear * -; bv_omega))
    $valPrf
    (SepStore16.left (SepStore16.halfRange (n := 8) (c := $c) (by decide) rfl))
    (by wp_norm_lhs) ?_
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg6c_e1_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Body) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 * k))
    (hx12 : s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = dstPtr) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if k < 31 then b + offSeg6E1Body else b + offSeg6E1Copy) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = s.readReg64 .x9 ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = s.readReg64 .x20 ∧
        s'.readReg64 .x21 = dstPtr ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
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
    (by simp [evalAddrMode, hx12]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_e1_strh cellPtr 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_e1_strh cellPtr 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_steps 2
  step_e1_strh cellPtr 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 3
  step_e1_strh cellPtr 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e1_strh cellPtr 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_e1_strh cellPtr 6 (cbd2CoeffFromWord w 6)
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
    refine step_bCond_taken (dst := blkPl04.base + offSeg6E1Body)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [offSeg6E1Br, offSeg6E1Body]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl04.base + offSeg6E1Copy)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg6E1Br, offSeg6E1Copy]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp,
        by simp, by simp,
        by simp [hx19], by simp, by simp [hx21], by simp, by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg6c_e1_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + offSeg6E1Body else b + offSeg6E1Copy) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x12 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x21 = dstPtr →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E1Copy) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readReg64 .x8 = s.readReg64 .x8 ∧
          s'.readReg64 .x9 = s.readReg64 .x9 ∧
          s'.readReg64 .x10 = s.readReg64 .x10 ∧
          s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = s.readReg64 .x20 ∧
          s'.readReg64 .x21 = dstPtr ∧
          s'.readReg64 .x22 = s.readReg64 .x22 ∧
          s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx21
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun
      ⟨hsp, hspA, rfl, rfl, rfl, rfl, hx19, rfl, hx21, rfl, rfl, by
        dsimp only [PolyMem]
        rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx11 hx12 hx19 hx21
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg6c_e1_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx11 hx12 hx19 hx21) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, rfp, r8, r9, r10, hx11_1, hx12_1, hx19_1, r20, hx21_1, r22, rv3, hP1⟩
    subst hP1
    refine SepWP.seq
      (ih (k + 1) (by omega) s1 _
        (fun i hi => by
          by_cases hik : i = k
          · subst hik; exact Function.update_self i _ f
          · rw [Function.update_of_ne hik]; exact hf i (by omega))
        (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
        hrun1 hsp1 hspA1 hx11_1 hx12_1 hx19_1 hx21_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, gfp, g8, g9, g10, gx19, g20, gx21, g22, gv3, hP2⟩
    exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, gfp.trans rfp, g8.trans r8, g9.trans r9, g10.trans r10,
      gx19, g20.trans r20, gx21, g22.trans r22, gv3.trans rv3, hP2⟩

local macro "ldr_src11856 " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · apply SepLoad128.left; exact SepLoad128.vec32 (by decide : $k < 32) (by bv_omega) rfl
  · wp_norm_lhs))

local macro "stp_dst_e1 " m:num : tactic => `(tactic| (
  apply step_stpQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · rfl
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.right; apply SepStore128.left
    exact SepStore128.vec32 (by decide : 2 * $m < 32) (by bv_omega) (by dsimp only [Vec32.set])
  · apply SepStore128.right; apply SepStore128.left
    exact SepStore128.vec32 (by decide : 2 * $m + 1 < 32) (by bv_omega) (by dsimp only [Vec32.set])
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

private theorem seg6c_e1_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Copy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (idx + 1))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64) :
    let dstPtr := sp + 20704#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg6E1 else b + offSeg6E2) s
      (Poly32Mem (sp + 11856#64) src ∗ Poly32Mem dstPtr dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        s'.readReg64 .x9 = s.readReg64 .x9 + 128#64 ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = sp + 20704#64 ∧
        s'.readReg64 .x21 = sp + 11856#64 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧
        s'.readVReg128 3#5 = s.readVReg128 3#5 ∧
        P' = (Poly32Mem (sp + 11856#64) src ∗ Poly32Mem dstPtr src ∗ Rest)) := by
  intro dstPtr
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hx11_eq : (sp + 20704#64) + (BitVec.ofNat 64 idx <<< 9) = dstPtr := by
    dsimp only [dstPtr]; clear * - hidx
    rcases (show idx = 0 ∨ idx = 1 ∨ idx = 2 by omega) with rfl | rfl | rfl <;> bv_omega
  wp_step
  ldr_src11856 0; ldr_src11856 1; ldr_src11856 3
  wp_steps 2
  stp_dst_e1 0
  ldr_src11856 2; ldr_src11856 5
  wp_step
  stp_dst_e1 1
  ldr_src11856 4;  ldr_src11856 7;  stp_dst_e1 2
  ldr_src11856 6;  ldr_src11856 9;  stp_dst_e1 3
  ldr_src11856 8;  ldr_src11856 11; stp_dst_e1 4
  ldr_src11856 10; ldr_src11856 13; stp_dst_e1 5
  ldr_src11856 12; ldr_src11856 15; stp_dst_e1 6
  ldr_src11856 14; ldr_src11856 17; stp_dst_e1 7
  ldr_src11856 16; ldr_src11856 19; stp_dst_e1 8
  ldr_src11856 18; ldr_src11856 21; stp_dst_e1 9
  ldr_src11856 20; ldr_src11856 23; stp_dst_e1 10
  ldr_src11856 22; ldr_src11856 25; stp_dst_e1 11
  ldr_src11856 24; ldr_src11856 27; stp_dst_e1 12
  ldr_src11856 26; ldr_src11856 29; stp_dst_e1 13
  ldr_src11856 28; ldr_src11856 31; stp_dst_e1 14
  ldr_src11856 30; stp_dst_e1 15
  by_cases hidx2 : idx < 2
  · simp only [hidx2, ↓reduceIte]
    refine step_bCond_taken (dst := blkPl04.base + offSeg6E1)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hidx2; rcases idx with _ | _ | idx <;> first | decide | omega)
      (by clear * -; dsimp [offSeg6E1Out, offSeg6E1]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp,
        by clear * -; cases src; rfl⟩
  · have hidx_eq : idx = 2 := by omega
    subst hidx_eq
    simp only [show ¬(2 < 2) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl04.base + offSeg6E2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [offSeg6E1Out, offSeg6E2]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
        by simp, by simp, by simp, by simp [hx19], by simp [hx20], by simp [hx21], by simp, by simp,
        by clear * -; cases src; rfl⟩

private theorem seg6c_e1_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {idx : Nat} (hidx : idx < 3)
    (prf : List (BitVec 8)) (hprf : prf.length = 128)
    (prev : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 idx)
    (hx9 : s.readReg64 .x9 = sp + 22401#64 + BitVec.ofNat 64 (128 * idx))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64) :
    let prfPtr := sp + 22400#64 + BitVec.ofNat 64 (128 * idx)
    let dstPtr := sp + 20704#64 + BitVec.ofNat 64 (512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none))
      (if idx < 2 then b + offSeg6E1 else b + offSeg6E2) s
      ((prfPtr ↦ₛ prf) ∗ memRegion (sp + 11856#64) 512 ∗ PolyMem dstPtr prev ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x9 = sp + 22401#64 + BitVec.ofNat 64 (128 * (idx + 1)) ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 20704#64 ∧
        sf.readReg64 .x21 = sp + 11856#64 ∧
        sf.readVReg128 3#5 = s.readVReg128 3#5 ∧
        (Pf ⊢ (prfPtr ↦ₛ prf) ∗ memRegion (sp + 11856#64) 512 ∗
          PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro prfPtr dstPtr
  rw [← wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 11856#64) 512 ∗
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg6c_e1_zero hb hbase s sp _ hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hfp1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1,
    hx19_1, hx20_1, hx21_1, _, hv3_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) rfl
  intro f11856
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 (sp + 11856#64) f11856 ∗
      (PolyMem dstPtr prev ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq
    (seg6c_e1_cbd2_steps hb hbase sp prfPtr (sp + 11856#64) prf _ 32 0 rfl s1 f11856
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx11_1
      (by rw [hx12_1, hx9]; dsimp only [prfPtr]; clear * -; bv_omega)
      (hx19_1.trans hx19) (hx21_1.trans hx21)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hfp2, hx8_2, hx9_2, hx10_2, hx19_2, hx20_2, hx21_2, _, hv3_2, hP2⟩
  subst hP2
  rw [← poly32Mem_ofFn (sp + 11856#64), ← poly32Mem_ofFn dstPtr prev]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf))) ∗
      Poly32Mem dstPtr (Vec32.ofFn prev) ∗ (WordRangeMem 32 prfPtr (readU32LE prf) ∗ Rest))
    (by sep_frame) ?_
  have hx10_eq : s2.readReg64 .x10 = BitVec.ofNat 64 (idx + 1) := by
    rw [hx10_2, hx10_1, hx8]; clear * - hidx; rcases idx with _ | _ | _ | idx <;> first | decide | omega
  refine SepWP.seq
    (seg6c_e1_copy hb hbase s2 sp hidx _ _ _ hpc2 hrun2 hsp2 hspA2
      (hx8_2.trans (hx8_1.trans hx8)) hx10_eq hx19_2
      (hx20_2.trans (hx20_1.trans hx20)) hx21_2) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, rfp, r8, r9, r19, r20, r21, _, rv3, hPf⟩
  refine SepWP.done hpcf hrunf
    ⟨hspf, hspAf, rfp.trans (hfp2.trans hfp1), r8, by rw [r9, hx9_2, hx9_1, hx9]; clear * -; bv_omega,
      r19, r20, r21, rv3.trans (hv3_2.trans hv3_1), ?_⟩
  rw [hPf, poly32Mem_ofFn dstPtr, wordRangeMem32_eq_pointsToBytes prfPtr hprf]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 11856#64) _) (by sep_frame) (by sep_frame)

theorem seg6c_e1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8))
    (z0 z1 z2 : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = sp + 22401#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 20704#64)
    (hx21 : s.readReg64 .x21 = sp + 11856#64)
    (hv3 : s.readVReg128 3#5 = 0#128) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E2) s
      (((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
       memRegion (sp + 11856#64) 512 ∗
       PolyMem (sp + 20704#64) z0 ∗ PolyMem (sp + 21216#64) z1 ∗ PolyMem (sp + 21728#64) z2 ∗
       Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ memRegion (sp + 22400#64) 384 ∗ memRegion (sp + 11856#64) 512 ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗ Rest)) := by
  intro prf3 prf4 prf5
  have h3 : prf3.length = 128 := shake256List_length 128 _
  have h4 : prf4.length = 128 := shake256List_length 128 _
  have h5 : prf5.length = 128 := shake256List_length 128 _
  have ha_22528 : sp + 22400#64 + 128#64 = sp + 22528#64 := by clear * -; bv_omega
  have ha_22656 : sp + 22400#64 + 256#64 = sp + 22656#64 := by clear * -; bv_omega
  have ha_21216 : sp + 20704#64 + 512#64 = sp + 21216#64 := by clear * -; bv_omega
  have ha_21728 : sp + 20704#64 + 1024#64 = sp + 21728#64 := by clear * -; bv_omega
  refine SepWP.weaken_pre
    (P' := ((sp + 22400#64 + 0#64) ↦ₛ prf3) ∗ memRegion (sp + 11856#64) 512 ∗
      PolyMem (sp + 20704#64 + 0#64) z0 ∗
      (((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
        PolyMem (sp + 21216#64) z1 ∗ PolyMem (sp + 21728#64) z2 ∗ Rest))
    (by simp only [BitVec.add_zero]; sep_frame) ?_
  refine SepWP.seq
    (seg6c_e1_iter hb hbase s sp (idx := 0) (by decide) prf3 h3 z0 _
      hpc hrun hsp hspA hx8 (by simpa using hx9) hx19 hx20 hx21) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, rfp1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hv3_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show (((sp + 22400#64 + 0#64) ↦ₛ prf3) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64 + 0#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
        (((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
          PolyMem (sp + 21216#64) z1 ∗ PolyMem (sp + 21728#64) z2 ∗ Rest)) ⊢
      ((sp + 22400#64 + 128#64) ↦ₛ prf4) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64 + 512#64) z1 ∗
        (((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21728#64) z2 ∗ Rest) by
      simp only [BitVec.add_zero, ha_22528, ha_21216]; sep_frame)) ?_
  refine SepWP.seq
    (seg6c_e1_iter hb hbase s1 sp (idx := 1) (by decide) prf4 h4 z1 _
      (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, rfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hv3_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2
    (show (((sp + 22400#64 + 128#64) ↦ₛ prf4) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64 + 512#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
        (((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21728#64) z2 ∗ Rest)) ⊢
      ((sp + 22400#64 + 256#64) ↦ₛ prf5) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64 + 1024#64) z2 ∗
        (((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗ Rest) by
      simp only [ha_22528, ha_22656, ha_21216, ha_21728]; sep_frame)) ?_
  refine SepWP.seq
    (seg6c_e1_iter hb hbase s2 sp (idx := 2) (by decide) prf5 h5 z2 _
      (by simpa using hpc2) hrun2 hsp2 hspA2 hx8_2 hx9_2 hx19_2 hx20_2 hx21_2) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, rfpf, _, _, hx19f, _, _, hv3f, hPf⟩
  refine SepWP.done (by simpa using hpcf) hrunf
    ⟨hspf, hspAf, rfpf.trans (rfp2.trans rfp1), hx19f, hv3f.trans (hv3_2.trans (hv3_1.trans hv3)), Entails.trans hPf ?_⟩
  simp only [ha_22656, ha_21728]
  have hm384 : ((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ⊢
      memRegion (sp + 22400#64) 384 := by
    rw [memRegion_split' (b' := sp + 22528#64) (n := 128) (k := (256 : Nat)) rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b' := sp + 22656#64) (n := 128) (k := (128 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono (by simpa [h3] using pointsToBytes_entails_memRegion (sp + 22400#64) prf3)
      (sepConj_mono (by simpa [h4] using pointsToBytes_entails_memRegion (sp + 22528#64) prf4)
        (by simpa [h5] using pointsToBytes_entails_memRegion (sp + 22656#64) prf5))
  exact entails_sub hm384 (by sep_frame) (by sep_frame)

/-- Full `e1[0..2]` sub-segment (`+0x85d8 → +0x89f0`). -/
theorem seg6c_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6E1Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg6E2) s
      (((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 20704#64) 1536 ∗
       memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 384 ∗
       memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
       memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 19120#64) ↦ₛ coins) ∗
          memRegion (sp + 11856#64) 512 ∗
          PolyMem (sp + 20704#64) (polyVecNat (neonCbd2Poly16 prf3)) ∗
          PolyMem (sp + 21216#64) (polyVecNat (neonCbd2Poly16 prf4)) ∗
          PolyMem (sp + 21728#64) (polyVecNat (neonCbd2Poly16 prf5)) ∗
          memRegion (sp + 22240#64) 99 ∗ memRegion (sp + 22400#64) 384 ∗
          memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
  intro prf3 prf4 prf5
  refine sepWP_seq_env hcl hro
    (seg6c_prf_setup hb hbase s sp coins Rest hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hv3_1, _, _, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1
    (show (((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21728#64) (fun _ => 0#128) ∗
        memRegion (sp + 22240#64) 99 ∗
        ((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
        memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
        memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest) ⊢
      ((sp + 22400#64) ↦ₛ prf3) ∗ ((sp + 22528#64) ↦ₛ prf4) ∗ ((sp + 22656#64) ↦ₛ prf5) ∗
        memRegion (sp + 11856#64) 512 ∗
        PolyMem (sp + 20704#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21216#64) (fun _ => 0#128) ∗
        PolyMem (sp + 21728#64) (fun _ => 0#128) ∗
        (((sp + 19120#64) ↦ₛ coins) ∗ memRegion (sp + 22240#64) 99 ∗
          memRegion (sp + 24448#64) 128 ∗ memRegion (sp + 24976#64) 128 ∗
          memRegion (sp + 25296#64) 128 ∗ stackAt sp 1136 ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6c_e1_ok hb hbase s1 sp coins _ _ _ _ hpc1 hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 hx21_1 hv3_1) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, rfpf, hx19f, hv3f, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, rfpf.trans hfp1, hx19f, hv3f, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6c
