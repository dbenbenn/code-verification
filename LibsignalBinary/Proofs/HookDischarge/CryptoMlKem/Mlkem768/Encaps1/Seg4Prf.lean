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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd

/-!
# `encapsulate1_serialized` (`B03`) — Segment 4a PRF Setup (`+0x4728 .. +0x4938`)

Zeroes `e1[0..2]` (`1536` B at `sp + 13984`), stages `coins ++ [3#8..5#8]` at `sp + 15520..15619`,
invokes `B01` (`RW2` + `RW1`) for `prf3..5`, and copies `prf3..5` to `[sp + 2192, sp + 2576)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4Prf

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec keccak2_136_31_RW2Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  pointsToBytes_eq_vecRangeMem step_ldrQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  blkPl03_ρ cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  exec_simdMovi_2d_0 orr_1_of_aligned16 sepWP_elim_byte setMem_setMem setPC_setMem_setPC
  shake256List_length stage_prf33_eq vec2_bytesToVecNat_eq vecRangeBytes_zero)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x4728 → 0x4938]
end

attribute [local irreducible] shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] abbrev offSeg4Start : BitVec 64 := BitVec.ofNat 64 18216
@[simp, arm64_norm, wp_norm] abbrev off4744      : BitVec 64 := BitVec.ofNat 64 18244
@[simp, arm64_norm, wp_norm] abbrev off4834      : BitVec 64 := BitVec.ofNat 64 18484
@[simp, arm64_norm, wp_norm] abbrev off4838      : BitVec 64 := BitVec.ofNat 64 18488
@[simp, arm64_norm, wp_norm] abbrev off486c      : BitVec 64 := BitVec.ofNat 64 18540
@[simp, arm64_norm, wp_norm] abbrev offSeg4E1    : BitVec 64 := BitVec.ofNat 64 18744

private theorem le_128_pow64 : 128 ≤ 2 ^ 64 := by decide

private theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  exact cells32_entails_memRegion sPtr _ _ _ _

private theorem aligned16_add2192 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 2192#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 2192#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

/-! ## 1. Zero `e1[0..2]` at `[sp + 13984, sp + 15520)` (`+0x4728 → +0x4744`) -/

theorem seg4_memset_e1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg4Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4744) s
      (memRegion (sp + 13984#64) 1536 ∗ stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 13984#64 ∧
        (Pm ⊢ PolyMem (sp + 13984#64) (fun _ => 0#128) ∗
          PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
          PolyMem (sp + 15008#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  wp_steps 6
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 13984#64, 0#8, (1536 : Nat))
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      Eq.trans ‹_› hx19, Eq.trans ‹_› (by simp), ?_⟩
  have hz3 : ((sp + 13984#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 13984#64) (fun _ => 0#128) ∗
      PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
      PolyMem (sp + 15008#64) (fun _ => 0#128) := by
    have hrep : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, show (1536 : Nat) = 512 + (512 + 512) from rfl,
        List.replicate_add, List.replicate_add]
    rw [hrep, pointsToBytes_append, pointsToBytes_append,
      vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp [PolyMem,
      show sp + 13984#64 + BitVec.ofNat 64 (16 * 32) = sp + 14496#64 by bv_omega,
      show sp + 14496#64 + BitVec.ofNat 64 (16 * 32) = sp + 15008#64 by bv_omega]
  rw [hz3]
  sep_frame

/-! ## 2. `Seg4` PRF Stage & Calls (`+0x4744 → +0x486c`) -/

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

section
attribute [local irreducible] blkPC03

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg4_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off4744) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4834) s
      (((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 4272#64) 32 ∗
       memRegion (sp + 15520#64) 99 ∗
       memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 128 ∗
       memRegion (sp + 16528#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4272#64 ∧
        sm.readReg64 .x1 = sp + 16208#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 16528#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = sp + 4272#64 ∧
        sm.readReg64 .x22 = 33#64 ∧
        sm.readReg64 .x23 = sp + 15586#64 ∧
        (Pm ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 4272#64) (sp + 15520#64) (sp + 15553#64) 33 33 ∗
          ((sp + 15520#64) ↦ₛ (coins ++ [3#8])) ∗
          ((sp + 15553#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 15586#64) ↦ₛ (coins ++ [5#8])) ∗
          memRegion (sp + 15680#64) 128 ∗
          memRegion (sp + 16208#64) 128 ∗
          memRegion (sp + 16528#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 12400#64) hc]
  have h99 : memRegion (sp + 15520#64) 99 =
      memRegion (sp + 15520#64) 16 ∗ memRegion (sp + 15536#64) 16 ∗ memRegion (sp + 15552#64) 1 ∗
      memRegion (sp + 15553#64) 16 ∗ memRegion (sp + 15569#64) 16 ∗ memRegion (sp + 15585#64) 1 ∗
      memRegion (sp + 15586#64) 16 ∗ memRegion (sp + 15602#64) 16 ∗ memRegion (sp + 15618#64) 1 := by
    rw [memRegion_split' (b' := sp + 15536#64) (n := 16) (k := (83 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15552#64) (n := 16) (k := (67 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15553#64) (n := 1)  (k := (66 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15569#64) (n := 16) (k := (50 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15585#64) (n := 16) (k := (34 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15586#64) (n := 1)  (k := (33 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15602#64) (n := 16) (k := (17 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 15618#64) (n := 16) (k := (1 : Nat))  rfl (by bv_omega) (by decide)]
  rw [h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15520#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15536#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15553#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15569#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15586#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 15602#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 15552#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 15585#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 15618#64)); intro c2
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4272#64)); intro k0 k1 k2 k3
  simp only [show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
    show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
    show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega]
  have _ := hpc
  wp_step
  refine step_ldrQ128 (wb := none) (ea := sp + 12400#64) (v := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := (sp + 12400#64) + 16#64) (v := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 4
  refine step_strQ128 (wb := none) (ea := sp + 15520#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 15553#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 15586#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 15569#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 15602#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 15536#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  step_dead_zero8 sp 16208
  step_dead_zero8 sp 16528
  step_dead_zero8 sp 15680
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 15520#64) 3#8 hc,
      ← stage_prf33_eq (sp + 15553#64) 4#8 hc,
      ← stage_prf33_eq (sp + 15586#64) 5#8 hc]
  unfold Keccak2SlicesRW
  simp only [show sp + 15520#64 + 16#64 = sp + 15536#64 by bv_omega,
    show sp + 15520#64 + 32#64 = sp + 15552#64 by bv_omega,
    show sp + 15553#64 + 16#64 = sp + 15569#64 by bv_omega,
    show sp + 15553#64 + 32#64 = sp + 15585#64 by bv_omega,
    show sp + 15586#64 + 16#64 = sp + 15602#64 by bv_omega,
    show sp + 15586#64 + 32#64 = sp + 15618#64 by bv_omega,
    show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
    show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
    show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 16208#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 16528#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 15680#64) _) (by sep_frame) (by sep_frame)))

private theorem seg4_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp p5 : BitVec 64) {l5 : Nat} (hl5 : l5 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off4838) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = 33#64) (hx23 : s.readReg64 .x23 = p5) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + BitVec.ofNat 64 18536) s
      (memRegion (sp + 2192#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 2192#64 ∧ sm.readReg64 .x1 = sp + 15680#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 4272#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp + 2192#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 2192#64) p5 p5 l5 l5 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 2192#64))
  intro d0 d1 d2 d3
  simp only [show sp + 2192#64 + 8#64 = sp + 2200#64 by bv_omega,
    show sp + 2192#64 + 16#64 = sp + 2208#64 by bv_omega,
    show sp + 2192#64 + 24#64 = sp + 2216#64 by bv_omega]
  wp_steps 12
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hl5, show sp + 2192#64 + 8#64 = sp + 2200#64 by bv_omega,
    show sp + 2192#64 + 16#64 = sp + 2208#64 by bv_omega,
    show sp + 2192#64 + 24#64 = sp + 2216#64 by bv_omega]
  sep_frame

end

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem seg4_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off4744) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off486c) s
      (((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 2192#64) 32 ∗
       memRegion (sp + 4272#64) 128 ∗
       memRegion (sp + 15520#64) 99 ∗
       memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 128 ∗
       memRegion (sp + 16528#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 13984#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readReg64 .x22 = sp + 2192#64 ∧
        (Pf ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          memRegion (sp + 2192#64) 32 ∗
          memRegion (sp + 4272#64) 128 ∗
          memRegion (sp + 15520#64) 99 ∗
          ((sp + 15680#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
          ((sp + 16208#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
          ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 4272#64) (b' := sp + 4304#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 4272#64) 32 ∗
      memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗
      (memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 4304#64) 96 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4_prf_stage hb rfl s sp coins _ hc hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc3_len : (coins ++ [3#8]).length = 33 := by simp [hc]
  have hc4_len : (coins ++ [4#8]).length = 33 := by simp [hc]
  have hc5_len : (coins ++ [5#8]).length = 33 := by simp [hc]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC03.rebase blkPl03.base (fun _ => none))
      (blkPl03.base + off4838) s1
      (((sp + 12400#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 4272#64) (sp + 15520#64) (sp + 15553#64) 33 33 ∗
        ((sp + 15520#64) ↦ₛ (coins ++ [3#8])) ∗
        ((sp + 15553#64) ↦ₛ (coins ++ [4#8])) ∗
        ((sp + 15586#64) ↦ₛ (coins ++ [5#8])) ∗
        memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16208#64) 128 ∗
        memRegion (sp + 16528#64) 128 ∗
        (memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 4304#64) 96 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 13984#64 ∧
        s2.readReg64 .x21 = sp + 4272#64 ∧ s2.readReg64 .x22 = 33#64 ∧
        s2.readReg64 .x23 = sp + 15586#64 ∧
        (P2 ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          memRegion (sp + 2192#64) 32 ∗
          memRegion (sp + 4272#64) 128 ∗
          ((sp + 15520#64) ↦ₛ (coins ++ [3#8])) ∗
          ((sp + 15553#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 15586#64) ↦ₛ (coins ++ [5#8])) ∗
          memRegion (sp + 15680#64) 128 ∗
          ((sp + 16208#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
          ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [show Keccak2SlicesRW (sp + 4272#64) (sp + 15520#64) (sp + 15553#64) 33 33 =
          Keccak2SlicesRW (sp + 4272#64) (sp + 15520#64) (sp + 15553#64)
            (coins ++ [3#8]).length (coins ++ [4#8]).length from by rw [hc3_len, hc4_len]]
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk01_keccak2_136_31_RW2_ok
      (⟨sp + 4272#64, sp + 15520#64, sp + 15553#64, sp + 16208#64, sp + 16528#64,
        (128 : Nat), coins ++ [3#8], coins ++ [4#8]⟩ : Keccak2ShakeArgs)
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› (hx19_1.trans hx19), Eq.trans ‹_› (hx20_1.trans hx20),
        Eq.trans ‹_› hx21_1, Eq.trans ‹_› hx22_1, Eq.trans ‹_› hx23_1, ?_⟩
    rw [hsp1]
    have hk4272 : Keccak2SlicesRW (sp + 4272#64) (sp + 15520#64) (sp + 15553#64)
          (coins ++ [3#8]).length (coins ++ [4#8]).length ∗
        memRegion (sp + 4304#64) 96 ⊢ memRegion (sp + 4272#64) 128 := by
      rw [memRegion_split' (b := sp + 4272#64) (b' := sp + 4304#64) (n := 32) (k := (96 : Nat))
            rfl (by bv_omega) (by decide)]
      exact sepConj_mono (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (Entails.refl _)
    exact entails_sub hk4272 (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 2192#64) 32 ∗ (((sp + 12400#64) ↦ₛ coins) ∗
      memRegion (sp + 4272#64) 128 ∗ ((sp + 15520#64) ↦ₛ (coins ++ [3#8])) ∗
      ((sp + 15553#64) ↦ₛ (coins ++ [4#8])) ∗ ((sp + 15586#64) ↦ₛ (coins ++ [5#8])) ∗
      memRegion (sp + 15680#64) 128 ∗
      ((sp + 16208#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
      ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg4_prf_stage2 hb rfl s2 sp (sp + 15586#64) hc5_len _ hpc2 hrun2 hsp2 hspA2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk01_keccak2_136_31_RW1_ok
    (sp + 2192#64, sp + 15586#64, sp + 15680#64, sp + 4272#64, (128 : Nat), coins ++ [5#8])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› (hx19_3.trans hx19_2), Eq.trans ‹_› (hx20_3.trans hx20_2),
      Eq.trans ‹_› (hx21_3.trans hx21_2), Eq.trans ‹_› hx22_3, ?_⟩
  rw [hsp3]
  have hm4272 : ((sp + 4272#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ⊢
      memRegion (sp + 4272#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 4272#64) (shake256List 128 (coins ++ [5#8]))
  have hm99 : ((sp + 15520#64) ↦ₛ (coins ++ [3#8])) ∗
      ((sp + 15553#64) ↦ₛ (coins ++ [4#8])) ∗
      ((sp + 15586#64) ↦ₛ (coins ++ [5#8])) ⊢ memRegion (sp + 15520#64) 99 := by
    rw [memRegion_split' (b := sp + 15520#64) (b' := sp + 15553#64) (n := 33) (k := (66 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 15553#64) (b' := sp + 15586#64) (n := 33) (k := (33 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by simpa [hc3_len] using pointsToBytes_entails_memRegion (sp + 15520#64) (coins ++ [3#8]))
      (sepConj_mono
        (by simpa [hc4_len] using pointsToBytes_entails_memRegion (sp + 15553#64) (coins ++ [4#8]))
        (by simpa [hc5_len] using pointsToBytes_entails_memRegion (sp + 15586#64) (coins ++ [5#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm4272 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))

/-! ## 3. Copy `prf3..5` to `[sp + 2192, sp + 2576)` (`+0x486c → +0x4938`) -/

attribute [local irreducible] blkPC03

@[simp, arm64_norm, wp_norm] private abbrev off48c4 : BitVec 64 := BitVec.ofNat 64 18628

local macro "ldr_p3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 16208#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p4 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 16528#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 15680#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "str_d0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 2192#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 2320#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 2448#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg4_copy_prfs_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (p3 p4 p5 d0 d1 d2 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off486c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hx22 : s.readReg64 .x22 = sp + 2192#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off48c4) s
      (Oct8Mem (sp + 16208#64) p3 ∗ Oct8Mem (sp + 16528#64) p4 ∗ Oct8Mem (sp + 15680#64) p5 ∗
       Oct8Mem (sp + 2192#64) d0 ∗ Oct8Mem (sp + 2320#64) d1 ∗ Oct8Mem (sp + 2448#64) d2 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x8 = 0#64 ∧ sm.readReg64 .x9 = sp + 2193#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧ sm.readReg64 .x20 = sp + 13984#64 ∧
        sm.readReg64 .x21 = sp + 4272#64 ∧
        sm.readVReg128 0#5 = p4.o5 ∧ sm.readVReg128 1#5 = p4.o4 ∧
        sm.readVReg128 2#5 = p4.o6 ∧ sm.readVReg128 3#5 = 0#128 ∧
        Pm = (Oct8Mem (sp + 16208#64) p3 ∗ Oct8Mem (sp + 16528#64) p4 ∗ Oct8Mem (sp + 15680#64) p5 ∗
          Oct8Mem (sp + 2192#64) p3 ∗ Oct8Mem (sp + 2320#64) d1 ∗ Oct8Mem (sp + 2448#64) d2 ∗ Rest)) := by
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
      by simp, by simp [orr_1_of_aligned16 _ (aligned16_add2192 sp hsp_chk)],
      by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [Oct8.get], by simp [Oct8.get], by simp [Oct8.get], by simp,
      by cases p3; cases d0; rfl⟩

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg4_copy_prfs_b [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (p3 p4 p5 d1 d2 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off48c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = sp + 2193#64)
    (hx19 : s.readReg64 .x19 = 0x55555555#64) (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hv0 : s.readVReg128 0#5 = p4.o5) (hv1 : s.readVReg128 1#5 = p4.o4)
    (hv2 : s.readVReg128 2#5 = p4.o6) (hv3 : s.readVReg128 3#5 = 0#128) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E1) s
      (Oct8Mem (sp + 16208#64) p3 ∗ Oct8Mem (sp + 16528#64) p4 ∗ Oct8Mem (sp + 15680#64) p5 ∗
       Oct8Mem (sp + 2192#64) p3 ∗ Oct8Mem (sp + 2320#64) d1 ∗ Oct8Mem (sp + 2448#64) d2 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 2193#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 13984#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        Pf = (Oct8Mem (sp + 16208#64) p3 ∗ Oct8Mem (sp + 16528#64) p4 ∗ Oct8Mem (sp + 15680#64) p5 ∗
          Oct8Mem (sp + 2192#64) p3 ∗ Oct8Mem (sp + 2320#64) p4 ∗ Oct8Mem (sp + 2448#64) p5 ∗ Rest)) := by
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
      by simp [hx8], by simp [hx9], by simp [hx19], by simp [hx20], by simp [hx21],
      by simp [hv3], by cases p4; cases p5; cases d1; cases d2; simp [Oct8.get]⟩

theorem seg4_copy_prfs [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (prf3 prf4 prf5 : List (BitVec 8)) (Rest : SepProp)
    (h3 : prf3.length = 128) (h4 : prf4.length = 128) (h5 : prf5.length = 128)
    (hpc : s.pc = b + off486c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 13984#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hx22 : s.readReg64 .x22 = sp + 2192#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E1) s
      (((sp + 16208#64) ↦ₛ prf3) ∗ ((sp + 16528#64) ↦ₛ prf4) ∗ ((sp + 15680#64) ↦ₛ prf5) ∗
       memRegion (sp + 2192#64) 384 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 2193#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 13984#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ ((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
          memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 128 ∗
          memRegion (sp + 16528#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 16208#64) h3,
      pointsToBytes128_eq_oct8Mem (sp + 16528#64) h4,
      pointsToBytes128_eq_oct8Mem (sp + 15680#64) h5,
      memRegion_split' (b := sp + 2192#64) (b' := sp + 2320#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2320#64) (b' := sp + 2448#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2192#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2320#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2448#64) (hf := by sep_focus); intro fd2
  rw [show VecRangeMem 8 (sp + 2192#64) fd0 = Oct8Mem (sp + 2192#64) (Oct8.ofFn fd0) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 2320#64) fd1 = Oct8Mem (sp + 2320#64) (Oct8.ofFn fd1) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 2448#64) fd2 = Oct8Mem (sp + 2448#64) (Oct8.ofFn fd2) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 16208#64) (Oct8.ofFn (bytesToVecNat prf3)) ∗
      Oct8Mem (sp + 16528#64) (Oct8.ofFn (bytesToVecNat prf4)) ∗
      Oct8Mem (sp + 15680#64) (Oct8.ofFn (bytesToVecNat prf5)) ∗
      Oct8Mem (sp + 2192#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 2320#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 2448#64) (Oct8.ofFn fd2) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (seg4_copy_prfs_a hb hbase s sp _ _ _ _ _ _ Rest hpc hrun hsp hspA hx19 hx20 hx21 hx22)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hx8m, hx9m, hx19m, hx20m, hx21m, hv0m, hv1m, hv2m, hv3m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (seg4_copy_prfs_b hb hbase sm sp _ _ _ _ _ Rest hpcm hrunm hspm hspAm
        hx8m hx9m hx19m hx20m hx21m hv0m hv1m hv2m hv3m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, rv3, ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 2192#64) h3,
      ← pointsToBytes128_eq_oct8Mem (sp + 2320#64) h4,
      ← pointsToBytes128_eq_oct8Mem (sp + 2448#64) h5]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 16208#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 16528#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 15680#64) _) (by sep_frame) (by sep_frame)))

theorem seg4_prf_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg4Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf3 := shake256List 128 (coins ++ [3#8])
    let prf4 := shake256List 128 (coins ++ [4#8])
    let prf5 := shake256List 128 (coins ++ [5#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg4E1) s
      (((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 4272#64) 512 ∗
       memRegion (sp + 13984#64) 1536 ∗ memRegion (sp + 15520#64) 99 ∗
       memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 128 ∗
       memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧ sf.readReg64 .x9 = sp + 2193#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧ sf.readReg64 .x20 = sp + 13984#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = 0#128 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          ((sp + 2192#64) ↦ₛ prf3) ∗ ((sp + 2320#64) ↦ₛ prf4) ∗ ((sp + 2448#64) ↦ₛ prf5) ∗
          memRegion (sp + 4272#64) 512 ∗
          PolyMem (sp + 13984#64) (fun _ => 0#128) ∗
          PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
          PolyMem (sp + 15008#64) (fun _ => 0#128) ∗
          memRegion (sp + 15520#64) 99 ∗ memRegion (sp + 15680#64) 128 ∗
          memRegion (sp + 16208#64) 128 ∗ memRegion (sp + 16528#64) 128 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf3 prf4 prf5
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 13984#64) 1536 ∗ stackAt sp 1136 ∗
      (((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 2192#64) 384 ∗
        memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 99 ∗
        memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 128 ∗
        memRegion (sp + 16528#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4_memset_e1 hb hbase s sp _ hpc hrun hsp hspA hx19 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [memRegion_split' (b := sp + 2192#64) (b' := sp + 2224#64) (n := 32) (k := (352 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4272#64) (b' := sp + 4400#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 2192#64) 32 ∗
      memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 15520#64) 99 ∗
      memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 128 ∗
      memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 2224#64) 352 ∗ memRegion (sp + 4400#64) 384 ∗
        PolyMem (sp + 13984#64) (fun _ => 0#128) ∗
        PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
        PolyMem (sp + 15008#64) (fun _ => 0#128) ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg4_prf_calls hb hbase s1 sp coins _ hc hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hcl1 hro1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm384 : memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 2224#64) 352 =
      memRegion (sp + 2192#64) 384 :=
    (memRegion_split' (b := sp + 2192#64) (b' := sp + 2224#64) (n := 32) (k := (352 : Nat))
      rfl (by bv_omega) (by decide)).symm
  have hm512 : memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 4400#64) 384 =
      memRegion (sp + 4272#64) 512 :=
    (memRegion_split' (b := sp + 4272#64) (b' := sp + 4400#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 16208#64) ↦ₛ prf3) ∗ ((sp + 16528#64) ↦ₛ prf4) ∗ ((sp + 15680#64) ↦ₛ prf5) ∗
      memRegion (sp + 2192#64) 384 ∗
      (((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 4272#64) 512 ∗
        PolyMem (sp + 13984#64) (fun _ => 0#128) ∗
        PolyMem (sp + 14496#64) (fun _ => 0#128) ∗
        PolyMem (sp + 15008#64) (fun _ => 0#128) ∗
        memRegion (sp + 15520#64) 99 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm384) (by sep_frame)
      (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame))) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg4_copy_prfs hb hbase s2 sp prf3 prf4 prf5 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, r8, r9, r19, r20, r21, rv3, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, r8, r9, r19, r20, r21, rv3, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4Prf
