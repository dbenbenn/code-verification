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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 `e1[0..3]` PRF Setup (`+0x8bd8 .. +0x8e64`)

1. `seg6_memset_e1` (`+0x8bd8 → +0x8bf4`): zeroes `e1[0..3]` (`2048` B) at `[sp + 28368, sp + 30416)`.
2. `seg6_e1_prf_calls` (`+0x8bf4 → +0x8d58`): stages `coins ++ [4..7#8]` at `[sp + 33008, sp + 33140)`
   and calls `B01` (`RW2` twice) to compute `prf4..7 = shake256List 128 (coins ++ [4..7#8])`.
3. `seg6_e1_copy_prf` (`+0x8d58 → +0x8e64`): copies `prf4..7` to `[sp + 30448, sp + 30960)` and
   initializes `v3 = 0`, `x8 = 0`, `x9 = sp + 30449`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Prf
open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemBlockPlacement_ρ mlkemCall_of_blockOk mlkemMpl
  resolve_blk01 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW2Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  pointsToBytes_eq_vecRangeMem step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  exec_simdMovi_2d_0 orr_1_of_aligned16 sepWP_elim_byte setMem_setMem setPC_setMem_setPC
  shake256List_length stage_prf33_eq vec2_bytesToVecNat_eq)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x8bd8 → 0x8e60]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

private theorem blk01_rw2_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW2Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk01_keccak2_136_31_RW2_ok

private theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC06 shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Setup : BitVec 64 := BitVec.ofNat 64 35800
@[simp, arm64_norm, wp_norm] abbrev off8bf4        : BitVec 64 := BitVec.ofNat 64 35828
@[simp, arm64_norm, wp_norm] private abbrev off8d10 : BitVec 64 := BitVec.ofNat 64 36112
@[simp, arm64_norm, wp_norm] private abbrev off8d14 : BitVec 64 := BitVec.ofNat 64 36116
@[simp, arm64_norm, wp_norm] abbrev off8d58        : BitVec 64 := BitVec.ofNat 64 36184
@[simp, arm64_norm, wp_norm] abbrev offSeg6E1Loop  : BitVec 64 := BitVec.ofNat 64 36452
private theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  exact cells32_entails_memRegion sPtr _ _ _ _

private theorem aligned16_add30448 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 30448#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 30448#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

private theorem vecRangeBytes_zero : ∀ n : Nat,
    vecRangeBytes n (fun _ => 0#128) = List.replicate (16 * n) (0#8)
  | 0 => rfl
  | n + 1 => by
    rw [vecRangeBytes, vecRangeBytes_zero n, show 16 * (n + 1) = 16 + 16 * n by omega,
      List.replicate_add]
    rfl

/-! ## 1. Zero `e1[0..3]` at `[sp + 28368, sp + 30416)` (`+0x8bd8 → +0x8bf4`) -/

theorem seg6_memset_e1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6E1Setup) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off8bf4) s
      (memRegion (sp + 28368#64) 2048 ∗ stackAt sp 1136 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 28368#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ PolyMem (sp + 28368#64) (fun _ => 0#128) ∗
          PolyMem (sp + 28880#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29392#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29904#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := hb
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s.mem := hcl
  wp_steps 6
  have h2048 : (2048 : Nat) ≤ 2 ^ 64 := by decide
  wp_call (blk29_memset_06 blkPl06.base) (sp + 28368#64, 0#8, (2048 : Nat))
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_sp_eq hspA hsp hsp_sf,
      by simp [*], by simp [*], by simp [*], ?_⟩
  have hz4 : ((sp + 28368#64) ↦ₛ List.replicate 2048 0#8) =
      PolyMem (sp + 28368#64) (fun _ => 0#128) ∗
      PolyMem (sp + 28880#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29392#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29904#64) (fun _ => 0#128) := by
    have hrep : List.replicate 2048 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
        (vecRangeBytes 32 (fun _ => 0#128) ++
         (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128))) := by
      rw [vecRangeBytes_zero 32, show (2048 : Nat) = 512 + (512 + (512 + 512)) from rfl,
        List.replicate_add, List.replicate_add, List.replicate_add]
    unfold PolyMem
    rw [hrep, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp only [
      show sp + 28368#64 + BitVec.ofNat 64 (16 * 32) = sp + 28880#64 by bv_omega,
      show sp + 28880#64 + BitVec.ofNat 64 (16 * 32) = sp + 29392#64 by bv_omega,
      show sp + 29392#64 + BitVec.ofNat 64 (16 * 32) = sp + 29904#64 by bv_omega]
  rw [hz4]
  sep_frame

/-! ## 2. `e1[0..3]` PRF Stage & Calls (`+0x8bf4 → +0x8d58`) -/

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

local syntax "find_store128" : tactic
local macro_rules
  | `(tactic| find_store128) => `(tactic| first
      | (with_reducible apply SepStore128.vec128At; with_reducible rfl)
      | (with_reducible apply SepStore128.left; find_store128)
      | (with_reducible apply SepStore128.right; find_store128))

local syntax "find_store8" : tactic
local macro_rules
  | `(tactic| find_store8) => `(tactic| first
      | (with_reducible apply SepStore8.here; with_reducible rfl)
      | (with_reducible apply SepStore8.left; find_store8)
      | (with_reducible apply SepStore8.right; find_store8))
local macro "step_strb_sp " eaTerm:term:arg valTerm:term:arg hrunId:term:arg hspId:term:arg : tactic => `(tactic| (
  apply SepWP.step_str8 (wb := none) (ea := $eaTerm) (val := $valTerm)
  · wp_norm_lhs
  · simp [$hrunId:term]
  · wp_norm_lhs
  · rfl
  · simp [evalAddrMode, $hspId:term]; try bv_omega
  · rfl
  · find_store8
  · wp_norm_lhs
  intro _
  (try rw [setPC_setMem_setPC]); (try rw [setMem_setMem]); (try rw [setPC_setMem_collapse])))

private theorem seg6_e1_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {coins : List (BitVec 8)} (hc : coins.length = 32)
    (Rest : SepProp)
    (hpc : s.pc = b + off8bf4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off8d10) s
      (((sp + 26272#64) ↦ₛ coins) ∗
       memRegion (sp + 33008#64) 132 ∗
       memRegion (sp + 30448#64) 32 ∗
       memRegion (sp + 14432#64) 128 ∗
       memRegion (sp + 34464#64) 128 ∗
       memRegion (sp + 33536#64) 128 ∗
       memRegion (sp + 33888#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 30448#64 ∧
        sm.readReg64 .x1 = sp + 34464#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 33536#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = 33#64 ∧
        sm.readReg64 .x22 = sp + 33074#64 ∧
        sm.readReg64 .x23 = sp + 33107#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 30448#64) (sp + 33008#64) (sp + 33041#64) 33 33 ∗
          ((sp + 33008#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 33041#64) ↦ₛ (coins ++ [5#8])) ∗
          ((sp + 33074#64) ↦ₛ (coins ++ [6#8])) ∗
          ((sp + 33107#64) ↦ₛ (coins ++ [7#8])) ∗
          memRegion (sp + 14432#64) 128 ∗
          memRegion (sp + 34464#64) 128 ∗
          memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := _hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 26272#64) hc]
  have h132 : memRegion (sp + 33008#64) 132 =
      memRegion (sp + 33008#64) 16 ∗ memRegion (sp + 33024#64) 16 ∗ memRegion (sp + 33040#64) 1 ∗
      memRegion (sp + 33041#64) 16 ∗ memRegion (sp + 33057#64) 16 ∗ memRegion (sp + 33073#64) 1 ∗
      memRegion (sp + 33074#64) 16 ∗ memRegion (sp + 33090#64) 16 ∗ memRegion (sp + 33106#64) 1 ∗
      memRegion (sp + 33107#64) 16 ∗ memRegion (sp + 33123#64) 16 ∗ memRegion (sp + 33139#64) 1 := by
    rw [memRegion_split' (b' := sp + 33024#64) (n := 16) (k := (116 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33040#64) (n := 16) (k := (100 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33041#64) (n := 1)  (k := (99 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33057#64) (n := 16) (k := (83 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33073#64) (n := 16) (k := (67 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33074#64) (n := 1)  (k := (66 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33090#64) (n := 16) (k := (50 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33106#64) (n := 16) (k := (34 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33107#64) (n := 1)  (k := (33 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33123#64) (n := 16) (k := (17 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 33139#64) (n := 16) (k := (1 : Nat))   rfl (by bv_omega) (by decide)]
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := sp + 26272#64) (v := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (SepLoad128.left (SepLoad128.left (SepLoad128.vec128At rfl)))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ldrQ128 (wb := none) (ea := (sp + 26272#64) + 16#64) (v := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.right (SepLoad128.vec128At rfl))) (by wp_norm_lhs) ?_
  rw [h132]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33008#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33024#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33041#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33057#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33074#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33090#64) (by decide) (by sep_focus); intro v2b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33107#64) (by decide) (by sep_focus); intro v3a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 33123#64) (by decide) (by sep_focus); intro v3b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 33040#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 33073#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 33106#64)); intro c2
  sep_frame_apply (sepWP_elim_byte (a := sp + 33139#64)); intro c3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 30448#64)); intro k0 k1 k2 k3
  simp only [sepConj_assoc,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  wp_step
  step_strb_sp (sp + 33040#64) 4#8 hrun hsp
  wp_steps 2
  step_strb_sp (sp + 33073#64) 5#8 hrun hsp
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33008#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33041#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33074#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33107#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  step_strb_sp (sp + 33106#64) 6#8 hrun hsp
  wp_step
  step_strb_sp (sp + 33139#64) 7#8 hrun hsp
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33057#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  refine step_strQ128 (wb := none) (ea := sp + 33090#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 33123#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 33024#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  step_dead_zero8 sp 14432
  step_dead_zero8 sp 34464
  step_dead_zero8 sp 33536
  step_dead_zero8 sp 33888
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 33008#64) 4#8 hc,
      ← stage_prf33_eq (sp + 33041#64) 5#8 hc,
      ← stage_prf33_eq (sp + 33074#64) 6#8 hc,
      ← stage_prf33_eq (sp + 33107#64) 7#8 hc]
  unfold Keccak2SlicesRW
  simp only [
    show sp + 33008#64 + 16#64 = sp + 33024#64 by bv_omega,
    show sp + 33008#64 + 32#64 = sp + 33040#64 by bv_omega,
    show sp + 33041#64 + 16#64 = sp + 33057#64 by bv_omega,
    show sp + 33041#64 + 32#64 = sp + 33073#64 by bv_omega,
    show sp + 33074#64 + 16#64 = sp + 33090#64 by bv_omega,
    show sp + 33074#64 + 32#64 = sp + 33106#64 by bv_omega,
    show sp + 33107#64 + 16#64 = sp + 33123#64 by bv_omega,
    show sp + 33107#64 + 32#64 = sp + 33139#64 by bv_omega,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 14432#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 34464#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 33536#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 33888#64) _) (by sep_frame) (by sep_frame))))

private theorem seg6_e1_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp p2 p3 : BitVec 64) {l2 l3 : Nat}
    (hl2 : l2 = 33) (hl3 : l3 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off8d14) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = 33#64)
    (hx22 : s.readReg64 .x22 = p2) (hx23 : s.readReg64 .x23 = p3) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + BitVec.ofNat 64 36180) s
      (memRegion (sp + 30448#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 30448#64 ∧ sm.readReg64 .x1 = sp + 33888#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 14432#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = sp + 14432#64 ∧
        sm.readReg64 .x22 = sp + 30448#64 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 30448#64) p2 p3 l2 l3 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := _hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 30448#64))
  intro d0 d1 d2 d3
  simp only [show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  wp_steps 16
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hl2, hl3,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  sep_frame
private theorem stage4_e1_entails_memRegion132 (sp : BitVec 64) {coins : List (BitVec 8)}
    (hc : coins.length = 32) :
    ((sp + 33008#64) ↦ₛ (coins ++ [4#8])) ∗
    ((sp + 33041#64) ↦ₛ (coins ++ [5#8])) ∗
    ((sp + 33074#64) ↦ₛ (coins ++ [6#8])) ∗
    ((sp + 33107#64) ↦ₛ (coins ++ [7#8])) ⊢ memRegion (sp + 33008#64) 132 := by
  have hc4_len : (coins ++ [4#8]).length = 33 := by simp [hc]
  have hc5_len : (coins ++ [5#8]).length = 33 := by simp [hc]
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  have hc7_len : (coins ++ [7#8]).length = 33 := by simp [hc]
  rw [memRegion_split' (b' := sp + 33041#64) (n := 33) (k := (99 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 33074#64) (n := 33) (k := (66 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 33107#64) (n := 33) (k := (33 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (by simpa [hc4_len] using pointsToBytes_entails_memRegion (sp + 33008#64) (coins ++ [4#8]))
    (sepConj_mono (by simpa [hc5_len] using pointsToBytes_entails_memRegion (sp + 33041#64) (coins ++ [5#8]))
      (sepConj_mono (by simpa [hc6_len] using pointsToBytes_entails_memRegion (sp + 33074#64) (coins ++ [6#8]))
        (by simpa [hc7_len] using pointsToBytes_entails_memRegion (sp + 33107#64) (coins ++ [7#8]))))

theorem seg6_e1_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {coins : List (BitVec 8)} (hc : coins.length = 32)
    (Rest : SepProp)
    (hpc : s.pc = b + off8bf4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off8d58) s
      (((sp + 26272#64) ↦ₛ coins) ∗
       memRegion (sp + 33008#64) 132 ∗
       memRegion (sp + 30448#64) 32 ∗
       memRegion (sp + 14432#64) 128 ∗
       memRegion (sp + 34464#64) 128 ∗
       memRegion (sp + 33536#64) 128 ∗
       memRegion (sp + 33888#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 28368#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 30448#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          memRegion (sp + 33008#64) 132 ∗
          memRegion (sp + 30448#64) 32 ∗
          ((sp + 34464#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
          ((sp + 33888#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
          ((sp + 14432#64) ↦ₛ shake256List 128 (coins ++ [7#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := hb
  have hc4_len : (coins ++ [4#8]).length = 33 := by simp [hc]
  have hc5_len : (coins ++ [5#8]).length = 33 := by simp [hc]
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  have hc7_len : (coins ++ [7#8]).length = 33 := by simp [hc]
  refine sepWP_seq_env hcl hro
    (seg6_e1_prf_stage hb rfl s sp hc (stackAt sp 1136 ∗ Rest) hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hfp1, hP1⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have _ : MlKemRoOk mlkemMpl s1.mem := hro1
  refine SepWP.weaken_pre hP1 ?_
  have hstep_rw2a : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + off8d14) s1
      (((sp + 26272#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 30448#64) (sp + 33008#64) (sp + 33041#64) 33 33 ∗
        ((sp + 33008#64) ↦ₛ (coins ++ [4#8])) ∗
        ((sp + 33041#64) ↦ₛ (coins ++ [5#8])) ∗
        ((sp + 33074#64) ↦ₛ (coins ++ [6#8])) ∗
        ((sp + 33107#64) ↦ₛ (coins ++ [7#8])) ∗
        memRegion (sp + 14432#64) 128 ∗
        memRegion (sp + 34464#64) 128 ∗
        memRegion (sp + 33536#64) 128 ∗
        memRegion (sp + 33888#64) 128 ∗ (stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 28368#64 ∧
        s2.readReg64 .x21 = 33#64 ∧ s2.readReg64 .x22 = sp + 33074#64 ∧
        s2.readReg64 .x23 = sp + 33107#64 ∧ s2.readReg64 .fp = s.readReg64 .fp ∧
        (P2 ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          memRegion (sp + 30448#64) 32 ∗
          ((sp + 33008#64) ↦ₛ (coins ++ [4#8])) ∗
          ((sp + 33041#64) ↦ₛ (coins ++ [5#8])) ∗
          ((sp + 33074#64) ↦ₛ (coins ++ [6#8])) ∗
          ((sp + 33107#64) ↦ₛ (coins ++ [7#8])) ∗
          memRegion (sp + 14432#64) 128 ∗
          ((sp + 34464#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
          ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
          memRegion (sp + 33888#64) 128 ∗ stackAt sp 1136 ∗ Rest)) := by
    have hsl1 : Keccak2SlicesRW (sp + 30448#64) (sp + 33008#64) (sp + 33041#64) 33 33 =
        Keccak2SlicesRW (sp + 30448#64) (sp + 33008#64) (sp + 33041#64)
          (coins ++ [4#8]).length (coins ++ [5#8]).length := by
      rw [hc4_len, hc5_len]
    rw [hsl1]
    have hlen45 : (coins ++ [4#8]).length = (coins ++ [5#8]).length := by rw [hc4_len, hc5_len]
    have hlt4 : (coins ++ [4#8]).length < 2 ^ 32 := by rw [hc4_len]; decide
    have hout128 : (128 : Nat) = 32 ∨ (128 : Nat) = 128 := Or.inr rfl
    wp_call (blk01_rw2_06 blkPl06.base)
      (⟨sp + 30448#64, sp + 33008#64, sp + 33041#64, sp + 34464#64, sp + 33536#64,
        (128 : Nat), coins ++ [4#8], coins ++ [5#8]⟩ : Keccak2ShakeArgs)
    clear hcl hro hcl1 hro1
    have hsp_sf : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption)
      ⟨hsp_sf, spAligned_of_sp_eq hspA1 hsp1 hsp_sf,
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], ?_⟩
    rw [hsp1]
    exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2a ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 30448#64) 32 ∗
      (((sp + 26272#64) ↦ₛ coins) ∗
        ((sp + 33008#64) ↦ₛ (coins ++ [4#8])) ∗
        ((sp + 33041#64) ↦ₛ (coins ++ [5#8])) ∗
        ((sp + 33074#64) ↦ₛ (coins ++ [6#8])) ∗
        ((sp + 33107#64) ↦ₛ (coins ++ [7#8])) ∗
        memRegion (sp + 14432#64) 128 ∗
        ((sp + 34464#64) ↦ₛ shake256List 128 (coins ++ [4#8])) ∗
        ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [5#8])) ∗
        memRegion (sp + 33888#64) 128 ∗
        stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_e1_prf_stage2 hb rfl s2 sp (sp + 33074#64) (sp + 33107#64) hc6_len hc7_len _
      hpc2 hrun2 hsp2 hspA2 hx21_2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hfp3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  have _ := hpc3
  refine SepWP.weaken_pre hP3 ?_
  have hlen67 : (coins ++ [6#8]).length = (coins ++ [7#8]).length := by rw [hc6_len, hc7_len]
  have hlt6 : (coins ++ [6#8]).length < 2 ^ 32 := by rw [hc6_len]; decide
  have hout128 : (128 : Nat) = 32 ∨ (128 : Nat) = 128 := Or.inr rfl
  wp_call (blk01_rw2_06 blkPl06.base)
    (⟨sp + 30448#64, sp + 33074#64, sp + 33107#64, sp + 33888#64, sp + 14432#64,
      (128 : Nat), coins ++ [6#8], coins ++ [7#8]⟩ : Keccak2ShakeArgs)
  clear hcl hro hcl1 hro1 hcl2 hro2 hcl3 hro3 ‹mlkemMultiLib.CodeLoaded mlkemMpl s3.mem› ‹MlKemRoOk mlkemMpl s3.mem›
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_sp_eq hspA3 hsp3 hsp_sf,
      by simp [*], by simp [*],
      by simp [*], by simp [*], by simp [*], ?_⟩
  rw [hsp3]
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub (stage4_e1_entails_memRegion132 sp hc) (by sep_frame) (by sep_frame))
/-! ## 3. Copy `prf4..7` to `[sp + 30448, sp + 30960)` (`+0x8d58 → +0x8e64`) -/

local macro "ldr_p4 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 34464#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 33536#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 33888#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "ldr_p7 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 14432#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))))
    (by wp_norm_lhs) ?_))

local macro "str_d4 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30448#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d5 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30576#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))
local macro "str_d6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30704#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d7 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30832#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6_e1_copy_oct8 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (p4 p5 p6 p7 d4 d5 d6 d7 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off8d58) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 30448#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6E1Loop) s
      (Oct8Mem (sp + 34464#64) p4 ∗ Oct8Mem (sp + 33536#64) p5 ∗
       Oct8Mem (sp + 33888#64) p6 ∗ Oct8Mem (sp + 14432#64) p7 ∗
       Oct8Mem (sp + 30448#64) d4 ∗ Oct8Mem (sp + 30576#64) d5 ∗
       Oct8Mem (sp + 30704#64) d6 ∗ Oct8Mem (sp + 30832#64) d7 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 30449#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 28368#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 30448#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = 0#128 ∧
        Pf = (Oct8Mem (sp + 34464#64) p4 ∗ Oct8Mem (sp + 33536#64) p5 ∗
          Oct8Mem (sp + 33888#64) p6 ∗ Oct8Mem (sp + 14432#64) p7 ∗
          Oct8Mem (sp + 30448#64) p4 ∗ Oct8Mem (sp + 30576#64) p5 ∗
          Oct8Mem (sp + 30704#64) p6 ∗ Oct8Mem (sp + 30832#64) p7 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p4 4 hrun hsp hsp_chk; ldr_p4 5 hrun hsp hsp_chk; wp_step
  ldr_p4 7 hrun hsp hsp_chk; wp_steps 2
  str_d4 4 hrun hsp hsp_chk; ldr_p4 6 hrun hsp hsp_chk
  str_d4 5 hrun hsp hsp_chk; ldr_p4 0 hrun hsp hsp_chk
  str_d4 6 hrun hsp hsp_chk; ldr_p4 1 hrun hsp hsp_chk
  str_d4 7 hrun hsp hsp_chk; ldr_p4 2 hrun hsp hsp_chk
  str_d4 1 hrun hsp hsp_chk; ldr_p4 3 hrun hsp hsp_chk
  str_d4 0 hrun hsp hsp_chk; ldr_p5 4 hrun hsp hsp_chk
  str_d4 3 hrun hsp hsp_chk; ldr_p5 5 hrun hsp hsp_chk
  str_d4 2 hrun hsp hsp_chk; ldr_p5 6 hrun hsp hsp_chk
  str_d5 5 hrun hsp hsp_chk; ldr_p5 7 hrun hsp hsp_chk
  str_d5 4 hrun hsp hsp_chk; ldr_p5 0 hrun hsp hsp_chk
  str_d5 7 hrun hsp hsp_chk; ldr_p5 1 hrun hsp hsp_chk
  str_d5 6 hrun hsp hsp_chk; ldr_p5 2 hrun hsp hsp_chk
  str_d5 1 hrun hsp hsp_chk; ldr_p5 3 hrun hsp hsp_chk
  str_d5 0 hrun hsp hsp_chk; ldr_p6 3 hrun hsp hsp_chk
  str_d5 3 hrun hsp hsp_chk; ldr_p6 1 hrun hsp hsp_chk
  str_d5 2 hrun hsp hsp_chk; ldr_p6 2 hrun hsp hsp_chk
  str_d6 1 hrun hsp hsp_chk; ldr_p6 7 hrun hsp hsp_chk
  str_d6 3 hrun hsp hsp_chk; ldr_p6 0 hrun hsp hsp_chk
  str_d6 7 hrun hsp hsp_chk; ldr_p6 5 hrun hsp hsp_chk
  str_d6 2 hrun hsp hsp_chk; ldr_p6 6 hrun hsp hsp_chk
  str_d6 5 hrun hsp hsp_chk; ldr_p7 3 hrun hsp hsp_chk
  str_d6 0 hrun hsp hsp_chk; ldr_p6 4 hrun hsp hsp_chk
  str_d7 3 hrun hsp hsp_chk; ldr_p7 1 hrun hsp hsp_chk
  str_d6 6 hrun hsp hsp_chk; ldr_p7 2 hrun hsp hsp_chk
  str_d6 4 hrun hsp hsp_chk; ldr_p7 0 hrun hsp hsp_chk
  str_d7 1 hrun hsp hsp_chk; ldr_p7 7 hrun hsp hsp_chk
  str_d7 2 hrun hsp hsp_chk; ldr_p7 6 hrun hsp hsp_chk
  str_d7 0 hrun hsp hsp_chk; ldr_p7 4 hrun hsp hsp_chk
  str_d7 7 hrun hsp hsp_chk; ldr_p7 5 hrun hsp hsp_chk
  str_d7 6 hrun hsp hsp_chk; str_d7 5 hrun hsp hsp_chk
  str_d7 4 hrun hsp hsp_chk
  have horr : (sp + 30448#64) ||| 1#64 = sp + 30449#64 := by
    rw [orr_1_of_aligned16 _ (aligned16_add30448 sp hsp_chk)]; bv_omega
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]),
      by simp, by simp [horr],
      by simp [hx19], by simp [hx20], by simp [hx21], by simp [hx22],
      by simp, by simp, by clear * -; cases p4; cases p5; cases p6; cases p7; rfl⟩
theorem seg6_e1_copy_prf [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {prf4 prf5 prf6 prf7 : List (BitVec 8)}
    (h4 : prf4.length = 128) (h5 : prf5.length = 128)
    (h6 : prf6.length = 128) (h7 : prf7.length = 128)
    (Rest : SepProp)
    (hpc : s.pc = b + off8d58) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 28368#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 30448#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg6E1Loop) s
      (((sp + 34464#64) ↦ₛ prf4) ∗ ((sp + 33536#64) ↦ₛ prf5) ∗
       ((sp + 33888#64) ↦ₛ prf6) ∗ ((sp + 14432#64) ↦ₛ prf7) ∗
       memRegion (sp + 30448#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = sp + 30449#64 ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 28368#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 30448#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = 0#128 ∧
        (Pf ⊢ ((sp + 30448#64) ↦ₛ prf4) ∗ ((sp + 30576#64) ↦ₛ prf5) ∗
          ((sp + 30704#64) ↦ₛ prf6) ∗ ((sp + 30832#64) ↦ₛ prf7) ∗
          memRegion (sp + 34464#64) 128 ∗ memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 14432#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 34464#64) h4,
      pointsToBytes128_eq_oct8Mem (sp + 33536#64) h5,
      pointsToBytes128_eq_oct8Mem (sp + 33888#64) h6,
      pointsToBytes128_eq_oct8Mem (sp + 14432#64) h7,
      memRegion_split' (b := sp + 30448#64) (b' := sp + 30576#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30576#64) (b' := sp + 30704#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30704#64) (b' := sp + 30832#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30448#64) (hf := by sep_focus); intro fd4
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30576#64) (hf := by sep_focus); intro fd5
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30704#64) (hf := by sep_focus); intro fd6
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30832#64) (hf := by sep_focus); intro fd7
  rw [show VecRangeMem 8 (sp + 30448#64) fd4 = Oct8Mem (sp + 30448#64) (Oct8.ofFn fd4) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30576#64) fd5 = Oct8Mem (sp + 30576#64) (Oct8.ofFn fd5) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30704#64) fd6 = Oct8Mem (sp + 30704#64) (Oct8.ofFn fd6) from (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30832#64) fd7 = Oct8Mem (sp + 30832#64) (Oct8.ofFn fd7) from (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 34464#64) (Oct8.ofFn (bytesToVecNat prf4)) ∗
      Oct8Mem (sp + 33536#64) (Oct8.ofFn (bytesToVecNat prf5)) ∗
      Oct8Mem (sp + 33888#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗
      Oct8Mem (sp + 14432#64) (Oct8.ofFn (bytesToVecNat prf7)) ∗
      Oct8Mem (sp + 30448#64) (Oct8.ofFn fd4) ∗ Oct8Mem (sp + 30576#64) (Oct8.ofFn fd5) ∗
      Oct8Mem (sp + 30704#64) (Oct8.ofFn fd6) ∗ Oct8Mem (sp + 30832#64) (Oct8.ofFn fd7) ∗ Rest)
    (by sep_frame) ?_
  refine SepWP.seq
    (seg6_e1_copy_oct8 hb hbase s sp _ _ _ _ _ _ _ _ Rest hpc hrun hsp hspA hx19 hx20 hx21 hx22) ?_
  rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, r22, rfp, rv3, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, r8, r9, r19, r20, r21, r22, rfp, rv3, ?_⟩
  rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 30448#64) h4,
      ← pointsToBytes128_eq_oct8Mem (sp + 30576#64) h5,
      ← pointsToBytes128_eq_oct8Mem (sp + 30704#64) h6,
      ← pointsToBytes128_eq_oct8Mem (sp + 30832#64) h7]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 34464#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 33536#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 33888#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 14432#64) _) (by sep_frame) (by sep_frame))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E1Prf
