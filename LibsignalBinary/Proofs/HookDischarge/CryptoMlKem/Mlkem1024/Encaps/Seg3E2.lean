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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd

/-!
# `kyber::encapsulate` (`B07`) — Segment 3 `e2` PRF + `cbd2` + Store + `uVec` `memset` (`+0x56c4 .. +0x59d0`) (`Seg3E2`)

Proves `+0x56c4..+0x59d0`: runs `B01` (`RW1`) on `coins ++ [8#8]` at `sp + 24672`, copies `prf8`
to `sp + 32736`, evaluates the 32-iteration SWAR `cbd2` loop into `sp + 12832`, stores `e2`'s 32
vectors into `[sp + 1488, sp + 2000)`, and zeroes `uVec[0..3]` (`2048` B) at `[sp + 28848, sp + 30896)`
via `B29` `memset`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk01 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW1Spec mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW1_ok)
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
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat pointsToBytes_eq_vecRangeMem
  step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq orr_1_of_aligned16
   setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64 shake256List_length
  step_bCond_not_taken step_bCond_taken truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8
  vec2_bytesToVecNat_eq vecRangeBytes_zero vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x56c4 → 0x59cc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 7 sym

theorem blk01_rw1_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW1Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk01_keccak2_136_31_RW1_ok

theorem blk29_memset_07 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC07.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC07.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC07 shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] abbrev offSeg3E2    : BitVec 64 := BitVec.ofNat 64 22212
@[simp, arm64_norm, wp_norm] abbrev off573c      : BitVec 64 := BitVec.ofNat 64 22332
@[simp, arm64_norm, wp_norm] abbrev off5740      : BitVec 64 := BitVec.ofNat 64 22336
@[simp, arm64_norm, wp_norm] abbrev off5814      : BitVec 64 := BitVec.ofNat 64 22548
@[simp, arm64_norm, wp_norm] abbrev off58b0      : BitVec 64 := BitVec.ofNat 64 22704
@[simp, arm64_norm, wp_norm] abbrev off58b4      : BitVec 64 := BitVec.ofNat 64 22708
@[simp, arm64_norm, wp_norm] abbrev off59cc      : BitVec 64 := BitVec.ofNat 64 22988
@[simp, arm64_norm, wp_norm] abbrev offSeg4Start : BitVec 64 := BitVec.ofNat 64 22992

private theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]; exact cells32_entails_memRegion sPtr _ _ _ _

private theorem aligned16_add32736 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 32736#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 32736#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

/-! ## 1. `e2` PRF Call (`+0x56c4 → +0x5740`) & `memset` (`+0x59cc → +0x59d0`) -/

local macro "step_strQ_oct8 " k:num : tactic => `(tactic| (
  apply step_strQ128 (wb := none)
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

private theorem seg3_e2_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off573c) s
      (((sp + 24704#64) ↦₈ b0) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
       memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 31408#64 ∧
        sm.readReg64 .x1 = sp + 28848#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 12832#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 12832#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 31408#64) (sp + 24672#64) (sp + 24672#64)
            (coins ++ [8#8]).length (coins ++ [8#8]).length ∗
          ((sp + 24672#64) ↦ₛ (coins ++ [8#8])) ∗
          memRegion (sp + 28848#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 31408#64)); intro k0 k1 k2 k3
  simp only [show sp + 31408#64 + 8#64 = sp + 31416#64 by clear * -; bv_omega,
    show sp + 31408#64 + 16#64 = sp + 31424#64 by clear * -; bv_omega,
    show sp + 31408#64 + 24#64 = sp + 31432#64 by clear * -; bv_omega]
  have _ := hpc
  wp_steps 17
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 28848#64) (by decide) (by sep_focus); intro zf
  rw [show VecRangeMem 8 (sp + 28848#64) zf = PolyOctMem (sp + 28848#64) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; wp_step; step_strQ_oct8 5; step_strQ_oct8 4
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
  have hcoins8 : ((sp + 24672#64) ↦ₛ coins) ∗ ((sp + 24704#64) ↦₈ 8#8) =
      ((sp + 24672#64) ↦ₛ (coins ++ [8#8])) := by
    have ha32 : sp + 24672#64 + 32#64 = sp + 24704#64 := by clear * -; bv_omega
    rw [pointsToBytes_append, hc, ha32, pointsToBytes_cons, pointsToBytes_nil]
    simp only [sepConj_emp]
  have hc8_len : (coins ++ [8#8]).length = 33 := by simp [hc]
  unfold Keccak2SlicesRW
  rw [hc8_len]
  simp only [show sp + 31408#64 + 8#64 = sp + 31416#64 by clear * -; bv_omega,
    show sp + 31408#64 + 16#64 = sp + 31424#64 by clear * -; bv_omega,
    show sp + 31408#64 + 24#64 = sp + 31432#64 by clear * -; bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 28848#64) _) (by sep_frame)
    (entails_sub (Entails.of_eq hcoins8) (by sep_frame) (by sep_frame))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg3_e2_prf [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off5740) s
      (((sp + 24704#64) ↦₈ b0) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
       memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 12832#64) 128 ∗
       memRegion (sp + 31408#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        s1.readReg64 .x20 = sp + 12832#64 ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        (P1 ⊢ memRegion (sp + 24672#64) 33 ∗
          ((sp + 28848#64) ↦ₛ shake256List 128 (coins ++ [8#8])) ∗
          memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl07 blkPl07.base := hb
  refine SepWP.weaken_pre
    (P' := ((sp + 24704#64) ↦₈ b0) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
      memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
      (memRegion (sp + 12832#64) 128 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg3_e2_stage hb rfl s sp coins b0 (memRegion (sp + 12832#64) 128 ∗ stackAt sp 1136 ∗ Rest) hc hpc hrun hsp hspA) ?_
  rintro sm Pm hpcm hrunm hclm hrom ⟨hspm, hspAm, hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hfpm, hPm⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem := hclm
  have _ : MlKemRoOk mlkemMpl sm.mem := hrom
  refine SepWP.weaken_pre hPm ?_
  have hc8_len : (coins ++ [8#8]).length = 33 := by simp [hc]
  have hlt8 : (coins ++ [8#8]).length < 2 ^ 32 := by rw [hc8_len]; decide
  have hout128 : (128 : Nat) = 32 ∨ (128 : Nat) = 128 := Or.inr rfl
  wp_call (blk01_rw1_07 blkPl07.base)
    (sp + 31408#64, sp + 24672#64, sp + 28848#64, sp + 12832#64, (128 : Nat), coins ++ [8#8])
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_sp_eq hspAm hspm hsp_sf,
      by simp [*], by simp [*], by simp [*], ?_⟩
  have hm12832 : ((sp + 12832#64) ↦ₛ shake256List 128 (coins ++ [8#8])) ⊢
      memRegion (sp + 12832#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 12832#64) (shake256List 128 (coins ++ [8#8]))
  have hm33 : ((sp + 24672#64) ↦ₛ (coins ++ [8#8])) ⊢ memRegion (sp + 24672#64) 33 := by
    simpa [hc8_len] using pointsToBytes_entails_memRegion (sp + 24672#64) (coins ++ [8#8])
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm12832 (by sep_frame)
      (entails_sub hm33 (by sep_frame) (by sep_frame)))

private theorem seg3_e2_memset_u [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off59cc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 28848#64)
    (hx1 : s.readReg64 .x1 = 0#64)
    (hx2 : s.readReg64 .x2 = 2048#64)
    (hx20 : s.readReg64 .x20 = sp + 28848#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Start) s
      (memRegion (sp + 28848#64) 2048 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 28848#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ PolyMem (sp + 28848#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29872#64) (fun _ => 0#128) ∗
          PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl07 blkPl07.base := hb
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s.mem := hcl
  have _ := hpc
  have h2048 : (2048 : Nat) ≤ 2 ^ 64 := by decide
  wp_call (blk29_memset_07 blkPl07.base) (sp + 28848#64, 0#8, (2048 : Nat))
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_sp_eq hspA hsp hsp_sf,
      by simp [*], by simp [*], ?_⟩
  have h2048_eq : ((sp + 28848#64) ↦ₛ List.replicate 2048 0#8) =
      PolyMem (sp + 28848#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
      PolyMem (sp + 29872#64) (fun _ => 0#128) ∗
      PolyMem (sp + 30384#64) (fun _ => 0#128) := by
    have hsplit : List.replicate 2048 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
          (vecRangeBytes 32 (fun _ => 0#128) ++
            (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128))) := by
      rw [vecRangeBytes_zero 32, ← List.replicate_add, ← List.replicate_add, ← List.replicate_add]
    rw [hsplit, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp only [show (16 * 32 : Nat) = 512 from rfl,
      show sp + 28848#64 + 512#64 = sp + 29360#64 by bv_omega,
      show sp + 29360#64 + 512#64 = sp + 29872#64 by bv_omega,
      show sp + 29872#64 + 512#64 = sp + 30384#64 by bv_omega]
    rfl
  exact entails_sub (Entails.of_eq h2048_eq) (by sep_frame) (by sep_frame)

/-! ## 2. Copy `prf8` to `sp + 32736` & Zero `sp + 12832` (`+0x5740 → +0x5814`) -/

local macro "ldr_p8 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 28848#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "str_d8 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 32736#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_z12832 " k:num : tactic => `(tactic| (
  apply step_strQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k); decide; bv_omega; rfl
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg3_e2_copy_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (p8 d8 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off5740) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12832#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off5814) s
      (Oct8Mem (sp + 28848#64) p8 ∗ Oct8Mem (sp + 32736#64) d8 ∗
       memRegion (sp + 12832#64) 512 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x8 = 0#64 ∧
        sm.readReg64 .x9 = sp + 32737#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 12832#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Oct8Mem (sp + 28848#64) p8 ∗ Oct8Mem (sp + 32736#64) p8 ∗
          memRegion (sp + 12832#64) 512 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  ldr_p8 4 hrun hsp hsp_chk; ldr_p8 5 hrun hsp hsp_chk; wp_step
  ldr_p8 7 hrun hsp hsp_chk; wp_steps 2
  str_d8 4 hrun hsp hsp_chk; ldr_p8 6 hrun hsp hsp_chk; wp_step
  str_d8 5 hrun hsp hsp_chk; ldr_p8 0 hrun hsp hsp_chk
  str_d8 6 hrun hsp hsp_chk; ldr_p8 1 hrun hsp hsp_chk
  str_d8 7 hrun hsp hsp_chk; ldr_p8 2 hrun hsp hsp_chk
  str_d8 1 hrun hsp hsp_chk; ldr_p8 3 hrun hsp hsp_chk
  str_d8 0 hrun hsp hsp_chk; str_d8 3 hrun hsp hsp_chk; wp_step
  str_d8 2 hrun hsp hsp_chk
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 12832#64) (by decide) (by sep_focus); intro fz
  rw [show VecRangeMem 32 (sp + 12832#64) fz = PolyMem (sp + 12832#64) fz from rfl, ← poly32Mem_ofFn]
  str_z12832 31; str_z12832 30; str_z12832 29; str_z12832 28; str_z12832 27; str_z12832 26; str_z12832 25; str_z12832 24
  str_z12832 23; str_z12832 22; str_z12832 21; str_z12832 20; str_z12832 19; str_z12832 18; str_z12832 17; str_z12832 16
  str_z12832 15; str_z12832 14; str_z12832 13; str_z12832 12; str_z12832 11; str_z12832 10; str_z12832 9;  str_z12832 8
  str_z12832 7;  str_z12832 6;  str_z12832 5;  str_z12832 4;  str_z12832 3;  str_z12832 2;  str_z12832 1;  str_z12832 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp,
      by simp [orr_1_of_aligned16 _ (aligned16_add32736 sp hsp_chk)],
      by simp [hx19], by simp [hx20], by simp, ?_⟩
  have hp8 : ({ o0 := p8.get 0, o1 := p8.get 1, o2 := p8.get 2, o3 := p8.get 3,
                o4 := p8.get 4, o5 := p8.get 5, o6 := p8.get 6, o7 := p8.get 7 } : Oct8) = p8 := by
    cases p8; rfl
  rw [hp8]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 12832#64) _) (by sep_frame) (by sep_frame)

/-! ## 3. `e2` 32-Iteration SWAR `cbd2` Loop (`+0x5814 → +0x58b4`) -/

local macro "step_e2_strh " cellPtr:ident c:num
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

private theorem seg3_e2_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off5814) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (16 * k))
    (hx9 : s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC07.rebase b (fun _ => none))
      (if k < 31 then b + off5814 else b + off58b4) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = dstPtr ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
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
    (by simp [evalAddrMode, hx9]; clear * -; bv_omega)
    (SepLoad32.right (SepLoad32.left (SepLoad32.wordRange (n := 32) (k := k) hk rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 20
  step_e2_strh cellPtr 0 (cbd2CoeffFromWord w 0)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e2_strh cellPtr 1 (cbd2CoeffFromWord w 1)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 2
  step_e2_strh cellPtr 3 (cbd2CoeffFromWord w 3)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j3_eq _) hrun
  wp_steps 2
  step_e2_strh cellPtr 4 (cbd2CoeffFromWord w 4)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_steps 3
  step_e2_strh cellPtr 5 (cbd2CoeffFromWord w 5)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e2_strh cellPtr 2 (cbd2CoeffFromWord w 2)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]) hrun
  wp_step
  step_e2_strh cellPtr 7 (cbd2CoeffFromWord w 7)
    (by simp [State.readReg32, cbd2_swar_eq, cbd2CoeffFromWord, w]; exact cbd2_j7_eq _) hrun
  step_e2_strh cellPtr 6 (cbd2CoeffFromWord w 6)
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
    refine step_bCond_taken (dst := blkPl07.base + off5814)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [off58b0, off5814]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp [hx20], by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl07.base + off58b4)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [off58b0, off58b4]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp [hx19], by simp [hx20], by simp,
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg3_e2_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (sp prfPtr dstPtr fp0 : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + off5814 else b + off58b4) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x8 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      s.readReg64 .fp = fp0 →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + off58b4) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = dstPtr ∧
          s'.readReg64 .fp = fp0 ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx20 hfp
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun ⟨hsp, hspA, hx19, hx20, hfp, by
      congr 2; exact vecRangeMem_congr fun i hi => hf i hi⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx8 hx9 hx19 hx20 hfp
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg3_e2_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx8 hx9 hx19 hx20) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hfp1, hP1⟩
    subst hP1
    exact ih (k + 1) (by omega) s1 _
      (fun i hi => by
        by_cases hik : i = k
        · subst hik; simp
        · simp [Function.update, hik, hf i (by omega)])
      (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
      hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1 (hfp1.trans hfp)

/-! ## 4. Store of `e2` to `[sp + 1488, sp + 2000)` (`+0x58b4 → +0x59cc`) -/

local macro "ldr_src12832 " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · apply SepLoad128.left; exact SepLoad128.vec32 (by decide : $k < 32) (by bv_omega) rfl
  · wp_norm_lhs))

local macro "str_dst1488 " k:num : tactic => `(tactic| (
  apply step_strQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.right; apply SepStore128.left
    exact SepStore128.vec32 (by decide : $k < 32) (by bv_omega) (by dsimp only [Vec32.set])
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg3_e2_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off58b4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off59cc) s
      (Poly32Mem (sp + 12832#64) src ∗ Poly32Mem (sp + 1488#64) dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = sp + 28848#64 ∧
        s'.readReg64 .x1 = 0#64 ∧
        s'.readReg64 .x2 = 2048#64 ∧
        s'.readReg64 .x20 = sp + 28848#64 ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        P' = (Poly32Mem (sp + 12832#64) src ∗ Poly32Mem (sp + 1488#64) src ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  ldr_src12832 0; wp_steps 5; str_dst1488 0
  ldr_src12832 1; wp_step; str_dst1488 1
  ldr_src12832 2;  str_dst1488 2;  ldr_src12832 3;  str_dst1488 3
  ldr_src12832 4;  str_dst1488 4;  ldr_src12832 5;  str_dst1488 5
  ldr_src12832 6;  str_dst1488 6;  ldr_src12832 7;  str_dst1488 7
  ldr_src12832 8;  str_dst1488 8;  ldr_src12832 9;  str_dst1488 9
  ldr_src12832 10; str_dst1488 10; ldr_src12832 11; str_dst1488 11
  ldr_src12832 12; str_dst1488 12; ldr_src12832 13; str_dst1488 13
  ldr_src12832 14; str_dst1488 14; ldr_src12832 15; str_dst1488 15
  ldr_src12832 16; str_dst1488 16; ldr_src12832 17; str_dst1488 17
  ldr_src12832 18; str_dst1488 18; ldr_src12832 19; str_dst1488 19
  ldr_src12832 20; str_dst1488 20; ldr_src12832 21; str_dst1488 21
  ldr_src12832 22; str_dst1488 22; ldr_src12832 23; str_dst1488 23
  ldr_src12832 24; str_dst1488 24; ldr_src12832 25; str_dst1488 25
  ldr_src12832 26; str_dst1488 26; ldr_src12832 27; str_dst1488 27
  ldr_src12832 28; str_dst1488 28; ldr_src12832 29; str_dst1488 29
  ldr_src12832 30; str_dst1488 30; ldr_src12832 31; str_dst1488 31
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hal_sp,
      by simp, by simp, by simp, by simp, by simp,
      by cases src; cases dst; rfl⟩

private theorem seg3_e2_body [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (prf8 : List (BitVec 8)) (h8 : prf8.length = 128) (Rest : SepProp)
    (hpc : s.pc = b + off5740) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12832#64) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + off59cc) s
      (((sp + 28848#64) ↦ₛ prf8) ∗ memRegion (sp + 1488#64) 512 ∗
       memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 32736#64) 128 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x0 = sp + 28848#64 ∧
        s3.readReg64 .x1 = 0#64 ∧
        s3.readReg64 .x2 = 2048#64 ∧
        s3.readReg64 .x20 = sp + 28848#64 ∧
        s3.readReg64 .fp = s.readReg64 .fp ∧
        (P3 ⊢ memRegion (sp + 28848#64) 128 ∗
          PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 prf8)) ∗
          memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 32736#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 28848#64) h8]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 32736#64) (hf := by sep_focus); intro fd8
  rw [show VecRangeMem 8 (sp + 32736#64) fd8 = Oct8Mem (sp + 32736#64) (Oct8.ofFn fd8) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 28848#64) (Oct8.ofFn (bytesToVecNat prf8)) ∗
      Oct8Mem (sp + 32736#64) (Oct8.ofFn fd8) ∗ memRegion (sp + 12832#64) 512 ∗
      (memRegion (sp + 1488#64) 512 ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg3_e2_copy_zero hb hbase s sp _ _ _ hpc hrun hsp hspA hx19 hx20) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [← pointsToBytes128_eq_oct8Mem (sp + 32736#64) h8,
      ← wordRangeMem32_eq_pointsToBytes (sp + 32736#64) h8]
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 12832#64) (hf := by sep_focus); intro f12832
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 (sp + 32736#64) (readU32LE prf8) ∗ VecRangeMem 32 (sp + 12832#64) f12832 ∗
      (Oct8Mem (sp + 28848#64) (Oct8.ofFn (bytesToVecNat prf8)) ∗ memRegion (sp + 1488#64) 512 ∗ Rest))
    (by sep_frame) ?_
  refine SepWP.seq
    (seg3_e2_cbd2_steps hb hbase sp (sp + 32736#64) (sp + 12832#64) (s.readReg64 .fp) prf8 _ 32 0 rfl s1 f12832
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1
      (by rw [hx9_1]; clear * -; bv_omega) hx19_1 hx20_1 hfp1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, _, _, hfp2, hP2⟩
  subst hP2
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 1488#64) (hf := by sep_focus); intro f1488
  rw [← poly32Mem_ofFn (sp + 12832#64),
      show VecRangeMem 32 (sp + 1488#64) f1488 = Poly32Mem (sp + 1488#64) (Vec32.ofFn f1488) from
        (poly32Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 12832#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf8))) ∗
      Poly32Mem (sp + 1488#64) (Vec32.ofFn f1488) ∗
      (WordRangeMem 32 (sp + 32736#64) (readU32LE prf8) ∗
        Oct8Mem (sp + 28848#64) (Oct8.ofFn (bytesToVecNat prf8)) ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg3_e2_store hb hbase s2 sp _ _ _ hpc2 hrun2 hsp2 hspA2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, hspA3, r0, r1, r2, r20, hfp3, hP3⟩
  refine SepWP.done hpc3 hrun3 ⟨hsp3, hspA3, r0, r1, r2, r20, hfp3.trans hfp2, ?_⟩
  rw [hP3, poly32Mem_ofFn (sp + 1488#64),
      wordRangeMem32_eq_pointsToBytes (sp + 32736#64) h8]
  have hm32736 : ((sp + 32736#64) ↦ₛ prf8) ⊢ memRegion (sp + 32736#64) 128 := by
    simpa [h8] using pointsToBytes_entails_memRegion (sp + 32736#64) prf8
  exact entails_sub (oct8Mem_entails_memRegion (sp + 28848#64) _) (by sep_frame)
    (entails_sub (poly32Mem_entails_memRegion (sp + 12832#64) _) (by sep_frame)
      (entails_sub hm32736 (by sep_frame) (by sep_frame)))

theorem seg3_e2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl07 b) (hbase : blkPl07.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg3E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf8 := shake256List 128 (coins ++ [8#8])
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg4Start) s
      (((sp + 24704#64) ↦₈ b0) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
       memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 28848#64) 2048 ∗
       memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 32736#64) 128 ∗
       memRegion (sp + 31408#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x20 = sp + 28848#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 prf8)) ∗
          PolyMem (sp + 28848#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29360#64) (fun _ => 0#128) ∗
          PolyMem (sp + 29872#64) (fun _ => 0#128) ∗
          PolyMem (sp + 30384#64) (fun _ => 0#128) ∗
          memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 24672#64) 33 ∗
          memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf8
  have h8 : prf8.length = 128 := shake256List_length 128 _
  rw [memRegion_split' (b := sp + 28848#64) (b' := sp + 28976#64) (n := 128) (k := (1920 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 12832#64) (b' := sp + 12960#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 24704#64) ↦₈ b0) ∗ ((sp + 24672#64) ↦ₛ coins) ∗
      memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 12832#64) 128 ∗
      memRegion (sp + 31408#64) 32 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1488#64) 512 ∗ memRegion (sp + 28976#64) 1920 ∗
        memRegion (sp + 12960#64) 384 ∗ memRegion (sp + 32736#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg3_e2_prf hb hbase s sp coins b0 _ hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hm512 : memRegion (sp + 12832#64) 128 ∗ memRegion (sp + 12960#64) 384 =
      memRegion (sp + 12832#64) 512 :=
    (memRegion_split' (b := sp + 12832#64) (b' := sp + 12960#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 28848#64) ↦ₛ prf8) ∗ memRegion (sp + 1488#64) 512 ∗
      memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 32736#64) 128 ∗
      (memRegion (sp + 28976#64) 1920 ∗ memRegion (sp + 24672#64) 33 ∗
        memRegion (sp + 31408#64) 32 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_e2_body hb hbase s1 sp prf8 h8 _ hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, r0, r1, r2, r20, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm2048 : memRegion (sp + 28848#64) 128 ∗ memRegion (sp + 28976#64) 1920 =
      memRegion (sp + 28848#64) 2048 :=
    (memRegion_split' (b := sp + 28848#64) (b' := sp + 28976#64) (n := 128) (k := (1920 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 28848#64) 2048 ∗ stackAt sp 1136 ∗
      (PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 prf8)) ∗
        memRegion (sp + 12832#64) 512 ∗ memRegion (sp + 24672#64) 33 ∗
        memRegion (sp + 32736#64) 128 ∗ memRegion (sp + 31408#64) 32 ∗ Rest))
    (entails_sub (Entails.of_eq hm2048) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg3_e2_memset_u hb hbase s2 sp _ hpc2 hrun2 hsp2 hspA2 r0 r1 r2 r20 hcl2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx20f, hfpf, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, hx20f, hfpf.trans (hfp2.trans hfp1), hclf, hrof, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3E2
