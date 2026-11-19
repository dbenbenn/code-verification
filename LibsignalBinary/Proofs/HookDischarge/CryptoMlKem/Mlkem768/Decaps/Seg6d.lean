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
# `decapsulate_compressed_key` (`B04`) — Segment 6d (`+0x89f0 .. +0x8d00`)

Runs `B01` (`RW1`) on `coins ++ [6#8]` at `sp + 19120`, copies `prf6` to `sp + 22240`, evaluates
the 32-iteration SWAR `cbd2` loop into `sp + 11856`, copies `e2` (`512` B) to `[sp + 1312, sp + 1824)`,
and zeroes `[sp + 22400, sp + 23936)` (`1536` B) via `B29` `memset`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ mlkemMpl
  resolve_blk01 resolve_blk29 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (Keccak2SlicesRW)
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
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat step_ldrQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq orr_1_of_aligned16
  setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64 shake256List_length
  step_bCond_not_taken step_bCond_taken truncate32_zext64 ubfx2_w32_norm
  vec128At_eq_halfRangeMem8 vecRangeBytes_zero vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6a (
  blk01_rw1_04 blk29_04 blkPl04_ρ keccak2SlicesRW_entails_memRegion32
  pointsToBytes128_eq_oct8Mem)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x89f0 → 0x8cfc]
end

attribute [local irreducible] blkPC04 shake256List neonCbd2Poly16 polyVecNat
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 ubfx2_w32_norm
  truncate32_zext64 setWidth32_shr_zext64

@[simp, arm64_norm, wp_norm] abbrev offSeg6E2   : BitVec 64 := BitVec.ofNat 64 35312
@[simp, arm64_norm, wp_norm] abbrev off8a68     : BitVec 64 := BitVec.ofNat 64 35432
@[simp, arm64_norm, wp_norm] abbrev off8a6c     : BitVec 64 := BitVec.ofNat 64 35436
@[simp, arm64_norm, wp_norm] abbrev off8b40     : BitVec 64 := BitVec.ofNat 64 35648
@[simp, arm64_norm, wp_norm] abbrev off8bdc     : BitVec 64 := BitVec.ofNat 64 35804
@[simp, arm64_norm, wp_norm] abbrev off8be0     : BitVec 64 := BitVec.ofNat 64 35808
@[simp, arm64_norm, wp_norm] abbrev off8cfc     : BitVec 64 := BitVec.ofNat 64 36092
@[simp, arm64_norm, wp_norm] abbrev offSeg7Start : BitVec 64 := BitVec.ofNat 64 36096

private theorem aligned16_add22240 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 22240#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 22240#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

/-! ## 1. `e2` PRF Call (`+0x89f0 → +0x8a6c`) & `memset` (`+0x8cfc → +0x8d00`) -/

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

private theorem seg6d_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8a68) s
      (((sp + 19152#64) ↦₈ b0) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 22400#64) 128 ∗ memRegion (sp + 24448#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x0 = sp + 24448#64 ∧
        sm.readReg64 .x1 = sp + 22400#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 11856#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 11856#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 24448#64) (sp + 19120#64) (sp + 19120#64)
            (coins ++ [6#8]).length (coins ++ [6#8]).length ∗
          ((sp + 19120#64) ↦ₛ (coins ++ [6#8])) ∗
          memRegion (sp + 22400#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 24448#64)); intro k0 k1 k2 k3
  simp only [show sp + 24448#64 + 8#64 = sp + 24456#64 by clear * -; bv_omega,
    show sp + 24448#64 + 16#64 = sp + 24464#64 by clear * -; bv_omega,
    show sp + 24448#64 + 24#64 = sp + 24472#64 by clear * -; bv_omega]
  wp_steps 17
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22400#64) (by decide) (by sep_focus); intro zf
  rw [show VecRangeMem 8 (sp + 22400#64) zf = PolyOctMem (sp + 22400#64) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; wp_step; step_strQ_oct8 5; step_strQ_oct8 4
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
  have hcoins6 : ((sp + 19120#64) ↦ₛ coins) ∗ ((sp + 19152#64) ↦₈ 6#8) =
      ((sp + 19120#64) ↦ₛ (coins ++ [6#8])) := by
    have ha32 : sp + 19120#64 + 32#64 = sp + 19152#64 := by clear * -; bv_omega
    rw [pointsToBytes_append, hc, ha32, pointsToBytes_cons, pointsToBytes_nil]
    simp only [sepConj_emp]
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  unfold Keccak2SlicesRW; rw [hc6_len]
  simp only [show sp + 24448#64 + 8#64 = sp + 24456#64 by clear * -; bv_omega,
    show sp + 24448#64 + 16#64 = sp + 24464#64 by clear * -; bv_omega,
    show sp + 24448#64 + 24#64 = sp + 24472#64 by clear * -; bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 22400#64) _) (by sep_frame)
    (entails_sub (Entails.of_eq hcoins6) (by sep_frame) (by sep_frame))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6d_prf [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8a6c) s
      (((sp + 19152#64) ↦₈ b0) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 22400#64) 128 ∗
       memRegion (sp + 24448#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .fp = s.readReg64 .fp ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        s1.readReg64 .x20 = sp + 11856#64 ∧
        (P1 ⊢ memRegion (sp + 19120#64) 33 ∗
          ((sp + 22400#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
          memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 24448#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  refine SepWP.weaken_pre
    (P' := ((sp + 19152#64) ↦₈ b0) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 22400#64) 128 ∗ memRegion (sp + 24448#64) 32 ∗
      (memRegion (sp + 11856#64) 128 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6d_stage hb rfl s sp coins b0 _ hc hpc hrun hsp hspA) ?_
  rintro sm Pm hpcm hrunm hclm hrom ⟨hspm, hspAm, hfpm, hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hPm⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem := hclm
  have _ : MlKemRoOk mlkemMpl sm.mem := hrom
  refine SepWP.weaken_pre hPm ?_
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  wp_step
  have hrom' : MlKemRoOk mlkemMpl
      ((sm.writeReg64 .lr (blkPl04.base + off8a6c)).setPC (mlkemMpl.base 1)).mem := hrom
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk01_rw1_04 blkPl04.base)
    (sp + 24448#64, sp + 19120#64, sp + 22400#64, sp + 11856#64, (128 : Nat), coins ++ [6#8])
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hspm, spAligned_of_sp_eq hspAm hspm (hsp_sf.trans hspm),
      Eq.trans ‹_› hfpm, Eq.trans ‹_› (hx19m.trans hx19), Eq.trans ‹_› hx20m, ?_⟩
  rw [hspm]
  have hm11856 : ((sp + 11856#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ⊢
      memRegion (sp + 11856#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 11856#64) (shake256List 128 (coins ++ [6#8]))
  have hm33 : ((sp + 19120#64) ↦ₛ (coins ++ [6#8])) ⊢ memRegion (sp + 19120#64) 33 := by
    simpa [hc6_len] using pointsToBytes_entails_memRegion (sp + 19120#64) (coins ++ [6#8])
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm11856 (by sep_frame)
      (entails_sub hm33 (by sep_frame) (by sep_frame)))

private theorem seg6d_memset_u [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off8cfc) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 22400#64)
    (hx1 : s.readReg64 .x1 = 0#64)
    (hx2 : s.readReg64 .x2 = 1536#64)
    (hx19 : s.readReg64 .x19 = 1536#64)
    (hx20 : s.readReg64 .x20 = sp + 22400#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Start) s
      (memRegion (sp + 22400#64) 1536 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 1536#64 ∧
        sf.readReg64 .x20 = sp + 22400#64 ∧
        (Pf ⊢ PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
          PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
          PolyMem (sp + 23424#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s.mem := hcl
  wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk29_04 blkPl04.base) (sp + 22400#64, 0#8, (1536 : Nat))
  apply SepWP.done (by assumption) (by assumption); intro _
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      ‹_›, Eq.trans ‹_› hx19, Eq.trans ‹_› hx20, ?_⟩
  have h1536 : ((sp + 22400#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
      PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
      PolyMem (sp + 23424#64) (fun _ => 0#128) := by
    have hsplit : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
          (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, ← List.replicate_add, ← List.replicate_add]
    rw [hsplit, pointsToBytes_append, pointsToBytes_append, vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp only [show (16 * 32 : Nat) = 512 from rfl,
      show sp + 22400#64 + 512#64 = sp + 22912#64 by bv_omega,
      show sp + 22912#64 + 512#64 = sp + 23424#64 by bv_omega]
    rfl
  exact entails_sub (Entails.of_eq h1536) (by sep_frame) (by sep_frame)

/-! ## 2. Copy `prf6` to `sp + 22240` & Zero `sp + 11856` (`+0x8a6c → +0x8b40`) -/

local macro "ldr_p6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 22400#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "str_d6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 22240#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_z11856 " k:num : tactic => `(tactic| (
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
private theorem seg6d_copy_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (p6 d6 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off8a6c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8b40) s
      (Oct8Mem (sp + 22400#64) p6 ∗ Oct8Mem (sp + 22240#64) d6 ∗
       memRegion (sp + 11856#64) 512 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readReg64 .x8 = 0#64 ∧
        sm.readReg64 .x9 = sp + 22241#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 11856#64 ∧
        (Pm ⊢ Oct8Mem (sp + 22400#64) p6 ∗ Oct8Mem (sp + 22240#64) p6 ∗
          memRegion (sp + 11856#64) 512 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p6 4 hrun hsp hsp_chk; ldr_p6 5 hrun hsp hsp_chk; wp_step
  ldr_p6 7 hrun hsp hsp_chk; wp_steps 2
  str_d6 4 hrun hsp hsp_chk; ldr_p6 6 hrun hsp hsp_chk; wp_step
  str_d6 5 hrun hsp hsp_chk; ldr_p6 0 hrun hsp hsp_chk
  str_d6 6 hrun hsp hsp_chk; ldr_p6 1 hrun hsp hsp_chk
  str_d6 7 hrun hsp hsp_chk; ldr_p6 2 hrun hsp hsp_chk
  str_d6 1 hrun hsp hsp_chk; ldr_p6 3 hrun hsp hsp_chk
  str_d6 0 hrun hsp hsp_chk; str_d6 3 hrun hsp hsp_chk; wp_step
  str_d6 2 hrun hsp hsp_chk
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) (by sep_focus); intro fz
  rw [show VecRangeMem 32 (sp + 11856#64) fz = PolyMem (sp + 11856#64) fz from rfl, ← poly32Mem_ofFn]
  str_z11856 31; str_z11856 30; str_z11856 29; str_z11856 28
  str_z11856 27; str_z11856 26; str_z11856 25; str_z11856 24
  str_z11856 23; str_z11856 22; str_z11856 21; str_z11856 20
  str_z11856 19; str_z11856 18; str_z11856 17; str_z11856 16
  str_z11856 15; str_z11856 14; str_z11856 13; str_z11856 12
  str_z11856 11; str_z11856 10; str_z11856 9;  str_z11856 8
  str_z11856 7;  str_z11856 6;  str_z11856 5;  str_z11856 4
  str_z11856 3;  str_z11856 2;  str_z11856 1;  str_z11856 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp,
      by simp [orr_1_of_aligned16 _ (aligned16_add22240 sp hsp_chk)],
      by simp [hx19], by simp [hx20], ?_⟩
  have hp6 : ({ o0 := p6.get 0, o1 := p6.get 1, o2 := p6.get 2, o3 := p6.get 3,
                o4 := p6.get 4, o5 := p6.get 5, o6 := p6.get 6, o7 := p6.get 7 } : Oct8) = p6 := by
    cases p6; rfl
  rw [hp6]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 11856#64) _) (by sep_frame) (by sep_frame)

/-! ## 3. `e2` 32-Iteration SWAR `cbd2` Loop (`+0x8b40 → +0x8be0`) -/

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

private theorem seg6d_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off8b40) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (16 * k))
    (hx9 : s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if k < 31 then b + off8b40 else b + off8be0) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (16 * (k + 1)) ∧
        s'.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * (k + 1)) ∧
        s'.readReg64 .x19 = 0x55555555#64 ∧
        s'.readReg64 .x20 = dstPtr ∧
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
    refine step_bCond_taken (dst := blkPl04.base + off8b40)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [off8bdc, off8b40]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp [hx20],
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl04.base + off8be0)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [off8bdc, off8be0]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp, by simp [hx19], by simp [hx20],
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg6d_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + off8b40 else b + off8be0) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x8 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + off8be0) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .fp = s.readReg64 .fp ∧
          s'.readReg64 .x19 = 0x55555555#64 ∧
          s'.readReg64 .x20 = dstPtr ∧
          P' = (WordRangeMem 32 prfPtr (readU32LE prf) ∗
            PolyMem dstPtr (polyVecNat (neonCbd2Poly16 prf)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro k hsum s f hf hpc hrun hsp hspA _ _ hx19 hx20
    have hk : k = 32 := by omega
    subst hk
    simp only [show ¬(32 < 32) by omega, ↓reduceIte] at hpc
    exact SepWP.done hpc hrun ⟨hsp, hspA, rfl, hx19, hx20, by
      dsimp only [PolyMem]; rw [vecRangeMem_congr hf]⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx8 hx9 hx19 hx20
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg6d_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx8 hx9 hx19 hx20) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, rfp1, hx8_1, hx9_1, hx19_1, hx20_1, hP1⟩
    subst hP1
    refine SepWP.seq
      (ih (k + 1) (by omega) s1 _
        (fun i hi => by
          by_cases hik : i = k
          · subst hik; exact Function.update_self i _ f
          · rw [Function.update_of_ne hik]; exact hf i (by omega))
        (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
        hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, rfp2, gx19, gx20, hP2⟩
    exact SepWP.done hpc2 hrun2 ⟨hsp2, hspA2, rfp2.trans rfp1, gx19, gx20, hP2⟩

/-! ## 4. Forward Store of `e2` to `[sp + 1312, sp + 1824)` (`+0x8be0 → +0x8cfc`) -/

local macro "ldr_src11856 " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · apply SepLoad128.left; exact SepLoad128.vec32 (by decide : $k < 32) (by bv_omega) rfl
  · wp_norm_lhs))

local macro "str_dst1312 " k:num : tactic => `(tactic| (
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
private theorem seg6d_store_e2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off8be0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8cfc) s
      (Poly32Mem (sp + 11856#64) src ∗ Poly32Mem (sp + 1312#64) dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x0 = sp + 22400#64 ∧
        s'.readReg64 .x1 = 0#64 ∧
        s'.readReg64 .x2 = 1536#64 ∧
        s'.readReg64 .x19 = 1536#64 ∧
        s'.readReg64 .x20 = sp + 22400#64 ∧
        P' = (Poly32Mem (sp + 11856#64) src ∗ Poly32Mem (sp + 1312#64) src ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_src11856 0; wp_steps 5; str_dst1312 0
  ldr_src11856 1; wp_steps 2; str_dst1312 1
  ldr_src11856 2;  str_dst1312 2;  ldr_src11856 3;  str_dst1312 3
  ldr_src11856 4;  str_dst1312 4;  ldr_src11856 5;  str_dst1312 5
  ldr_src11856 6;  str_dst1312 6;  ldr_src11856 7;  str_dst1312 7
  ldr_src11856 8;  str_dst1312 8;  ldr_src11856 9;  str_dst1312 9
  ldr_src11856 10; str_dst1312 10; ldr_src11856 11; str_dst1312 11
  ldr_src11856 12; str_dst1312 12; ldr_src11856 13; str_dst1312 13
  ldr_src11856 14; str_dst1312 14; ldr_src11856 15; str_dst1312 15
  ldr_src11856 16; str_dst1312 16; ldr_src11856 17; str_dst1312 17
  ldr_src11856 18; str_dst1312 18; ldr_src11856 19; str_dst1312 19
  ldr_src11856 20; str_dst1312 20; ldr_src11856 21; str_dst1312 21
  ldr_src11856 22; str_dst1312 22; ldr_src11856 23; str_dst1312 23
  ldr_src11856 24; str_dst1312 24; ldr_src11856 25; str_dst1312 25
  ldr_src11856 26; str_dst1312 26; ldr_src11856 27; str_dst1312 27
  ldr_src11856 28; str_dst1312 28; ldr_src11856 29; str_dst1312 29
  ldr_src11856 30; str_dst1312 30; ldr_src11856 31; str_dst1312 31
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hal_sp,
      by simp, by simp, by simp, by simp, by simp, by simp,
      by cases src; cases dst; rfl⟩

private theorem seg6d_body [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (prf6 : List (BitVec 8)) (h6 : prf6.length = 128) (Rest : SepProp)
    (hpc : s.pc = b + off8a6c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 11856#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + off8cfc) s
      (((sp + 22400#64) ↦ₛ prf6) ∗ memRegion (sp + 1312#64) 512 ∗
       memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 22240#64) 128 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .fp = s.readReg64 .fp ∧
        s3.readReg64 .x0 = sp + 22400#64 ∧
        s3.readReg64 .x1 = 0#64 ∧
        s3.readReg64 .x2 = 1536#64 ∧
        s3.readReg64 .x19 = 1536#64 ∧
        s3.readReg64 .x20 = sp + 22400#64 ∧
        (P3 ⊢ memRegion (sp + 22400#64) 128 ∗
          PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 22240#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 22400#64) h6]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 22240#64) (by decide) (by sep_focus); intro fd6
  rw [show VecRangeMem 8 (sp + 22240#64) fd6 = Oct8Mem (sp + 22240#64) (Oct8.ofFn fd6) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 22400#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗
      Oct8Mem (sp + 22240#64) (Oct8.ofFn fd6) ∗ memRegion (sp + 11856#64) 512 ∗
      (memRegion (sp + 1312#64) 512 ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg6d_copy_zero hb hbase s sp _ _ _ hpc hrun hsp hspA hx19 hx20) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hfp1, hx8_1, hx9_1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [← pointsToBytes128_eq_oct8Mem (sp + 22240#64) h6,
      ← wordRangeMem32_eq_pointsToBytes (sp + 22240#64) h6]
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 11856#64) (by decide) (by sep_focus); intro f11856
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 (sp + 22240#64) (readU32LE prf6) ∗ VecRangeMem 32 (sp + 11856#64) f11856 ∗
      (Oct8Mem (sp + 22400#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗ memRegion (sp + 1312#64) 512 ∗ Rest))
    (by sep_frame) ?_
  refine SepWP.seq
    (seg6d_cbd2_steps hb hbase sp (sp + 22240#64) (sp + 11856#64) prf6 _ 32 0 rfl s1 f11856
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1
      (by rw [hx9_1]; clear * -; bv_omega) hx19_1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hfp2, _, _, hP2⟩
  subst hP2
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 1312#64) (by decide) (by sep_focus); intro f1312
  rw [← poly32Mem_ofFn (sp + 11856#64),
      show VecRangeMem 32 (sp + 1312#64) f1312 = Poly32Mem (sp + 1312#64) (Vec32.ofFn f1312) from
        (poly32Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf6))) ∗
      Poly32Mem (sp + 1312#64) (Vec32.ofFn f1312) ∗
      (WordRangeMem 32 (sp + 22240#64) (readU32LE prf6) ∗
        Oct8Mem (sp + 22400#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg6d_store_e2 hb hbase s2 sp _ _ _ hpc2 hrun2 hsp2 hspA2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, hspA3, hfp3, r0, r1, r2, r19, r20, hP3⟩
  refine SepWP.done hpc3 hrun3 ⟨hsp3, hspA3, hfp3.trans (hfp2.trans hfp1), r0, r1, r2, r19, r20, ?_⟩
  rw [hP3, poly32Mem_ofFn (sp + 1312#64), wordRangeMem32_eq_pointsToBytes (sp + 22240#64) h6]
  have hm22240 : ((sp + 22240#64) ↦ₛ prf6) ⊢ memRegion (sp + 22240#64) 128 := by
    simpa [h6] using pointsToBytes_entails_memRegion (sp + 22240#64) prf6
  exact entails_sub (oct8Mem_entails_memRegion (sp + 22400#64) _) (by sep_frame)
    (entails_sub (poly32Mem_entails_memRegion (sp + 11856#64) _) (by sep_frame)
      (entails_sub hm22240 (by sep_frame) (by sep_frame)))

/-- Full `e2` sub-segment (`+0x89f0 → +0x8d00`). -/
theorem seg6d_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg6E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf6 := shake256List 128 (coins ++ [6#8])
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Start) s
      (((sp + 19152#64) ↦₈ b0) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
       memRegion (sp + 1312#64) 512 ∗ memRegion (sp + 11856#64) 512 ∗
       memRegion (sp + 22240#64) 128 ∗ memRegion (sp + 22400#64) 1536 ∗
       memRegion (sp + 24448#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = 1536#64 ∧
        sf.readReg64 .x20 = sp + 22400#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
          PolyMem (sp + 22400#64) (fun _ => 0#128) ∗
          PolyMem (sp + 22912#64) (fun _ => 0#128) ∗
          PolyMem (sp + 23424#64) (fun _ => 0#128) ∗
          memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 19120#64) 33 ∗
          memRegion (sp + 22240#64) 128 ∗ memRegion (sp + 24448#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf6
  have h6 : prf6.length = 128 := shake256List_length 128 _
  rw [memRegion_split' (b := sp + 22400#64) (b' := sp + 22528#64) (n := 128) (k := (1408 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 19152#64) ↦₈ b0) ∗ ((sp + 19120#64) ↦ₛ coins) ∗
      memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 22400#64) 128 ∗
      memRegion (sp + 24448#64) 32 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1312#64) 512 ∗ memRegion (sp + 22528#64) 1408 ∗
        memRegion (sp + 11984#64) 384 ∗ memRegion (sp + 22240#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg6d_prf hb hbase s sp coins b0 _ hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hm512 : memRegion (sp + 11856#64) 128 ∗ memRegion (sp + 11984#64) 384 =
      memRegion (sp + 11856#64) 512 :=
    (memRegion_split' (b := sp + 11856#64) (b' := sp + 11984#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 22400#64) ↦ₛ prf6) ∗ memRegion (sp + 1312#64) 512 ∗
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 22240#64) 128 ∗
      (memRegion (sp + 22528#64) 1408 ∗ memRegion (sp + 19120#64) 33 ∗
        memRegion (sp + 24448#64) 32 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg6d_body hb hbase s1 sp prf6 h6 _ hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, r0, r1, r2, r19, r20, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm1536 : memRegion (sp + 22400#64) 128 ∗ memRegion (sp + 22528#64) 1408 =
      memRegion (sp + 22400#64) 1536 :=
    (memRegion_split' (b := sp + 22400#64) (b' := sp + 22528#64) (n := 128) (k := (1408 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 22400#64) 1536 ∗ stackAt sp 1136 ∗
      (PolyMem (sp + 1312#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
        memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 19120#64) 33 ∗
        memRegion (sp + 22240#64) 128 ∗ memRegion (sp + 24448#64) 32 ∗ Rest))
    (entails_sub (Entails.of_eq hm1536) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6d_memset_u hb hbase s2 sp _ hpc2 hrun2 hsp2 hspA2 r0 r1 r2 r19 r20 hcl2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, rfpf, r19f, r20f, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, rfpf.trans (hfp2.trans hfp1), r19f, r20f, hclf, hrof,
      Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6d
