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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
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
# `encapsulate1_serialized` (`B03`) — Segment 4c `e2` PRF + `cbd2` + Reversed Store (`+0x4b38 .. +0x4e38`)

Proves `+0x4b38..+0x4e38`: runs `B01` (`RW1`) on `coins ++ [6#8]` at `sp + 12400`, copies `prf6`
to `sp + 15520`, evaluates the 32-iteration SWAR `cbd2` loop into `sp + 4272`, stores `e2`'s 32
vectors in reversed order into `[sp + 1248, sp + 1760)`, and zeroes `uVec[0..2]` (`1536` B) at
`[sp + 2192, sp + 3728)` via `B29` `memset`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E2

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
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem Poly32Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At Vec32 VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  poly32Mem_entails_memRegion poly32Mem_ofFn polyVecNat pointsToBytes_eq_vecRangeMem
  step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg3Pure (
  HalfRangeMem SepStore16.halfRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4Pure (
  SepLoad32.wordRange WordRangeMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  blkPl03_ρ cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  cbd2_j3_eq cbd2_j7_eq cbd2_swar_eq exec_simdMovi_2d_0 halfRangeMem8_cbd2_eq orr_1_of_aligned16
  sepWP_elim_byte setMem_setMem setPC_setMem_setPC setWidth32_shr_zext64 shake256List_length
  step_bCond_not_taken step_bCond_taken truncate32_zext64 ubfx2_w32_norm vec128At_eq_halfRangeMem8
  vec2_bytesToVecNat_eq vecRangeBytes_zero vecRangeMem_focus wordRangeMem32_eq_pointsToBytes)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x4b38 → 0x4e34]
end

attribute [local irreducible] shake256List
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0

@[simp, arm64_norm, wp_norm] abbrev offSeg4E2    : BitVec 64 := BitVec.ofNat 64 19256

@[simp, arm64_norm, wp_norm] abbrev off4bac     : BitVec 64 := BitVec.ofNat 64 19372
@[simp, arm64_norm, wp_norm] abbrev off4bb0     : BitVec 64 := BitVec.ofNat 64 19376
@[simp, arm64_norm, wp_norm] abbrev off4c84     : BitVec 64 := BitVec.ofNat 64 19588
@[simp, arm64_norm, wp_norm] abbrev off4d20     : BitVec 64 := BitVec.ofNat 64 19744
@[simp, arm64_norm, wp_norm] abbrev off4d24     : BitVec 64 := BitVec.ofNat 64 19748
@[simp, arm64_norm, wp_norm] abbrev off4e34     : BitVec 64 := BitVec.ofNat 64 20020
@[simp, arm64_norm, wp_norm] abbrev offSeg5Start : BitVec 64 := BitVec.ofNat 64 20024

private theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]; exact cells32_entails_memRegion sPtr _ _ _ _

private theorem aligned16_add15520 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 15520#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 15520#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

/-! ## 1. `e2` PRF Call (`+0x4b38 → +0x4bb0`) & `memset` (`+0x4e34 → +0x4e38`) -/

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

section
attribute [local irreducible] blkPC03

private theorem seg4_e2_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg4E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4bac) s
      (((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 2192#64) 128 ∗ memRegion (sp + 15680#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 15680#64 ∧
        sm.readReg64 .x1 = sp + 2192#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 4272#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 4272#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 15680#64) (sp + 12400#64) (sp + 12400#64)
            (coins ++ [6#8]).length (coins ++ [6#8]).length ∗
          ((sp + 12400#64) ↦ₛ (coins ++ [6#8])) ∗
          memRegion (sp + 2192#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 15680#64)); intro k0 k1 k2 k3
  simp only [show sp + 15680#64 + 8#64 = sp + 15688#64 by clear * -; bv_omega,
    show sp + 15680#64 + 16#64 = sp + 15696#64 by clear * -; bv_omega,
    show sp + 15680#64 + 24#64 = sp + 15704#64 by clear * -; bv_omega]
  have _ := hpc
  wp_steps 16
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2192#64) (by decide) (by sep_focus); intro zf
  rw [show VecRangeMem 8 (sp + 2192#64) zf = PolyOctMem (sp + 2192#64) zf from rfl, ← oct8Mem_ofFn]
  step_strQ_oct8 7; step_strQ_oct8 6; wp_step; step_strQ_oct8 5; step_strQ_oct8 4
  step_strQ_oct8 3; step_strQ_oct8 2; step_strQ_oct8 1; step_strQ_oct8 0
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp,
      by simp,
      by simp,
      by simp,
      by simp, by simp,
      by simp, ?_⟩
  have hcoins6 : ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 6#8) =
      ((sp + 12400#64) ↦ₛ (coins ++ [6#8])) := by
    have ha32 : sp + 12400#64 + 32#64 = sp + 12432#64 := by clear * -; bv_omega
    rw [pointsToBytes_append, hc, ha32, pointsToBytes_cons, pointsToBytes_nil]
    simp only [sepConj_emp]
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  unfold Keccak2SlicesRW
  rw [hc6_len]
  simp only [show sp + 15680#64 + 8#64 = sp + 15688#64 by clear * -; bv_omega,
    show sp + 15680#64 + 16#64 = sp + 15696#64 by clear * -; bv_omega,
    show sp + 15680#64 + 24#64 = sp + 15704#64 by clear * -; bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 2192#64) _) (by sep_frame)
    (entails_sub (Entails.of_eq hcoins6) (by sep_frame) (by sep_frame))

end

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg4_e2_prf [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg4E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4bb0) s
      (((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 2192#64) 128 ∗ memRegion (sp + 4272#64) 128 ∗
       memRegion (sp + 15680#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .x19 = 0x55555555#64 ∧
        s1.readReg64 .x20 = sp + 4272#64 ∧
        (P1 ⊢ memRegion (sp + 12400#64) 33 ∗
          ((sp + 2192#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ∗
          memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 15680#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  refine SepWP.weaken_pre
    (P' := ((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
      memRegion (sp + 2192#64) 128 ∗ memRegion (sp + 15680#64) 32 ∗
      (memRegion (sp + 4272#64) 128 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4_e2_stage hb rfl s sp coins b0 (memRegion (sp + 4272#64) 128 ∗ stackAt sp 1136 ∗ Rest) hc hpc hrun hsp hspA) ?_
  rintro sm Pm hpcm hrunm hclm hrom ⟨hspm, hspAm, hx0m, hx1m, hx2m, hx3m, hx4m, hx19m, hx20m, hPm⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl sm.mem := hclm
  have _ : MlKemRoOk mlkemMpl sm.mem := hrom
  refine SepWP.weaken_pre hPm ?_
  have hc6_len : (coins ++ [6#8]).length = 33 := by simp [hc]
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk01_keccak2_136_31_RW1_ok
    (sp + 15680#64, sp + 12400#64, sp + 2192#64, sp + 4272#64, (128 : Nat), coins ++ [6#8])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hspm, spAligned_of_sp_eq hspAm hspm (hsp_sf.trans hspm),
      Eq.trans ‹_› (hx19m.trans hx19), Eq.trans ‹_› hx20m, ?_⟩
  rw [hspm]
  have hm4272 : ((sp + 4272#64) ↦ₛ shake256List 128 (coins ++ [6#8])) ⊢
      memRegion (sp + 4272#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 4272#64) (shake256List 128 (coins ++ [6#8]))
  have hm33 : ((sp + 12400#64) ↦ₛ (coins ++ [6#8])) ⊢ memRegion (sp + 12400#64) 33 := by
    simpa [hc6_len] using pointsToBytes_entails_memRegion (sp + 12400#64) (coins ++ [6#8])
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm4272 (by sep_frame)
      (entails_sub hm33 (by sep_frame) (by sep_frame)))

private theorem seg4_e2_memset_u [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + off4e34) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 2192#64)
    (hx1 : s.readReg64 .x1 = 0#64)
    (hx2 : s.readReg64 .x2 = 1536#64)
    (hx19 : s.readReg64 .x19 = sp + 2192#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg5Start) s
      (memRegion (sp + 2192#64) 1536 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 2192#64 ∧
        (Pf ⊢ PolyMem (sp + 2192#64) (fun _ => 0#128) ∗
          PolyMem (sp + 2704#64) (fun _ => 0#128) ∗
          PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s.mem := hcl
  have _ := hpc
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk29_memset_ok (sp + 2192#64, 0#8, (1536 : Nat))
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      Eq.trans ‹_› hx19, ?_⟩
  have h1536 : ((sp + 2192#64) ↦ₛ List.replicate 1536 0#8) =
      PolyMem (sp + 2192#64) (fun _ => 0#128) ∗
      PolyMem (sp + 2704#64) (fun _ => 0#128) ∗
      PolyMem (sp + 3216#64) (fun _ => 0#128) := by
    have hsplit : List.replicate 1536 (0#8) =
        vecRangeBytes 32 (fun _ => 0#128) ++
          (vecRangeBytes 32 (fun _ => 0#128) ++ vecRangeBytes 32 (fun _ => 0#128)) := by
      rw [vecRangeBytes_zero 32, ← List.replicate_add, ← List.replicate_add]
    rw [hsplit, pointsToBytes_append, pointsToBytes_append, vecRangeBytes_length,
      ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes]
    simp only [show (16 * 32 : Nat) = 512 from rfl,
      show sp + 2192#64 + 512#64 = sp + 2704#64 by bv_omega,
      show sp + 2704#64 + 512#64 = sp + 3216#64 by bv_omega]
    rfl
  exact entails_sub (Entails.of_eq h1536) (by sep_frame) (by sep_frame)

/-! ## 2. Copy `prf6` to `sp + 15520` & Zero `sp + 4272` (`+0x4bb0 → +0x4c84`) -/

attribute [local irreducible] blkPC03

local macro "ldr_p6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 2192#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "str_d6 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 15520#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_z4272 " k:num : tactic => `(tactic| (
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
private theorem seg4_e2_copy_zero [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (p6 d6 : Oct8) (Rest : SepProp)
    (hpc : s.pc = b + off4bb0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 4272#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4c84) s
      (Oct8Mem (sp + 2192#64) p6 ∗ Oct8Mem (sp + 15520#64) d6 ∗
       memRegion (sp + 4272#64) 512 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x8 = 0#64 ∧
        sm.readReg64 .x9 = sp + 15521#64 ∧
        sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 4272#64 ∧
        (Pm ⊢ Oct8Mem (sp + 2192#64) p6 ∗ Oct8Mem (sp + 15520#64) p6 ∗
          memRegion (sp + 4272#64) 512 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  ldr_p6 4 hrun hsp hsp_chk; ldr_p6 5 hrun hsp hsp_chk; wp_step
  ldr_p6 7 hrun hsp hsp_chk; wp_steps 2
  str_d6 4 hrun hsp hsp_chk; ldr_p6 6 hrun hsp hsp_chk; wp_step
  str_d6 5 hrun hsp hsp_chk; ldr_p6 0 hrun hsp hsp_chk
  str_d6 6 hrun hsp hsp_chk; ldr_p6 1 hrun hsp hsp_chk
  str_d6 7 hrun hsp hsp_chk; ldr_p6 2 hrun hsp hsp_chk
  str_d6 1 hrun hsp hsp_chk; ldr_p6 3 hrun hsp hsp_chk
  str_d6 0 hrun hsp hsp_chk; str_d6 3 hrun hsp hsp_chk; wp_step
  str_d6 2 hrun hsp hsp_chk
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (by decide) (by sep_focus); intro fz
  rw [show VecRangeMem 32 (sp + 4272#64) fz = PolyMem (sp + 4272#64) fz from rfl, ← poly32Mem_ofFn]
  str_z4272 31; str_z4272 30; str_z4272 29; str_z4272 28; str_z4272 27; str_z4272 26; str_z4272 25; str_z4272 24
  str_z4272 23; str_z4272 22; str_z4272 21; str_z4272 20; str_z4272 19; str_z4272 18; str_z4272 17; str_z4272 16
  str_z4272 15; str_z4272 14; str_z4272 13; str_z4272 12; str_z4272 11; str_z4272 10; str_z4272 9;  str_z4272 8
  str_z4272 7;  str_z4272 6;  str_z4272 5;  str_z4272 4;  str_z4272 3;  str_z4272 2;  str_z4272 1;  str_z4272 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp,
      by simp [orr_1_of_aligned16 _ (aligned16_add15520 sp hsp_chk)],
      by simp [hx19], by simp [hx20], ?_⟩
  have hp6 : ({ o0 := p6.get 0, o1 := p6.get 1, o2 := p6.get 2, o3 := p6.get 3,
                o4 := p6.get 4, o5 := p6.get 5, o6 := p6.get 6, o7 := p6.get 7 } : Oct8) = p6 := by
    cases p6; rfl
  rw [hp6]
  exact entails_sub (poly32Mem_entails_memRegion (sp + 4272#64) _) (by sep_frame) (by sep_frame)

/-! ## 3. `e2` 32-Iteration SWAR `cbd2` Loop (`+0x4c84 → +0x4d24`) -/

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

private theorem seg4_e2_cbd2_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8))
    {k : Nat} (hk : k < 32) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off4c84) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (16 * k))
    (hx9 : s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k))
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = dstPtr) :
    SepWP (blkPC03.rebase b (fun _ => none))
      (if k < 31 then b + off4c84 else b + off4d24) s
      (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
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
    refine step_bCond_taken (dst := blkPl03.base + off4c84)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hk31
          rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
            _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega)
      (by clear * -; dsimp [off4d20, off4c84]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * -; bv_omega,
        by simp; clear * -; bv_omega,
        by simp [hx19], by simp [hx20],
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩
  · have hk_eq : k = 31 := by omega
    subst hk_eq
    simp only [show ¬(31 < 31) by omega, ↓reduceIte]
    refine step_bCond_not_taken (dst := blkPl03.base + off4d24)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by clear * -; dsimp [off4d20, off4d24]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp [hx19], by simp [hx20],
        hmem_eq _ fun j hj => by rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega⟩

private theorem seg4_e2_cbd2_steps [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (sp prfPtr dstPtr : BitVec 64) (prf : List (BitVec 8)) (Rest : SepProp) :
    ∀ (rem k : Nat), rem + k = 32 → ∀ (s : State) (f : Nat → BitVec 128),
      (∀ i, i < k → f i = polyVecNat (neonCbd2Poly16 prf) i) →
      s.pc = (if k < 32 then b + off4c84 else b + off4d24) →
      s.status = .Running → s.sp = sp → s.spAligned = true →
      s.readReg64 .x8 = BitVec.ofNat 64 (16 * k) →
      s.readReg64 .x9 = prfPtr + 1#64 + BitVec.ofNat 64 (4 * k) →
      s.readReg64 .x19 = 0x55555555#64 → s.readReg64 .x20 = dstPtr →
      SepWP (blkPC03.rebase b (fun _ => none)) (b + off4d24) s
        (WordRangeMem 32 prfPtr (readU32LE prf) ∗ VecRangeMem 32 dstPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
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
    exact SepWP.done hpc hrun ⟨hsp, hspA, hx19, hx20, by
      congr 2; exact vecRangeMem_congr fun i hi => hf i hi⟩
  | succ rem ih =>
    intro k hsum s f hf hpc hrun hsp hspA hx8 hx9 hx19 hx20
    have hk : k < 32 := by omega
    simp only [hk, ↓reduceIte] at hpc
    refine SepWP.seq
      (seg4_e2_cbd2_iter hb hbase s sp prfPtr dstPtr prf hk f Rest
        hpc hrun hsp hspA hx8 hx9 hx19 hx20) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hP1⟩
    subst hP1
    exact ih (k + 1) (by omega) s1 _
      (fun i hi => by
        by_cases hik : i = k
        · subst hik; simp
        · simp [Function.update, hik, hf i (by omega)])
      (by by_cases hk31 : k < 31 <;> simp [hk31, show (k + 1 < 32) ↔ k < 31 by omega] at hpc1 ⊢ <;> exact hpc1)
      hrun1 hsp1 hspA1 hx8_1 hx9_1 hx19_1 hx20_1

/-! ## 4. Reversed Store of `e2` to `[sp + 1248, sp + 1760)` (`+0x4d24 → +0x4e34`) -/

@[expose] def revVec32 (v : Vec32) : Vec32 :=
  ⟨v.v31, v.v30, v.v29, v.v28, v.v27, v.v26, v.v25, v.v24,
   v.v23, v.v22, v.v21, v.v20, v.v19, v.v18, v.v17, v.v16,
   v.v15, v.v14, v.v13, v.v12, v.v11, v.v10, v.v9,  v.v8,
   v.v7,  v.v6,  v.v5,  v.v4,  v.v3,  v.v2,  v.v1,  v.v0⟩

theorem poly32Mem_revVec32_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    Poly32Mem ptr (revVec32 (Vec32.ofFn f)) = PolyMem ptr (fun i => f (31 - i)) := by
  rw [show revVec32 (Vec32.ofFn f) = Vec32.ofFn (fun i => f (31 - i)) from rfl]
  exact poly32Mem_ofFn ptr (fun i => f (31 - i))

local macro "ldr_src4272 " k:num : tactic => `(tactic| (
  apply step_ldrQ128 (wb := none)
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *]
  · wp_norm_lhs
  · apply SepLoad128.left; exact SepLoad128.vec32 (by decide : $k < 32) (by bv_omega) rfl
  · wp_norm_lhs))

local macro "str_dst1248 " k:num : tactic => `(tactic| (
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
private theorem seg4_e2_rev_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (src dst : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off4d24) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4e34) s
      (Poly32Mem (sp + 4272#64) src ∗ Poly32Mem (sp + 1248#64) dst ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = sp + 2192#64 ∧
        s'.readReg64 .x1 = 0#64 ∧
        s'.readReg64 .x2 = 1536#64 ∧
        s'.readReg64 .x19 = sp + 2192#64 ∧
        P' = (Poly32Mem (sp + 4272#64) src ∗ Poly32Mem (sp + 1248#64) (revVec32 src) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have _ := hpc
  ldr_src4272 0; wp_steps 4; str_dst1248 31
  ldr_src4272 1;  str_dst1248 30; ldr_src4272 2;  str_dst1248 29; ldr_src4272 3;  str_dst1248 28
  ldr_src4272 4;  str_dst1248 27; ldr_src4272 5;  str_dst1248 26; ldr_src4272 6;  str_dst1248 25
  ldr_src4272 7;  str_dst1248 24; ldr_src4272 8;  str_dst1248 23; ldr_src4272 9;  str_dst1248 22
  ldr_src4272 10; str_dst1248 21; ldr_src4272 11; str_dst1248 20; ldr_src4272 12; str_dst1248 19
  ldr_src4272 13; str_dst1248 18; ldr_src4272 14; str_dst1248 17; ldr_src4272 15; str_dst1248 16
  ldr_src4272 16; str_dst1248 15; ldr_src4272 17; str_dst1248 14; ldr_src4272 18; str_dst1248 13
  ldr_src4272 19; str_dst1248 12; ldr_src4272 20; str_dst1248 11; ldr_src4272 21; str_dst1248 10
  ldr_src4272 22; str_dst1248 9;  ldr_src4272 23; str_dst1248 8;  ldr_src4272 24; str_dst1248 7
  ldr_src4272 25; str_dst1248 6;  ldr_src4272 26; str_dst1248 5;  ldr_src4272 27; str_dst1248 4
  ldr_src4272 28; str_dst1248 3;  ldr_src4272 29; str_dst1248 2;  ldr_src4272 30; str_dst1248 1
  ldr_src4272 31; str_dst1248 0
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hal_sp,
      by simp, by simp, by simp, by simp,
      by cases src; cases dst; rfl⟩

private theorem seg4_e2_body [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (prf6 : List (BitVec 8)) (h6 : prf6.length = 128) (Rest : SepProp)
    (hpc : s.pc = b + off4bb0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 4272#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off4e34) s
      (((sp + 2192#64) ↦ₛ prf6) ∗ memRegion (sp + 1248#64) 512 ∗
       memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 128 ∗ Rest)
      (fun s3 P3 =>
        s3.sp = sp ∧ s3.spAligned = true ∧
        s3.readReg64 .x0 = sp + 2192#64 ∧
        s3.readReg64 .x1 = 0#64 ∧
        s3.readReg64 .x2 = 1536#64 ∧
        s3.readReg64 .x19 = sp + 2192#64 ∧
        (P3 ⊢ memRegion (sp + 2192#64) 128 ∗
          PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
          memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 2192#64) h6]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 15520#64) (hf := by sep_focus); intro fd6
  rw [show VecRangeMem 8 (sp + 15520#64) fd6 = Oct8Mem (sp + 15520#64) (Oct8.ofFn fd6) from
        (oct8Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 2192#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗
      Oct8Mem (sp + 15520#64) (Oct8.ofFn fd6) ∗ memRegion (sp + 4272#64) 512 ∗
      (memRegion (sp + 1248#64) 512 ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg4_e2_copy_zero hb hbase s sp _ _ _ hpc hrun hsp hspA hx19 hx20) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [← pointsToBytes128_eq_oct8Mem (sp + 15520#64) h6,
      ← wordRangeMem32_eq_pointsToBytes (sp + 15520#64) h6]
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 4272#64) (hf := by sep_focus); intro f4272
  refine SepWP.weaken_pre
    (P' := WordRangeMem 32 (sp + 15520#64) (readU32LE prf6) ∗ VecRangeMem 32 (sp + 4272#64) f4272 ∗
      (Oct8Mem (sp + 2192#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗ memRegion (sp + 1248#64) 512 ∗ Rest))
    (by sep_frame) ?_
  refine SepWP.seq
    (seg4_e2_cbd2_steps hb hbase sp (sp + 15520#64) (sp + 4272#64) prf6 _ 32 0 rfl s1 f4272
      (fun _ h => by omega) (by simpa using hpc1) hrun1 hsp1 hspA1 hx8_1
      (by rw [hx9_1]; clear * -; bv_omega) hx19_1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, _, _, hP2⟩
  subst hP2
  apply SepWP.of_memRegion_vecRangeMem 32 (sp + 1248#64) (hf := by sep_focus); intro f1248
  rw [← poly32Mem_ofFn (sp + 4272#64),
      show VecRangeMem 32 (sp + 1248#64) f1248 = Poly32Mem (sp + 1248#64) (Vec32.ofFn f1248) from
        (poly32Mem_ofFn _ _).symm]
  refine SepWP.weaken_pre
    (P' := Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat (neonCbd2Poly16 prf6))) ∗
      Poly32Mem (sp + 1248#64) (Vec32.ofFn f1248) ∗
      (WordRangeMem 32 (sp + 15520#64) (readU32LE prf6) ∗
        Oct8Mem (sp + 2192#64) (Oct8.ofFn (bytesToVecNat prf6)) ∗ Rest)) (by sep_frame) ?_
  refine SepWP.seq (seg4_e2_rev_store hb hbase s2 sp _ _ _ hpc2 hrun2 hsp2 hspA2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨hsp3, hspA3, r0, r1, r2, r19, hP3⟩
  refine SepWP.done hpc3 hrun3 ⟨hsp3, hspA3, r0, r1, r2, r19, ?_⟩
  rw [hP3, poly32Mem_revVec32_ofFn (sp + 1248#64),
      wordRangeMem32_eq_pointsToBytes (sp + 15520#64) h6]
  have hm15520 : ((sp + 15520#64) ↦ₛ prf6) ⊢ memRegion (sp + 15520#64) 128 := by
    simpa [h6] using pointsToBytes_entails_memRegion (sp + 15520#64) prf6
  exact entails_sub (oct8Mem_entails_memRegion (sp + 2192#64) _) (by sep_frame)
    (entails_sub (poly32Mem_entails_memRegion (sp + 4272#64) _) (by sep_frame)
      (entails_sub hm15520 (by sep_frame) (by sep_frame)))

theorem seg4_e2_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (b0 : BitVec 8) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + offSeg4E2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let prf6 := shake256List 128 (coins ++ [6#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg5Start) s
      (((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2192#64) 1536 ∗
       memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 128 ∗
       memRegion (sp + 15680#64) 32 ∗ stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = sp + 2192#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
          PolyMem (sp + 2192#64) (fun _ => 0#128) ∗
          PolyMem (sp + 2704#64) (fun _ => 0#128) ∗
          PolyMem (sp + 3216#64) (fun _ => 0#128) ∗
          memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 12400#64) 33 ∗
          memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15680#64) 32 ∗
          stackAt sp 1136 ∗ Rest)) := by
  intro prf6
  have h6 : prf6.length = 128 := shake256List_length 128 _
  rw [memRegion_split' (b := sp + 2192#64) (b' := sp + 2320#64) (n := 128) (k := (1408 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4272#64) (b' := sp + 4400#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12432#64) ↦₈ b0) ∗ ((sp + 12400#64) ↦ₛ coins) ∗
      memRegion (sp + 2192#64) 128 ∗ memRegion (sp + 4272#64) 128 ∗
      memRegion (sp + 15680#64) 32 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2320#64) 1408 ∗
        memRegion (sp + 4400#64) 384 ∗ memRegion (sp + 15520#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg4_e2_prf hb hbase s sp coins b0 _ hc hpc hrun hsp hspA hx19 hcl hro) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hm512 : memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 4400#64) 384 =
      memRegion (sp + 4272#64) 512 :=
    (memRegion_split' (b := sp + 4272#64) (b' := sp + 4400#64) (n := 128) (k := (384 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := ((sp + 2192#64) ↦ₛ prf6) ∗ memRegion (sp + 1248#64) 512 ∗
      memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 15520#64) 128 ∗
      (memRegion (sp + 2320#64) 1408 ∗ memRegion (sp + 12400#64) 33 ∗
        memRegion (sp + 15680#64) 32 ∗ stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg4_e2_body hb hbase s1 sp prf6 h6 _ hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, r0, r1, r2, r19, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hm1536 : memRegion (sp + 2192#64) 128 ∗ memRegion (sp + 2320#64) 1408 =
      memRegion (sp + 2192#64) 1536 :=
    (memRegion_split' (b := sp + 2192#64) (b' := sp + 2320#64) (n := 128) (k := (1408 : Nat))
      rfl (by bv_omega) (by decide)).symm
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 2192#64) 1536 ∗ stackAt sp 1136 ∗
      (PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
        memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 12400#64) 33 ∗
        memRegion (sp + 15520#64) 128 ∗ memRegion (sp + 15680#64) 32 ∗ Rest))
    (entails_sub (Entails.of_eq hm1536) (by sep_frame) (by sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg4_e2_memset_u hb hbase s2 sp _ hpc2 hrun2 hsp2 hspA2 r0 r1 r2 r19 hcl2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hx19f, hPf⟩
  exact SepWP.done hpcf hrunf ⟨hspf, hspAf, hx19f, hclf, hrof, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg4E2
