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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a

/-!
# `encapsulate1_serialized` (`B03`) — Segment 3 PRF Calls & Zeta Spill (`+0x32d4 .. +0x3624`)

1. `seg3_prf_calls` (`+0x32d4 → +0x33f8`): stages `coins ++ [0#8]`, `coins ++ [1#8]`,
   `coins ++ [2#8]` at `[sp + 16208, sp + 16307)` and invokes `B01` (`RW2` + `RW1`) to compute
   `prf0..2 = shake256List 128 (coins ++ [0/1/2#8])`.
2. `seg3_copy_and_zetas` (`+0x33f8 → +0x3624`): copies `prf0..2` to `[sp + 2192, sp + 2576)`,
   writes the 24 `Fwd2` `dup8x16` zeta vectors into `[sp + 1552, sp + 1936)`, and initializes
   the `Seg3` NTT loop registers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Prf
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse step_strQ128_region)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn oct8_ofFn_get
  pointsToBytes_eq_vecRangeMem step_ldrQ128 step_strQ128 vecRangeMem_congr
  vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdDup_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SepStore128.spillSlice Spill40 SpillSliceMem SymEnv evalSExpr spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  blkPl03_ρ cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Sym (seg3SpillConsts)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  exec_simdMovi_2d_0 offSeg3CbdStart orr_1_of_aligned16 seg3_memset_a sepWP_elim_byte
  setMem_setMem setPC_setMem_setPC shake256List_length stage_prf33_eq vec2_bytesToVecNat_eq)

attribute [local irreducible] shake256List dup8x16
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 exec_simdDup_8h

@[simp, arm64_norm, wp_norm] abbrev off32d4 : BitVec 64 := BitVec.ofNat 64 13012
@[simp, arm64_norm, wp_norm] abbrev off33c4 : BitVec 64 := BitVec.ofNat 64 13252
@[simp, arm64_norm, wp_norm] abbrev off33f8 : BitVec 64 := BitVec.ofNat 64 13304

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

private theorem le_128_pow64 : 128 ≤ 2 ^ 64 := by decide

private theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  exact cells32_entails_memRegion sPtr _ _ _ _
/-! ## 1. `Seg3` PRF Calls (`+0x32d4 → +0x33f8`) -/

@[simp, arm64_norm, wp_norm] private abbrev off33c0 : BitVec 64 := BitVec.ofNat 64 13248

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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg3_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off32d4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off33c0) s
      (((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 4272#64) 32 ∗
       memRegion (sp + 13984#64) 128 ∗
       memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 99 ∗
       memRegion (sp + 16528#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 4272#64 ∧
        sm.readReg64 .x1 = sp + 16528#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 15680#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = sp + 4272#64 ∧
        sm.readReg64 .x22 = 33#64 ∧
        sm.readReg64 .x23 = sp + 16274#64 ∧
        (Pm ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 4272#64) (sp + 16208#64) (sp + 16241#64) 33 33 ∗
          ((sp + 16208#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 16241#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 16274#64) ↦ₛ (coins ++ [2#8])) ∗
          memRegion (sp + 13984#64) 128 ∗
          memRegion (sp + 15680#64) 128 ∗
          memRegion (sp + 16528#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 12400#64) hc]
  have h99 : memRegion (sp + 16208#64) 99 =
      memRegion (sp + 16208#64) 16 ∗ memRegion (sp + 16224#64) 16 ∗ memRegion (sp + 16240#64) 1 ∗
      memRegion (sp + 16241#64) 16 ∗ memRegion (sp + 16257#64) 16 ∗ memRegion (sp + 16273#64) 1 ∗
      memRegion (sp + 16274#64) 16 ∗ memRegion (sp + 16290#64) 16 ∗ memRegion (sp + 16306#64) 1 := by
    rw [memRegion_split' (b' := sp + 16224#64) (n := 16) (k := (83 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16240#64) (n := 16) (k := (67 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16241#64) (n := 1)  (k := (66 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16257#64) (n := 16) (k := (50 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16273#64) (n := 16) (k := (34 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16274#64) (n := 1)  (k := (33 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16290#64) (n := 16) (k := (17 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 16306#64) (n := 16) (k := (1 : Nat))  rfl (by bv_omega) (by decide)]
  rw [h99]
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16208#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16224#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16241#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16257#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16274#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 16290#64) (by decide) (by sep_focus); intro v2b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 16240#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 16273#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 16306#64)); intro c2
  sep_frame_apply (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a.sepWP_elim_region32 (a := sp + 4272#64)); intro k0 k1 k2 k3
  simp only [show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
    show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
    show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega]
  refine step_ldrQ128 (wb := none) (ea := sp + 12400#64) (v := bytesToVecNat coins 0)
    hpc hrun (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_steps 3
  refine step_ldrQ128 (wb := none) (ea := (sp + 12400#64) + 16#64) (v := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) (by find_load128) (by wp_norm_lhs) ?_
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 16208#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 16241#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 16274#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 9
  refine step_strQ128 (wb := none) (ea := sp + 16257#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 16290#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 5
  refine step_strQ128 (wb := none) (ea := sp + 16224#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  step_dead_zero8 sp 16528
  step_dead_zero8 sp 15680
  step_dead_zero8 sp 13984
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 16208#64) 0#8 hc,
      ← stage_prf33_eq (sp + 16241#64) 1#8 hc,
      ← stage_prf33_eq (sp + 16274#64) 2#8 hc]
  unfold Keccak2SlicesRW
  simp only [show sp + 16208#64 + 16#64 = sp + 16224#64 by bv_omega,
    show sp + 16208#64 + 32#64 = sp + 16240#64 by bv_omega,
    show sp + 16241#64 + 16#64 = sp + 16257#64 by bv_omega,
    show sp + 16241#64 + 32#64 = sp + 16273#64 by bv_omega,
    show sp + 16274#64 + 16#64 = sp + 16290#64 by bv_omega,
    show sp + 16274#64 + 32#64 = sp + 16306#64 by bv_omega,
    show sp + 4272#64 + 8#64 = sp + 4280#64 by bv_omega,
    show sp + 4272#64 + 16#64 = sp + 4288#64 by bv_omega,
    show sp + 4272#64 + 24#64 = sp + 4296#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 16528#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 15680#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 13984#64) _) (by sep_frame) (by sep_frame)))

private theorem seg3_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp p2 : BitVec 64) {l2 : Nat} (hl2 : l2 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off33c4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = 33#64) (hx23 : s.readReg64 .x23 = p2) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + BitVec.ofNat 64 13300) s
      (memRegion (sp + 2192#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 2192#64 ∧ sm.readReg64 .x1 = sp + 13984#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 4272#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = sp + 2192#64 ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 2192#64) p2 p2 l2 l2 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a.sepWP_elim_region32 (a := sp + 2192#64))
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
  simp only [hl2, show sp + 2192#64 + 8#64 = sp + 2200#64 by bv_omega,
    show sp + 2192#64 + 16#64 = sp + 2208#64 by bv_omega,
    show sp + 2192#64 + 24#64 = sp + 2216#64 by bv_omega]
  sep_frame

end

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem seg3_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off32d4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12448#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off33f8) s
      (((sp + 12400#64) ↦ₛ coins) ∗
       memRegion (sp + 2192#64) 32 ∗
       memRegion (sp + 4272#64) 128 ∗
       memRegion (sp + 13984#64) 128 ∗
       memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 99 ∗
       memRegion (sp + 16528#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧
        sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readReg64 .x22 = sp + 2192#64 ∧
        (Pf ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          memRegion (sp + 2192#64) 32 ∗
          memRegion (sp + 4272#64) 128 ∗
          ((sp + 13984#64) ↦ₛ shake256List 128 (coins ++ [2#8])) ∗
          ((sp + 15680#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          memRegion (sp + 16208#64) 99 ∗
          ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  subst hbase
  rw [memRegion_split' (b := sp + 4272#64) (b' := sp + 4304#64) (n := 32) (k := (96 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 4272#64) 32 ∗
      memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
      memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
      (memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 4304#64) 96 ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg3_prf_stage hb rfl s sp coins _ hc hpc hrun hsp hspA) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc0_len : (coins ++ [0#8]).length = 33 := by simp [hc]
  have hc1_len : (coins ++ [1#8]).length = 33 := by simp [hc]
  have hc2_len : (coins ++ [2#8]).length = 33 := by simp [hc]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have hstep_rw2 : SepWP (blkPC03.rebase blkPl03.base (fun _ => none))
      (blkPl03.base + off33c4) s1
      (((sp + 12400#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 4272#64) (sp + 16208#64) (sp + 16241#64) 33 33 ∗
        ((sp + 16208#64) ↦ₛ (coins ++ [0#8])) ∗
        ((sp + 16241#64) ↦ₛ (coins ++ [1#8])) ∗
        ((sp + 16274#64) ↦ₛ (coins ++ [2#8])) ∗
        memRegion (sp + 13984#64) 128 ∗
        memRegion (sp + 15680#64) 128 ∗
        memRegion (sp + 16528#64) 128 ∗
        (memRegion (sp + 2192#64) 32 ∗ memRegion (sp + 4304#64) 96 ∗ stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = sp + 12448#64 ∧
        s2.readReg64 .x21 = sp + 4272#64 ∧ s2.readReg64 .x22 = 33#64 ∧
        s2.readReg64 .x23 = sp + 16274#64 ∧
        (P2 ⊢ ((sp + 12400#64) ↦ₛ coins) ∗
          memRegion (sp + 2192#64) 32 ∗
          memRegion (sp + 4272#64) 128 ∗
          memRegion (sp + 13984#64) 128 ∗
          ((sp + 15680#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          ((sp + 16208#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 16241#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 16274#64) ↦ₛ (coins ++ [2#8])) ∗
          ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    rw [show Keccak2SlicesRW (sp + 4272#64) (sp + 16208#64) (sp + 16241#64) 33 33 =
          Keccak2SlicesRW (sp + 4272#64) (sp + 16208#64) (sp + 16241#64)
            (coins ++ [0#8]).length (coins ++ [1#8]).length from by rw [hc0_len, hc1_len]]
    wp_cut_codeLoaded; wp_step
    wp_mlkem_call blk01_keccak2_136_31_RW2_ok
      (⟨sp + 4272#64, sp + 16208#64, sp + 16241#64, sp + 16528#64, sp + 15680#64,
        (128 : Nat), coins ++ [0#8], coins ++ [1#8]⟩ : Keccak2ShakeArgs)
    refine SepWP.done hpc_sf hrun_sf
      ⟨hsp_sf.trans hsp1, spAligned_of_sp_eq hspA1 hsp1 (hsp_sf.trans hsp1),
        Eq.trans ‹_› (hx19_1.trans hx19), Eq.trans ‹_› (hx20_1.trans hx20),
        Eq.trans ‹_› hx21_1, Eq.trans ‹_› hx22_1, Eq.trans ‹_› hx23_1, ?_⟩
    rw [hsp1]
    have hk4272 : Keccak2SlicesRW (sp + 4272#64) (sp + 16208#64) (sp + 16241#64)
          (coins ++ [0#8]).length (coins ++ [1#8]).length ∗
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
      memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 13984#64) 128 ∗
      ((sp + 15680#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
      ((sp + 16208#64) ↦ₛ (coins ++ [0#8])) ∗ ((sp + 16241#64) ↦ₛ (coins ++ [1#8])) ∗
      ((sp + 16274#64) ↦ₛ (coins ++ [2#8])) ∗
      ((sp + 16528#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗ stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg3_prf_stage2 hb rfl s2 sp (sp + 16274#64) hc2_len _ hpc2 hrun2 hsp2 hspA2 hx22_2 hx23_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  refine SepWP.weaken_pre hP3 ?_
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk01_keccak2_136_31_RW1_ok
    (sp + 2192#64, sp + 16274#64, sp + 13984#64, sp + 4272#64, (128 : Nat), coins ++ [2#8])
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp3, spAligned_of_sp_eq hspA3 hsp3 (hsp_sf.trans hsp3),
      Eq.trans ‹_› (hx19_3.trans hx19_2), Eq.trans ‹_› (hx20_3.trans hx20_2),
      Eq.trans ‹_› (hx21_3.trans hx21_2), Eq.trans ‹_› hx22_3, ?_⟩
  rw [hsp3]
  have hm4272 : ((sp + 4272#64) ↦ₛ shake256List 128 (coins ++ [2#8])) ⊢
      memRegion (sp + 4272#64) 128 := by
    simpa [shake256List_length] using
      pointsToBytes_entails_memRegion (sp + 4272#64) (shake256List 128 (coins ++ [2#8]))
  have hm99 : ((sp + 16208#64) ↦ₛ (coins ++ [0#8])) ∗
      ((sp + 16241#64) ↦ₛ (coins ++ [1#8])) ∗
      ((sp + 16274#64) ↦ₛ (coins ++ [2#8])) ⊢ memRegion (sp + 16208#64) 99 := by
    rw [memRegion_split' (b := sp + 16208#64) (b' := sp + 16241#64) (n := 33) (k := (66 : Nat))
          rfl (by clear * -; bv_omega) (by decide),
        memRegion_split' (b := sp + 16241#64) (b' := sp + 16274#64) (n := 33) (k := (33 : Nat))
          rfl (by clear * -; bv_omega) (by decide)]
    exact sepConj_mono
      (by simpa [hc0_len] using pointsToBytes_entails_memRegion (sp + 16208#64) (coins ++ [0#8]))
      (sepConj_mono
        (by simpa [hc1_len] using pointsToBytes_entails_memRegion (sp + 16241#64) (coins ++ [1#8]))
        (by simpa [hc2_len] using pointsToBytes_entails_memRegion (sp + 16274#64) (coins ++ [2#8])))
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub hm4272 (by sep_frame)
      (entails_sub hm99 (by sep_frame) (by sep_frame)))
/-! ## 2. Copy `prf0..2` & Spill 24 `Fwd2` Zeta Vectors (`+0x33f8 → +0x3624`) -/

attribute [local irreducible] blkPC03

@[simp, arm64_norm, wp_norm] private abbrev off3508 : BitVec 64 := BitVec.ofNat 64 13576

local macro "ldr_p0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 16528#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 15680#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 13984#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
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

local macro "str_sp " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1552#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.spillSlice (n := 40) (k := $k) (by decide) (by decide) rfl (by dsimp only [Spill40.set])))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))
@[expose] def setSpillZetas (t : Spill40) : Spill40 :=
  ⟨dup8x16 0xd43e#16, dup8x16 0xfa3e#16, dup8x16 0x054e#16, dup8x16 0xfb4e#16,
   dup8x16 0x29c2#16, dup8x16 0x03c2#16, dup8x16 0xc2b6#16, dup8x16 0xf129#16,
   dup8x16 0x0629#16, dup8x16 0x6c6e#16, dup8x16 0x026e#16, dup8x16 0xae55#16,
   dup8x16 0xbeca#16, dup8x16 0x6e1f#16, dup8x16 0x011f#16, dup8x16 0xcf8e#16,
   dup8x16 0x058e#16, dup8x16 0x34d5#16, dup8x16 0x05d5#16, dup8x16 0x0313#16,
   dup8x16 0xfa13#16, dup8x16 0x3999#16, dup8x16 0xfe99#16, dup8x16 0xf9c0#16,
   t.s24, t.s25, t.s26, t.s27, t.s28, t.s29, t.s30, t.s31,
   t.s32, t.s33, t.s34, t.s35, t.s36, t.s37, t.s38, t.s39⟩

private def midSpillZetas (t : Spill40) : Spill40 :=
  { t with
    s19 := dup8x16 0x0313#16, s20 := dup8x16 0xfa13#16, s21 := dup8x16 0x3999#16,
    s22 := dup8x16 0xfe99#16, s23 := dup8x16 0xf9c0#16 }

private def midD1 (p1 d1 : Oct8) : Oct8 :=
  ⟨p1.o0, d1.o1, p1.o2, d1.o3, p1.o4, p1.o5, p1.o6, d1.o7⟩

private def midD2 (p2 d2 : Oct8) : Oct8 :=
  ⟨d2.o0, p2.o1, p2.o2, d2.o3, d2.o4, d2.o5, p2.o6, d2.o7⟩

private theorem aligned16_add2192 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 2192#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 2192#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg3_copy_zetas_a [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d0 d1 d2 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off33f8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12448#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hx22 : s.readReg64 .x22 = sp + 2192#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off3508) s
      (Oct8Mem (sp + 16528#64) p0 ∗ Oct8Mem (sp + 15680#64) p1 ∗ Oct8Mem (sp + 13984#64) p2 ∗
       Oct8Mem (sp + 2192#64) d0 ∗ Oct8Mem (sp + 2320#64) d1 ∗ Oct8Mem (sp + 2448#64) d2 ∗
       SpillSliceMem 40 (sp + 1552#64) t ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x5 = 0#64 ∧ sm.readReg64 .x7 = sp + 2193#64 ∧
        sm.readReg64 .x8 = 0xcf8e#64 ∧ sm.readReg64 .x9 = sp + 12464#64 ∧
        sm.readReg64 .x10 = 16#64 ∧ sm.readReg64 .x11 = 0x058e#64 ∧
        sm.readReg64 .x12 = 0xfb4e#64 ∧ sm.readReg64 .x13 = 0x47fa#64 ∧
        sm.readReg64 .x14 = 0x019b#64 ∧ sm.readReg64 .x15 = 0x229b#64 ∧
        sm.readReg64 .x16 = 0x6833#64 ∧ sm.readReg64 .x17 = 0xf9dd#64 ∧
        sm.readReg64 .x18 = 0xc0dd#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 12448#64 ∧ sm.readReg64 .x21 = sp + 4272#64 ∧
        sm.readReg64 .x22 = sp + 2192#64 ∧ sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readVReg128 0#5 = dup8x16 0x34d5#16 ∧ sm.readVReg128 1#5 = p1.o7 ∧
        sm.readVReg128 2#5 = p2.o3 ∧ sm.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        sm.readVReg128 4#5 = dup8x16 0x05d5#16 ∧
        Pm = (Oct8Mem (sp + 16528#64) p0 ∗ Oct8Mem (sp + 15680#64) p1 ∗ Oct8Mem (sp + 13984#64) p2 ∗
          Oct8Mem (sp + 2192#64) p0 ∗ Oct8Mem (sp + 2320#64) (midD1 p1 d1) ∗
          Oct8Mem (sp + 2448#64) (midD2 p2 d2) ∗ SpillSliceMem 40 (sp + 1552#64) (midSpillZetas t) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p0 4 hrun hsp hsp_chk; ldr_p0 7 hrun hsp hsp_chk; wp_steps 2
  ldr_p0 5 hrun hsp hsp_chk; wp_step; str_d0 4 hrun hsp hsp_chk
  ldr_p0 6 hrun hsp hsp_chk; wp_step; str_d0 7 hrun hsp hsp_chk; wp_steps 2
  str_d0 6 hrun hsp hsp_chk; ldr_p0 0 hrun hsp hsp_chk; wp_step
  str_sp 20 hrun hsp hsp_chk; ldr_p2 1 hrun hsp hsp_chk; wp_step
  str_d0 0 hrun hsp hsp_chk; ldr_p0 2 hrun hsp hsp_chk; wp_step
  str_sp 23 hrun hsp hsp_chk; wp_steps 2; str_d0 2 hrun hsp hsp_chk
  ldr_p1 4 hrun hsp hsp_chk; wp_step; str_d2 1 hrun hsp hsp_chk; wp_steps 2
  str_d1 4 hrun hsp hsp_chk; ldr_p1 6 hrun hsp hsp_chk; wp_step
  str_sp 22 hrun hsp hsp_chk; wp_steps 2; str_d1 6 hrun hsp hsp_chk
  ldr_p1 0 hrun hsp hsp_chk; wp_steps 2; str_d0 5 hrun hsp hsp_chk
  ldr_p0 1 hrun hsp hsp_chk; str_d1 0 hrun hsp hsp_chk; ldr_p1 2 hrun hsp hsp_chk
  wp_steps 2; str_d0 1 hrun hsp hsp_chk; ldr_p0 3 hrun hsp hsp_chk
  str_d1 2 hrun hsp hsp_chk; ldr_p2 2 hrun hsp hsp_chk; wp_step
  str_sp 19 hrun hsp hsp_chk; wp_steps 2; str_d2 2 hrun hsp hsp_chk
  ldr_p2 6 hrun hsp hsp_chk; wp_step; str_d0 3 hrun hsp hsp_chk
  ldr_p1 5 hrun hsp hsp_chk; wp_step; str_d2 6 hrun hsp hsp_chk; wp_steps 2
  str_d1 5 hrun hsp hsp_chk; ldr_p1 7 hrun hsp hsp_chk; wp_step
  str_sp 21 hrun hsp hsp_chk; ldr_p2 3 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp [orr_1_of_aligned16 _ (aligned16_add2192 sp hsp_chk)],
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp [hx19],
      by simp [hx20], by simp [hx21], by simp [hx22], by simp,
      by simp, by simp [Oct8.get], by simp [Oct8.get], by simp, by simp,
      by dsimp [Oct8.get, midD1, midD2, midSpillZetas]; rfl⟩


theorem setSpillZetas_slot (t : Spill40) (env : SymEnv) (i : Nat) (hi : i < 24) :
    (setSpillZetas t).get i = evalSExpr env (seg3SpillConsts.get i) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | rfl | omega

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 200000 in
private theorem seg3_copy_zetas_b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (_hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 d1 d2 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off3508) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx5 : s.readReg64 .x5 = 0#64) (hx7 : s.readReg64 .x7 = sp + 2193#64)
    (hx8 : s.readReg64 .x8 = 0xcf8e#64) (hx9 : s.readReg64 .x9 = sp + 12464#64)
    (hx10 : s.readReg64 .x10 = 16#64) (hx11 : s.readReg64 .x11 = 0x058e#64)
    (hx12 : s.readReg64 .x12 = 0xfb4e#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12448#64) (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 0x34d5#16) (hv1 : s.readVReg128 1#5 = p1.o7)
    (hv2 : s.readVReg128 2#5 = p2.o3) (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hv4 : s.readVReg128 4#5 = dup8x16 0x05d5#16) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdStart) s
      (Oct8Mem (sp + 16528#64) p0 ∗ Oct8Mem (sp + 15680#64) p1 ∗ Oct8Mem (sp + 13984#64) p2 ∗
       Oct8Mem (sp + 2192#64) p0 ∗ Oct8Mem (sp + 2320#64) (midD1 p1 d1) ∗
       Oct8Mem (sp + 2448#64) (midD2 p2 d2) ∗
       SpillSliceMem 40 (sp + 1552#64) (midSpillZetas t) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 2193#64 ∧
        sf.readReg64 .x9 = sp + 12464#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧ sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        Pf = (Oct8Mem (sp + 16528#64) p0 ∗ Oct8Mem (sp + 15680#64) p1 ∗ Oct8Mem (sp + 13984#64) p2 ∗
          Oct8Mem (sp + 2192#64) p0 ∗ Oct8Mem (sp + 2320#64) p1 ∗ Oct8Mem (sp + 2448#64) p2 ∗
          SpillSliceMem 40 (sp + 1552#64) (setSpillZetas t) ∗ Rest)) := by
  subst _hbase
  have _ : MlKemBase blkPl03 blkPl03.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  cases p1; cases p2; cases t
  wp_step; str_sp 17 hrun hsp hsp_chk; wp_steps 2
  str_d1 7 hrun hsp hsp_chk; ldr_p1 1 hrun hsp hsp_chk
  str_d2 3 hrun hsp hsp_chk; ldr_p2 7 hrun hsp hsp_chk; wp_step
  str_sp 16 hrun hsp hsp_chk; wp_steps 2; str_d1 1 hrun hsp hsp_chk; ldr_p1 3 hrun hsp hsp_chk
  wp_step; str_sp 18 hrun hsp hsp_chk; ldr_p2 5 hrun hsp hsp_chk; str_sp 15 hrun hsp hsp_chk
  wp_steps 2; str_d1 3 hrun hsp hsp_chk; ldr_p2 0 hrun hsp hsp_chk; wp_step
  str_d2 7 hrun hsp hsp_chk; str_sp 14 hrun hsp hsp_chk; wp_steps 2
  str_d2 0 hrun hsp hsp_chk; ldr_p2 4 hrun hsp hsp_chk; str_d2 5 hrun hsp hsp_chk
  str_sp 13 hrun hsp hsp_chk; wp_steps 2; str_d2 4 hrun hsp hsp_chk; str_sp 12 hrun hsp hsp_chk
  wp_steps 2; str_sp 11 hrun hsp hsp_chk; wp_steps 2; str_sp 10 hrun hsp hsp_chk
  wp_steps 2; str_sp 9 hrun hsp hsp_chk; wp_steps 2; str_sp 8 hrun hsp hsp_chk
  wp_steps 2; str_sp 7 hrun hsp hsp_chk; wp_steps 2; str_sp 6 hrun hsp hsp_chk
  wp_steps 2; str_sp 5 hrun hsp hsp_chk; wp_steps 2; str_sp 4 hrun hsp hsp_chk
  wp_steps 2; str_sp 3 hrun hsp hsp_chk; wp_step; str_sp 2 hrun hsp hsp_chk
  wp_step; str_sp 1 hrun hsp hsp_chk; wp_steps 2; str_sp 0 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp [ro00Sym], by simp,
      by simp [ro00Sym], by simp,
      by simp [hx5], by simp [hx7], by simp [hx9], by simp [hx10],
      by simp, by simp [hx13], by simp [hx14], by simp [hx15],
      by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx19],
      by simp [hx20], by simp [hx21], by simp, by simp [hv3],
      by simp [Oct8.get, midD1, midD2, midSpillZetas, setSpillZetas]⟩

private theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

private theorem spillSliceMem40_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    SpillSliceMem 40 ptr (Spill40.ofFn f) = VecRangeMem 40 ptr f :=
  vecRangeMem_congr fun i hi => spill40_ofFn_get f i hi

theorem seg3_copy_and_zetas [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (prf0 prf1 prf2 : List (BitVec 8)) (Rest : SepProp)
    (h0 : prf0.length = 128) (h1 : prf1.length = 128) (h2 : prf2.length = 128)
    (hpc : s.pc = b + off33f8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 12448#64)
    (hx21 : s.readReg64 .x21 = sp + 4272#64)
    (hx22 : s.readReg64 .x22 = sp + 2192#64) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdStart) s
      (((sp + 16528#64) ↦ₛ prf0) ∗ ((sp + 15680#64) ↦ₛ prf1) ∗ ((sp + 13984#64) ↦ₛ prf2) ∗
       memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 1552#64) 640 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 2193#64 ∧
        sf.readReg64 .x9 = sp + 12464#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧ sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        ∃ t : Spill40, (∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2320#64) ↦ₛ prf1) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
            SpillSliceMem 40 (sp + 1552#64) t ∗
            memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
            memRegion (sp + 16528#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 16528#64) h0,
      pointsToBytes128_eq_oct8Mem (sp + 15680#64) h1,
      pointsToBytes128_eq_oct8Mem (sp + 13984#64) h2,
      memRegion_split' (b := sp + 2192#64) (b' := sp + 2320#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 2320#64) (b' := sp + 2448#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2192#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2320#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 2448#64) (hf := by sep_focus); intro fd2
  apply SepWP.of_memRegion_vecRangeMem 40 (sp + 1552#64) (hf := by sep_focus); intro fsp
  rw [show VecRangeMem 8 (sp + 2192#64) fd0 = Oct8Mem (sp + 2192#64) (Oct8.ofFn fd0) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 2320#64) fd1 = Oct8Mem (sp + 2320#64) (Oct8.ofFn fd1) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 2448#64) fd2 = Oct8Mem (sp + 2448#64) (Oct8.ofFn fd2) from
        (oct8Mem_ofFn _ _).symm,
      ← spillSliceMem40_ofFn (sp + 1552#64) fsp]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 16528#64) (Oct8.ofFn (bytesToVecNat prf0)) ∗
      Oct8Mem (sp + 15680#64) (Oct8.ofFn (bytesToVecNat prf1)) ∗
      Oct8Mem (sp + 13984#64) (Oct8.ofFn (bytesToVecNat prf2)) ∗
      Oct8Mem (sp + 2192#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 2320#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 2448#64) (Oct8.ofFn fd2) ∗
      SpillSliceMem 40 (sp + 1552#64) (Spill40.ofFn fsp) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (seg3_copy_zetas_a hb hbase s sp _ _ _ _ _ _ _ Rest hpc hrun hsp hspA hx19 hx20 hx21 hx22)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hx5m, hx7m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m,
      hx14m, hx15m, hx16m, hx17m, hx18m, hx19m, hx20m, hx21m, _, _, hv0m, hv1m, hv2m, hv3m, hv4m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (seg3_copy_zetas_b hb hbase sm sp _ _ _ _ _ _ Rest hpcm hrunm hspm hspAm
        hx5m hx7m hx8m hx9m hx10m hx11m hx12m hx13m hx14m hx15m hx16m hx17m hx18m
        hx19m hx20m hx21m hv0m hv1m hv2m hv3m hv4m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, _, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, rv3, setSpillZetas (Spill40.ofFn fsp),
      setSpillZetas_slot (Spill40.ofFn fsp), ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 2192#64) h0,
      ← pointsToBytes128_eq_oct8Mem (sp + 2320#64) h1,
      ← pointsToBytes128_eq_oct8Mem (sp + 2448#64) h2]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 16528#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 15680#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 13984#64) _) (by sep_frame) (by sep_frame)))

@[simp, arm64_norm, wp_norm] abbrev offSeg3Start : BitVec 64 := BitVec.ofNat 64 12928

theorem seg3_prf_setup [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (hashed : List (BitVec 8)) (Rest : SepProp)
    (hh : hashed.length = 64)
    (hpc : s.pc = b + offSeg3Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    let coins := hashed.drop 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offSeg3CbdStart) s
      (((sp + 6768#64) ↦ₛ hashed) ∗
       memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
       memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
       memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12448#64) 1536 ∗
       memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
       memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 2193#64 ∧
        sf.readReg64 .x9 = sp + 12464#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 12448#64 ∧ sf.readReg64 .x21 = sp + 4272#64 ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        ∃ t : Spill40, (∀ env i, i < 24 → t.get i = evalSExpr env (seg3SpillConsts.get i)) ∧
          (Pf ⊢ ((sp + 6768#64) ↦ₛ hashed) ∗
            SpillSliceMem 40 (sp + 1552#64) t ∗
            ((sp + 2192#64) ↦ₛ prf0) ∗ ((sp + 2320#64) ↦ₛ prf1) ∗ ((sp + 2448#64) ↦ₛ prf2) ∗
            memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 11440#64) 960 ∗
            ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
            PolyMem (sp + 12448#64) (fun _ => 0#128) ∗
            PolyMem (sp + 12960#64) (fun _ => 0#128) ∗
            PolyMem (sp + 13472#64) (fun _ => 0#128) ∗
            memRegion (sp + 13984#64) 128 ∗ memRegion (sp + 15680#64) 128 ∗
            memRegion (sp + 16208#64) 99 ∗ memRegion (sp + 16528#64) 128 ∗
            stackAt sp 1136 ∗ Rest)) := by
  intro coins prf0 prf1 prf2
  have hc_len : coins.length = 32 := by simp [coins, hh]
  refine SepWP.weaken_pre
    (P' := ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 11440#64) 960 ∗
      memRegion (sp + 12400#64) 33 ∗ memRegion (sp + 12448#64) 1536 ∗ stackAt sp 1136 ∗
      (memRegion (sp + 1552#64) 640 ∗ memRegion (sp + 2192#64) 384 ∗
        memRegion (sp + 4272#64) 512 ∗ memRegion (sp + 13984#64) 128 ∗
        memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 99 ∗
        memRegion (sp + 16528#64) 128 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg3_memset_a hb hbase s sp hashed _ hh hpc hrun hsp hspA hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  rw [memRegion_split' (b := sp + 2192#64) (b' := sp + 2224#64) (n := 32) (k := (352 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4272#64) (b' := sp + 4400#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre
    (P' := ((sp + 12400#64) ↦ₛ coins) ∗ memRegion (sp + 2192#64) 32 ∗
      memRegion (sp + 4272#64) 128 ∗ memRegion (sp + 13984#64) 128 ∗
      memRegion (sp + 15680#64) 128 ∗ memRegion (sp + 16208#64) 99 ∗
      memRegion (sp + 16528#64) 128 ∗ stackAt sp 1136 ∗
      (((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 1552#64) 640 ∗
        memRegion (sp + 2224#64) 352 ∗ memRegion (sp + 4400#64) 384 ∗
        memRegion (sp + 11440#64) 960 ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
        PolyMem (sp + 12448#64) (fun _ => 0#128) ∗
        PolyMem (sp + 12960#64) (fun _ => 0#128) ∗
        PolyMem (sp + 13472#64) (fun _ => 0#128) ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg3_prf_calls hb hbase s1 sp coins _ hc_len hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hcl1 hro1) ?_
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
    (P' := ((sp + 16528#64) ↦ₛ prf0) ∗ ((sp + 15680#64) ↦ₛ prf1) ∗ ((sp + 13984#64) ↦ₛ prf2) ∗
      memRegion (sp + 2192#64) 384 ∗ memRegion (sp + 1552#64) 640 ∗
      (((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 4272#64) 512 ∗
        memRegion (sp + 11440#64) 960 ∗ ((sp + 12400#64) ↦ₛ coins) ∗ ((sp + 12432#64) ↦₈ 0#8) ∗
        PolyMem (sp + 12448#64) (fun _ => 0#128) ∗ PolyMem (sp + 12960#64) (fun _ => 0#128) ∗
        PolyMem (sp + 13472#64) (fun _ => 0#128) ∗ memRegion (sp + 16208#64) 99 ∗
        stackAt sp 1136 ∗ Rest))
    (entails_sub (Entails.of_eq hm384) (by sep_frame)
      (entails_sub (Entails.of_eq hm512) (by sep_frame) (by sep_frame))) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg3_copy_and_zetas hb hbase s2 sp prf0 prf1 prf2 _
      (shake256List_length 128 _) (shake256List_length 128 _) (shake256List_length 128 _)
      hpc2 hrun2 hsp2 hspA2 hx19_2 hx20_2 hx21_2 hx22_2) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13,
    r14, r15, r16, r17, r18, r19, r20, r21, rv3, t, ht, hPf⟩
  exact SepWP.done hpcf hrunf
    ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15, r16, r17, r18,
      r19, r20, r21, rv3, hclf, hrof, t, ht, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Prf
