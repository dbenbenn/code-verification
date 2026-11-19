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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a

/-!
# `kyber_decapsulate` (`B06`) — Segment 6 `rHat` PRF Calls & Zeta Spill (`Seg6Prf`)

1. `seg6_prf_calls` (`+0x7718 → +0x7868`): stages `coins ++ [0..3#8]` at `[sp + 28368, sp + 28500)`
   and invokes `B01` (`RW2` twice) to compute `prf0..3 = shake256List 128 (coins ++ [0..3#8])`.
2. `seg6_copy_and_zetas` (`+0x7868 → +0x7ad4`): copies `prf0..3` to `[sp + 30448, sp + 30960)`,
   writes the 24 `Fwd2` `dup8x16` zeta vectors into `[sp + 1792, sp + 2176)`, and initializes
   the `Seg6` `rHat` NTT loop registers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Prf

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mlkemBlockPlacement_ρ mlkemCall_of_blockOk
  mlkemMpl resolve_blk01 resolve_ro00 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  Keccak2ShakeArgs Keccak2SlicesRW keccak2_136_31_RW2Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_31 (
  blk01_keccak2_136_31_RW2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2 (
  setPC_setMem_collapse)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Oct8 Oct8Mem PolyMem PolyOctMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem
  Vec128At VecRangeMem bytesToVecNat oct8Mem_entails_memRegion oct8Mem_ofFn
  pointsToBytes_eq_vecRangeMem step_ldrQ128 step_strQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (exec_simdDup_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  cells32_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SepStore128.spillSlice Spill40 SpillSliceMem SymEnv evalSExpr spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatSym1a (
  symSeg6FwdInit)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  PublicKeyStateAt exec_simdMovi_2d_0 orr_1_of_aligned16 sepWP_elim_byte setMem_setMem
  setPC_setMem_setPC shake256List_length stage_prf33_eq vec2_bytesToVecNat_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Cbd (
  off76a8 off7718 offRhatCbdStart seg6_entry_ops)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x7718 → 0x7ad0]
end

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym :=
  mlkemBlockPlacement_ρ 6 sym

theorem blk01_rw2_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 1)
      (mlkemMultiLib.withCodeLoaded mlkemMpl (keccak2_136_31_RW2Spec mlkemMpl)) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk01_keccak2_136_31_RW2_ok

attribute [local irreducible] blkPC06 shake256List dup8x16
attribute [local wp_norm ↓ high] exec_simdMovi_2d_0 exec_simdDup_8h

@[simp, arm64_norm, wp_norm] private abbrev off7828 : BitVec 64 := BitVec.ofNat 64 30760
@[simp, arm64_norm, wp_norm] private abbrev off782c : BitVec 64 := BitVec.ofNat 64 30764
@[simp, arm64_norm, wp_norm] abbrev off7868 : BitVec 64 := BitVec.ofNat 64 30824
@[simp, arm64_norm, wp_norm] private abbrev off7980 : BitVec 64 := BitVec.ofNat 64 31104

theorem keccak2SlicesRW_entails_memRegion32 (sPtr p0 p1 : BitVec 64) (l0 l1 : Nat) :
    Keccak2SlicesRW sPtr p0 p1 l0 l1 ⊢ memRegion sPtr 32 := by
  dsimp only [Keccak2SlicesRW]
  exact cells32_entails_memRegion sPtr _ _ _ _

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

local syntax "find_load128" : tactic
local macro_rules
  | `(tactic| find_load128) => `(tactic| first
      | exact SepLoad128.vec128At rfl
      | (apply SepLoad128.left; find_load128)
      | (apply SepLoad128.right; find_load128))

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

local macro "step_strb_x25 " eaTerm:term:arg valTerm:term:arg hrunId:term:arg hx25Id:term:arg : tactic => `(tactic| (
  apply SepWP.step_str8 (wb := none) (ea := $eaTerm) (val := $valTerm)
  · wp_norm_lhs
  · simp [$hrunId:term]
  · wp_norm_lhs
  · rfl
  · simp [evalAddrMode, $hx25Id:term]
  · rfl
  · find_store8
  · wp_norm_lhs
  intro _
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6_prf_stage [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off7718) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off7828) s
      (((sp + 26272#64) ↦ₛ coins) ∗
       memRegion (sp + 14432#64) 128 ∗
       memRegion (sp + 28368#64) 132 ∗
       memRegion (sp + 30448#64) 32 ∗
       memRegion (sp + 33008#64) 128 ∗
       memRegion (sp + 33536#64) 128 ∗
       memRegion (sp + 33888#64) 128 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 30448#64 ∧
        sm.readReg64 .x1 = sp + 33536#64 ∧
        sm.readReg64 .x2 = 128#64 ∧
        sm.readReg64 .x3 = sp + 33888#64 ∧
        sm.readReg64 .x4 = 128#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = 33#64 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = sp + 28434#64 ∧
        sm.readReg64 .x24 = sp + 28467#64 ∧
        sm.readReg64 .x25 = sp + 28368#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          Keccak2SlicesRW (sp + 30448#64) (sp + 28368#64) (sp + 28401#64) 33 33 ∗
          ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ∗
          ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ∗
          memRegion (sp + 14432#64) 128 ∗
          memRegion (sp + 33008#64) 128 ∗
          memRegion (sp + 33536#64) 128 ∗
          memRegion (sp + 33888#64) 128 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rw [← vec2_bytesToVecNat_eq (sp + 26272#64) hc]
  have h132 : memRegion (sp + 28368#64) 132 =
      memRegion (sp + 28368#64) 16 ∗ memRegion (sp + 28384#64) 16 ∗ memRegion (sp + 28400#64) 1 ∗
      memRegion (sp + 28401#64) 16 ∗ memRegion (sp + 28417#64) 16 ∗ memRegion (sp + 28433#64) 1 ∗
      memRegion (sp + 28434#64) 16 ∗ memRegion (sp + 28450#64) 16 ∗ memRegion (sp + 28466#64) 1 ∗
      memRegion (sp + 28467#64) 16 ∗ memRegion (sp + 28483#64) 16 ∗ memRegion (sp + 28499#64) 1 := by
    rw [memRegion_split' (b' := sp + 28384#64) (n := 16) (k := (116 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28400#64) (n := 16) (k := (100 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28401#64) (n := 1)  (k := (99 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28417#64) (n := 16) (k := (83 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28433#64) (n := 16) (k := (67 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28434#64) (n := 1)  (k := (66 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28450#64) (n := 16) (k := (50 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28466#64) (n := 16) (k := (34 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28467#64) (n := 1)  (k := (33 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28483#64) (n := 16) (k := (17 : Nat))  rfl (by bv_omega) (by decide),
        memRegion_split' (b' := sp + 28499#64) (n := 16) (k := (1 : Nat))   rfl (by bv_omega) (by decide)]
  refine step_ldrQ128 (wb := none) (ea := sp + 26272#64) (v := bytesToVecNat coins 0)
    hpc hrun (by wp_norm_lhs)
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
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28368#64) (by decide) (by sep_focus); intro v0a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28384#64) (by decide) (by sep_focus); intro v0b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28401#64) (by decide) (by sep_focus); intro v1a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28417#64) (by decide) (by sep_focus); intro v1b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28434#64) (by decide) (by sep_focus); intro v2a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28450#64) (by decide) (by sep_focus); intro v2b
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28467#64) (by decide) (by sep_focus); intro v3a
  apply SepWP.of_memRegion_vecRangeMem 1 (sp + 28483#64) (by decide) (by sep_focus); intro v3b
  dsimp only [VecRangeMem]; simp only [sepConj_emp]
  sep_frame_apply (sepWP_elim_byte (a := sp + 28400#64)); intro c0
  sep_frame_apply (sepWP_elim_byte (a := sp + 28433#64)); intro c1
  sep_frame_apply (sepWP_elim_byte (a := sp + 28466#64)); intro c2
  sep_frame_apply (sepWP_elim_byte (a := sp + 28499#64)); intro c3
  sep_frame_apply (sepWP_elim_region32 (a := sp + 30448#64)); intro k0 k1 k2 k3
  simp only [sepConj_assoc,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  step_strb_x25 (sp + 28433#64) 1#8 hrun hx25
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28368#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28401#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28434#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28467#64) (val := bytesToVecNat coins 0)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_steps 2
  step_strb_x25 (sp + 28466#64) 2#8 hrun hx25
  wp_steps 2
  step_strb_x25 (sp + 28499#64) 3#8 hrun hx25
  wp_steps 2
  refine step_strQ128 (wb := none) (ea := sp + 28384#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, hsp, hsp_chk])
    (by simp [evalAddrMode, hsp]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 28417#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 28450#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  wp_step
  refine step_strQ128 (wb := none) (ea := sp + 28483#64) (val := bytesToVecNat coins 1)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx25]) rfl (by find_store128) (by wp_norm_lhs) fun _ => ?_
  rw [setMem_setMem]
  step_strb_x25 (sp + 28400#64) 0#8 hrun hx25
  step_dead_zero8 sp 14432
  step_dead_zero8 sp 33536
  step_dead_zero8 sp 33888
  step_dead_zero8 sp 33008
  wp_steps 4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp [hx25], by simp, ?_⟩
  rw [← stage_prf33_eq (sp + 28368#64) 0#8 hc,
      ← stage_prf33_eq (sp + 28401#64) 1#8 hc,
      ← stage_prf33_eq (sp + 28434#64) 2#8 hc,
      ← stage_prf33_eq (sp + 28467#64) 3#8 hc]
  unfold Keccak2SlicesRW
  simp only [
    show sp + 28368#64 + 16#64 = sp + 28384#64 by bv_omega,
    show sp + 28368#64 + 32#64 = sp + 28400#64 by bv_omega,
    show sp + 28401#64 + 16#64 = sp + 28417#64 by bv_omega,
    show sp + 28401#64 + 32#64 = sp + 28433#64 by bv_omega,
    show sp + 28434#64 + 16#64 = sp + 28450#64 by bv_omega,
    show sp + 28434#64 + 32#64 = sp + 28466#64 by bv_omega,
    show sp + 28467#64 + 16#64 = sp + 28483#64 by bv_omega,
    show sp + 28467#64 + 32#64 = sp + 28499#64 by bv_omega,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  exact entails_sub (oct8Mem_entails_memRegion (sp + 14432#64) _) (by sep_frame)
    (entails_sub (oct8Mem_entails_memRegion (sp + 33536#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 33888#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 33008#64) _) (by sep_frame) (by sep_frame))))

@[simp, arm64_norm, wp_norm] private abbrev off7864 : BitVec 64 := BitVec.ofNat 64 30820

private theorem seg6_prf_stage2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp p2 p3 : BitVec 64) {l2 l3 : Nat} (hl2 : l2 = 33) (hl3 : l3 = 33) (Rest : SepProp)
    (hpc : s.pc = b + off782c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = 33#64) (hx23 : s.readReg64 .x23 = p2) (hx24 : s.readReg64 .x24 = p3) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off7864) s
      (memRegion (sp + 30448#64) 32 ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = sp + 30448#64 ∧ sm.readReg64 .x1 = sp + 33008#64 ∧
        sm.readReg64 .x2 = 128#64 ∧ sm.readReg64 .x3 = sp + 14432#64 ∧
        sm.readReg64 .x4 = 128#64 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 30448#64 ∧ sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        (Pm ⊢ Keccak2SlicesRW (sp + 30448#64) p2 p3 l2 l3 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_region32 (a := sp + 30448#64))
  intro d0 d1 d2 d3
  simp only [show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  wp_steps 14
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp,
      by simp, by simp, by simp, ?_⟩
  unfold Keccak2SlicesRW
  simp only [hl2, hl3,
    show sp + 30448#64 + 8#64 = sp + 30456#64 by bv_omega,
    show sp + 30448#64 + 16#64 = sp + 30464#64 by bv_omega,
    show sp + 30448#64 + 24#64 = sp + 30472#64 by bv_omega]
  sep_frame

private theorem stage4_entails_memRegion132 (sp : BitVec 64) {coins : List (BitVec 8)}
    (hc : coins.length = 32) :
    ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ∗ ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ∗
      ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ∗ ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ⊢
      memRegion (sp + 28368#64) 132 := by
  have hc0 : (coins ++ [0#8]).length = 33 := by simp [hc]
  have hc1 : (coins ++ [1#8]).length = 33 := by simp [hc]
  have hc2 : (coins ++ [2#8]).length = 33 := by simp [hc]
  have hc3 : (coins ++ [3#8]).length = 33 := by simp [hc]
  rw [memRegion_split' (b := sp + 28368#64) (b' := sp + 28401#64) (n := 33) (k := (99 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28401#64) (b' := sp + 28434#64) (n := 33) (k := (66 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 28434#64) (b' := sp + 28467#64) (n := 33) (k := (33 : Nat))
        rfl (by bv_omega) (by decide)]
  have hmr0 : ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ⊢ memRegion (sp + 28368#64) 33 := by
    have h := pointsToBytes_entails_memRegion (sp + 28368#64) (coins ++ [0#8]); rwa [hc0] at h
  have hmr1 : ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ⊢ memRegion (sp + 28401#64) 33 := by
    have h := pointsToBytes_entails_memRegion (sp + 28401#64) (coins ++ [1#8]); rwa [hc1] at h
  have hmr2 : ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ⊢ memRegion (sp + 28434#64) 33 := by
    have h := pointsToBytes_entails_memRegion (sp + 28434#64) (coins ++ [2#8]); rwa [hc2] at h
  have hmr3 : ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ⊢ memRegion (sp + 28467#64) 33 := by
    have h := pointsToBytes_entails_memRegion (sp + 28467#64) (coins ++ [3#8]); rwa [hc3] at h
  exact entails_sub hmr0 (by sep_frame)
    (entails_sub hmr1 (by sep_frame)
      (entails_sub hmr2 (by sep_frame)
        (entails_sub hmr3 (by sep_frame) (by sep_frame))))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
theorem seg6_prf_calls [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (coins : List (BitVec 8)) (Rest : SepProp)
    (hc : coins.length = 32)
    (hpc : s.pc = b + off7718) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 26320#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off7868) s
      (((sp + 26272#64) ↦ₛ coins) ∗
       memRegion (sp + 14432#64) 128 ∗
       memRegion (sp + 28368#64) 132 ∗
       memRegion (sp + 30448#64) 32 ∗
       memRegion (sp + 33008#64) 128 ∗
       memRegion (sp + 33536#64) 128 ∗
       memRegion (sp + 33888#64) 128 ∗
       stackAt sp 1136 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧
        sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 26320#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          ((sp + 14432#64) ↦ₛ shake256List 128 (coins ++ [3#8])) ∗
          memRegion (sp + 28368#64) 132 ∗
          memRegion (sp + 30448#64) 32 ∗
          ((sp + 33008#64) ↦ₛ shake256List 128 (coins ++ [2#8])) ∗
          ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          ((sp + 33888#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  subst hbase
  refine sepWP_seq_env hcl hro
    (seg6_prf_stage hb rfl s sp coins _ hc hpc hrun hsp hspA hx25) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hfp1, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  have hc0_len : (coins ++ [0#8]).length = 33 := by simp [hc]
  have hc1_len : (coins ++ [1#8]).length = 33 := by simp [hc]
  have hc2_len : (coins ++ [2#8]).length = 33 := by simp [hc]
  have hc3_len : (coins ++ [3#8]).length = 33 := by simp [hc]
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem := hcl1
  have _ : MlKemRoOk mlkemMpl s1.mem := hro1
  have hstep_rw2a : SepWP (blkPC06.rebase blkPl06.base (fun _ => none))
      (blkPl06.base + off782c) s1
      (((sp + 26272#64) ↦ₛ coins) ∗
        Keccak2SlicesRW (sp + 30448#64) (sp + 28368#64) (sp + 28401#64) 33 33 ∗
        ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ∗
        ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ∗
        ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ∗
        ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ∗
        memRegion (sp + 14432#64) 128 ∗
        memRegion (sp + 33008#64) 128 ∗
        memRegion (sp + 33536#64) 128 ∗
        memRegion (sp + 33888#64) 128 ∗
        (stackAt sp 1136 ∗ Rest))
      (fun s2 P2 =>
        s2.sp = sp ∧ s2.spAligned = true ∧
        s2.readReg64 .x19 = 0x55555555#64 ∧ s2.readReg64 .x20 = 33#64 ∧
        s2.readReg64 .x21 = sp + 14432#64 ∧ s2.readReg64 .x22 = sp + 26320#64 ∧
        s2.readReg64 .x23 = sp + 28434#64 ∧ s2.readReg64 .x24 = sp + 28467#64 ∧
        s2.readReg64 .x25 = sp + 28368#64 ∧ s2.readReg64 .fp = s.readReg64 .fp ∧
        (P2 ⊢ ((sp + 26272#64) ↦ₛ coins) ∗
          memRegion (sp + 30448#64) 32 ∗
          ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ∗
          ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ∗
          ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ∗
          ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ∗
          memRegion (sp + 14432#64) 128 ∗
          memRegion (sp + 33008#64) 128 ∗
          ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
          ((sp + 33888#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
          stackAt sp 1136 ∗ Rest)) := by
    have hsl1 : Keccak2SlicesRW (sp + 30448#64) (sp + 28368#64) (sp + 28401#64) 33 33 =
        Keccak2SlicesRW (sp + 30448#64) (sp + 28368#64) (sp + 28401#64)
          (coins ++ [0#8]).length (coins ++ [1#8]).length := by
      rw [hc0_len, hc1_len]
    rw [hsl1]
    have hlen01 : (coins ++ [0#8]).length = (coins ++ [1#8]).length := by rw [hc0_len, hc1_len]
    have hlt0 : (coins ++ [0#8]).length < 2 ^ 32 := by rw [hc0_len]; decide
    have hout128 : (128 : Nat) = 32 ∨ (128 : Nat) = 128 := Or.inr rfl
    wp_call (blk01_rw2_06 blkPl06.base)
      (⟨sp + 30448#64, sp + 28368#64, sp + 28401#64, sp + 33536#64, sp + 33888#64,
        (128 : Nat), coins ++ [0#8], coins ++ [1#8]⟩ : Keccak2ShakeArgs)
    clear hcl hro hcl1 hro1
    have hsp_sf : sf.sp = sp := by simp [*]
    refine SepWP.done (by wp_norm_lhs) (by assumption)
      ⟨hsp_sf, spAligned_of_sp_eq hspA1 hsp1 hsp_sf,
        by simp [*], by simp [*], by simp [*], by simp [*],
        by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
    rw [hsp1]
    exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame) (by sep_frame)
  refine sepWP_seq_env hcl1 hro1 hstep_rw2a ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hfp2, hP2⟩
  refine SepWP.weaken_pre hP2 ?_
  refine SepWP.weaken_pre
    (P' := memRegion (sp + 30448#64) 32 ∗
      (((sp + 26272#64) ↦ₛ coins) ∗
        ((sp + 28368#64) ↦ₛ (coins ++ [0#8])) ∗
        ((sp + 28401#64) ↦ₛ (coins ++ [1#8])) ∗
        ((sp + 28434#64) ↦ₛ (coins ++ [2#8])) ∗
        ((sp + 28467#64) ↦ₛ (coins ++ [3#8])) ∗
        memRegion (sp + 14432#64) 128 ∗
        memRegion (sp + 33008#64) 128 ∗
        ((sp + 33536#64) ↦ₛ shake256List 128 (coins ++ [0#8])) ∗
        ((sp + 33888#64) ↦ₛ shake256List 128 (coins ++ [1#8])) ∗
        stackAt sp 1136 ∗ Rest))
    (by sep_frame) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg6_prf_stage2 hb rfl s2 sp (sp + 28434#64) (sp + 28467#64) hc2_len hc3_len _
      hpc2 hrun2 hsp2 hspA2 hx20_2 hx23_2 hx24_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx0_3, hx1_3, hx2_3, hx3_3, hx4_3, hx19_3, hx20_3, hx21_3, hx22_3, hx25_3, hfp3, hP3⟩
  have _ : mlkemMultiLib.CodeLoaded mlkemMpl s3.mem := hcl3
  have _ : MlKemRoOk mlkemMpl s3.mem := hro3
  have _ := hpc3
  refine SepWP.weaken_pre hP3 ?_
  have hlen23 : (coins ++ [2#8]).length = (coins ++ [3#8]).length := by rw [hc2_len, hc3_len]
  have hlt2 : (coins ++ [2#8]).length < 2 ^ 32 := by rw [hc2_len]; decide
  have hout128 : (128 : Nat) = 32 ∨ (128 : Nat) = 128 := Or.inr rfl
  wp_call (blk01_rw2_06 blkPl06.base)
    (⟨sp + 30448#64, sp + 28434#64, sp + 28467#64, sp + 33008#64, sp + 14432#64,
      (128 : Nat), coins ++ [2#8], coins ++ [3#8]⟩ : Keccak2ShakeArgs)
  clear hcl hro hcl1 hro1 hcl2 hro2 hcl3 hro3 ‹mlkemMultiLib.CodeLoaded mlkemMpl s3.mem› ‹MlKemRoOk mlkemMpl s3.mem›
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by wp_norm_lhs) (by assumption)
    ⟨hsp_sf, spAligned_of_sp_eq hspA3 hsp3 hsp_sf,
      by simp [*], by simp [*],
      by simp [*], by simp [*],
      by simp [*], by simp [*], ?_⟩
  rw [hsp3]
  exact entails_sub (keccak2SlicesRW_entails_memRegion32 _ _ _ _ _) (by sep_frame)
    (entails_sub (stage4_entails_memRegion132 sp hc) (by sep_frame) (by sep_frame))

/-! ## 2. Copy `prf0..3` & Spill 24 `Fwd2` Zeta Vectors (`+0x7868 → +0x7ad4`) -/

local macro "ldr_p0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 33536#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)) (by wp_norm_lhs) ?_))

local macro "ldr_p1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 33888#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))
    (by wp_norm_lhs) ?_))

local macro "ldr_p2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 33008#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left (SepLoad128.oct8 (k := $k) (by decide) rfl rfl))))
    (by wp_norm_lhs) ?_))

local macro "ldr_p3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_ldrQ128 (wb := none) (ea := _ + 14432#64 + BitVec.ofNat 64 (16 * $k)) (v := Oct8.get _ $k)
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega))
    (SepLoad128.right (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.oct8 (k := $k) (by decide) rfl rfl)))))
    (by wp_norm_lhs) ?_))

local macro "str_d0 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30448#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d1 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30576#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d2 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30704#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set])))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_d3 " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 30832#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.oct8 (k := $k) (by decide) rfl (by dsimp only [Oct8.set]))))))))))
    (by wp_norm_lhs) fun _ => ?_
  try simp only [setPC_setMem_setPC, setMem_setMem, setPC_setMem_collapse]))

local macro "str_sp " k:num hrunId:term:arg hspId:term:arg hchkId:term:arg : tactic => `(tactic| (
  refine step_strQ128 (wb := none) (ea := _ + 1792#64 + BitVec.ofNat 64 (16 * $k))
    (by wp_norm_lhs) (by simp [$hrunId:term]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, $hspId:term, $hchkId:term])
    (by simp [evalAddrMode, $hspId:term]; try (clear * -; bv_omega)) (by wp_norm_lhs)
    (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.right (SepStore128.left
      (SepStore128.spillSlice (n := 40) (k := $k) (by decide) (by decide) rfl (by dsimp only [Spill40.set])))))))))))
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
    s18 := dup8x16 0x05d5#16, s19 := dup8x16 0x0313#16, s20 := dup8x16 0xfa13#16,
    s21 := dup8x16 0x3999#16, s22 := dup8x16 0xfe99#16, s23 := dup8x16 0xf9c0#16 }

private def midD1 (p1 d1 : Oct8) : Oct8 :=
  ⟨p1.o0, d1.o1, p1.o2, d1.o3, p1.o4, d1.o5, p1.o6, d1.o7⟩

private def midD2 (p2 d2 : Oct8) : Oct8 :=
  ⟨d2.o0, p2.o1, d2.o2, p2.o3, d2.o4, d2.o5, d2.o6, p2.o7⟩

private theorem aligned16_add30448 (sp : BitVec 64) (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 30448#64) &&& 15#64 == 0#64) = true := by
  have h0 : sp &&& 15#64 = 0#64 := of_decide_eq_true h
  have h1 : (sp + 30448#64) &&& 15#64 = sp &&& 15#64 := by bv_bits
  simp [h1, h0]

theorem setSpillZetas_slot (t : Spill40) (env : SymEnv) (i : Nat) (hi : i < 24) :
    (setSpillZetas t).get i = evalSExpr env (symSeg6FwdInit.spill.get i) := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    first | rfl | omega

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6_copy_zetas_a [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 p3 d0 d1 d2 d3 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off7868) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 30448#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 26320#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off7980) s
      (Oct8Mem (sp + 33536#64) p0 ∗ Oct8Mem (sp + 33888#64) p1 ∗
       Oct8Mem (sp + 33008#64) p2 ∗ Oct8Mem (sp + 14432#64) p3 ∗
       Oct8Mem (sp + 30448#64) d0 ∗ Oct8Mem (sp + 30576#64) d1 ∗
       Oct8Mem (sp + 30704#64) d2 ∗ Oct8Mem (sp + 30832#64) d3 ∗
       SpillSliceMem 40 (sp + 1792#64) t ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = true ∧
        sm.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧
        sm.readReg64 .x5 = 0#64 ∧ sm.readReg64 .x7 = sp + 30449#64 ∧
        sm.readReg64 .x8 = 0x058e#64 ∧ sm.readReg64 .x9 = sp + 26336#64 ∧
        sm.readReg64 .x10 = 16#64 ∧ sm.readReg64 .x11 = 0x6c6e#64 ∧
        sm.readReg64 .x12 = 0xfb4e#64 ∧ sm.readReg64 .x13 = 0x47fa#64 ∧
        sm.readReg64 .x14 = 0x019b#64 ∧ sm.readReg64 .x15 = 0x229b#64 ∧
        sm.readReg64 .x16 = 0x6833#64 ∧ sm.readReg64 .x17 = 0xf9dd#64 ∧
        sm.readReg64 .x18 = 0xc0dd#64 ∧ sm.readReg64 .x19 = 0x55555555#64 ∧
        sm.readReg64 .x20 = sp + 30448#64 ∧ sm.readReg64 .x21 = sp + 14432#64 ∧
        sm.readReg64 .x22 = sp + 26320#64 ∧ sm.readReg64 .x25 = sp + 28368#64 ∧
        sm.readReg64 .fp = s.readReg64 .fp ∧
        sm.readVReg128 0#5 = p2.o2 ∧ sm.readVReg128 1#5 = p1.o5 ∧
        sm.readVReg128 2#5 = dup8x16 0x34d5#16 ∧ sm.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        sm.readVReg128 4#5 = p2.o5 ∧
        Pm = (Oct8Mem (sp + 33536#64) p0 ∗ Oct8Mem (sp + 33888#64) p1 ∗
          Oct8Mem (sp + 33008#64) p2 ∗ Oct8Mem (sp + 14432#64) p3 ∗
          Oct8Mem (sp + 30448#64) p0 ∗ Oct8Mem (sp + 30576#64) (midD1 p1 d1) ∗
          Oct8Mem (sp + 30704#64) (midD2 p2 d2) ∗ Oct8Mem (sp + 30832#64) d3 ∗
          SpillSliceMem 40 (sp + 1792#64) (midSpillZetas t) ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_p0 7 hrun hsp hsp_chk; wp_step; ldr_p0 4 hrun hsp hsp_chk
  wp_step; ldr_p0 5 hrun hsp hsp_chk; wp_step
  str_d0 7 hrun hsp hsp_chk; wp_steps 2; str_d0 4 hrun hsp hsp_chk
  ldr_p0 6 hrun hsp hsp_chk; wp_step; str_d0 5 hrun hsp hsp_chk
  ldr_p0 1 hrun hsp hsp_chk; wp_step; str_sp 23 hrun hsp hsp_chk
  wp_steps 2; str_d0 6 hrun hsp hsp_chk; ldr_p0 0 hrun hsp hsp_chk
  wp_step; str_d0 1 hrun hsp hsp_chk; ldr_p0 3 hrun hsp hsp_chk
  wp_step; str_sp 22 hrun hsp hsp_chk; wp_steps 2
  str_d0 0 hrun hsp hsp_chk; ldr_p0 2 hrun hsp hsp_chk; wp_steps 2
  str_d0 3 hrun hsp hsp_chk; ldr_p1 5 hrun hsp hsp_chk; str_sp 21 hrun hsp hsp_chk
  ldr_p2 3 hrun hsp hsp_chk; wp_steps 2; str_d0 2 hrun hsp hsp_chk
  ldr_p1 4 hrun hsp hsp_chk; str_d2 3 hrun hsp hsp_chk; wp_steps 2
  str_d1 4 hrun hsp hsp_chk; ldr_p1 6 hrun hsp hsp_chk; wp_step
  str_sp 20 hrun hsp hsp_chk; ldr_p2 1 hrun hsp hsp_chk; wp_step
  str_sp 19 hrun hsp hsp_chk; ldr_p2 7 hrun hsp hsp_chk; wp_step
  str_d1 6 hrun hsp hsp_chk; ldr_p1 0 hrun hsp hsp_chk; wp_step
  str_d2 1 hrun hsp hsp_chk; wp_steps 2; str_d2 7 hrun hsp hsp_chk
  wp_steps 2; str_d1 0 hrun hsp hsp_chk; ldr_p1 2 hrun hsp hsp_chk
  wp_step; str_sp 18 hrun hsp hsp_chk; ldr_p2 5 hrun hsp hsp_chk
  wp_step; str_d1 2 hrun hsp hsp_chk; ldr_p2 2 hrun hsp hsp_chk
  wp_steps 2
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp [ro00Sym], by simp,
      by simp [orr_1_of_aligned16 _ (aligned16_add30448 sp hsp_chk), *]; try bv_omega,
      by simp,
      by simp [*]; try bv_omega,
      by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [hx19], by simp [hx20], by simp [hx21], by simp [hx22], by simp [hx25], by simp,
      by simp [Oct8.get], by simp [Oct8.get], by simp, by simp, by simp [Oct8.get],
      by dsimp [Oct8.get, midD1, midD2, midSpillZetas]; rfl⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 200000 in
private theorem seg6_copy_zetas_b [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (p0 p1 p2 p3 d1 d2 d3 : Oct8) (t : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + off7980) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx5 : s.readReg64 .x5 = 0#64) (hx7 : s.readReg64 .x7 = sp + 30449#64)
    (hx8 : s.readReg64 .x8 = 0x058e#64) (hx9 : s.readReg64 .x9 = sp + 26336#64)
    (hx10 : s.readReg64 .x10 = 16#64) (hx11 : s.readReg64 .x11 = 0x6c6e#64)
    (hx12 : s.readReg64 .x12 = 0xfb4e#64) (hx13 : s.readReg64 .x13 = 0x47fa#64)
    (hx14 : s.readReg64 .x14 = 0x019b#64) (hx15 : s.readReg64 .x15 = 0x229b#64)
    (hx16 : s.readReg64 .x16 = 0x6833#64) (hx17 : s.readReg64 .x17 = 0xf9dd#64)
    (hx18 : s.readReg64 .x18 = 0xc0dd#64) (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 30448#64) (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 26320#64) (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hv0 : s.readVReg128 0#5 = p2.o2) (hv1 : s.readVReg128 1#5 = p1.o5)
    (hv2 : s.readVReg128 2#5 = dup8x16 0x34d5#16) (hv3 : s.readVReg128 3#5 = dup8x16 0x0d01#16)
    (hv4 : s.readVReg128 4#5 = p2.o5) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offRhatCbdStart) s
      (Oct8Mem (sp + 33536#64) p0 ∗ Oct8Mem (sp + 33888#64) p1 ∗
       Oct8Mem (sp + 33008#64) p2 ∗ Oct8Mem (sp + 14432#64) p3 ∗
       Oct8Mem (sp + 30448#64) p0 ∗ Oct8Mem (sp + 30576#64) (midD1 p1 d1) ∗
       Oct8Mem (sp + 30704#64) (midD2 p2 d2) ∗ Oct8Mem (sp + 30832#64) d3 ∗
       SpillSliceMem 40 (sp + 1792#64) (midSpillZetas t) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 30449#64 ∧
        sf.readReg64 .x9 = sp + 26336#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 26320#64 ∧ sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        Pf = (Oct8Mem (sp + 33536#64) p0 ∗ Oct8Mem (sp + 33888#64) p1 ∗
          Oct8Mem (sp + 33008#64) p2 ∗ Oct8Mem (sp + 14432#64) p3 ∗
          Oct8Mem (sp + 30448#64) p0 ∗ Oct8Mem (sp + 30576#64) p1 ∗
          Oct8Mem (sp + 30704#64) p2 ∗ Oct8Mem (sp + 30832#64) p3 ∗
          SpillSliceMem 40 (sp + 1792#64) (setSpillZetas t) ∗ Rest)) := by
  subst hbase
  have _ : MlKemBase blkPl06 blkPl06.base := hb
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  cases p1; cases p2; cases p3; cases t
  str_sp 17 hrun hsp hsp_chk; ldr_p3 3 hrun hsp hsp_chk; str_d2 5 hrun hsp hsp_chk
  wp_steps 2; str_d2 2 hrun hsp hsp_chk; ldr_p2 6 hrun hsp hsp_chk
  wp_step; str_d3 3 hrun hsp hsp_chk; wp_steps 2
  str_d2 6 hrun hsp hsp_chk; ldr_p3 2 hrun hsp hsp_chk; wp_steps 2
  str_sp 16 hrun hsp hsp_chk; ldr_p3 1 hrun hsp hsp_chk; str_sp 15 hrun hsp hsp_chk
  ldr_p3 7 hrun hsp hsp_chk; wp_step; str_d3 2 hrun hsp hsp_chk
  ldr_p3 6 hrun hsp hsp_chk; str_d3 1 hrun hsp hsp_chk; wp_steps 2
  str_d3 7 hrun hsp hsp_chk; wp_steps 2; str_d3 6 hrun hsp hsp_chk
  wp_steps 2; str_d1 5 hrun hsp hsp_chk; ldr_p1 7 hrun hsp hsp_chk
  str_sp 14 hrun hsp hsp_chk; ldr_p3 5 hrun hsp hsp_chk; str_sp 12 hrun hsp hsp_chk
  wp_steps 2; str_d1 7 hrun hsp hsp_chk; ldr_p1 1 hrun hsp hsp_chk
  str_sp 13 hrun hsp hsp_chk; str_sp 11 hrun hsp hsp_chk; wp_steps 2
  str_d1 1 hrun hsp hsp_chk; ldr_p1 3 hrun hsp hsp_chk; str_d3 5 hrun hsp hsp_chk
  str_sp 10 hrun hsp hsp_chk; wp_steps 2; str_d1 3 hrun hsp hsp_chk
  ldr_p2 0 hrun hsp hsp_chk; str_sp 9 hrun hsp hsp_chk; wp_steps 2
  str_d2 0 hrun hsp hsp_chk; ldr_p2 4 hrun hsp hsp_chk; str_sp 8 hrun hsp hsp_chk
  wp_steps 2; str_d2 4 hrun hsp hsp_chk; ldr_p3 0 hrun hsp hsp_chk
  str_sp 7 hrun hsp hsp_chk; wp_steps 2; str_d3 0 hrun hsp hsp_chk
  ldr_p3 4 hrun hsp hsp_chk; str_sp 6 hrun hsp hsp_chk; wp_steps 2
  str_d3 4 hrun hsp hsp_chk; str_sp 5 hrun hsp hsp_chk; wp_steps 2
  str_sp 4 hrun hsp hsp_chk; wp_steps 2; str_sp 3 hrun hsp hsp_chk
  wp_step; str_sp 2 hrun hsp hsp_chk; wp_step
  str_sp 1 hrun hsp hsp_chk; wp_steps 2; str_sp 0 hrun hsp hsp_chk
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned, hsp] using hsp_chk,
      by simp [hx0], by simp, by simp [ro00Sym], by simp,
      by simp [hx5], by simp [hx7], by simp [hx9], by simp [hx10],
      by simp, by simp [hx13], by simp [hx14], by simp [hx15],
      by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx19],
      by simp [hx20], by simp [hx21], by simp [hx22], by simp [hx25], by simp, by simp [hv3],
      by simp [Oct8.get, midD1, midD2, midSpillZetas, setSpillZetas]⟩

theorem pointsToBytes128_eq_oct8Mem (ptr : BitVec 64) {bs : List (BitVec 8)}
    (h : bs.length = 128) :
    (ptr ↦ₛ bs) = Oct8Mem ptr (Oct8.ofFn (bytesToVecNat bs)) := by
  rw [pointsToBytes_eq_vecRangeMem 8 ptr h]
  exact (oct8Mem_ofFn ptr (bytesToVecNat bs)).symm

private theorem spillSliceMem40_ofFn (ptr : BitVec 64) (f : Nat → BitVec 128) :
    SpillSliceMem 40 ptr (Spill40.ofFn f) = VecRangeMem 40 ptr f :=
  vecRangeMem_congr fun i hi => spill40_ofFn_get f i hi

theorem seg6_copy_and_zetas [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (prf0 prf1 prf2 prf3 : List (BitVec 8)) (Rest : SepProp)
    (h0 : prf0.length = 128) (h1 : prf1.length = 128)
    (h2 : prf2.length = 128) (h3 : prf3.length = 128)
    (hpc : s.pc = b + off7868) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 0x55555555#64)
    (hx20 : s.readReg64 .x20 = sp + 30448#64)
    (hx21 : s.readReg64 .x21 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = sp + 26320#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offRhatCbdStart) s
      (((sp + 33536#64) ↦ₛ prf0) ∗ ((sp + 33888#64) ↦ₛ prf1) ∗
       ((sp + 33008#64) ↦ₛ prf2) ∗ ((sp + 14432#64) ↦ₛ prf3) ∗
       memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 1792#64) 640 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = mlkemMpl.ρ ro00Sym + 66#64 ∧ sf.readReg64 .x1 = 0xf301#64 ∧
        sf.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64 ∧ sf.readReg64 .x3 = 0x4ebf#64 ∧
        sf.readReg64 .x5 = 0#64 ∧ sf.readReg64 .x7 = sp + 30449#64 ∧
        sf.readReg64 .x9 = sp + 26336#64 ∧ sf.readReg64 .x10 = 16#64 ∧
        sf.readReg64 .x12 = 0xf9fa#64 ∧ sf.readReg64 .x13 = 0x47fa#64 ∧
        sf.readReg64 .x14 = 0x019b#64 ∧ sf.readReg64 .x15 = 0x229b#64 ∧
        sf.readReg64 .x16 = 0x6833#64 ∧ sf.readReg64 .x17 = 0xf9dd#64 ∧
        sf.readReg64 .x18 = 0xc0dd#64 ∧ sf.readReg64 .x19 = 0x55555555#64 ∧
        sf.readReg64 .x20 = sp + 30448#64 ∧ sf.readReg64 .x21 = sp + 14432#64 ∧
        sf.readReg64 .x22 = sp + 26320#64 ∧ sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readVReg128 3#5 = dup8x16 0x0d01#16 ∧
        ∃ t : Spill40,
          (∀ env i, i < 24 → t.get i = evalSExpr env (symSeg6FwdInit.spill.get i)) ∧
          (Pf ⊢ ((sp + 30448#64) ↦ₛ prf0) ∗ ((sp + 30576#64) ↦ₛ prf1) ∗
            ((sp + 30704#64) ↦ₛ prf2) ∗ ((sp + 30832#64) ↦ₛ prf3) ∗
            SpillSliceMem 40 (sp + 1792#64) t ∗
            memRegion (sp + 14432#64) 128 ∗ memRegion (sp + 33008#64) 128 ∗
            memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗ Rest)) := by
  rw [pointsToBytes128_eq_oct8Mem (sp + 33536#64) h0,
      pointsToBytes128_eq_oct8Mem (sp + 33888#64) h1,
      pointsToBytes128_eq_oct8Mem (sp + 33008#64) h2,
      pointsToBytes128_eq_oct8Mem (sp + 14432#64) h3,
      memRegion_split' (b := sp + 30448#64) (b' := sp + 30576#64) (n := 128) (k := (384 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30576#64) (b' := sp + 30704#64) (n := 128) (k := (256 : Nat))
        rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 30704#64) (b' := sp + 30832#64) (n := 128) (k := (128 : Nat))
        rfl (by bv_omega) (by decide)]
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30448#64) (hf := by sep_focus); intro fd0
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30576#64) (hf := by sep_focus); intro fd1
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30704#64) (hf := by sep_focus); intro fd2
  apply SepWP.of_memRegion_vecRangeMem 8 (sp + 30832#64) (hf := by sep_focus); intro fd3
  apply SepWP.of_memRegion_vecRangeMem 40 (sp + 1792#64) (hf := by sep_focus); intro fsp
  rw [show VecRangeMem 8 (sp + 30448#64) fd0 = Oct8Mem (sp + 30448#64) (Oct8.ofFn fd0) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30576#64) fd1 = Oct8Mem (sp + 30576#64) (Oct8.ofFn fd1) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30704#64) fd2 = Oct8Mem (sp + 30704#64) (Oct8.ofFn fd2) from
        (oct8Mem_ofFn _ _).symm,
      show VecRangeMem 8 (sp + 30832#64) fd3 = Oct8Mem (sp + 30832#64) (Oct8.ofFn fd3) from
        (oct8Mem_ofFn _ _).symm,
      ← spillSliceMem40_ofFn (sp + 1792#64) fsp]
  refine SepWP.weaken_pre
    (P' := Oct8Mem (sp + 33536#64) (Oct8.ofFn (bytesToVecNat prf0)) ∗
      Oct8Mem (sp + 33888#64) (Oct8.ofFn (bytesToVecNat prf1)) ∗
      Oct8Mem (sp + 33008#64) (Oct8.ofFn (bytesToVecNat prf2)) ∗
      Oct8Mem (sp + 14432#64) (Oct8.ofFn (bytesToVecNat prf3)) ∗
      Oct8Mem (sp + 30448#64) (Oct8.ofFn fd0) ∗ Oct8Mem (sp + 30576#64) (Oct8.ofFn fd1) ∗
      Oct8Mem (sp + 30704#64) (Oct8.ofFn fd2) ∗ Oct8Mem (sp + 30832#64) (Oct8.ofFn fd3) ∗
      SpillSliceMem 40 (sp + 1792#64) (Spill40.ofFn fsp) ∗ Rest) (by sep_frame) ?_
  refine SepWP.seq
    (seg6_copy_zetas_a hb hbase s sp _ _ _ _ _ _ _ _ _ Rest
      hpc hrun hsp hspA hx19 hx20 hx21 hx22 hx25)
    fun sm Pm hpcm hrunm ⟨hspm, hspAm, hx0m, hx5m, hx7m, hx8m, hx9m, hx10m, hx11m, hx12m,
      hx13m, hx14m, hx15m, hx16m, hx17m, hx18m, hx19m, hx20m, hx21m, hx22m, hx25m, hfpm,
      hv0m, hv1m, hv2m, hv3m, hv4m, hPm⟩ => by
    subst hPm
    refine SepWP.seq
      (seg6_copy_zetas_b hb hbase sm sp _ _ _ _ _ _ _ _ Rest hpcm hrunm hspm hspAm
        hx0m hx5m hx7m hx8m hx9m hx10m hx11m hx12m hx13m hx14m hx15m hx16m hx17m hx18m
        hx19m hx20m hx21m hx22m hx25m hv0m hv1m hv2m hv3m hv4m) ?_
    rintro sf Pf hpcf hrunf ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, r22, r25, rfp, rv3, hPf⟩
    refine SepWP.done hpcf hrunf ⟨hspf, hspAf, r0, r1, r2, r3, r5, r7, r9, r10, r12, r13, r14, r15,
      r16, r17, r18, r19, r20, r21, r22, r25, rfp.trans hfpm, rv3,
      setSpillZetas (Spill40.ofFn fsp), setSpillZetas_slot (Spill40.ofFn fsp), ?_⟩
    rw [hPf, ← pointsToBytes128_eq_oct8Mem (sp + 30448#64) h0,
      ← pointsToBytes128_eq_oct8Mem (sp + 30576#64) h1,
      ← pointsToBytes128_eq_oct8Mem (sp + 30704#64) h2,
      ← pointsToBytes128_eq_oct8Mem (sp + 30832#64) h3]
    exact entails_sub (oct8Mem_entails_memRegion (sp + 33536#64) _) (by sep_frame)
      (entails_sub (oct8Mem_entails_memRegion (sp + 33888#64) _) (by sep_frame)
        (entails_sub (oct8Mem_entails_memRegion (sp + 33008#64) _) (by sep_frame)
          (entails_sub (oct8Mem_entails_memRegion (sp + 14432#64) _) (by sep_frame) (by sep_frame))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6Prf
