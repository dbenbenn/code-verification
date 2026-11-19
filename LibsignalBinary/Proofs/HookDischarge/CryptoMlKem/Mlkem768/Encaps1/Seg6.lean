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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemEncaps2Fips
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6SerLoop

/-!
# `encapsulate1_serialized` (`B03`) — Segment 6 (`+0x6a78 .. +0x6ed8` `ret`)

Composes `Seg6SerLoop.seg6_ser_ok` (`ct1` `compress_and_serialize_10`) with stack staging,
32-vector `e2` un-reversal, `B11` `EncapsState::to_bytes`, caller output writes (`ss`, `ct1`,
`ret = 0#8`), and the 160-byte `SavedFrame03` epilogue restoring `stackAt s0.sp 18160`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk11 resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.EncapsStateToBytes (
  EncapsStateToBytesArgs blk11_encaps_state_to_bytes_RW_ok encapsStateBytes
  mlkemEncapsStateToBytesRWSpec pointsToBytes_encapsStateBytes_eq polyToCenteredI16Bytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 bytesToPoly16 mlkemQ polyNtt polyToCenteredI16Bytes
  sampleNtt samplePolyCbd2 sampleVecCbd2 sha3_512List shake256List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemEncaps2Fips (
  bytesToPoly16_polyToCenteredI16Bytes_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (PolyBounded16 PolyRepresents)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16 neonCbd2Poly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At Vec32
  VecRangeMem bytesToVecNat pointsToBytes_eq_vecRangeMem poly32Mem_entails_memRegion
  poly32Mem_ofFn polyMem_bytesToPoly16 polyVecNat step_ldrQ128 step_strQ128 vecRangeBytes
  vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_region32 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  MlkemBlk03Args SavedFrame03 blk03_code_eq blk03_tree_size blkLib03 blkPC03
  blkPl03 blkPlaceable03 blkTree03 encaps1OutCt1 encaps1OutEs
  encaps1OutSs mlkemBlk03RawSpec savedFrame03_entails_memRegion160)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (
  SavedArgs03 blkPl03_ρ cells32_entails_memRegion sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg2 (ATransMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3 (
  rHatPoly16 rHatPoly16_spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  sepWP_elim_byte shake256List_length step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5 (offSeg5End uVecPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd (
  encaps1OutCt1_eq neonCompressSerialize10Poly_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser (
  blk28_memcpy_03 offSeg6SerEnd offSeg6Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6SerLoop (
  seg6_ser_ok step_ldrQ128_sp_vecRange step_strQ128_sp_vecRange)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x6cd8 → 0x6ed8]
end

/-! ## 1. Centered `Poly16` → `EncapsState::to_bytes` Bridge -/

private theorem polyBounded16_mono {B1 B2 : Int} {p : Poly16}
    (hle : B1 ≤ B2) (hp : PolyBounded16 B1 p) : PolyBounded16 B2 p :=
  ⟨hp.1, fun i hi => ⟨by have := (hp.2 i hi).1; omega, by have := (hp.2 i hi).2; omega⟩⟩

private theorem array_getElem_eq_getD16 (a : Array (BitVec 16)) {i : Nat} (hi : i < a.size) :
    a[i]'hi = a.getD i 0#16 := by
  simp [Array.getD, hi]

private theorem polyMem_eq_centeredBytes {q : Poly16} {p : Poly}
    (hq : q.size = 256) (hb : PolyBounded16 1664 q) (hr : PolyRepresents q p)
    (ptr : BitVec 64) :
    PolyMem ptr (polyVecNat q) = (ptr ↦ₛ polyToCenteredI16Bytes p) := by
  have hq_eq : q = bytesToPoly16 (polyToCenteredI16Bytes p) := by
    rw [bytesToPoly16_polyToCenteredI16Bytes_eq]
    apply Array.ext
    · simp [hq]
    · intro i hi1 _
      have hi : i < 256 := hq ▸ hi1
      rw [array_getElem_eq_getD16 q hi1, Array.getElem_ofFn]; dsimp only
      have hb1 := hb.2 i hi
      have hr1 := hr.2 i hi
      dsimp [mlkemQ] at hr1 ⊢
      set c := p.getD i 0 % 3329
      have hc_lt : c < 3329 := Nat.mod_lt _ (by decide)
      have hc_int : ((p.getD i 0 : Int) % 3329) = (c : Int) := by exact_mod_cast rfl
      rw [hc_int] at hr1
      apply BitVec.eq_of_toInt_eq
      change (q.getD i 0#16).toInt =
        (BitVec.ofInt 16 (if c ≤ 1664 then (c : Int) else (c : Int) - 3329)).toInt
      rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
      omega
  rw [hq_eq, polyMem_bytesToPoly16 ptr (polyToCenteredI16Bytes_length p)]

attribute [local irreducible] samplePolyCbd2 polyNtt polyToCenteredI16Bytes shake256List sha3_512List

private theorem encapsState_at_2192_eq (sp : BitVec 64) {hdr rand : List (BitVec 8)}
    (_hhdr : hdr.length = 64) (hrand : rand.length = 32) :
    let coins := ((sha3_512List (rand ++ (hdr.drop 32).take 32)).drop 32).take 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    PolyMem (sp + 2192#64) (polyVecNat (rHatPoly16 prf0)) ∗
      PolyMem (sp + 2704#64) (polyVecNat (rHatPoly16 prf1)) ∗
      PolyMem (sp + 3216#64) (polyVecNat (rHatPoly16 prf2)) ∗
      PolyMem (sp + 3728#64) (polyVecNat (neonCbd2Poly16 prf6)) ∗
      ((sp + 4240#64) ↦ₛ rand) =
      ((sp + 2192#64) ↦ₛ encaps1OutEs hdr rand) := by
  intro coins prf0 prf1 prf2 prf6
  have hcoins : coins.length = 32 := by simp [coins, sha3_512List_length]
  have htc : coins.take 32 = coins := List.take_of_length_le (Nat.le_of_eq hcoins)
  have htr : rand.take 32 = rand := List.take_of_length_le (Nat.le_of_eq hrand)
  set rHat := (sampleVecCbd2 3 coins 0).map polyNtt
  set e2 := samplePolyCbd2 prf6
  have hrg (j : Nat) (hj : j < 3) :
      rHat.getD j zeroPoly = polyNtt (samplePolyCbd2 (shake256List 128 (coins ++ [BitVec.ofNat 8 j]))) := by
    unfold rHat sampleVecCbd2
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_ofFn]
    simp only [htc, hj, Nat.zero_add, ↓reduceDIte, Option.map_some, Option.getD_some]
  obtain ⟨_, h0b, h0r⟩ := rHatPoly16_spec (shake256List_length 128 (coins ++ [0#8]))
  obtain ⟨_, h1b, h1r⟩ := rHatPoly16_spec (shake256List_length 128 (coins ++ [1#8]))
  obtain ⟨_, h2b, h2r⟩ := rHatPoly16_spec (shake256List_length 128 (coins ++ [2#8]))
  obtain ⟨he2b, he2r⟩ := neonCbd2Poly16_spec (shake256List_length 128 (coins ++ [6#8]))
  have h0r' : PolyRepresents (rHatPoly16 prf0) (rHat.getD 0 zeroPoly) := by rw [hrg 0 (by decide)]; exact h0r
  have h1r' : PolyRepresents (rHatPoly16 prf1) (rHat.getD 1 zeroPoly) := by rw [hrg 1 (by decide)]; exact h1r
  have h2r' : PolyRepresents (rHatPoly16 prf2) (rHat.getD 2 zeroPoly) := by rw [hrg 2 (by decide)]; exact h2r
  rw [polyMem_eq_centeredBytes h0r.1 (polyBounded16_mono (by decide) h0b) h0r',
      polyMem_eq_centeredBytes h1r.1 (polyBounded16_mono (by decide) h1b) h1r',
      polyMem_eq_centeredBytes h2r.1 (polyBounded16_mono (by decide) h2b) h2r',
      polyMem_eq_centeredBytes he2r.1 (polyBounded16_mono (by decide) he2b) he2r]
  have hes : encaps1OutEs hdr rand = encapsStateBytes rHat e2 rand := by
    unfold encaps1OutEs; dsimp only; rw [htr]
  have hflat : ((List.range 3).map fun i => polyToCenteredI16Bytes (rHat.getD i zeroPoly)).flatten =
      polyToCenteredI16Bytes (rHat.getD 0 zeroPoly) ++
      (polyToCenteredI16Bytes (rHat.getD 1 zeroPoly) ++
       polyToCenteredI16Bytes (rHat.getD 2 zeroPoly)) := by
    have hr3 : List.range 3 = [0, 1, 2] := by decide
    rw [hr3]; simp only [List.map, List.flatten, List.append_eq, List.append_nil]
  rw [hes, ← pointsToBytes_encapsStateBytes_eq (sp + 2192#64) rHat e2 rand, hflat,
      pointsToBytes_append, polyToCenteredI16Bytes_length,
      show (sp + 2192#64) + BitVec.ofNat 64 512 = sp + 2704#64 by clear * -; bv_omega,
      pointsToBytes_append, polyToCenteredI16Bytes_length,
      show (sp + 2704#64) + BitVec.ofNat 64 512 = sp + 3216#64 by clear * -; bv_omega,
      show (sp + 2192#64) + 1536#64 = sp + 3728#64 by clear * -; bv_omega,
      show (sp + 2192#64) + 2048#64 = sp + 4240#64 by clear * -; bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

/-! ## 2. State Assembly, `B11` Call, Output Copy, & Epilogue (`+0x6cd8 .. +0x6ed8`) -/

@[simp, arm64_norm, wp_norm] private abbrev off6d1c : BitVec 64 := BitVec.ofNat 64 27932
@[simp, arm64_norm, wp_norm] private abbrev off6d54 : BitVec 64 := BitVec.ofNat 64 27988
@[simp, arm64_norm, wp_norm] private abbrev off6e5c : BitVec 64 := BitVec.ofNat 64 28252

private theorem vec2_cells_eq_bytes (ptr : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 32) :
    let v0 := bytesToVecNat bs 0
    let v1 := bytesToVecNat bs 1
    ((ptr ↦₆₄ v0.extractLsb' 0 64) ∗ ((ptr + 8#64) ↦₆₄ v0.extractLsb' 64 64) ∗
      ((ptr + 16#64) ↦₆₄ v1.extractLsb' 0 64) ∗ ((ptr + 24#64) ↦₆₄ v1.extractLsb' 64 64)) =
      (ptr ↦ₛ bs) := by
  intro v0 v1
  rw [pointsToBytes_eq_vecRangeMem 2 ptr h]
  dsimp only [VecRangeMem, Vec128At, v0, v1, Nat.zero_add]
  rw [show (ptr + 16#64) + 8#64 = ptr + 24#64 by clear * -; bv_omega]
  exact sepProp_ext (by sep_frame) (by sep_frame)

private theorem seg6_stage_12 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (rBytes ct1 : List (BitVec 8)) (Rest : SepProp)
    (hrand : a.rand.length = 32) (hr : rBytes.length = 1536) (hct1 : ct1.length = 960)
    (hpc : s.pc = b + offSeg6SerEnd) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6d1c) s
      (SavedArgs03 sp a ∗ (a.randA ↦ₛ a.rand) ∗ memRegion (sp + 4240#64) 32 ∗
        memRegion (sp + 4272#64) 960 ∗ memRegion (sp + 5232#64) 1536 ∗
        ((sp + 11440#64) ↦ₛ ct1) ∗ ((sp + 12448#64) ↦ₛ rBytes) ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x19 = sp + 4272#64 ∧
        (Pf ⊢ SavedArgs03 sp a ∗ (a.randA ↦ₛ a.rand) ∗ ((sp + 4240#64) ↦ₛ a.rand) ∗
          ((sp + 4272#64) ↦ₛ ct1) ∗ ((sp + 5232#64) ↦ₛ rBytes) ∗
          ((sp + 11440#64) ↦ₛ ct1) ∗ ((sp + 12448#64) ↦ₛ rBytes) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 5232#64, sp + 12448#64, rBytes)
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1
  have hx19_1 : sf.readReg64 .x19 = sp + 4272#64 := ‹_›
  sep_frame_apply (sepWP_elim_region32 (a := sp + 4240#64)); intro c0 c1 c2 c3
  dsimp only [SavedArgs03]
  rw [← vec2_cells_eq_bytes a.randA hrand]
  simp only [show sp + 4240#64 + 8#64 = sp + 4248#64 by clear * -; bv_omega,
    show sp + 4240#64 + 16#64 = sp + 4256#64 by clear * -; bv_omega,
    show sp + 4240#64 + 24#64 = sp + 4264#64 by clear * -; bv_omega]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 4272#64, sp + 11440#64, ct1)
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans hsp1
  have h19_1 : sf_1.readReg64 (.gpr 19#5) = _ := ‹_›
  refine SepWP.done hpc_sf_1 hrun_sf_1
    ⟨hsp2, spAligned_of_sp_eq hspA1 hsp1 hsp2, h19_1.trans hx19_1, ?_⟩
  simp only [htrunc]
  have hd := vec2_cells_eq_bytes (sp + 4240#64) hrand
  simp only [show sp + 4240#64 + 8#64 = sp + 4248#64 by clear * -; bv_omega,
    show sp + 4240#64 + 16#64 = sp + 4256#64 by clear * -; bv_omega,
    show sp + 4240#64 + 24#64 = sp + 4264#64 by clear * -; bv_omega] at hd
  conv_rhs => rw [← hd]
  sep_frame

private theorem seg6_stage_34 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (ss rBytes ct1 : List (BitVec 8)) (Rest : SepProp)
    (hss : ss.length = 32) (hr : rBytes.length = 1536) (hct1 : ct1.length = 960)
    (hpc : s.pc = b + off6d1c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hx19 : s.readReg64 .x19 = sp + 4272#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6d54) s
      (memRegion (sp + 2192#64) 1536 ∗ ((sp + 4272#64) ↦ₛ ct1) ∗ ((sp + 5232#64) ↦ₛ rBytes) ∗
        ((sp + 6768#64) ↦ₛ ss) ∗ memRegion (sp + 6832#64) 960 ∗
        memRegion (sp + 13984#64) 32 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        (Pf ⊢ ((sp + 2192#64) ↦ₛ rBytes) ∗ ((sp + 4272#64) ↦ₛ ct1) ∗ ((sp + 5232#64) ↦ₛ rBytes) ∗
          ((sp + 6768#64) ↦ₛ ss) ∗ ((sp + 6832#64) ↦ₛ ct1) ∗
          ((sp + 13984#64) ↦ₛ ss) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  sep_frame_apply (sepWP_elim_region32 (a := sp + 13984#64)); intro c0 c1 c2 c3
  rw [← vec2_cells_eq_bytes (sp + 6768#64) hss]
  simp only [show sp + 6768#64 + 8#64 = sp + 6776#64 by clear * -; bv_omega,
    show sp + 6768#64 + 16#64 = sp + 6784#64 by clear * -; bv_omega,
    show sp + 6768#64 + 24#64 = sp + 6792#64 by clear * -; bv_omega,
    show sp + 13984#64 + 8#64 = sp + 13992#64 by clear * -; bv_omega,
    show sp + 13984#64 + 16#64 = sp + 14000#64 by clear * -; bv_omega,
    show sp + 13984#64 + 24#64 = sp + 14008#64 by clear * -; bv_omega]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 6832#64, sp + 4272#64, ct1)
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1
  have h19_0 : sf.readReg64 (.gpr 19#5) = _ := ‹_›
  have hx19_1 : sf.readReg64 .x19 = sp + 4272#64 := h19_0.trans hx19
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (sp + 2192#64, sp + 5232#64, rBytes)
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans hsp1
  refine SepWP.done hpc_sf_1 hrun_sf_1 ⟨hsp2, spAligned_of_sp_eq hspA1 hsp1 hsp2, ?_⟩
  simp only [htrunc]
  have hd := vec2_cells_eq_bytes (sp + 13984#64) hss
  simp only [show sp + 13984#64 + 8#64 = sp + 13992#64 by clear * -; bv_omega,
    show sp + 13984#64 + 16#64 = sp + 14000#64 by clear * -; bv_omega,
    show sp + 13984#64 + 24#64 = sp + 14008#64 by clear * -; bv_omega] at hd
  conv_rhs => rw [← hd]
  sep_frame

local macro "ldr_rev " k:num : tactic => `(tactic|
  refine step_ldrQ128 (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *])
    (by wp_norm_lhs) (SepLoad128.vec32 (k := $k) (by decide) (by simp [*]; try bv_omega) rfl).left
    (by wp_norm_lhs) ?_)

local macro "str_rev " k:num : tactic => `(tactic|
  refine step_strQ128 (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
    (by simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned, *])
    (by wp_norm_lhs) rfl
    (SepStore128.vec32 (k := $k) (by decide) (by simp [*]; try bv_omega) rfl).left.right
    (by wp_norm_lhs) fun _ => ?_)

private theorem seg6_unreverse_e2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (g : Nat → BitVec 128) (td : Vec32)
    (Rest : SepProp)
    (hpc : s.pc = b + off6d54) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    let ts := Vec32.ofFn (fun i => g (31 - i))
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6e5c) s
      (Poly32Mem (sp + 1248#64) ts ∗ Poly32Mem (sp + 3728#64) td ∗ SavedArgs03 sp a ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 2192#64 ∧ sf.readReg64 .x1 = a.esA ∧
        sf.readReg64 .x2 = 2080#64 ∧
        Pf = (Poly32Mem (sp + 1248#64) ts ∗ PolyMem (sp + 3728#64) g ∗ SavedArgs03 sp a ∗ Rest)) := by
  intro ts; subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  ldr_rev 31
  dsimp only [SavedArgs03]; wp_steps 2
  str_rev 0
  ldr_rev 30; str_rev 1; ldr_rev 29; str_rev 2; ldr_rev 28; str_rev 3
  ldr_rev 27; str_rev 4; ldr_rev 26; str_rev 5; ldr_rev 25; str_rev 6
  ldr_rev 24; str_rev 7; ldr_rev 23; str_rev 8; ldr_rev 22; str_rev 9
  ldr_rev 21; str_rev 10; ldr_rev 20; str_rev 11; ldr_rev 19; str_rev 12
  ldr_rev 18; str_rev 13; ldr_rev 17; str_rev 14; ldr_rev 16; str_rev 15
  ldr_rev 15; str_rev 16; ldr_rev 14; str_rev 17; ldr_rev 13; str_rev 18
  ldr_rev 12; str_rev 19; ldr_rev 11; str_rev 20; ldr_rev 10; str_rev 21
  ldr_rev 9; str_rev 22; ldr_rev 8; str_rev 23; ldr_rev 7; str_rev 24
  ldr_rev 6; str_rev 25; ldr_rev 5; str_rev 26; ldr_rev 4; str_rev 27
  ldr_rev 3; str_rev 28; ldr_rev 2; str_rev 29; ldr_rev 1; str_rev 30
  ldr_rev 0; str_rev 31
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun]) ⟨by simp [hsp],
    by simpa [State.spAligned, hsp] using hspA, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, ?_⟩
  rw [← poly32Mem_ofFn (sp + 3728#64) g]; rfl

@[simp, arm64_norm, wp_norm] private abbrev off6ea8 : BitVec 64 := BitVec.ofNat 64 28328

private theorem seg6_b11_and_outputs [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (es ss ct1 : List (BitVec 8)) (Rest : SepProp)
    (hes : es.length = 2080) (hss : ss.length = 32) (hct1 : ct1.length = 960)
    (hpc : s.pc = b + off6e5c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 2192#64) (hx1 : s.readReg64 .x1 = a.esA)
    (hx2 : s.readReg64 .x2 = 2080#64) (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6ea8) s
      (SavedArgs03 sp a ∗ ((sp + 2192#64) ↦ₛ es) ∗ ((sp + 6832#64) ↦ₛ ct1) ∗
        ((sp + 13984#64) ↦ₛ ss) ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
        memRegion a.ret 961 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        (Pf ⊢ SavedArgs03 sp a ∗ ((sp + 2192#64) ↦ₛ es) ∗ ((sp + 6832#64) ↦ₛ ct1) ∗
          ((sp + 13984#64) ↦ₛ ss) ∗ (a.esA ↦ₛ es) ∗ (a.ssA ↦ₛ ss) ∗
          (a.ret ↦₈ 0#8) ∗ ((a.ret + 1#64) ↦ₛ ct1) ∗ Rest)) := by
  subst hbase
  have hal_sp : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have htrunc (v : BitVec 128) : v.truncate 64 = v.extractLsb' 0 64 := by bv_bits
  rw [memRegion_split' (b := a.ret) (b' := a.ret + 1#64) (n := 1) (k := (960 : Nat))
    rfl (by bv_omega) (by decide)]
  sep_frame_apply (sepWP_elim_byte (a := a.ret)); intro b0
  sep_frame_apply (sepWP_elim_region32 (a := a.ssA)); intro d0 d1 d2 d3
  rw [← vec2_cells_eq_bytes (sp + 13984#64) hss]
  simp only [show sp + 13984#64 + 8#64 = sp + 13992#64 by clear * -; bv_omega,
    show sp + 13984#64 + 16#64 = sp + 14000#64 by clear * -; bv_omega,
    show sp + 13984#64 + 24#64 = sp + 14008#64 by clear * -; bv_omega]
  wp_cut_codeLoaded; wp_step
  wp_mlkem_call blk11_encaps_state_to_bytes_RW_ok
    ({ statePtr := sp + 2192#64, outPtr := a.esA, stateBytes := es })
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1
  wp_steps 2
  refine step_bCond_taken (dst := blkPl03.base + BitVec.ofNat 64 28288)
    (by wp_norm_lhs) (by simp [hrun_sf]) (by wp_norm_lhs)
    (by simp [*]) (by clear * -; bv_omega) ?_
  dsimp only [SavedArgs03]
  wp_cut_codeLoaded; wp_steps
  wp_mlkem_call blk28_memcpy_ok (a.ret + 1#64, sp + 6832#64, ct1)
  have hsp2 : sf_1.sp = sp := by simpa [State.setPC] using hsp_sf_1.trans hsp1
  have h19 : sf_1.readReg64 (.gpr 19#5) = _ := ‹_›
  have hx19 : sf_1.readReg64 .x19 = a.ret := by simpa [State.setPC] using h19
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf_1])
    ⟨by simp [hsp2], spAligned_of_sp_eq hspA hsp (by simp [hsp2]), ?_⟩
  simp only [htrunc]
  have hd := vec2_cells_eq_bytes a.ssA hss
  conv_rhs => rw [← hd]
  sep_frame

private theorem calleeSavedVRegs_eq_of_readVReg128 (s0 sf : State)
    (h : ∀ r : Fin 8, sf.readVReg128 (BitVec.ofNat 5 (8 + r.val)) =
      ((s0.readVReg128 (BitVec.ofNat 5 (8 + r.val))).truncate 64).zeroExtend 128) :
    calleeSavedVRegs sf = calleeSavedVRegs s0 := by
  have htr (v : BitVec 128) : ((v.truncate 64).zeroExtend 128).truncate 64 = v.truncate 64 := by
    apply BitVec.eq_of_getLsbD_eq; intro k hk
    simp [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, hk]
  have hr (i : Fin 8) :
      (sf.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 =
        (s0.readVReg128 (BitVec.ofNat 5 (8 + i.val))).truncate 64 := by
    rw [h i, htr]
  exact Prod.ext (hr 0) (Prod.ext (hr 1) (Prod.ext (hr 2) (Prod.ext (hr 3)
    (Prod.ext (hr 4) (Prod.ext (hr 5) (Prod.ext (hr 6) (hr 7)))))))

private theorem seg6_epilogue [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s0 s : State) (Rest : SepProp) (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + off6ea8) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - BitVec.ofNat 64 17024) :
    let spSave := s0.sp - 160#64
    SepWP (blkPC03.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedFrame03 spSave s0 ∗ Rest)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ memRegion spSave 160 ∗ Rest)) := by
  intro spSave; subst hbase
  dsimp only [SavedFrame03, spSave]
  have hsp160 : (s0.sp - BitVec.ofNat 64 17024) + BitVec.ofNat 64 16384 + 480#64 = s0.sp - 160#64 := by
    bv_omega
  have hsp160_al :
      ((((s0.sp - BitVec.ofNat 64 17024) + BitVec.ofNat 64 16384 + 480#64) &&& 15#64) == 0#64) = true := by
    rw [hsp160]; exact spAligned_sub s0.sp 160#64 hsp0 (by decide)
  wp_steps
  refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
    ⟨Eq.trans (by wp_norm_lhs) (by bv_omega), ?_,
      sepConj_mono_left (savedFrame03_entails_memRegion160 (s0.sp - 160#64) s0)⟩
  refine ⟨by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs,
    by wp_norm_lhs, ?_⟩
  exact calleeSavedVRegs_eq_of_readVReg128 s0 _ fun r => by fin_cases r <;> wp_norm_lhs

theorem encaps1Out_lengths {hdr rand : List (BitVec 8)} (hhdr : hdr.length = 64)
    (hrand : rand.length = 32) :
    (encaps1OutCt1 hdr rand).length = 960 ∧
    (encaps1OutEs hdr rand).length = 2080 ∧
    (encaps1OutSs hdr rand).length = 32 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← encaps1OutCt1_eq hhdr hrand]
    simp [neonCompressSerialize10Poly_length]
  · unfold encaps1OutEs encapsStateBytes
    have hr3 : List.range 3 = [0, 1, 2] := by decide
    rw [hr3, List.take_of_length_le (Nat.le_of_eq hrand)]
    simp [polyToCenteredI16Bytes_length, hrand]
  · unfold encaps1OutSs
    simp [sha3_512List_length]

private theorem poly3_bytes_join (ptr : BitVec 64) (q0 q1 q2 : Poly16) :
    let bs := vecRangeBytes 32 (polyVecNat q0) ++
      vecRangeBytes 32 (polyVecNat q1) ++ vecRangeBytes 32 (polyVecNat q2)
    bs.length = 1536 ∧
      (PolyMem ptr (polyVecNat q0) ∗ PolyMem (ptr + 512#64) (polyVecNat q1) ∗
        PolyMem (ptr + 1024#64) (polyVecNat q2)) = (ptr ↦ₛ bs) := by
  intro bs
  refine ⟨by simp [bs, vecRangeBytes_length], ?_⟩
  dsimp only [PolyMem, bs]
  rw [List.append_assoc, pointsToBytes_append, vecRangeBytes_length,
    pointsToBytes_append, vecRangeBytes_length,
    ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
    ← vecRangeMem_eq_pointsToBytes,
    show ptr + BitVec.ofNat 64 (16 * 32) = ptr + 512#64 by clear * -; bv_omega,
    show (ptr + 512#64) + BitVec.ofNat 64 (16 * 32) = ptr + 1024#64 by clear * -; bv_omega]

private theorem savedArgs03_entails_memRegion40 (sp : BitVec 64) (a : MlkemBlk03Args) :
    SavedArgs03 sp a ⊢ memRegion sp 40 := by
  unfold SavedArgs03
  rw [memRegion_split' (b' := sp + 8#64) (n := 8) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 8#64) (b' := sp + 16#64) (n := 8) (k := (24 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 16#64) (b' := sp + 24#64) (n := 8) (k := (16 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 24#64) (b' := sp + 32#64) (n := 8) (k := (8 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _)
    (sepConj_mono (cell_entails_memRegion8 _ _)
      (sepConj_mono (cell_entails_memRegion8 _ _)
        (sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _))))

private theorem seg6_post_collapse (sp : BitVec 64) (a : MlkemBlk03Args) (ts : Vec32)
    {es ct1 rBytes ss hashedTail : List (BitVec 8)}
    (hes : es.length = 2080) (hct1 : ct1.length = 960) (hr : rBytes.length = 1536)
    (hss : ss.length = 32) (htl : hashedTail.length = 32) :
    SavedArgs03 sp a ∗ Poly32Mem (sp + 1248#64) ts ∗ memRegion (sp + 2128#64) 64 ∗
      ((sp + 2192#64) ↦ₛ es) ∗ ((sp + 4272#64) ↦ₛ ct1) ∗ ((sp + 5232#64) ↦ₛ rBytes) ∗
      ((sp + 6768#64) ↦ₛ ss) ∗ ((sp + 6800#64) ↦ₛ hashedTail) ∗ ((sp + 6832#64) ↦ₛ ct1) ∗
      ((sp + 11440#64) ↦ₛ ct1) ∗ ((sp + 12448#64) ↦ₛ rBytes) ∗ ((sp + 13984#64) ↦ₛ ss) ⊢
      memRegion sp 40 ∗ memRegion (sp + 1248#64) 512 ∗ memRegion (sp + 2128#64) 5664 ∗
      memRegion (sp + 11440#64) 960 ∗ memRegion (sp + 12448#64) 1568 := by
  have hb {p : BitVec 64} {l : List (BitVec 8)} {n : Nat} (hl : l.length = n) :
      (p ↦ₛ l) ⊢ memRegion p n := hl ▸ pointsToBytes_entails_memRegion p l
  rw [memRegion_split' (b := sp + 2128#64) (b' := sp + 2192#64) (n := 64) (k := (5600 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 2192#64) (b' := sp + 4272#64) (n := 2080) (k := (3520 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 4272#64) (b' := sp + 5232#64) (n := 960) (k := (2560 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 5232#64) (b' := sp + 6768#64) (n := 1536) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6768#64) (b' := sp + 6800#64) (n := 32) (k := (992 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 6800#64) (b' := sp + 6832#64) (n := 32) (k := (960 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12448#64) (b' := sp + 13984#64) (n := 1536) (k := (32 : Nat)) rfl (by bv_omega) (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono (savedArgs03_entails_memRegion40 sp a)
    (sepConj_mono (poly32Mem_entails_memRegion (sp + 1248#64) ts)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (hb hes)
          (sepConj_mono (hb hct1)
            (sepConj_mono (hb hr)
              (sepConj_mono (hb hss)
                (sepConj_mono (hb htl)
                  (sepConj_mono (hb hct1)
                    (sepConj_mono (hb hct1)
                      (sepConj_mono (hb hr) (hb hss)))))))))))

private theorem seg6_mid_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (Rest : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let rho := a.hdr64.take 32
    let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
    let coins := (hashed.drop 32).take 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    let rBytes := vecRangeBytes 32 (polyVecNat (rHatPoly16 prf0)) ++
      vecRangeBytes 32 (polyVecNat (rHatPoly16 prf1)) ++
      vecRangeBytes 32 (polyVecNat (rHatPoly16 prf2))
    let ts := Vec32.ofFn (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i))
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6e5c) s
      (SavedArgs03 sp a ∗ (a.randA ↦ₛ a.rand) ∗
        PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
        memRegion (sp + 2128#64) 64 ∗
        PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
        PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
        PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
        memRegion (sp + 3728#64) 544 ∗ memRegion (sp + 4272#64) 2496 ∗
        ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 6832#64) 960 ∗
        memRegion (sp + 11440#64) 960 ∗
        PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
        memRegion (sp + 13984#64) 32 ∗ memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 640 ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 2192#64 ∧ sf.readReg64 .x1 = a.esA ∧
        sf.readReg64 .x2 = 2080#64 ∧ mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧
        (Pf ⊢ SavedArgs03 sp a ∗ (a.randA ↦ₛ a.rand) ∗ Poly32Mem (sp + 1248#64) ts ∗
          memRegion (sp + 2128#64) 64 ∗ ((sp + 2192#64) ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
          ((sp + 4272#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗ ((sp + 5232#64) ↦ₛ rBytes) ∗
          ((sp + 6768#64) ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
          ((sp + 6800#64) ↦ₛ hashed.drop 32) ∗
          ((sp + 6832#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
          ((sp + 11440#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
          ((sp + 12448#64) ↦ₛ rBytes) ∗
          ((sp + 13984#64) ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
          memRegion (sp + 15680#64) 520 ∗ memRegion (sp + 16208#64) 640 ∗ Rest)) := by
  intro rho hashed coins prf0 prf1 prf2 prf6 rBytes ts
  obtain ⟨hct1, _, hss⟩ := encaps1Out_lengths hhdr hrand
  obtain ⟨hr_len, hr_eq⟩ := poly3_bytes_join (sp + 12448#64) (rHatPoly16 prf0)
    (rHatPoly16 prf1) (rHatPoly16 prf2)
  have htd32 : (a.hdr64.drop 32).take 32 = a.hdr64.drop 32 := List.take_of_length_le (by simp [hhdr])
  have htr32 : a.rand.take 32 = a.rand := List.take_of_length_le (Nat.le_of_eq hrand)
  have hhash_pts : ((sp + 6768#64) ↦ₛ sha3_512List (a.rand ++ a.hdr64.drop 32)) =
      ((sp + 6768#64) ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗ ((sp + 6800#64) ↦ₛ hashed.drop 32) := by
    have hheq : sha3_512List (a.rand ++ a.hdr64.drop 32) =
        encaps1OutSs a.hdr64 a.rand ++ hashed.drop 32 := by
      unfold encaps1OutSs; rw [htr32, htd32]; exact (List.take_append_drop 32 hashed).symm
    rw [hheq, pointsToBytes_append, hss,
      show (sp + 6768#64) + BitVec.ofNat 64 32 = sp + 6800#64 by bv_omega]
  rw [show (sp + 12448#64) + 512#64 = sp + 12960#64 by bv_omega,
      show (sp + 12448#64) + 1024#64 = sp + 13472#64 by bv_omega] at hr_eq
  rw [memRegion_split' (b := sp + 4272#64) (b' := sp + 4288#64) (n := 16) (k := (2480 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 4288#64) (b' := sp + 5832#64) (n := 1544) (k := (936 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b := sp + 3728#64) (b' := sp + 4240#64) (n := 512) (k := (32 : Nat)) rfl (by bv_omega) (by decide),
      ← poly32Mem_ofFn (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i))]
  refine SepWP.weaken_pre
    (entails_sub (Entails.of_eq hr_eq) (by sep_frame) (by rw [htd32]; sep_frame))
    (sepWP_seq_env hcl hro (seg6_ser_ok hb hbase s sp hhdr hrand _ hpc hrun hsp hspA hcl hro) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, _, _, hP1⟩
  have hm2496 : memRegion (sp + 4272#64) 16 ∗ memRegion (sp + 4288#64) 1544 ∗ memRegion (sp + 5832#64) 936 =
      memRegion (sp + 4272#64) 960 ∗ memRegion (sp + 5232#64) 1536 := by
    rw [← memRegion_split' (b := sp + 4288#64) (b' := sp + 5832#64) (n := 1544) (k := (936 : Nat)) rfl (by bv_omega) (by decide),
        ← memRegion_split' (b := sp + 4272#64) (b' := sp + 4288#64) (n := 16) (k := (2480 : Nat)) rfl (by bv_omega) (by decide),
        memRegion_split' (b := sp + 4272#64) (b' := sp + 5232#64) (n := 960) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]
  refine SepWP.weaken_pre (Entails.trans hP1 (by
      rw [memRegion_split' (b := sp + 2128#64) (b' := sp + 2192#64) (n := 64) (k := (1536 : Nat)) rfl (by bv_omega) (by decide)]
      exact entails_sub (Entails.of_eq hm2496) (by sep_frame) (by sep_frame)))
    (sepWP_seq_env hcl1 hro1 (seg6_stage_12 hb hbase s1 sp a rBytes _ _ hrand hr_len hct1 hpc1 hrun1 hsp1 hspA1 hcl1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2
      (entails_sub (Entails.of_eq hhash_pts) (by sep_frame) (by sep_frame)))
    (sepWP_seq_env hcl2 hro2 (seg6_stage_34 hb hbase s2 sp _ rBytes _ _ hss hr_len hct1 hpc2 hrun2 hsp2 hspA2 hx19_2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hP3⟩
  refine SepWP.weaken_pre hP3 ?_
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 3728#64) (by decide) (by sep_focus) fun fd => ?_
  have hfd_eq : VecRangeMem 32 (sp + 3728#64) fd = Poly32Mem (sp + 3728#64) (Vec32.ofFn fd) :=
    (poly32Mem_ofFn (sp + 3728#64) fd).symm
  rw [hfd_eq]
  refine SepWP.weaken_pre (by sep_frame) (sepWP_seq_env hcl3 hro3
    (seg6_unreverse_e2 hb hbase s3 sp a (polyVecNat (neonCbd2Poly16 prf6)) (Vec32.ofFn fd) _ hpc3 hrun3 hsp3 hspA3) ?_)
  rintro sf Pf hpcf hrunf hclf _ ⟨hspf, hspAf, hx0f, hx1f, hx2f, rfl⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hx0f, hx1f, hx2f, hclf, ?_⟩
  have hes_eq := encapsState_at_2192_eq sp hhdr hrand
  dsimp only at hes_eq
  rw [htd32] at hes_eq
  obtain ⟨_, hr2192⟩ := poly3_bytes_join (sp + 2192#64) (rHatPoly16 prf0)
    (rHatPoly16 prf1) (rHatPoly16 prf2)
  rw [show (sp + 2192#64) + 512#64 = sp + 2704#64 by bv_omega,
      show (sp + 2192#64) + 1024#64 = sp + 3216#64 by bv_omega] at hr2192
  exact entails_sub (Entails.of_eq hr2192.symm) (by sep_frame)
    (entails_sub (Entails.of_eq hes_eq) (by sep_frame) (by sep_frame))

theorem seg6_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s0 s : State) (sp : BitVec 64) (a : MlkemBlk03Args) (Rest : SepProp)
    (hhdr : a.hdr64.length = 64) (hrand : a.rand.length = 32)
    (hsp0 : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = b + offSeg5End) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hsp_def : sp = s0.sp - BitVec.ofNat 64 17024)
    (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let rho := a.hdr64.take 32
    let hashed := sha3_512List (a.rand ++ a.hdr64.drop 32)
    let coins := (hashed.drop 32).take 32
    let prf0 := shake256List 128 (coins ++ [0#8])
    let prf1 := shake256List 128 (coins ++ [1#8])
    let prf2 := shake256List 128 (coins ++ [2#8])
    let prf6 := shake256List 128 (coins ++ [6#8])
    SepWP (blkPC03.rebase b (fun _ => none)) (s0.readReg64 .lr) s
      (SavedArgs03 sp a ∗ SavedFrame03 (s0.sp - 160#64) s0 ∗
        (a.randA ↦ₛ a.rand) ∗ memRegion a.ret 961 ∗ memRegion a.esA 2080 ∗ memRegion a.ssA 32 ∗
        PolyMem (sp + 1248#64) (fun i => polyVecNat (neonCbd2Poly16 prf6) (31 - i)) ∗
        memRegion (sp + 2128#64) 64 ∗
        PolyMem (sp + 2192#64) (polyVecNat (uVecPoly16 rho coins 0)) ∗
        PolyMem (sp + 2704#64) (polyVecNat (uVecPoly16 rho coins 1)) ∗
        PolyMem (sp + 3216#64) (polyVecNat (uVecPoly16 rho coins 2)) ∗
        memRegion (sp + 3728#64) 544 ∗ memRegion (sp + 4272#64) 2496 ∗
        ((sp + 6768#64) ↦ₛ hashed) ∗ memRegion (sp + 6832#64) 960 ∗
        memRegion (sp + 11440#64) 960 ∗
        PolyMem (sp + 12448#64) (polyVecNat (rHatPoly16 prf0)) ∗
        PolyMem (sp + 12960#64) (polyVecNat (rHatPoly16 prf1)) ∗
        PolyMem (sp + 13472#64) (polyVecNat (rHatPoly16 prf2)) ∗
        memRegion (sp + 13984#64) 32 ∗ memRegion (sp + 15680#64) 520 ∗
        memRegion (sp + 16208#64) 640 ∗ Rest)
      (fun sf Pf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (Pf ⊢ (a.randA ↦ₛ a.rand) ∗ (a.ret ↦₈ 0#8) ∗
          ((a.ret + 1#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
          (a.esA ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
          (a.ssA ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
          memRegion sp 40 ∗ memRegion (sp + 1248#64) 512 ∗
          memRegion (sp + 2128#64) 5664 ∗ memRegion (sp + 11440#64) 960 ∗
          memRegion (sp + 12448#64) 1568 ∗ memRegion (sp + 15680#64) 520 ∗
          memRegion (sp + 16208#64) 640 ∗ memRegion (s0.sp - 160#64) 160 ∗ Rest)) := by
  intro rho hashed coins prf0 prf1 prf2 prf6
  obtain ⟨hct1, hes, hss⟩ := encaps1Out_lengths hhdr hrand
  obtain ⟨hr_len, _⟩ := poly3_bytes_join (sp + 12448#64) (rHatPoly16 prf0)
    (rHatPoly16 prf1) (rHatPoly16 prf2)
  have htl : (hashed.drop 32).length = 32 := by simp [hashed, sha3_512List_length]
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro (seg6_mid_ok hb hbase s sp a _ hhdr hrand hpc hrun hsp hspA hcl hro) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx0_1, hx1_1, hx2_1, _, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (by sep_frame))
    (sepWP_seq_env hcl1 hro1 (seg6_b11_and_outputs hb hbase s1 sp a _ _ _ _
      hes hss hct1 hpc1 hrun1 hsp1 hspA1 hx0_1 hx1_1 hx2_1 hcl1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, _, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2 (seg6_epilogue hb hbase s0 s2 _ hsp0 hpc2 hrun2 (hsp2.trans hsp_def)) ?_)
  rintro sf Pf hpcf hrunf _ _ ⟨hspf, hcs, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hcs, Entails.trans hPf ?_⟩
  exact entails_sub
    (Rest := (a.randA ↦ₛ a.rand) ∗ (a.ret ↦₈ 0#8) ∗
      ((a.ret + 1#64) ↦ₛ encaps1OutCt1 a.hdr64 a.rand) ∗
      (a.esA ↦ₛ encaps1OutEs a.hdr64 a.rand) ∗
      (a.ssA ↦ₛ encaps1OutSs a.hdr64 a.rand) ∗
      memRegion (sp + 15680#64) 520 ∗ memRegion (sp + 16208#64) 640 ∗
      memRegion (s0.sp - 160#64) 160 ∗ Rest)
    (seg6_post_collapse sp a _ hes hct1 hr_len hss htl) (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6

