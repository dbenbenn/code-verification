/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 1c (`+0x02d0 .. +0x052c`) & Composed `seg1_ok`

Copies `sHat[1]` to `[sp + 22912, sp + 23424)`, spills `dkA + 384` at `sp + 1888`, runs AdvSIMD
unreduced `deserialize_12` loop 2 on `(dk.drop 768).take 384`, copies `sHat[2]` to
`[sp + 23424, sp + 23936)`, zeroes `[sp + 11856, sp + 13392)` via `B29` (`memset`), populates the
21-vector `uHatZetaSpill21` table at `[sp + 1920, sp + 2256)` plus Segment 2 entry registers, and
composes `seg1a_ok` + `seg1b_ok` + `seg1c_ok` into `seg1_ok` (`+0x0000 .. +0x052c`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c

open Arm64 Arm64.Obj ProofLib SepProp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase
  MlKemPlacement
  mlkemCall_of_blockOk
  mlkemMpl
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemsetSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk29_memset_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem
  PolyMem
  SepLoad128
  SepStore128
  Vec128At
  Vec32
  poly32Mem_ofFn
  polyVecNat
  step_ldrQ128
  step_stpQ128
  step_strQ128
  vecRangeBytes
  vecRangeBytes_length
  vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub
  sepWP_elim_cell8
  spAligned_of_chk
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  loadVec12
  rawDeser12
  rawDeser12_loadVec12_eq
  tHatPoly16
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdDup_8h
  exec_simdTbl_16b_1
  exec_simdUshl_8h
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  SavedFrame04
  blk04_code_eq
  blk04_tree_size
  blkLib04
  blkPC04
  blkPl04
  blkPlaceable04
  blkTree04
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepStore128.spill21
  Spill21
  Spill21Mem
  spill21Mem_ofFn
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (
  Seg1aSpatial
  seg1a_ok
  sepWP_elim_poly32
  sepWP_elim_vec128At
  sepWP_elim_vecRange
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1b (
  blk28_memcpy_04
  cst16_3_val
  dk_pointsTo_split
  exec_simdBic_8h_240
  exec_simdMovi_2d_0
  exec_simdMvni_4s_3
  mvni_4s_3_val
  seg1b_ok
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x02d0 → 0x0528]
end

theorem blk29_memset_04 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC04.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC04.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC04

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

private theorem mask_getElem_16_128 (k : Nat) (_hk : k < 128) :
    (65535#128)[k] = decide (k < 16) := by
  have hm : (65535#128) = (BitVec.allOnes 16).setWidth 128 := rfl
  rw [hm, BitVec.getElem_setWidth]
  by_cases h : k < 16
  · rw [BitVec.getLsbD_eq_getElem h, BitVec.getElem_allOnes, decide_eq_true h]
  · rw [BitVec.getLsbD_of_ge _ _ (by omega), decide_eq_false h]

private theorem zext64_and_ffff_eq (w : BitVec 64) :
    (w.zeroExtend 128) &&& (1#128 <<< 16 - 1#128) = (w.truncate 16).zeroExtend 128 := by
  ext k hk
  simp only [show (1#128 <<< 16 - 1#128 : BitVec 128) = 65535#128 from rfl,
    BitVec.getElem_and, mask_getElem_16_128 k hk]
  rw [BitVec.getElem_setWidth, BitVec.getElem_setWidth]
  simp [Bool.and_comm]

private theorem mapLanes4_zext16_eq_dup4hLow (x : BitVec 16) :
    mapLanes 16 0#128 (fun _ => BitVec.setWidth 128 x) 4 = dup4hLow x := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hm : laneMask 16 = 65535#128 := rfl
  have hm_lsb : ∀ k, (65535#128).getLsbD k = decide (k < 16) := by
    intro k
    by_cases hk : k < 128
    · rw [BitVec.getLsbD_eq_getElem hk, mask_getElem_16_128 k hk]
    · rw [BitVec.getLsbD_of_ge _ _ (by omega), decide_eq_false (by omega)]
  by_cases h4 : b < 64
  · simp only [mapLanes, hm, dup4hLow, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
      BitVec.getLsbD_zero, hm_lsb, hb, decide_true, Bool.true_and]
    by_cases h1 : b < 16
    · simp [h1, hb, show b < 32 by omega, show b < 48 by omega]
    · by_cases h2 : b < 32
      · simp [h1, h2, show b < 48 by omega, show b - 16 < 16 by omega, show b - 16 < 128 by omega]
      · by_cases h3 : b < 48
        · have heq : b - 16 - 16 = b - 32 := by omega
          simp [heq, h1, h2, h3, show ¬ (b - 16 < 16) by omega,
            show b - 32 < 16 by omega, show b - 32 < 128 by omega]
        · have heq : b - 16 - 16 - 16 = b - 48 := by omega
          simp [heq, h1, h2, h3, show ¬ (b - 16 < 16) by omega, show ¬ (b - 32 < 16) by omega,
            show ¬ (b - 16 - 16 < 16) by omega, show b - 48 < 16 by omega,
            show b - 48 < 128 by omega]
  · simp only [mapLanes, hm, dup4hLow, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero,
      hm_lsb, hb, decide_true, Bool.true_and, BitVec.getLsbD_of_ge (x ++ x ++ x ++ x) b (by omega)]
    simp [show ¬ (b < 16) by omega, show ¬ (b < 32) by omega, show ¬ (b < 48) by omega,
      show ¬ (b - 16 < 16) by omega, show ¬ (b - 32 < 16) by omega, show ¬ (b - 48 < 16) by omega]

@[simp, arm64_norm, wp_norm]
theorem exec_simdDup_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup4hLow ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc] at hz ⊢
  rw [hz, mapLanes4_zext16_eq_dup4hLow]

attribute [local wp_norm ↓ high]
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdDup_8h exec_simdDup_4h
  exec_simdMovi_2d_0 exec_simdMvni_4s_3 exec_simdBic_8h_240

/-! ## 1. `uHatZetaSpill21` & Shared Helpers -/

@[expose] def uHatZetaVal : Nat → BitVec 16
  | 0 => 962#16 | 1 => 49846#16 | 2 => 61737#16 | 3 => 1577#16 | 4 => 27758#16
  | 5 => 622#16 | 6 => 44629#16 | 7 => 48842#16 | 8 => 28191#16 | 9 => 287#16
  | 10 => 53134#16 | 11 => 1422#16 | 12 => 13525#16 | 13 => 1493#16 | 14 => 787#16
  | 15 => 64019#16 | 16 => 14745#16 | 17 => 65177#16 | 18 => 3329#16 | 19 => 31498#16
  | 20 => 64778#16 | _ => 0#16

@[expose] def uHatZetaSpill21 : Spill21 :=
  Spill21.ofFn fun i => dup8x16 (uHatZetaVal i)

theorem sepWP_elim_spill21 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Spill21, SepWP prog target s (Spill21Mem a t ∗ R0) post) :
    SepWP prog target s (memRegion a 336 ∗ R0) post := by
  change SepWP prog target s (memRegion a (16 * 21) ∗ R0) post
  refine sepWP_elim_vecRange 21 (by decide) fun f => ?_
  rw [← spill21Mem_ofFn a f]
  exact h (Spill21.ofFn f)

private theorem update2_prefix {f g : Nat → BitVec 128} {k : Nat}
    (hf : ∀ j, j < 2 * k → f j = g j) :
    ∀ j, j < 2 * (k + 1) →
      Function.update (Function.update f (2 * k) (g (2 * k))) (2 * k + 1) (g (2 * k + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * k + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * k
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g := vecRangeMem_congr h

private theorem poly32Mem_zero_eq (ptr : BitVec 64) :
    Poly32Mem ptr Vec32.zero = PolyMem ptr (fun _ => 0#128) :=
  poly32Mem_ofFn ptr (fun _ => 0#128)

local macro "step_strQ_poly0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { bv_omega }; { rfl }
  · wp_norm_lhs
  intro _))

local macro "step_strQ_spill21 " k:num : tactic => `(tactic| (
  apply step_strQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · wp_norm_lhs
  · apply SepStore128.left; apply SepStore128.spill21 (k := $k)
    · decide
    · bv_omega
    · rfl
  · wp_norm_lhs
  intro _))

local macro "step_ldrQ_vec0" : tactic => `(tactic| (
  apply step_ldrQ128
  · wp_norm_lhs
  · first | wp_norm_lhs | simp [*]
  · wp_norm_lhs
  · first | rfl | wp_norm_lhs | wp_norm_goal | simp [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, *]
  · wp_norm_lhs
  · apply SepLoad128.left; apply SepLoad128.vec128At; bv_omega
  · wp_norm_lhs))

local macro "step_zero32_poly0" : tactic => `(tactic| (
  step_strQ_poly0 31; step_strQ_poly0 30; step_strQ_poly0 29; step_strQ_poly0 28;
  step_strQ_poly0 27; step_strQ_poly0 26; step_strQ_poly0 25; step_strQ_poly0 24;
  step_strQ_poly0 23; step_strQ_poly0 22; step_strQ_poly0 21; step_strQ_poly0 20;
  step_strQ_poly0 19; step_strQ_poly0 18; step_strQ_poly0 17; step_strQ_poly0 16;
  step_strQ_poly0 15; step_strQ_poly0 14; step_strQ_poly0 13; step_strQ_poly0 12;
  step_strQ_poly0 11; step_strQ_poly0 10; step_strQ_poly0 9; step_strQ_poly0 8;
  step_strQ_poly0 7; step_strQ_poly0 6; step_strQ_poly0 5; step_strQ_poly0 4;
  step_strQ_poly0 3; step_strQ_poly0 2; step_strQ_poly0 1; step_strQ_poly0 0))

/-! ## 2. Sub-Segments of `Seg1c` (`+0x02d0 .. +0x052c`) -/

private theorem seg1c_copy1_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp dkA : BitVec 64) (dk1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 720#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = dkA + 384#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 908#64) s
      (memRegion (sp + 1888#64) 8 ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 22912#64) 512 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk1)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = dkA + 768#64 ∧ sf.readReg64 .x20 = sp + 11856#64 ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = mvni_4s_3_val ∧
        sf.readVReg128 3#5 = cst16_3_val ∧
        (Pf ⊢ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗
          Vec128At (sp + 1904#64) cst16_3_val ∗
          PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) ∗
          Poly32Mem (sp + 11856#64) Vec32.zero ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 1888#64)); intro c1888
  generalize hbs1_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 dk1)) = bs1
  have hbs1 : bs1.length = 512 := by rw [← hbs1_def, vecRangeBytes_length]
  have hp11856 : PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk1)) = ((sp + 11856#64) ↦ₛ bs1) := by
    rw [← hbs1_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp22912 : ((sp + 22912#64) ↦ₛ bs1) = PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) := by
    rw [← hbs1_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp11856_32 : ((sp + 11856#64) ↦ₛ bs1) =
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk1))) := by
    rw [← hp11856, poly32Mem_ofFn]
  have ha768 : dkA + 384#64 + 384#64 = dkA + 768#64 := by clear * -; bv_omega
  rw [hp11856]
  wp_cut_codeLoaded
  wp_steps 8
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 22912#64, sp + 11856#64, bs1)
  rw [hp22912, hp11856_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hreord0 : PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk1))) ∗
      (((sp + 1888#64) ↦₆₄ c1888) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗ Rest) ⊢
      Vec128At (sp + 1904#64) cst16_3_val ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk1))) ∗
      ((sp + 1888#64) ↦₆₄ c1888) ∗
      PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) ∗ Rest := by sep_frame
  refine SepWP.weaken_pre hreord0 ?_
  wp_steps 2
  step_ldrQ_vec0
  wp_steps 3
  have hreord1 : Vec128At (sp + 1904#64) cst16_3_val ∗
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk1))) ∗
      ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗
      PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) ∗ Rest ⊢
      Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (tHatPoly16 dk1))) ∗
      (((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 dk1)) ∗ Rest) := by sep_frame
  refine SepWP.weaken_pre hreord1 ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp, by simp [*], by simp [*], by simp [*],
      by simp [*], by simp [*], by simp, by simp, ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

local macro "prove_deser12_loop " src:ident dst:ident bs:ident hbs:ident
    pc0:term:arg pc1:term:arg pc2:term:arg pc3:term:arg pc4:term:arg
    srcReg:term:arg : tactic => `(tactic| (
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih =>
    intro k hkrem s f hpc hrun hspA hx_src hx8 hx_dst hv0 hv3 hf
    have hk16 : k < 16 := by omega
    refine SepWP.step_ldrSimd64 (pc := $pc0) hpc hrun (by wp_norm_lhs) rfl
      (show evalAddrMode s (.Offset $srcReg 0#64) = ($src + BitVec.ofNat 64 (24 * k), none) by
        simp [evalAddrMode, hx_src])
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    refine SepWP.step_ldrSimd64 (pc := $pc1) (by simp [wp_norm, arm64_norm]) hrun
      (by wp_norm_lhs) rfl
      (show evalAddrMode _ (.UnscaledOffset $srcReg 12#64) =
          ($src + BitVec.ofNat 64 (24 * k + 12), none) by
        simp [evalAddrMode, hx_src]; clear * -; bv_omega)
      (SepLoad64.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    wp_steps 3
    refine step_simdLd1Single32 (pc := $pc2) (by simp [wp_norm, arm64_norm])
      (by simp [hrun]) (by wp_norm_lhs) rfl
      (show _ = $src + BitVec.ofNat 64 (24 * k + 8) by simp [hx_src]; clear * -; bv_omega)
      (SepLoad32.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    refine step_simdLd1Single32 (pc := $pc3) (by simp [wp_norm, arm64_norm])
      (by simp [hrun]) (by wp_norm_lhs) rfl
      (show _ = $src + BitVec.ofNat 64 (24 * k + 20) by simp [hx_src]; clear * -; bv_omega)
      (SepLoad32.of_pointsToBytes rfl (by omega) rfl) (by wp_norm_lhs) ?_
    wp_steps 9
    have hv1_eq : rawDeser12 (loadVec12 $bs (24 * k)) = polyVecNat (tHatPoly16 $bs) (2 * k) := by
      simpa [show 12 * (2 * k) = 24 * k by omega] using rawDeser12_loadVec12_eq $hbs (2 * k) (by omega)
    have hv2_eq : rawDeser12 (loadVec12 $bs (24 * k + 12)) = polyVecNat (tHatPoly16 $bs) (2 * k + 1) := by
      simpa [show 12 * (2 * k + 1) = 24 * k + 12 by omega] using
        rawDeser12_loadVec12_eq $hbs (2 * k + 1) (by omega)
    refine step_stpQ128 (pc := $pc4) (wb := none) (ea := $dst + BitVec.ofNat 64 (32 * k))
      (ea16 := $dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (tHatPoly16 $bs) (2 * k)) (v2 := polyVecNat (tHatPoly16 $bs) (2 * k + 1))
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_dst, hx8]) rfl
      (by simp [hv0, hv3, ← hv1_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
      (by simp [hv0, hv3, ← hv2_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k) (by omega) (by clear * -; bv_omega))))
      (SepStore128.right (SepStore128.left
        (SepStore128.polyMem (k := 2 * k + 1) (by omega) (by clear * -; bv_omega))))
      (by wp_norm_lhs) ?_
    intro m'
    wp_step
    wp_if hne
    · rcases rem with _ | rem'
      · have hk15 : k = 15 := by omega
        subst hk15; simp [hx8] at hne
      · refine SepWP.mono
          (ih rem' (by omega) (k + 1) (by omega) _ _
            (by wp_norm_lhs) (by first | rfl | simp [hrun])
            (by simpa [State.spAligned] using hspA)
            (by simp [hx_src]; clear * -; bv_omega)
            (by simp [hx8]; clear * -; bv_omega)
            (by simp [hx_dst]) (by simp [hv0]) (by simp [hv3])
            (update2_prefix hf)) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx26_f, hx28_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hfp_f,
          by simpa using hx26_f, by simpa using hx28_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa [hx8] using hne
        have hlt1 : 32 * k < 2 ^ 64 := by omega
        have hlt2 : 32 * k + 32 < 2 ^ 64 := by omega
        have hnat := congrArg BitVec.toNat hbv
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
            show (32#64).toNat = 32 from rfl, Nat.mod_eq_of_lt hlt2,
            show (512#64).toNat = 512 from rfl] at hnat
        omega
      subst hk15
      have hf32 : ∀ j, j < 32 →
          Function.update (Function.update f 30 (polyVecNat (tHatPoly16 $bs) 30))
            31 (polyVecNat (tHatPoly16 $bs) 31) j = polyVecNat (tHatPoly16 $bs) j :=
        update2_prefix (k := 15) hf
      refine SepWP.done (by wp_norm_lhs) (by first | rfl | simp [hrun])
        ⟨by simp, by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp, ?_⟩
      rw [polyMem_congr hf32]; sep_frame))

private theorem seg1c_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 908#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x20 = dst →
      s.readVReg128 0#5 = mvni_4s_3_val →
      s.readVReg128 3#5 = cst16_3_val →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 980#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          sf.readReg64 .x28 = s.readReg64 .x28 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 908#64) (b + 912#64) (b + 928#64) (b + 932#64) (b + 972#64) Reg.x9

private theorem seg1c_copy2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (dk2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 980#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1016#64) s
      (PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk2)) ∗
        memRegion (sp + 12368#64) 1024 ∗ memRegion (sp + 23424#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Pf ⊢ memRegion (sp + 11856#64) 1536 ∗
          PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 dk2)) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 dk2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp11856 : PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 dk2)) = ((sp + 11856#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp23424 : ((sp + 23424#64) ↦ₛ bs2) = PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 dk2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hreord_in :
      ((sp + 11856#64) ↦ₛ bs2) ∗ memRegion (sp + 12368#64) 1024 ∗
        memRegion (sp + 23424#64) 512 ∗ Rest ⊢
      memRegion (sp + 23424#64) 512 ∗ ((sp + 11856#64) ↦ₛ bs2) ∗
        (memRegion (sp + 12368#64) 1024 ∗ Rest) := by sep_frame
  rw [hp11856]
  refine SepWP.weaken_pre hreord_in ?_
  wp_cut_codeLoaded
  wp_steps 8
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 23424#64, sp + 11856#64, bs2)
  rw [hp23424]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have h512 : ((sp + 11856#64) ↦ₛ bs2) ∗ memRegion (sp + 12368#64) 1024 ⊢
      memRegion (sp + 11856#64) 1536 := by
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (1024 : Nat))
      rfl (by bv_omega) (by decide)]
    have hpb := pointsToBytes_entails_memRegion (sp + 11856#64) bs2
    rw [hbs2] at hpb
    exact sepConj_mono_left hpb
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  exact entails_sub h512 (by sep_frame) (by sep_frame)

private theorem seg1c_zero_spill [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 1016#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = sp + 11856#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1324#64) s
      (memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 1920#64) 336 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x20 = 62209#64 ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x23 = sp + 11872#64 ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = sp + 3353#64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 8#5 = dup4hLow 3329#16 ∧
        sf.readVReg128 11#5 = dup8x16 3329#16 ∧
        (Pf ⊢ Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
          memRegion (sp + 11856#64) 1536 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk29_memset_04 blkPl04.base) (sp + 11856#64, 0#8, 1536)
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have h1536 : ((sp + 11856#64) ↦ₛ List.replicate 1536 0#8) ⊢ memRegion (sp + 11856#64) 1536 := by
    have hpb := pointsToBytes_entails_memRegion (sp + 11856#64) (List.replicate 1536 0#8)
    rwa [List.length_replicate] at hpb
  have hreord_sp :
      ((sp + 11856#64) ↦ₛ List.replicate 1536 0#8) ∗ (memRegion (sp + 1920#64) 336 ∗ Rest) ⊢
      memRegion (sp + 1920#64) 336 ∗ (memRegion (sp + 11856#64) 1536 ∗ Rest) :=
    entails_sub h1536 (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hreord_sp ?_
  sep_frame_apply (sepWP_elim_spill21 (a := sp + 1920#64)); intro t0
  wp_steps 12
  step_strQ_spill21 20
  wp_steps 5
  step_strQ_spill21 18
  step_strQ_spill21 19
  wp_steps 2; step_strQ_spill21 17
  wp_steps 2; step_strQ_spill21 16
  wp_steps 2; step_strQ_spill21 15
  wp_steps 2; step_strQ_spill21 14
  wp_steps 2; step_strQ_spill21 13
  wp_steps 2; step_strQ_spill21 12
  wp_steps 2; step_strQ_spill21 11
  wp_steps 2; step_strQ_spill21 10
  wp_steps 2; step_strQ_spill21 9
  wp_steps 2; step_strQ_spill21 8
  wp_steps 2; step_strQ_spill21 7
  wp_steps 2; step_strQ_spill21 6
  wp_steps 2; step_strQ_spill21 5
  wp_steps 2; step_strQ_spill21 4
  wp_steps 2; step_strQ_spill21 3
  wp_steps 1; step_strQ_spill21 2
  wp_steps 2; step_strQ_spill21 1
  wp_steps 1; step_strQ_spill21 0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp, by simp,
      by simp [*], by simp [*], by simp,
      by simp, by simp [*],
      by simp, by simp [*],
      by simp, by simp, ?_⟩
  have hspill_eq :
      (((((((((((((((((((((t0.set 20 (dup8x16 64778#16)).set 18 (dup8x16 3329#16)).set 19
        (dup8x16 31498#16)).set 17 (dup8x16 65177#16)).set 16 (dup8x16 14745#16)).set 15
        (dup8x16 64019#16)).set 14 (dup8x16 787#16)).set 13 (dup8x16 1493#16)).set 12
        (dup8x16 13525#16)).set 11 (dup8x16 1422#16)).set 10 (dup8x16 53134#16)).set 9
        (dup8x16 287#16)).set 8 (dup8x16 28191#16)).set 7 (dup8x16 48842#16)).set 6
        (dup8x16 44629#16)).set 5 (dup8x16 622#16)).set 4 (dup8x16 27758#16)).set 3
        (dup8x16 1577#16)).set 2 (dup8x16 61737#16)).set 1 (dup8x16 49846#16)).set 0
        (dup8x16 962#16)) = uHatZetaSpill21 := by
    cases t0; rfl
  rw [hspill_eq]
  sep_frame

/-- Composed Segment 1c contract (`+0x02d0 → +0x052c`). -/
theorem seg1c_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fp0 dkA : BitVec 64) (dk : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 720#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hfp : s.readReg64 .fp = fp0)
    (hx24 : s.readReg64 .x24 = dkA + 384#64)
    (hx26 : s.readReg64 .x26 = sp + 20704#64)
    (hx28 : s.readReg64 .x28 = sp + 20968#64)
    (hdk : dk.length = 2400) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1324#64) s
      (memRegion (sp + 1888#64) 8 ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 1920#64) 336 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        memRegion (sp + 12368#64) 1024 ∗
        memRegion (sp + 22912#64) 512 ∗ memRegion (sp + 23424#64) 512 ∗
        ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fp0 ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x20 = 62209#64 ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x23 = sp + 11872#64 ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = sp + 3353#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        sf.readVReg128 8#5 = dup4hLow 3329#16 ∧
        sf.readVReg128 11#5 = dup8x16 3329#16 ∧
        (Pf ⊢ ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗
          Vec128At (sp + 1904#64) cst16_3_val ∗
          Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
          memRegion (sp + 11856#64) 1536 ∗
          PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
          PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
          ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest)) := by
  have hl2 : ((dk.drop 768).take 384).length = 384 := by simp [hdk]
  have hP0 :
      memRegion (sp + 1888#64) 8 ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 1920#64) 336 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        memRegion (sp + 12368#64) 1024 ∗
        memRegion (sp + 22912#64) 512 ∗ memRegion (sp + 23424#64) 512 ∗
        ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest ⊢
      memRegion (sp + 1888#64) 8 ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 22912#64) 512 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        (memRegion (sp + 1920#64) 336 ∗ memRegion (sp + 12368#64) 1024 ∗
          memRegion (sp + 23424#64) 512 ∗ ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hP0
    (sepWP_seq_env hcl hro
      (seg1c_copy1_zero2 hb hbase s sp dkA ((dk.drop 384).take 384) _
        hpc hrun hsp hspA hx24 hcl) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx20_1, hfp_1, hx26_1, hx28_1, hv0_1, hv3_1, hP1⟩
  have hP1' : P1 ⊢ ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗
      PolyMem (sp + 11856#64) (fun _ => 0#128) ∗
      (((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 1920#64) 336 ∗ memRegion (sp + 12368#64) 1024 ∗
        PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        memRegion (sp + 23424#64) 512 ∗ Rest) := by
    refine Entails.trans hP1 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg1c_loop2 hb (dkA + 768#64) (sp + 11856#64) ((dk.drop 768).take 384) _ hl2 15 0 rfl s1
        (fun _ => 0#128) hpc1 hrun1 hspA1
        (by simp [hx9_1]) (by simp [hx8_1]) hx20_1 hv0_1 hv3_1 (by omega)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp_2, hx26_2, hx28_2, hP2⟩
  have hP2' : P2 ⊢ PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
      memRegion (sp + 12368#64) 1024 ∗ memRegion (sp + 23424#64) 512 ∗
      (((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 1920#64) 336 ∗
        PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest) :=
    Entails.trans hP2 (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg1c_copy2 hb hbase s2 sp ((dk.drop 768).take 384) _
        hpc2 hrun2 (hsp2.trans hsp1) hspA2 hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hsp3, hspA3, hfp_3, hx22_3, hx26_3, hx28_3, hP3⟩
  have hP3' : P3 ⊢ memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 1920#64) 336 ∗
      (((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
        ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗ Rest) :=
    Entails.trans hP3 (by sep_frame)
  refine SepWP.weaken_pre hP3'
    (SepWP.mono
      (seg1c_zero_spill hb hbase s3 sp _
        hpc3 hrun3 hsp3 hspA3 hx22_3 hcl3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx8_f, hx20_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, hPf⟩
  refine ⟨hsp_f, hspA_f,
    by rw [hfp_f, hfp_3, hfp_2, hfp_1, hfp],
    hx8_f, hx20_f, hx22_f, hx23_f, hx24_f, hx25_f,
    by rw [hx26_f, hx26_3, hx26_2, hx26_1, hx26],
    hx27_f,
    by rw [hx28_f, hx28_3, hx28_2, hx28_1, hx28],
    hv8_f, hv11_f, Entails.trans hPf (by sep_frame)⟩

/-! ## 3. Full Segment 1 Composition (`+0x0000 .. +0x052c`) -/

@[expose] def Seg1Spatial (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 25824#64
  stackAt sp 1136 ∗
  SavedFrame04 s0.sp s0 ∗
  memRegion sp 136 ∗
  ((sp + 136#64) ↦₆₄ ret) ∗
  memRegion (sp + 144#64) 56 ∗
  ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
  memRegion (sp + 208#64) 1632 ∗
  ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
  memRegion (sp + 1848#64) 8 ∗
  ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
  memRegion (sp + 1864#64) 8 ∗
  ((sp + 1872#64) ↦₆₄ dkA) ∗
  memRegion (sp + 1880#64) 8 ∗
  ((sp + 1888#64) ↦₆₄ (dkA + 384#64)) ∗
  memRegion (sp + 1896#64) 8 ∗
  Vec128At (sp + 1904#64) cst16_3_val ∗
  Spill21Mem (sp + 1920#64) uHatZetaSpill21 ∗
  ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗
  ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
  memRegion (sp + 4432#64) 17968 ∗
  PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
  PolyMem (sp + 22912#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
  PolyMem (sp + 23424#64) (polyVecNat (tHatPoly16 ((dk.drop 768).take 384))) ∗
  memRegion (sp + 23936#64) 1728 ∗
  (dkA ↦ₛ dk) ∗
  (ct1A ↦ₛ ct1) ∗
  (ct2A ↦ₛ ct2) ∗
  F

private theorem memRegion_392_seg1_split (sp : BitVec 64) :
    memRegion (sp + 1864#64) 392 =
      memRegion (sp + 1864#64) 8 ∗ memRegion (sp + 1872#64) 8 ∗
      memRegion (sp + 1880#64) 8 ∗ memRegion (sp + 1888#64) 8 ∗
      memRegion (sp + 1896#64) 8 ∗ memRegion (sp + 1904#64) 16 ∗
      memRegion (sp + 1920#64) 336 := by
  rw [memRegion_split' (b := sp + 1864#64) (b' := sp + 1872#64) (n := 8) (k := (384 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1872#64) (b' := sp + 1880#64) (n := 8) (k := (376 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1880#64) (b' := sp + 1888#64) (n := 8) (k := (368 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1888#64) (b' := sp + 1896#64) (n := 8) (k := (360 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1896#64) (b' := sp + 1904#64) (n := 8) (k := (352 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 1904#64) (b' := sp + 1920#64) (n := 16) (k := (336 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_21232_seg1_split (sp : BitVec 64) :
    memRegion (sp + 4432#64) 21232 =
      memRegion (sp + 4432#64) 7424 ∗ memRegion (sp + 11856#64) 512 ∗
      memRegion (sp + 12368#64) 1024 ∗ memRegion (sp + 13392#64) 9008 ∗
      memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 512 ∗
      memRegion (sp + 23424#64) 512 ∗ memRegion (sp + 23936#64) 1728 := by
  rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 11856#64) (n := 7424) (k := (13808 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 12368#64) (n := 512) (k := (13296 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 12368#64) (b' := sp + 13392#64) (n := 1024) (k := (12272 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 13392#64) (b' := sp + 22400#64) (n := 9008) (k := (3264 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22912#64) (n := 512) (k := (2752 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 22912#64) (b' := sp + 23424#64) (n := 512) (k := (2240 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 23424#64) (b' := sp + 23936#64) (n := 512) (k := (1728 : Nat)) rfl (by bv_omega) (by decide)]

private theorem memRegion_17968_seg1_merge (sp : BitVec 64) :
    memRegion (sp + 4432#64) 7424 ∗ memRegion (sp + 11856#64) 1536 ∗
      memRegion (sp + 13392#64) 9008 ⊢ memRegion (sp + 4432#64) 17968 := by
  rw [memRegion_split' (b := sp + 4432#64) (b' := sp + 11856#64) (n := 7424) (k := (10544 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := sp + 11856#64) (b' := sp + 13392#64) (n := 1536) (k := (9008 : Nat)) rfl (by bv_omega) (by decide)]
  exact Entails.refl _

/-- Composed Segment 1 contract (`+0x0000 → +0x052c`). -/
theorem seg1_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64)
    (dk ct1 ct2 : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = dkA)
    (hx2 : s0.readReg64 .x2 = ct1A) (hx3 : s0.readReg64 .x3 = ct2A)
    (hdk : dk.length = 2400) (hct1 : ct1.length = 960) (hct2 : ct2.length = 128) :
    let sp := s0.sp - 25824#64
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 1324#64) s0
      (stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x20 = 62209#64 ∧
        sf.readReg64 .x22 = sp + 11856#64 ∧
        sf.readReg64 .x23 = sp + 11872#64 ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = sp + 3353#64 ∧
        sf.readReg64 .x26 = sp + 20704#64 ∧
        sf.readReg64 .x27 = sp + 5680#64 ∧
        sf.readReg64 .x28 = sp + 20968#64 ∧
        sf.readVReg128 8#5 = dup4hLow 3329#16 ∧
        sf.readVReg128 11#5 = dup8x16 3329#16 ∧
        (Pf ⊢ Seg1Spatial s0 ret dkA ct1A ct2A dk ct1 ct2 F)) := by
  intro sp
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl hro
      (seg1a_ok hb hbase s0 ret dkA ct1A ct2A ct1 ct2 ((dkA ↦ₛ dk) ∗ F)
        hpc hrun hsp0 hcl hro hx0 hx1 hx2 hx3 hct1 hct2) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx20_1, hx23_1, hx24_1, hx26_1, hx28_1, hP1⟩
  have hP1' : P1 ⊢
      memRegion (sp + 11856#64) 512 ∗ memRegion (sp + 1904#64) 16 ∗
      (memRegion (sp + 1872#64) 8 ∗ memRegion (sp + 22400#64) 512 ∗
        (dkA ↦ₛ dk.take 384) ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗
        (memRegion (sp + 1888#64) 8 ∗ memRegion (sp + 1920#64) 336 ∗
          memRegion (sp + 12368#64) 1024 ∗
          memRegion (sp + 22912#64) 512 ∗ memRegion (sp + 23424#64) 512 ∗
          ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗
          ((dkA + 1152#64) ↦ₛ dk.drop 1152) ∗
          stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
          memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
          memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
          memRegion (sp + 208#64) 1632 ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
          memRegion (sp + 1848#64) 8 ∗ ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
          memRegion (sp + 1864#64) 8 ∗ memRegion (sp + 1880#64) 8 ∗
          memRegion (sp + 1896#64) 8 ∗
          ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
          memRegion (sp + 4432#64) 7424 ∗ memRegion (sp + 13392#64) 9008 ∗
          memRegion (sp + 23936#64) 1728 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F)) := by
    refine Entails.trans hP1 ?_
    dsimp only [Seg1aSpatial]
    rw [memRegion_392_seg1_split sp, memRegion_21232_seg1_split sp, dk_pointsTo_split dkA hdk]
    sep_frame
  refine SepWP.weaken_pre hP1' ?_
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 11856#64)); intro vInit
  sep_frame_apply (sepWP_elim_vec128At (a := sp + 1904#64)); intro v1904
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg1b_ok hb hbase s1 sp (s0.sp - 96#64) dkA vInit v1904 dk _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hfp1 hx20_1 hx23_1 hx24_1 hx26_1 hx28_1 hdk) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, _hx21_2, hx24_2, hx26_2, hx28_2, hP2⟩
  have hP2' : P2 ⊢
      memRegion (sp + 1888#64) 8 ∗ Vec128At (sp + 1904#64) cst16_3_val ∗
        memRegion (sp + 1920#64) 336 ∗
        PolyMem (sp + 11856#64) (polyVecNat (tHatPoly16 ((dk.drop 384).take 384))) ∗
        memRegion (sp + 12368#64) 1024 ∗
        memRegion (sp + 22912#64) 512 ∗ memRegion (sp + 23424#64) 512 ∗
        ((dkA + 768#64) ↦ₛ (dk.drop 768).take 384) ∗
        (((sp + 1872#64) ↦₆₄ dkA) ∗
          PolyMem (sp + 22400#64) (polyVecNat (tHatPoly16 (dk.take 384))) ∗
          (dkA ↦ₛ dk.take 384) ∗ ((dkA + 384#64) ↦ₛ (dk.drop 384).take 384) ∗
          ((dkA + 1152#64) ↦ₛ dk.drop 1152) ∗
          stackAt sp 1136 ∗ SavedFrame04 s0.sp s0 ∗
          memRegion sp 136 ∗ ((sp + 136#64) ↦₆₄ ret) ∗
          memRegion (sp + 144#64) 56 ∗ ((sp + 200#64) ↦₆₄ (sp + 22664#64)) ∗
          memRegion (sp + 208#64) 1632 ∗ ((sp + 1840#64) ↦₆₄ (dkA + 2336#64)) ∗
          memRegion (sp + 1848#64) 8 ∗ ((sp + 1856#64) ↦₆₄ (dkA + 2368#64)) ∗
          memRegion (sp + 1864#64) 8 ∗ memRegion (sp + 1880#64) 8 ∗
          memRegion (sp + 1896#64) 8 ∗
          ((sp + 2256#64) ↦ₛ (ct1 ++ ct2)) ∗ ((sp + 3344#64) ↦ₛ (ct1 ++ ct2)) ∗
          memRegion (sp + 4432#64) 7424 ∗ memRegion (sp + 13392#64) 9008 ∗
          memRegion (sp + 23936#64) 1728 ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ F) :=
    Entails.trans hP2 (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (SepWP.mono
      (seg1c_ok hb hbase s2 sp (s0.sp - 96#64) dkA dk _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hfp2 hx24_2 hx26_2 hx28_2 hdk) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx8_f, hx20_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, hPf⟩
  refine ⟨hsp_f, hspA_f, hfp_f, hx8_f, hx20_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, ?_⟩
  dsimp only [Seg1Spatial]
  rw [dk_pointsTo_split dkA hdk]
  exact Entails.trans hPf (entails_sub (memRegion_17968_seg1_merge sp) (by sep_frame) (by sep_frame))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1c
