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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `kyber_decapsulate` (`B06`) — Segment 1c (`+0x0380 .. +0x05dc`)

Copies `sHat[2]` to `[sp + 31472, sp + 31984)`, spills `ctA` at `sp + 136` and `skA + 384` at
`sp + 2016`, runs AdvSIMD unreduced `deserialize_12` loop 3 on `(sk.drop 1152).take 384`, copies
`sHat[3]` to `[sp + 31984, sp + 32496)`, zeroes `[sp + 14432, sp + 16480)` via `B29` (`memset`),
and populates the 21-vector `uHatZetaSpill40` table at `[sp + 2064, sp + 2400)` together with
entry registers for Segment 2 (`uHat` loop at `+0x05dc`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c

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
  VecRangeMem
  poly32Mem_ofFn
  polyVecNat
  step_ldrQ128
  step_stpQ128
  step_strQ128
  vecRangeBytes
  vecRangeBytes_length
  vecRangeMem_congr
  vecRangeMem_entails_memRegion
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq
  blk06_tree_size
  blkLib06
  blkPC06
  blkPl06
  blkPlaceable06
  blkTree06
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  SepStore128.spillSlice
  Spill40
  SpillSliceMem
  spill40_ofFn_get
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (
  blk28_memcpy_06
  cst16_3_val
  exec_simdBic_8h_240
  exec_simdMovi_2d_0
  exec_simdMvni_4s_3
  uHatZetaSpill40
)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x0380 → 0x05d8]
end

theorem blk29_memset_06 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC06.rebase b (fun _ => none)) (mlkemMpl.base 29)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemsetSpec) :=
  mlkemCall_of_blockOk (blkPC06.rebase b (fun _ => none)) blk29_memset_ok

attribute [local irreducible] blkPC06

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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
private theorem exec_simdDup_4h {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup false false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup4hLow ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC := by
  have hz := zext64_and_ffff_eq (s.readReg64 (Reg.fromZRBits rn))
  simp [execInstWithSvc] at hz ⊢
  rw [hz, mapLanes4_zext16_eq_dup4hLow]

attribute [local wp_norm ↓ high]
  exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdDup_8h exec_simdDup_4h
  exec_simdMovi_2d_0 exec_simdMvni_4s_3 exec_simdBic_8h_240

/-! ## 1. Vector Region Elimination & Store Helpers -/

theorem sepWP_elim_vec128At {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 128, SepWP prog target s (Vec128At a v ∗ R0) post) :
    SepWP prog target s (memRegion a 16 ∗ R0) post := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := (8 : Nat)) rfl rfl (by decide)]
  sep_frame_apply (sepWP_elim_cell8 (a := a)); intro v0
  sep_frame_apply (sepWP_elim_cell8 (a := a + 8#64)); intro v1
  have hv : Vec128At a (v1 ++ v0) = (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) := by
    unfold Vec128At
    have h0 : (v1 ++ v0).extractLsb' 0 64 = v0 := by bv_bits
    have h1 : (v1 ++ v0).extractLsb' 64 64 = v1 := by bv_bits
    rw [h0, h1]
  refine SepWP.weaken_pre ?_ (h (v1 ++ v0))
  rw [hv]; sep_frame

theorem sepWP_elim_vecRange :
    ∀ (n : Nat), n ≤ 40 → ∀ {prog : Program} {target : BitVec 64} {s : State}
      {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop},
      (∀ f : Nat → BitVec 128, SepWP prog target s (VecRangeMem n a f ∗ R0) post) →
      SepWP prog target s (memRegion a (16 * n) ∗ R0) post
  | 0, _, _, _, _, a, _, _, h => by
    simpa [VecRangeMem, memRegion_zero] using h (fun _ => 0#128)
  | n + 1, hn, _, _, _, a, _, _, h => by
    rw [show 16 * (n + 1) = 16 + 16 * n by omega,
      memRegion_split' (b := a) (b' := a + 16#64) (n := 16) (k := (16 * n : Nat)) rfl rfl
        (by change 16 + 16 * n ≤ 18446744073709551616; omega)]
    sep_frame_apply (sepWP_elim_vec128At (a := a)); intro v0
    sep_frame_apply (sepWP_elim_vecRange n (by omega) (a := a + 16#64)); intro f'
    let f : Nat → BitVec 128 := fun i => match i with | 0 => v0 | j + 1 => f' j
    have hf : VecRangeMem (n + 1) a f = Vec128At a v0 ∗ VecRangeMem n (a + 16#64) f' := rfl
    refine SepWP.weaken_pre ?_ (h f)
    rw [hf]; sep_frame

theorem sepWP_elim_spillSlice {n : Nat} (hn : n ≤ 40)
    {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Spill40, SepWP prog target s (SpillSliceMem n a t ∗ R0) post) :
    SepWP prog target s (memRegion a (16 * n) ∗ R0) post := by
  refine sepWP_elim_vecRange n hn fun f => ?_
  have heq : SpillSliceMem n a (Spill40.ofFn f) = VecRangeMem n a f :=
    vecRangeMem_congr fun i hi => spill40_ofFn_get f i (by omega)
  rw [← heq]
  exact h (Spill40.ofFn f)

theorem sepWP_elim_poly32 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ t : Vec32, SepWP prog target s (Poly32Mem a t ∗ R0) post) :
    SepWP prog target s (memRegion a 512 ∗ R0) post := by
  change SepWP prog target s (memRegion a (16 * 32) ∗ R0) post
  refine sepWP_elim_vecRange 32 (by decide) fun f => ?_
  change SepWP prog target s (PolyMem a f ∗ R0) post
  rw [← poly32Mem_ofFn a f]
  exact h (Vec32.ofFn f)

theorem spillSliceMem_entails_memRegion (n : Nat) (ptr : BitVec 64) (t : Spill40) :
    SpillSliceMem n ptr t ⊢ memRegion ptr (16 * n) :=
  vecRangeMem_entails_memRegion n ptr t.get

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
  · apply SepStore128.left; apply SepStore128.spillSlice (n := 21) (k := $k)
    · decide
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

/-! ## 2. Sub-Segments of `Seg1c` (`+0x0380 .. +0x05dc`) -/

private theorem seg1c_copy2_zero3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (sk2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0380#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ctA)
    (hx22 : s.readReg64 .x22 = skA + 384#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0440#64) s
      (memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 31472#64) 512 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk2)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = skA + 1152#64 ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧ sf.readReg64 .x20 = ctA ∧
        sf.readReg64 .x22 = skA + 384#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 3#5 = cst16_3_val ∧
        (Pf ⊢ ((sp + 136#64) ↦₆₄ ctA) ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
          Vec128At (sp + 2048#64) cst16_3_val ∗
          PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) ∗
          Poly32Mem (sp + 14432#64) Vec32.zero ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 136#64)); intro c136
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 2016#64)); intro c2016
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 sk2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp14432 : PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk2)) = ((sp + 14432#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp31472 : ((sp + 31472#64) ↦ₛ bs2) = PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp14432_32 : ((sp + 14432#64) ↦ₛ bs2) =
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk2))) := by
    rw [← hp14432, poly32Mem_ofFn]
  have ha1152 : skA + 384#64 + 768#64 = skA + 1152#64 := by clear * -; bv_omega
  rw [hp14432]
  wp_cut_codeLoaded
  wp_steps 9
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 31472#64, sp + 14432#64, bs2)
  rw [hp31472, hp14432_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have hreord0 : PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk2))) ∗
      (((sp + 2016#64) ↦₆₄ c2016) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ Rest) ⊢
      Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk2))) ∗
      ((sp + 2016#64) ↦₆₄ c2016) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) ∗ Rest := by sep_frame
  refine SepWP.weaken_pre hreord0 ?_
  wp_steps 2
  step_ldrQ_vec0
  wp_steps 3
  have hreord1 : Vec128At (sp + 2048#64) cst16_3_val ∗
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk2))) ∗
      ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) ∗ Rest ⊢
      Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (tHatPoly16 sk2))) ∗
      (((sp + 136#64) ↦₆₄ ctA) ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 sk2)) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hreord1 ?_
  step_zero32_poly0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp, by simp [*], by simp [*], by simp [*], by simp [*],
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
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hkr_f, hx20_f, hx22_f, hx25_f, hx26_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hfp_f, by simpa using hkr_f,
          by simpa using hx20_f, by simpa using hx22_f, by simpa using hx25_f,
          by simpa using hx26_f, hPf⟩
    · have hk15 : k = 15 := by
        have hbv : BitVec.ofNat 64 (32 * k) + 32#64 = 512#64 := by simpa [hx8] using hne
        have hlt1 : 32 * k < 18446744073709551616 := by omega
        have hlt2 : 32 * k + 32 < 18446744073709551616 := by omega
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
          by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
      rw [polyMem_congr hf32]; sep_frame))

private theorem seg1c_loop3 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x0440#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x19 = dst →
      s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x0488#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .fp = s.readReg64 .fp ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
          sf.readReg64 .x26 = s.readReg64 .x26 ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs hbs
    (b + 0x0440#64) (b + 0x0444#64) (b + 0x0454#64) (b + 0x0458#64) (b + 0x0480#64) Reg.x9

private theorem seg1c_copy3 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (sk3 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0488#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x04ac#64) s
      (PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk3)) ∗
        memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 31984#64) 512 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .x26 = sp + 28632#64 ∧
        (Pf ⊢ memRegion (sp + 14432#64) 2048 ∗
          PolyMem (sp + 31984#64) (polyVecNat (tHatPoly16 sk3)) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs3_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 sk3)) = bs3
  have hbs3 : bs3.length = 512 := by rw [← hbs3_def, vecRangeBytes_length]
  have hp14432 : PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 sk3)) = ((sp + 14432#64) ↦ₛ bs3) := by
    rw [← hbs3_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp31984 : ((sp + 31984#64) ↦ₛ bs3) = PolyMem (sp + 31984#64) (polyVecNat (tHatPoly16 sk3)) := by
    rw [← hbs3_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hreord_in :
      ((sp + 14432#64) ↦ₛ bs3) ∗ memRegion (sp + 14944#64) 1536 ∗
        memRegion (sp + 31984#64) 512 ∗ Rest ⊢
      memRegion (sp + 31984#64) 512 ∗ ((sp + 14432#64) ↦ₛ bs3) ∗
        (memRegion (sp + 14944#64) 1536 ∗ Rest) := by sep_frame
  rw [hp14432]
  refine SepWP.weaken_pre hreord_in ?_
  wp_cut_codeLoaded
  wp_steps 8
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 31984#64, sp + 14432#64, bs3)
  rw [hp31984]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have h512 : ((sp + 14432#64) ↦ₛ bs3) ∗ memRegion (sp + 14944#64) 1536 ⊢
      memRegion (sp + 14432#64) 2048 := by
    rw [memRegion_split' (b := sp + 14432#64) (b' := sp + 14944#64) (n := 512) (k := (1536 : Nat))
      rfl (by bv_omega) (by decide)]
    have hpb := pointsToBytes_entails_memRegion (sp + 14432#64) bs3
    rw [hbs3] at hpb
    exact sepConj_mono_left hpb
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp [*], by simp [*], by simp [*], ?_⟩
  exact entails_sub h512 (by sep_frame) (by sep_frame)

private theorem seg1c_zero_spill [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp ctA : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + 0x04ac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 14432#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x05dc#64) s
      (memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 2064#64) 336 ∗
        ((sp + 136#64) ↦₆₄ ctA) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = ctA ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x22 = 0#64 ∧
        sf.readReg64 .x23 = sp + 14448#64 ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .x26 = sp + 28632#64 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = 62209#64 ∧
        sf.readVReg128 8#5 = dup4hLow 3329#16 ∧
        sf.readVReg128 11#5 = dup8x16 3329#16 ∧
        (Pf ⊢ ((sp + 136#64) ↦₆₄ ctA) ∗
          SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 14432#64) 2048 ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  wp_cut_codeLoaded
  wp_steps 4
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk29_memset_06 blkPl06.base) (sp + 14432#64, 0#8, 2048)
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  have h2048 : ((sp + 14432#64) ↦ₛ List.replicate 2048 0#8) ⊢ memRegion (sp + 14432#64) 2048 := by
    have hpb := pointsToBytes_entails_memRegion (sp + 14432#64) (List.replicate 2048 0#8)
    rwa [List.length_replicate] at hpb
  have hreord_sp :
      ((sp + 14432#64) ↦ₛ List.replicate 2048 0#8) ∗
        (memRegion (sp + 2064#64) 336 ∗ ((sp + 136#64) ↦₆₄ ctA) ∗ Rest) ⊢
      memRegion (sp + 2064#64) (16 * 21) ∗
        (((sp + 136#64) ↦₆₄ ctA) ∗ memRegion (sp + 14432#64) 2048 ∗ Rest) :=
    entails_sub h2048 (by sep_frame) (by change _ ⊢ memRegion (sp + 2064#64) 336 ∗ _; sep_frame)
  refine SepWP.weaken_pre hreord_sp ?_
  sep_frame_apply (sepWP_elim_spillSlice (n := 21) (by decide) (a := sp + 2064#64)); intro t0
  wp_steps 12
  step_strQ_spill21 20
  wp_steps 4
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
  wp_steps 2; step_strQ_spill21 2
  wp_steps 1; step_strQ_spill21 1
  wp_steps 1; step_strQ_spill21 0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, hspA_sf, by simp [*], by simp, by simp [*], by simp,
      by simp [*], by simp, by simp [*], by simp [*],
      by simp, by simp, by simp, by simp, ?_⟩
  have hspill_eq :
      ∀ i, i < 21 →
        (((((((((((((((((((((t0.set 20 (dup8x16 64778#16)).set 18 (dup8x16 3329#16)).set 19
          (dup8x16 31498#16)).set 17 (dup8x16 65177#16)).set 16 (dup8x16 14745#16)).set 15
          (dup8x16 64019#16)).set 14 (dup8x16 787#16)).set 13 (dup8x16 1493#16)).set 12
          (dup8x16 13525#16)).set 11 (dup8x16 1422#16)).set 10 (dup8x16 53134#16)).set 9
          (dup8x16 287#16)).set 8 (dup8x16 28191#16)).set 7 (dup8x16 48842#16)).set 6
          (dup8x16 44629#16)).set 5 (dup8x16 622#16)).set 4 (dup8x16 27758#16)).set 3
          (dup8x16 1577#16)).set 2 (dup8x16 61737#16)).set 1 (dup8x16 49846#16)).set 0
          (dup8x16 962#16)).get i = uHatZetaSpill40.get i := by
    intro i hi
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10
    | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 => rfl
    | _ + 21 => omega
  have hsm := vecRangeMem_congr (n := 21) (ptr := sp + 2064#64) hspill_eq
  change SpillSliceMem 21 (sp + 2064#64) _ = SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 at hsm
  rw [hsm]
  sep_frame

/-- Composed Segment 1c contract (`+0x0380 → +0x05dc`). -/
theorem seg1c_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp skA ctA : BitVec 64) (sk : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0380#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx20 : s.readReg64 .x20 = ctA)
    (hx22 : s.readReg64 .x22 = skA + 384#64)
    (hx25 : s.readReg64 .x25 = sp + 28368#64)
    (hx26 : s.readReg64 .x26 = sp + 28632#64)
    (hsk : sk.length = 3168) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x05dc#64) s
      (memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 336 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        memRegion (sp + 14944#64) 1536 ∗
        memRegion (sp + 31472#64) 512 ∗ memRegion (sp + 31984#64) 512 ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = s.readReg64 .fp ∧
        sf.readReg64 .x0 = ctA ∧
        sf.readReg64 .x19 = sp + 14432#64 ∧
        sf.readReg64 .x22 = 0#64 ∧
        sf.readReg64 .x23 = sp + 14448#64 ∧
        sf.readReg64 .x24 = 16#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧
        sf.readReg64 .x26 = sp + 28632#64 ∧
        sf.readReg64 .x27 = sp + 4160#64 ∧
        sf.readReg64 .x28 = 62209#64 ∧
        sf.readVReg128 8#5 = dup4hLow 3329#16 ∧
        sf.readVReg128 11#5 = dup8x16 3329#16 ∧
        (Pf ⊢ ((sp + 136#64) ↦₆₄ ctA) ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
          Vec128At (sp + 2048#64) cst16_3_val ∗
          SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
          memRegion (sp + 14432#64) 2048 ∗
          PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
          PolyMem (sp + 31984#64) (polyVecNat (tHatPoly16 ((sk.drop 1152).take 384))) ∗
          ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest)) := by
  have hl3 : ((sk.drop 1152).take 384).length = 384 := by simp [hsk]
  have hP0 :
      memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 336 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        memRegion (sp + 14944#64) 1536 ∗
        memRegion (sp + 31472#64) 512 ∗ memRegion (sp + 31984#64) 512 ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest ⊢
      memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 31472#64) 512 ∗
        PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        (memRegion (sp + 2064#64) 336 ∗ memRegion (sp + 14944#64) 1536 ∗
          memRegion (sp + 31984#64) 512 ∗ ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest) := by
    sep_frame
  refine SepWP.weaken_pre hP0
    (sepWP_seq_env hcl hro
      (seg1c_copy2_zero3 hb hbase s sp skA ctA ((sk.drop 768).take 384) _
        hpc hrun hsp hspA hx20 hx22 hcl) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp_1, hx8_1, hx9_1, hx19_1, _hx20_1, _hx22_1, hx25_1, hx26_1, hv0_1, hv3_1, hP1⟩
  have hP1' : P1 ⊢ ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      PolyMem (sp + 14432#64) (fun _ => 0#128) ∗
      (((sp + 136#64) ↦₆₄ ctA) ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 336 ∗
        memRegion (sp + 14944#64) 1536 ∗
        PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        memRegion (sp + 31984#64) 512 ∗ Rest) := by
    refine Entails.trans hP1 ?_
    rw [poly32Mem_zero_eq]; sep_frame
  refine SepWP.weaken_pre hP1'
    (sepWP_seq_env hcl1 hro1
      (seg1c_loop3 hb (skA + 1152#64) (sp + 14432#64) ((sk.drop 1152).take 384) _ hl3 15 0 rfl s1
        (fun _ => 0#128) hpc1 hrun1 hspA1
        (by simp [hx9_1]) (by simp [hx8_1]) hx19_1 hv0_1 hv3_1 (by omega)) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp_2, _hx19_2, _hx20_2, _hx22_2, hx25_2, hx26_2, hP2⟩
  have hP2' : P2 ⊢ PolyMem (sp + 14432#64) (polyVecNat (tHatPoly16 ((sk.drop 1152).take 384))) ∗
      memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 31984#64) 512 ∗
      (((sp + 136#64) ↦₆₄ ctA) ∗ ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗
        Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 336 ∗
        PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest) :=
    Entails.trans hP2 (by sep_frame)
  refine SepWP.weaken_pre hP2'
    (sepWP_seq_env hcl2 hro2
      (seg1c_copy3 hb hbase s2 sp ((sk.drop 1152).take 384) _
        hpc2 hrun2 (hsp2.trans hsp1) hspA2
        (by rw [hx25_2, hx25_1, hx25]) (by rw [hx26_2, hx26_1, hx26]) hcl2) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hsp3, hspA3, hfp_3, hx19_3, hx25_3, hx26_3, hP3⟩
  have hP3' : P3 ⊢ memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 2064#64) 336 ∗
      ((sp + 136#64) ↦₆₄ ctA) ∗
      (((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ Vec128At (sp + 2048#64) cst16_3_val ∗
        PolyMem (sp + 31472#64) (polyVecNat (tHatPoly16 ((sk.drop 768).take 384))) ∗
        PolyMem (sp + 31984#64) (polyVecNat (tHatPoly16 ((sk.drop 1152).take 384))) ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ Rest) :=
    Entails.trans hP3 (by sep_frame)
  refine SepWP.weaken_pre hP3'
    (SepWP.mono
      (seg1c_zero_spill hb hbase s3 sp ctA _
        hpc3 hrun3 hsp3 hspA3 hx19_3 hx25_3 hx26_3 hcl3) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hfp_f, hx0_f, hx19_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, hPf⟩
  exact ⟨hsp_f, hspA_f, by rw [hfp_f, hfp_3, hfp_2, hfp_1],
    hx0_f, hx19_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hv8_f, hv11_f, Entails.trans hPf (by sep_frame)⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c
