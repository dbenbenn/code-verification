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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd

/-!
# `encapsulate2` (`B20`) — Segment 2a (`+0x04b8 .. +0x0710`)

Steps the three 16-iteration AdvSIMD `deserialize_12` loops (`ek0`, `ek1`, `ek2`),
the three `B28` (`memcpy`) copies writing `tHat[0..2]` to `[sp + 3952 .. sp + 5488)`,
and the intervening 32-vector scratch clears of `[sp + 5488 .. sp + 6000)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (bytesToPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_simdLd1Single32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  SavedFrame20 UnspilledSaved20 blk20_code_eq blk20_tree_size blkLib20 blkPC20 blkPl20
  blkPlaceable20 blkTree20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepStore128 Spill13 Spill13Mem Vec32 VecRangeMem
  poly32Mem_ofFn polyVecNat spill13Mem_entails_memRegion spill13Mem_ofFn step_stpQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1 (
  Seg1Post Seg1Spatial)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_chk spAligned_of_sp_eq trans_unspilled)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Pure (
  ek_pointsTo_split loadVec12 rawDeser12 rawDeser12_loadVec12_eq tHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2Simd (
  exec_simdTbl_16b_1 exec_simdUshl_8h)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x04b8 → 0x070c]
end

private theorem blk28_memcpy_20 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC20.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC20.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC20

@[simp, arm64_norm, wp_norm]
private theorem blkPl20_ρ [MlKemPlacement] (sym : String) :
    blkPl20.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := by simp [execInstWithSvc]

attribute [local wp_norm ↓ high] exec_simdTbl_16b_1 exec_simdUshl_8h exec_simdMovi_2d_0

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

private theorem memRegion_2560_seg2a_split (sp : BitVec 64) :
    memRegion (sp + 2416#64) 2560 =
      memRegion (sp + 2416#64) 1536 ∗ memRegion (sp + 3952#64) 512 ∗ memRegion (sp + 4464#64) 512 := by
  rw [memRegion_split' (b' := sp + 3952#64) (n := 1536) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
      memRegion_split' (b' := sp + 4464#64) (n := 512) (k := 512) rfl (by bv_omega) (by decide)]

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g := vecRangeMem_congr h

/-! ## 1. Shared `deserialize_12` Loop Macro & Zero-Clear Macro -/

local macro "prove_deser12_loop " src:ident dst:ident bs:ident _Rest:ident hbs:ident
    pc0:term:arg pc1:term:arg pc2:term:arg pc3:term:arg pc4:term:arg srcReg:term:arg : tactic => `(tactic| (
  intro rem; induction rem using Nat.strongRecOn with | ind rem ih =>
    intro k hkrem s f hpc hrun hspA hx_src hx8 hx_dst hv_sh hv3 hus hf
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
    have hv0_eq : rawDeser12 (loadVec12 $bs (24 * k)) = polyVecNat (tHatPoly16 $bs) (2 * k) := by
      simpa [show 12 * (2 * k) = 24 * k by omega] using rawDeser12_loadVec12_eq $hbs (2 * k) (by omega)
    have hv2_eq : rawDeser12 (loadVec12 $bs (24 * k + 12)) = polyVecNat (tHatPoly16 $bs) (2 * k + 1) := by
      simpa [show 12 * (2 * k + 1) = 24 * k + 12 by omega] using
        rawDeser12_loadVec12_eq $hbs (2 * k + 1) (by omega)
    refine step_stpQ128 (pc := $pc4) (wb := none) (ea := $dst + BitVec.ofNat 64 (32 * k))
      (ea16 := $dst + BitVec.ofNat 64 (32 * k) + 16#64)
      (v1 := polyVecNat (tHatPoly16 $bs) (2 * k)) (v2 := polyVecNat (tHatPoly16 $bs) (2 * k + 1))
      (by simp [wp_norm, arm64_norm]) (by simp [hrun]) (by wp_norm_lhs) rfl
      (by simp [evalAddrMode, hx_dst, hx8]) rfl
      (by simp [hv_sh, hv3, ← hv0_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
      (by simp [hv_sh, hv3, ← hv2_eq, rawDeser12, loadVec12, simdLdSt1SingleLaneIdx, Nat.add_assoc])
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
            (by simp [hx_dst]) (by simp [hv_sh]) (by simp [hv3])
            ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩
            (update2_prefix hf)) ?_
        rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx19_f, hx20_f, hx21_f, hx22_f, hv3_f, hus_f, hPf⟩
        exact ⟨by simpa using hsp_f, hspA_f, by simpa using hx19_f, by simpa using hx20_f,
          by simpa using hx21_f, by simpa using hx22_f, hv3_f, hus_f, hPf⟩
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
          by simp, by simp, by simp, by simp, by simp [hv3],
          ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, ?_⟩
      rw [polyMem_congr hf32]
      exact Entails.refl _))

local macro "step_zero32_q1" : tactic => `(tactic| (
  step_strQ 1 31; step_strQ 1 30; step_strQ 1 29; step_strQ 1 28;
  step_strQ 1 27; step_strQ 1 26; step_strQ 1 25; step_strQ 1 24;
  step_strQ 1 23; step_strQ 1 22; step_strQ 1 21; step_strQ 1 20;
  step_strQ 1 19; step_strQ 1 18; step_strQ 1 17; step_strQ 1 16;
  step_strQ 1 15; step_strQ 1 14; step_strQ 1 13; step_strQ 1 12;
  step_strQ 1 11; step_strQ 1 10; step_strQ 1 9; step_strQ 1 8;
  step_strQ 1 7; step_strQ 1 6; step_strQ 1 5; step_strQ 1 4;
  step_strQ 1 3; step_strQ 1 2; step_strQ 1 1; step_strQ 1 0))

/-! ## 2. Loop 0 (`+0x04b8 → +0x0500`) & Copy 0 + Zero 1 (`+0x0500 → +0x05b0`) -/

private theorem seg2a_loop0 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x04b8#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x1 = src + BitVec.ofNat 64 (24 * k) → s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x9 = dst → s.readVReg128 1#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 → UnspilledSaved20 s0 s →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0500#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧ UnspilledSaved20 s0 sf ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs Rest hbs
    (b + 0x04b8#64) (b + 0x04bc#64) (b + 0x04cc#64) (b + 0x04d0#64) (b + 0x04f8#64) Reg.x1

private theorem seg2a_copy0_zero1 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s0 s : State) (sp : BitVec 64) (sp13 : Spill13) (ek0 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x0500#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hv3 : s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128)
    (hus : UnspilledSaved20 s0 s)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x05b0#64) s
      (Spill13Mem sp sp13 ∗ memRegion (sp + 3952#64) 512 ∗
        PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek0)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = sp + 5488#64 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = 0#128 ∧
        sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        UnspilledSaved20 s0 sf ∧
        (Pf ⊢ Spill13Mem sp (sp13.set 12 0x0b0a0a09080707060504040302010100#128) ∗
          PolyMem (sp + 3952#64) (polyVecNat (tHatPoly16 ek0)) ∗
          Poly32Mem (sp + 5488#64) Vec32.zero ∗ Rest)) := by
  subst _hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs0_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 ek0)) = bs0
  have hbs0 : bs0.length = 512 := by rw [← hbs0_def, vecRangeBytes_length]
  have hp5488 : PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek0)) = ((sp + 5488#64) ↦ₛ bs0) := by
    rw [← hbs0_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp3952 : ((sp + 3952#64) ↦ₛ bs0) = PolyMem (sp + 3952#64) (polyVecNat (tHatPoly16 ek0)) := by
    rw [← hbs0_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp5488_32 : ((sp + 5488#64) ↦ₛ bs0) =
      Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ek0))) := by
    rw [← hp5488, poly32Mem_ofFn]
  have ha5488 : sp + 4096#64 + 1392#64 = sp + 5488#64 := by clear * -; bv_omega
  rw [hp5488]
  wp_cut_codeLoaded
  wp_steps 5
  step_strQ 0 12
  wp_steps 2
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_20 blkPl20.base) (sp + 3952#64, sp + 5488#64, bs0)
  rw [hp3952, hp5488_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  wp_steps 2
  step_ldrQ 2 12
  wp_step
  step_zero32_q1
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp_sf], by simp [State.spAligned, hsp_sf, hsp_chk],
      by simp, by simp [*], by simp [*], by simp [*], by simp [*],
      by simp [*],
      by simp, by simp, by simp [Spill13.set, Spill13.get],
      ⟨by simp [*, hus.1], by simp [*, hus.2.1], by simp [*, hus.2.2.1], by simp [*, hus.2.2.2]⟩,
      ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

/-! ## 3. Loop 1 (`+0x05b0 → +0x05f8`), Copy 1 + Zero 2 (`+0x05f8 → +0x06a8`), Loop 2 & Copy 2 -/

private theorem seg2a_loop1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x05b0#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x22 = src + BitVec.ofNat 64 (24 * k) → s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x23 = dst → s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 → UnspilledSaved20 s0 s →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x05f8#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧ UnspilledSaved20 s0 sf ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs Rest hbs
    (b + 0x05b0#64) (b + 0x05b4#64) (b + 0x05c4#64) (b + 0x05c8#64) (b + 0x05f0#64) Reg.x22

private theorem seg2a_copy1_zero2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s0 s : State) (sp ekA : BitVec 64) (sp13 : Spill13) (ek1 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x05f8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ekA + 384#64) (hx21 : s.readReg64 .x21 = sp + 3952#64)
    (hus : UnspilledSaved20 s0 s) (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem)
    (hsp13 : sp13.s12 = 0x0b0a0a09080707060504040302010100#128) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x06a8#64) s
      (Spill13Mem sp sp13 ∗ memRegion (sp + 4464#64) 512 ∗
        PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek1)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x8 = 0#64 ∧
        sf.readReg64 .x9 = ekA + 768#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = sp + 5488#64 ∧
        sf.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 ∧
        sf.readVReg128 1#5 = 0#128 ∧
        sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧
        UnspilledSaved20 s0 sf ∧
        (Pf ⊢ Spill13Mem sp sp13 ∗
          PolyMem (sp + 4464#64) (polyVecNat (tHatPoly16 ek1)) ∗
          Poly32Mem (sp + 5488#64) Vec32.zero ∗ Rest)) := by
  subst _hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs1_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 ek1)) = bs1
  have hbs1 : bs1.length = 512 := by rw [← hbs1_def, vecRangeBytes_length]
  have hp5488 : PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek1)) = ((sp + 5488#64) ↦ₛ bs1) := by
    rw [← hbs1_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp4464 : ((sp + 4464#64) ↦ₛ bs1) = PolyMem (sp + 4464#64) (polyVecNat (tHatPoly16 ek1)) := by
    rw [← hbs1_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp5488_32 : ((sp + 5488#64) ↦ₛ bs1) =
      Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ek1))) := by
    rw [← hp5488, poly32Mem_ofFn]
  have ha4464 : sp + 3952#64 + 512#64 = sp + 4464#64 := by clear * -; bv_omega
  have ha5488 : sp + 4096#64 + 1392#64 = sp + 5488#64 := by clear * -; bv_omega
  have ha768 : ekA + 384#64 + 384#64 = ekA + 768#64 := by clear * -; bv_omega
  rw [hp5488]
  wp_cut_codeLoaded
  wp_steps 6
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_20 blkPl20.base) (sp + 4464#64, sp + 5488#64, bs1)
  rw [hp4464, hp5488_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  have hspA_sf : sf.spAligned = true := spAligned_of_chk hsp_sf hsp_chk
  wp_steps 2
  step_ldrQ 2 12
  wp_steps 2
  step_zero32_q1
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp_sf], by simp [State.spAligned, hsp_sf, hsp_chk],
      by simp, by simp [*], by simp [*], by simp [*],
      by simp, by simp, by simp [Spill13.get, hsp13],
      ⟨by simp [*, hus.1], by simp [*, hus.2.1], by simp [*, hus.2.2.1], by simp [*, hus.2.2.2]⟩,
      ?_⟩
  simp only [Vec32.set, Vec32.zero, Vec32.ofFn]
  sep_frame

private theorem seg2a_loop2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl20 b)
    (s0 : State) (src dst : BitVec 64) (bs : List (BitVec 8)) (Rest : SepProp) (hbs : bs.length = 384) :
    ∀ (rem k : Nat), k + 1 + rem = 16 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x06a8#64 → s.status = .Running → s.spAligned = true →
      s.readReg64 .x9 = src + BitVec.ofNat 64 (24 * k) → s.readReg64 .x8 = BitVec.ofNat 64 (32 * k) →
      s.readReg64 .x21 = dst → s.readVReg128 0#5 = 0xfffc0000fffc0000fffc0000fffc0000#128 →
      s.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 → UnspilledSaved20 s0 s →
      (∀ j, j < 2 * k → f j = polyVecNat (tHatPoly16 bs) j) →
      SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x06f0#64) s ((src ↦ₛ bs) ∗ PolyMem dst f ∗ Rest)
        (fun sf Pf => sf.sp = s.sp ∧ sf.spAligned = true ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
          sf.readVReg128 3#5 = 0x0b0a0a09080707060504040302010100#128 ∧ UnspilledSaved20 s0 sf ∧
          (Pf ⊢ (src ↦ₛ bs) ∗ PolyMem dst (polyVecNat (tHatPoly16 bs)) ∗ Rest)) := by
  prove_deser12_loop src dst bs Rest hbs
    (b + 0x06a8#64) (b + 0x06ac#64) (b + 0x06bc#64) (b + 0x06c0#64) (b + 0x06e8#64) Reg.x9

private theorem seg2a_copy2 [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (_hbase : blkPl20.base = b)
    (s0 s : State) (sp : BitVec 64) (ek2 : List (BitVec 8)) (Rest : SepProp)
    (hpc : s.pc = b + 0x06f0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hus : UnspilledSaved20 s0 s) (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0710#64) s
      (memRegion (sp + 4976#64) 512 ∗ PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek2)) ∗ Rest)
      (fun sf Pf => sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = sp + 3952#64 ∧
        sf.readReg64 .x21 = sp + 5488#64 ∧ UnspilledSaved20 s0 sf ∧
        (Pf ⊢ PolyMem (sp + 4976#64) (polyVecNat (tHatPoly16 ek2)) ∗
          Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ek2))) ∗ Rest)) := by
  subst _hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs2_def : vecRangeBytes 32 (polyVecNat (tHatPoly16 ek2)) = bs2
  have hbs2 : bs2.length = 512 := by rw [← hbs2_def, vecRangeBytes_length]
  have hp5488 : PolyMem (sp + 5488#64) (polyVecNat (tHatPoly16 ek2)) = ((sp + 5488#64) ↦ₛ bs2) := by
    rw [← hbs2_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp4976 : ((sp + 4976#64) ↦ₛ bs2) = PolyMem (sp + 4976#64) (polyVecNat (tHatPoly16 ek2)) := by
    rw [← hbs2_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  have hp5488_32 : ((sp + 5488#64) ↦ₛ bs2) =
      Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ek2))) := by
    rw [← hp5488, poly32Mem_ofFn]
  have ha4976 : sp + 3952#64 + 1024#64 = sp + 4976#64 := by clear * -; bv_omega
  have ha5488 : sp + 4096#64 + 1392#64 = sp + 5488#64 := by clear * -; bv_omega
  rw [hp5488]
  wp_cut_codeLoaded
  wp_steps 7
  apply SepWP.done (by wp_norm_lhs) (by assumption)
  intro _hcl2
  wp_call (blk28_memcpy_20 blkPl20.base) (sp + 4976#64, sp + 5488#64, bs2)
  rw [hp4976, hp5488_32]
  have hsp_sf : sf.sp = sp := by simp [*]
  refine SepWP.done (by simp [*]) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk,
      by simp [*], by simp [*], by simp [*],
      ⟨by simp [*, hus.1], by simp [*, hus.2.1], by simp [*, hus.2.2.1], by simp [*, hus.2.2.2]⟩,
      Entails.refl _⟩

/-! ## 4. Exported Segment 2a Contract (`+0x04b8 → +0x0710`) -/

@[expose] def Seg2aPost (s0 s2 : State) (ret : BitVec 64) : Prop :=
  let sp := s0.sp - 6128#64
  s2.sp = sp ∧ s2.spAligned = true ∧
  s2.readReg64 .x19 = ret ∧ s2.readReg64 .x20 = sp + 3952#64 ∧
  s2.readReg64 .x21 = sp + 5488#64 ∧ UnspilledSaved20 s0 s2

@[expose] def Seg2aSpatial (s0 : State) (esA : BitVec 64) (es : List (BitVec 8))
    (ekA : BitVec 64) (ek : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 6128#64
  (esA ↦ₛ es) ∗ (ekA ↦ₛ ek) ∗ SavedFrame20 s0.sp s0 ∗ memRegion sp 208 ∗
  PolyMem (sp + 208#64) (polyVecNat (bytesToPoly16 (es.take 512))) ∗
  PolyMem (sp + 720#64) (polyVecNat (bytesToPoly16 ((es.drop 512).take 512))) ∗
  PolyMem (sp + 1232#64) (polyVecNat (bytesToPoly16 ((es.drop 1024).take 512))) ∗
  PolyMem (sp + 1744#64) (polyVecNat (bytesToPoly16 ((es.drop 1536).take 512))) ∗
  ((sp + 2256#64) ↦ₛ ((es.drop 2048).take 32)) ∗
  memRegion (sp + 2288#64) 128 ∗ memRegion (sp + 2416#64) 1536 ∗
  PolyMem (sp + 3952#64) (polyVecNat (tHatPoly16 (ek.take 384))) ∗
  PolyMem (sp + 4464#64) (polyVecNat (tHatPoly16 ((ek.drop 384).take 384))) ∗
  PolyMem (sp + 4976#64) (polyVecNat (tHatPoly16 ((ek.drop 768).take 384))) ∗
  Poly32Mem (sp + 5488#64) (Vec32.ofFn (polyVecNat (tHatPoly16 ((ek.drop 768).take 384)))) ∗ F

theorem seg2a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s1 : State) (ret esA ekA : BitVec 64) (es ek : List (BitVec 8)) (F : SepProp)
    (hpc : s1.pc = b + 0x04b8#64) (hrun : s1.status = .Running)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s1.mem) (hro : MlKemRoOk mlkemMpl s1.mem)
    (hek : ek.length = 1152) (hpost1 : Seg1Post s0 s1 ret ekA) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x0710#64) s1
      ((ekA ↦ₛ ek) ∗ Seg1Spatial s0 esA es F)
      (fun s2 P2 => Seg2aPost s0 s2 ret ∧ (P2 ⊢ Seg2aSpatial s0 esA es ekA ek F)) := by
  rcases hpost1 with ⟨hsp1, hspA1, hx1_1, hx8_1, hx9_1, hx19_1, hx20_1, hx21_1, hx22_1,
    _, hv1_1, hv3_1, hus1⟩
  let sp := s0.sp - 6128#64
  dsimp only [Seg1Spatial]
  rw [ek_pointsTo_split ekA hek, memRegion_2560_seg2a_split sp]
  refine VecMem.SepWP.of_memRegion_vecRangeMem 13 sp (by decide) (by sep_focus) fun f0 => ?_
  rw [show VecRangeMem 13 sp f0 = Spill13Mem sp (Spill13.ofFn f0) from (spill13Mem_ofFn sp f0).symm]
  have hek0 : (ek.take 384).length = 384 := by simp [hek]
  have hek1 : ((ek.drop 384).take 384).length = 384 := by simp [hek]
  have hek2 : ((ek.drop 768).take 384).length = 384 := by simp [hek]
  have stepf : ∀ {prog : Program} {pc1 pc2 : BitVec 64} {s : State} {P P1 : SepProp}
      {Q1 Q2 : State → SepProp → Prop},
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      SepWP prog pc1 s P1 Q1 → (P ⊢ P1) →
      (∀ s' P', s'.pc = pc1 → s'.status = .Running →
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem → MlKemRoOk mlkemMpl s'.mem →
        Q1 s' P' → SepWP prog pc2 s' P' Q2) →
      SepWP prog pc2 s P Q2 :=
    fun hcl' hro' h1 hP' h2 => SepWP.weaken_pre hP' (sepWP_seq_env hcl' hro' h1 h2)
  have hp32_zero : ∀ addr, Poly32Mem addr Vec32.zero = PolyMem addr Vec32.zero.get :=
    fun _ => rfl
  refine stepf hcl hro
    (seg2a_loop0 hb s0 ekA (sp + 5488#64) (ek.take 384) _ hek0 15 0 rfl s1 Vec32.zero.get
      hpc hrun hspA1 (by simpa using hx1_1) hx8_1 hx9_1 hv1_1 hv3_1 hus1 (by omega))
    (by simp only [hp32_zero]; sep_frame) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx19_2, hx20_2, hx21_2, hx22_2, hv3_2, hus2, hP2⟩
  refine stepf hcl2 hro2
    (seg2a_copy0_zero1 hb hbase s0 s2 sp (Spill13.ofFn f0) (ek.take 384) _
      hpc2 hrun2 (by simpa [hsp1] using hsp2) hspA2 hv3_2 hus2 hcl2)
    (Entails.trans hP2 (by sep_frame)) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hv0_3, _, hv3_3, hus3, hP3⟩
  refine stepf hcl3 hro3
    (seg2a_loop1 hb s0 (ekA + 384#64) (sp + 5488#64) ((ek.drop 384).take 384) _ hek1 15 0 rfl
      s3 Vec32.zero.get hpc3 hrun3 hspA3 (by simpa [hx22_1, hx22_2] using hx22_3)
      hx8_3 hx23_3 hv0_3 hv3_3 hus3 (by omega))
    (Entails.trans hP3 (by simp only [hp32_zero]; sep_frame)) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hx19_4, hx20_4, hx21_4, _, _, hus4, hP4⟩
  refine stepf hcl4 hro4
    (seg2a_copy1_zero2 hb hbase s0 s4 sp ekA
      ((Spill13.ofFn f0).set 12 0x0b0a0a09080707060504040302010100#128)
      ((ek.drop 384).take 384) _ hpc4 hrun4 (by simpa [hsp3] using hsp4) hspA4
      (by simpa [hx20_1, hx20_2, hx20_3] using hx20_4)
      (by simpa [hx21_1, hx21_2, hx21_3] using hx21_4) hus4 hcl4 rfl)
    (Entails.trans hP4 (by sep_frame)) ?_
  rintro s5 P5 hpc5 hrun5 hcl5 hro5
    ⟨hsp5, hspA5, hx8_5, hx9_5, hx19_5, hx21_5, hv0_5, _, hv3_5, hus5, hP5⟩
  refine stepf hcl5 hro5
    (seg2a_loop2 hb s0 (ekA + 768#64) (sp + 5488#64) ((ek.drop 768).take 384) _ hek2 15 0 rfl
      s5 Vec32.zero.get hpc5 hrun5 hspA5 (by simpa using hx9_5) hx8_5 hx21_5 hv0_5 hv3_5
      hus5 (by omega))
    (Entails.trans hP5 (by simp only [hp32_zero]; sep_frame)) ?_
  rintro s6 P6 hpc6 hrun6 hcl6 _ ⟨hsp6, hspA6, hx19_6, _, _, _, _, hus6, hP6⟩
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.trans hP6 (by sep_frame))
      (seg2a_copy2 hb hbase s0 s6 sp ((ek.drop 768).take 384) _
        hpc6 hrun6 (by simpa [hsp5] using hsp6) hspA6 hus6 hcl6)) ?_
  rintro s7 P7 _ _ ⟨hsp7, hspA7, hx19_7, hx20_7, hx21_7, hus7, hP7⟩
  refine ⟨⟨hsp7, hspA7, by simpa [hx19_1, hx19_2, hx19_3, hx19_4, hx19_5, hx19_6] using hx19_7,
    hx20_7, hx21_7, hus7⟩, Entails.trans hP7 ?_⟩
  dsimp only [Seg2aSpatial]
  rw [ek_pointsTo_split ekA hek]
  exact entails_sub (spill13Mem_entails_memRegion sp _) (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg2a
