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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd

/-!
# `encapsulate2` (`B20`) — Segment 5a (`+0x28e8 .. +0x29a8`)

Steps the `B28` (`memcpy`) copy of `inv` from `[sp + 2928 .. sp + 3440)` to
`[sp + 3440 .. sp + 3952)`, the post-`memcpy` SIMD constant loads from `Spill13Mem sp`,
and the 16-iteration post-`inv_ntt` normalizer + `err2` + `msgPoly` + Barrett reduction loop
producing `seg5FinalPoly inv err2 msgPoly` in `[sp + 3440 .. sp + 3952)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5a

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemCall_of_blockOk mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  UnspilledSaved20 blk20_code_eq blk20_tree_size blkLib20 blkPC20 blkPl20
  blkPlaceable20 blkTree20 sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 Spill13 Spill13Mem polyVecNat step_ldpQ128
  step_ldrQ128 step_stpQ128 vecRangeBytes vecRangeBytes_length vecRangeMem_congr
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  exec_simdAdd_8h exec_simdDup_8h_gpr exec_simdMla_8h exec_simdMovi_8h_1024
  exec_simdMul_8h exec_simdMvni_8h_f2ff exec_simdSqdmulh_8h exec_simdSshr_8h_1
  exec_simdSshr_8h_11 exec_simdSub_8h sqdmulh8hFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg4 (Seg4Post)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  seg5FinalPoly seg5Loop1_vec_eq)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC20 blkLib20 blkTree20 blk20_code_eq blk20_tree_size
  via_placement blkPl20 blkPlaceable20 [0x28e8 → 0x29a4]
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
private theorem exec_simdAdd_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdAdd8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdAdd_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSub_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true true 0b01#2 rm 0b10000#5 rn rd) s =
      (s.writeVReg128 rd (simdSub8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSub_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMul_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10011#5 rn rd) s =
      (s.writeVReg128 rd (simdMul8h (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMul_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMla_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10010#5 rn rd) s =
      (s.writeVReg128 rd
        (simdMla8h (s.readVReg128 rd) (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdMla_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSqdmulh_8h' {svc : State → State} (rm rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdThreeSame true false 0b01#2 rm 0b10110#5 rn rd) s =
      ((s.writeVReg128 rd (simdSqdmulh8h (s.readVReg128 rn) (s.readVReg128 rm))).orFpsr
        (sqdmulh8hFlags (s.readVReg128 rn) (s.readVReg128 rm))).advancePC :=
  exec_simdSqdmulh_8h rm rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_1' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0011#4 0b111#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 1)).advancePC :=
  exec_simdSshr_8h_1 rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdSshr_8h_11' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0b0010#4 0b101#3 0b00000#5 rn rd) s =
      (s.writeVReg128 rd (simdSshr8h (s.readVReg128 rn) 11)).advancePC :=
  exec_simdSshr_8h_11 rn rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMovi_8h_1024' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true false 0#4 0#3 0b10100#5 4#5 rd) s =
      (s.writeVReg128 rd (dup8x16 1024#16)).advancePC := exec_simdMovi_8h_1024 rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdMvni_8h_f2ff' {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b10100#5 13#5 rd) s =
      (s.writeVReg128 rd (dup8x16 0xf2ff#16)).advancePC := exec_simdMvni_8h_f2ff rd s
@[simp, arm64_norm, wp_norm]
private theorem exec_simdDup_8h_gpr' {svc : State → State} (rn rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdInsDup true false 0b00010#5 0b0001#4 rn rd) s =
      (s.writeVReg128 rd (dup8x16 ((s.readReg64 (Reg.fromZRBits rn)).truncate 16))).advancePC :=
  exec_simdDup_8h_gpr rn rd s

attribute [local wp_norm ↓ high]
  exec_simdAdd_8h' exec_simdSub_8h' exec_simdMul_8h' exec_simdMla_8h'
  exec_simdSqdmulh_8h' exec_simdSshr_8h_1' exec_simdSshr_8h_11'
  exec_simdMovi_8h_1024' exec_simdMvni_8h_f2ff' exec_simdDup_8h_gpr'

/-! ## 1. `memcpy` (`+0x28e8`) & Loop-1 Register/Vector Setup (`+0x28ec → +0x291c`) -/

private theorem seg5a_memcpy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s4 : State) (sp ret : BitVec 64) (spill : Spill13) (inv : Poly16) (Rest : SepProp)
    (hpc : s4.pc = b + 0x28e8#64) (hrun : s4.status = .Running)
    (hpost4 : Seg4Post s0 s4 sp ret)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s4.mem) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x28ec#64) s4
      (Spill13Mem sp spill ∗ memRegion (sp + 3440#64) 512 ∗
        PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x19 = ret ∧ sf.readReg64 .x20 = sp + 3440#64 ∧
        UnspilledSaved20 s0 sf ∧
        Pf = (Spill13Mem sp spill ∗ PolyMem (sp + 3440#64) (polyVecNat inv) ∗
          PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Rest)) := by
  subst hbase
  rcases hpost4 with ⟨hsp, hspA, hx19, hus, hx0, hx1, hx2, hx20⟩
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp2928 : PolyMem (sp + 2928#64) (polyVecNat inv) = ((sp + 2928#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp3440 : ((sp + 3440#64) ↦ₛ bsInv) = PolyMem (sp + 3440#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp2928]
  wp_call (blk28_memcpy_20 blkPl20.base) (sp + 3440#64, sp + 2928#64, bsInv)
  rw [← hp2928, hp3440]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*],
      ⟨by simp [*, hus.1], by simp [*, hus.2.1], by simp [*, hus.2.2.1], by simp [*, hus.2.2.2]⟩,
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg5a_setup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (spill : Spill13) (Rest : SepProp)
    (hpc : s.pc = b + 0x28ec#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = ret) (hx20 : s.readReg64 .x20 = sp + 3440#64)
    (hus : UnspilledSaved20 s0 s)
    (hs6 : spill.s6 = dup8x16 20159#16) (hs11 : spill.s11 = dup8x16 3329#16) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x291c#64) s
      (Spill13Mem sp spill ∗ Rest)
      (fun s5 P5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧ s5.readReg64 .x19 = ret ∧
        s5.readReg64 .x8 = sp + 3456#64 ∧ s5.readReg64 .x9 = sp + 2432#64 ∧
        s5.readReg64 .x10 = sp + 1760#64 ∧ s5.readReg64 .x11 = 16#64 ∧
        s5.readReg64 .x12 = 1441#64 ∧ s5.readReg64 .x13 = 55457#64 ∧
        s5.readVReg128 16#5 = dup8x16 3329#16 ∧ s5.readVReg128 17#5 = dup8x16 20159#16 ∧
        s5.readVReg128 18#5 = dup8x16 1024#16 ∧ s5.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        UnspilledSaved20 s0 s5 ∧ P5 = (Spill13Mem sp spill ∗ Rest)) := by
  wp_steps 2
  refine step_ldrQ128 (pc := b + 0x28f4#64) (wb := none) (ea := sp + 96#64)
    (v := dup8x16 20159#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill13 (ptr := sp) (ea := sp + 96#64) (k := 6) (by decide)
      (by clear * -; bv_omega) (by simpa [Spill13.get] using hs6)))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (pc := b + 0x28f8#64) (wb := none) (ea := sp + 176#64)
    (v := dup8x16 3329#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.spill13 (ptr := sp) (ea := sp + 176#64) (k := 11) (by decide)
      (by clear * -; bv_omega) (by simpa [Spill13.get] using hs11)))
    (by wp_norm_lhs) ?_
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hx19],
      by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp,
      ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem update2_split {f g0 g1 : Nat → BitVec 128} {r : Nat}
    (hlo : ∀ j, j < 2 * r → f j = g1 j)
    (hhi : ∀ j, 2 * r ≤ j → j < 32 → f j = g0 j) :
    let f' := Function.update (Function.update f (2 * r) (g1 (2 * r)))
      (2 * r + 1) (g1 (2 * r + 1))
    (∀ j, j < 2 * (r + 1) → f' j = g1 j) ∧
    (∀ j, 2 * (r + 1) ≤ j → j < 32 → f' j = g0 j) := by
  refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · by_cases h1 : j = 2 * r + 1
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h0 : j = 2 * r
      · subst h0; simp
      · rw [Function.update_of_ne h0]; exact hlo j (by omega)
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hhi j (by omega) hj2

private theorem seg5a_iter [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl20 b)
    (s0 s : State) (sp ret : BitVec 64) (inv err2 msgPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x291c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 3456#64 + BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = sp + 2432#64 + BitVec.ofNat 64 (32 * r))
    (hx10 : s.readReg64 .x10 = sp + 1760#64 + BitVec.ofNat 64 (32 * r))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = 1441#64) (hx13 : s.readReg64 .x13 = 55457#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 1024#16) (hv19 : s.readVReg128 19#5 = dup8x16 0xf2ff#16)
    (hus : UnspilledSaved20 s0 s)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC20.rebase b (fun _ => none))
      (if r < 15 then b + 0x291c#64 else b + 0x29a8#64) s
      (PolyMem (sp + 3440#64) f ∗ PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = sp + 3456#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = sp + 2432#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x10 = sp + 1760#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x12 = 1441#64 ∧ s'.readReg64 .x13 = 55457#64 ∧
        s'.readReg64 .x19 = ret ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 1024#16 ∧ s'.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        UnspilledSaved20 s0 s' ∧
        P' = (PolyMem (sp + 3440#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))) ∗
          PolyMem (sp + 1744#64) (polyVecNat err2) ∗
          PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)) := by
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 1744#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 1744#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat err2 (2 * r)) (v2 := polyVecNat err2 (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx10]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 6
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 2416#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 2416#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat msgPoly (2 * r)) (v2 := polyVecNat msgPoly (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))))
    (SepLoad128.right (SepLoad128.right (SepLoad128.left
      (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))))
    (by wp_norm_lhs) ?_
  wp_steps 21
  have hv1_eq := seg5Loop1_vec_eq inv err2 msgPoly (2 * r) (by omega) true
  have hv0_eq := seg5Loop1_vec_eq inv err2 msgPoly (2 * r + 1) (by omega) false
  dsimp only [Bool.false_eq_true, ↓reduceIte] at hv1_eq hv0_eq
  refine step_stpQ128 (wb := none)
    (ea := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 3440#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r))
    (v2 := polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by simp [← hv1_eq]) (by simp [← hv0_eq])
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  wp_steps 2
  wp_if hne
  · have hr15 : r < 15 := by
      clear * - hr hne hx11
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp_all
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp [hx12], by simp [hx13], by simp [hx19],
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19],
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      clear * - hne hx11
      intro hlt
      rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r
      all_goals try simp_all
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq],
        by simp [hr_eq], by simp [hr_eq],
        by simp [hx12], by simp [hx13], by simp [hx19],
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19],
        ⟨by simp [hus.1], by simp [hus.2.1], by simp [hus.2.2.1], by simp [hus.2.2.2]⟩, rfl⟩

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

private theorem seg5a_loop1 [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b)
    (s0 : State) (sp ret : BitVec 64) (inv err2 msgPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x291c#64 → s.status = .Running →
      s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem →
      MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = sp + 3456#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = sp + 2432#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x10 = sp + 1760#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = 1441#64 →
      s.readReg64 .x13 = 55457#64 →
      s.readReg64 .x19 = ret →
      s.readVReg128 16#5 = dup8x16 3329#16 →
      s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 18#5 = dup8x16 1024#16 →
      s.readVReg128 19#5 = dup8x16 0xf2ff#16 →
      UnspilledSaved20 s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (seg5FinalPoly inv err2 msgPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x29a8#64) s
        (PolyMem (sp + 3440#64) f ∗
          PolyMem (sp + 1744#64) (polyVecNat err2) ∗
          PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x19 = ret ∧
          UnspilledSaved20 s0 s' ∧
          P' = (PolyMem (sp + 3440#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
            PolyMem (sp + 1744#64) (polyVecNat err2) ∗
            PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx12 hx13 hx19
      hv16 hv17 hv18 hv19 hus hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg5a_iter hb s0 s sp ret inv err2 msgPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hx19 hv16 hv17 hv18 hv19 hus
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, hx19', _, _, _, _, hus', hP'⟩
    refine ⟨hsp', hspA', hx19', hus', ?_⟩
    rw [hP', polyMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx19
      hv16 hv17 hv18 hv19 hus hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg5a_iter hb s0 s sp ret inv err2 msgPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hx19 hv16 hv17 hv18 hv19 hus
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm Pm hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx19',
        hv16', hv17', hv18', hv19', hus', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx12' hx13' hx19' hv16' hv17' hv18' hv19' hus' hlo' hhi'

/-- Segment 5a (`+0x28e8 → +0x29a8`): `memcpy` + 16-iter normalizer/error/message/Barrett loop. -/
theorem seg5a_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl20 b) (hbase : blkPl20.base = b)
    (s0 s4 : State) (sp ret : BitVec 64) (spill : Spill13)
    (inv err2 msgPoly : Poly16) (Rest : SepProp)
    (hpc : s4.pc = b + 0x28e8#64) (hrun : s4.status = .Running)
    (hpost4 : Seg4Post s0 s4 sp ret)
    (hs6 : spill.s6 = dup8x16 20159#16)
    (hs11 : spill.s11 = dup8x16 3329#16)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s4.mem)
    (hro : MlKemRoOk mlkemMpl s4.mem) :
    SepWP (blkPC20.rebase b (fun _ => none)) (b + 0x29a8#64) s4
      (Spill13Mem sp spill ∗ memRegion (sp + 3440#64) 512 ∗
        PolyMem (sp + 2928#64) (polyVecNat inv) ∗
        PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)
      (fun s5 P5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧ s5.readReg64 .x19 = ret ∧
        UnspilledSaved20 s0 s5 ∧
        P5 = (PolyMem (sp + 3440#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
          PolyMem (sp + 1744#64) (polyVecNat err2) ∗
          PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗
          Spill13Mem sp spill ∗
          PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Rest)) := by
  have h1 := seg5a_memcpy hb hbase s0 s4 sp ret spill inv
    (PolyMem (sp + 1744#64) (polyVecNat err2) ∗
      PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest)
    hpc hrun hpost4 hcl
  refine sepWP_seq_env hcl hro h1 ?_
  rintro s4' _ hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx19_1, hx20_1, hus1, rfl⟩
  have h2 := seg5a_setup hb s0 s4' sp ret spill
    (PolyMem (sp + 3440#64) (polyVecNat inv) ∗
      PolyMem (sp + 2928#64) (polyVecNat inv) ∗
      (PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest))
    hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hus1 hs6 hs11
  refine sepWP_seq_env hcl1 hro1 h2 ?_
  rintro sm _ hpc' hrun' hcl' hro'
    ⟨hsp, hspA, hx19, hx8, hx9, hx10, hx11, hx12, hx13, hv16, hv17, hv18, hv19, hus, rfl⟩
  have hreord :
      (Spill13Mem sp spill ∗
        (PolyMem (sp + 3440#64) (polyVecNat inv) ∗
          PolyMem (sp + 2928#64) (polyVecNat inv) ∗
          (PolyMem (sp + 1744#64) (polyVecNat err2) ∗
            PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗ Rest))) =
      (PolyMem (sp + 3440#64) (polyVecNat inv) ∗
        PolyMem (sp + 1744#64) (polyVecNat err2) ∗
        PolyMem (sp + 2416#64) (polyVecNat msgPoly) ∗
        (Spill13Mem sp spill ∗ PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Rest)) :=
    sepProp_ext (by sep_frame) (by sep_frame)
  rw [hreord]
  exact seg5a_loop1 hb s0 sp ret inv err2 msgPoly
    (Spill13Mem sp spill ∗ PolyMem (sp + 2928#64) (polyVecNat inv) ∗ Rest)
    15 0 rfl sm (polyVecNat inv) hpc' hrun' hsp hspA hcl' hro'
    (by simpa using hx8) (by simpa using hx9) (by simpa using hx10) (by simpa using hx11)
    hx12 hx13 hx19 hv16 hv17 hv18 hv19 hus
    (fun _ hj => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5a
