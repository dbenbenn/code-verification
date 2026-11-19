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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `kyber_decapsulate` (`B06`) — Site 1 Inverse NTT Low-Stage Loops (`+0x1e84 → +0x1fd0`)

Steps the lower 2 stages (`len = 2` then `len = 4`) of `invert_ntt_montgomery` on
`PolyMem (sp + 28368#64)` at Site 1 (`+0x1e84 → +0x1fd0`), producing
`PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot))` while preserving `Inv13Preserved`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Inv1LowLoops

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_ro00)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonInvNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ld1r4h_ro step_ldrh16_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_stpQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (bv128_or_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdIns_d1_d0 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7
  svc_simdMla_8h svc_simdMovi_8h_1024 svc_simdMul_8h svc_simdMvni_8h_f2ff svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn2_4s svc_simdZip1_2d svc_simdZip2_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZetaLayer2 invNttAfterStage2 invNttAfterStage2_size
  layer2RawPair layer2RawPair_eq_polyVecNat
  layer4RawPair layer4RawPair_eq_polyVecNat lowerInvNtt16)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x1e84 → 0x1fcc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible]
  blkPC06 zetaTableAt dup8x16 dup4hLow polyVecNat
  simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
  simdTrn1_4s simdTrn2_4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff
  svc_simdDup_8h_gpr svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7 svc_simdIns_d1_d0
  svc_simdTrn1_4s svc_simdTrn2_4s svc_simdZip1_2d svc_simdZip2_2d

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

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

private abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

private theorem inv1_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x1eac#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (16 + 32 * r)) (hx10 : s.readReg64 .x10 = sp + 28368#64)
    (hx11 : s.readReg64 .x11 = 20159#64) (hx12 : s.readReg64 .x12 = 62209#64)
    (hx13 : s.readReg64 .x13 = 3329#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1024#16) (hv1 : s.readVReg128 1#5 = dup8x16 0xf2ff#16)
    (hpres : Inv13Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x1eac#64 else b + 0x1f48#64) s (PolyMem (sp + 28368#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * (r + 1)) ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧ s'.readReg64 .x10 = sp + 28368#64 ∧
        s'.readReg64 .x11 = 20159#64 ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readVReg128 0#5 = dup8x16 1024#16 ∧ s'.readVReg128 1#5 = dup8x16 0xf2ff#16 ∧
        Inv13Preserved s0 s' ∧
        P' = (PolyMem (sp + 28368#64)
          (Function.update (Function.update f (2 * r) (polyVecNat (invNttAfterStage2 p) (2 * r)))
            (2 * r + 1) (polyVecNat (invNttAfterStage2 p) (2 * r + 1))) ∗ Rest)) := by
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  let k := 127 - 4 * r
  refine step_ldrh16_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k)) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 7
  refine step_ldrh16_ro (k := k - 2) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 2)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 7
  refine step_ldrh16_ro (k := k - 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 1)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 4
  refine step_ldrh16_ro (k := k - 3) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 3)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 12
  have hpair := layer2RawPair_eq_polyVecNat hp r hr
  dsimp only [layer2RawPair, buildZetaLayer2] at hpair
  refine step_stpQ128 (wb := none)
    (ea := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (invNttAfterStage2 p) (2 * r))
    (v2 := polyVecNat (invNttAfterStage2 p) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by simp [← hpair.1]; rfl) (by simp [← hpair.2]; rfl)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'; wp_step; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp [hx10], by simp [hx11], by simp [hx12], by simp [hx13],
        by simp [hv0], by simp [hv1],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hbv : BitVec.ofNat 64 (16 + 32 * r) + 32#64 = 528#64 := by simpa using hne
      have hnat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq],
        by simp [hx10], by simp [hx11], by simp [hx12], by simp [hx13],
        by simp [hv0], by simp [hv1],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem inv1_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x1eac#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r) →
      s.readReg64 .x9 = BitVec.ofNat 64 (16 + 32 * r) → s.readReg64 .x10 = sp + 28368#64 →
      s.readReg64 .x11 = 20159#64 → s.readReg64 .x12 = 62209#64 → s.readReg64 .x13 = 3329#64 →
      s.readVReg128 0#5 = dup8x16 1024#16 → s.readVReg128 1#5 = dup8x16 0xf2ff#16 →
      Inv13Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (invNttAfterStage2 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1f48#64) s
        (PolyMem (sp + 28368#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem (sp + 28368#64) (polyVecNat (invNttAfterStage2 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hv0 hv1 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv1_layer2_iter hb s0 s sp hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hv0 hv1 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hv0 hv1 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := inv1_layer2_iter hb s0 s sp hp (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hv0 hv1 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hv0_m, hv1_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx13_m hv0_m hv1_m hpres_m hlo' hhi'

private theorem inv1_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) {q : Poly16} (hq : q.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x1f6c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r))
    (hx10 : s.readReg64 .x10 = sp + 28368#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv1 : s.readVReg128 1#5 = dup8x16 3329#16)
    (hpres : Inv13Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonInvNttStage16 4 63 false q).1
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x1f6c#64 else b + 0x1fd0#64) s (PolyMem (sp + 28368#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * (r + 1)) ∧
        s'.readReg64 .x10 = sp + 28368#64 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 1#5 = dup8x16 3329#16 ∧
        Inv13Preserved s0 s' ∧
        P' = (PolyMem (sp + 28368#64)
          (Function.update (Function.update f (2 * r) (polyVecNat q' (2 * r)))
            (2 * r + 1) (polyVecNat q' (2 * r + 1))) ∗ Rest)) := by
  intro q'
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  let k := 63 - 2 * r
  wp_step
  refine step_ld1r4h_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [hx9]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_step
  refine step_ld1r4h_ro (k := k - 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 1)))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q (2 * r)) (v2 := polyVecNat q (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 16
  have hpair := layer4RawPair_eq_polyVecNat hq r hr
  dsimp only [layer4RawPair] at hpair
  refine step_stpQ128 (wb := none)
    (ea := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 28368#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q' (2 * r)) (v2 := polyVecNat q' (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [q', k]; rw [← hpair.1]; simp) (by dsimp only [q', k]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'; wp_step; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp [hx10], by simp [hv0], by simp [hv1],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hbv : BitVec.ofNat 64 (32 * r) + 32#64 = 512#64 := by simpa using hne
      have hnat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq],
        by simp [hx10], by simp [hv0], by simp [hv1],
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
         by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem inv1_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp : BitVec 64) {q : Poly16} (hq : q.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x1f6c#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r) →
      s.readReg64 .x10 = sp + 28368#64 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 1#5 = dup8x16 3329#16 →
      Inv13Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonInvNttStage16 4 63 false q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1fd0#64) s
        (PolyMem (sp + 28368#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem (sp + 28368#64) (polyVecNat (neonInvNttStage16 4 63 false q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hv0 hv1 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv1_layer4_iter hb s0 s sp hq (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hv0 hv1 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hv0 hv1 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := inv1_layer4_iter hb s0 s sp hq (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hv0 hv1 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hv0_m, hv1_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hv0_m hv1_m hpres_m hlo' hhi'

theorem inv1_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + 0x1e84#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1fd0#64) s
      (PolyMem (sp + 28368#64) (polyVecNat dot) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s s' ∧
        P' = (PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  refine sepWP_seq_env hcl hro (mid := b + 0x1eac#64)
    (post1 := fun s1 P1 =>
      s1.sp = sp ∧ s1.spAligned = true ∧ s1.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 254#64 ∧
      s1.readReg64 .x9 = 16#64 ∧ s1.readReg64 .x10 = sp + 28368#64 ∧
      s1.readReg64 .x11 = 20159#64 ∧ s1.readReg64 .x12 = 62209#64 ∧ s1.readReg64 .x13 = 3329#64 ∧
      s1.readVReg128 0#5 = dup8x16 1024#16 ∧ s1.readVReg128 1#5 = dup8x16 0xf2ff#16 ∧
      Inv13Preserved s s1 ∧ P1 = (PolyMem (sp + 28368#64) (polyVecNat dot) ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
        ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
          by simp, by simp, by simp,
          by simp, by simp, by simp, by simp, by simp,
          ⟨by simp, by simp, by simp, by simp, by simp, by simp,
           by simp, by simp, by simp, by simp, by simp⟩, rfl⟩) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hv0_1, hv1_1, hpres1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1
    (inv1_layer2_loop hb s sp hdot Rest 15 0 rfl s1 (polyVecNat dot)
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hv0_1 hv1_1 hpres1
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hpres2, hP2⟩
  subst hP2
  rcases hpres2 with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine sepWP_seq_env hcl2 hro2 (mid := b + 0x1f6c#64)
    (post1 := fun s3 P3 =>
      s3.sp = sp ∧ s3.spAligned = true ∧ s3.readReg64 .x8 = 0#64 ∧
      s3.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 126#64 ∧ s3.readReg64 .x10 = sp + 28368#64 ∧
      s3.readVReg128 0#5 = dup8x16 62209#16 ∧ s3.readVReg128 1#5 = dup8x16 3329#16 ∧
      Inv13Preserved s s3 ∧
      P3 = (PolyMem (sp + 28368#64) (polyVecNat (invNttAfterStage2 dot)) ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun2])
        ⟨by simp [hsp2], by simpa [State.spAligned] using hspA2,
          by simp, by simp, by simp, by simp, by simp,
          ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
           by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hv0_3, hv1_3, hpres3, hP3⟩
  subst hP3
  exact inv1_layer4_loop hb s sp (invNttAfterStage2_size hdot) Rest 15 0 rfl s3 _
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3 hx9_3 hx10_3 hv0_3 hv1_3 hpres3
    (fun _ h => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Inv1LowLoops
