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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1c

/-!
# `kyber_decapsulate` (`B06`) — Segment 8 `InvNTT` + `e2` + `mPoly` (`+0xbc6c .. +0xd6e0`)

Proves `seg8_inv_add_ok` (`+0xbc6c → +0xd6e0`): 7-stage `InvNTT` (`+0xbc6c → +0xd618`) followed by
`B28` `memcpy` + 16-iteration post-`InvNTT` normalizer + `e2` + `msgPoly` + Barrett loop
(`+0xd618 → +0xd6e0`), producing `PolyMem (sp + 32496#64) (polyVecNat (seg5FinalPoly inv e2 msgPoly))`
while preserving `x22 = ctA` and `fp = fpVal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (MlKemBase MlKemPlacement mlkemMpl resolve_ro00)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonInvNttMontgomery16 neonInvNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env step_ld1r4h_ro step_ldrh16_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub spAligned_of_chk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec32 VecRangeMem
  poly32Mem_ofFn polyVecNat step_ldpQ128 step_ldrQ128 step_stpQ128 vecRangeBytes
  vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZetaLayer2 invNttAfterStage2 invNttAfterStage2_size layer2RawPair layer2RawPair_eq_polyVecNat
  layer4RawPair layer4RawPair_eq_polyVecNat lowerInvNtt16 lowerInvNtt16_size upperInvNtt16_lowerInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdIns_d1_d0 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7
  svc_simdMla_8h svc_simdMovi_8h_1024 svc_simdMul_8h svc_simdMvni_8h_f2ff svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn2_4s svc_simdZip1_2d svc_simdZip2_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (seg5FinalPoly seg5Loop1_vec_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40 SpillSliceMem SymEnv SymGprs evalSymGpr symInitState)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SymSpatial SymStateMatches blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymPure (poly_eq_upperInvNtt16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (blk28_memcpy_06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1a (cfgSeg8InvSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvSym1c (
  run_seg8_inv1 seg8_inv_ast_eq seg8_inv_noSpillVreg symSeg8InvSymEnd)

abbrev offBc6c : BitVec 64 := BitVec.ofNat 64 0xbc6c
private abbrev offBc94 : BitVec 64 := BitVec.ofNat 64 0xbc94
private abbrev offBd30 : BitVec 64 := BitVec.ofNat 64 0xbd30
private abbrev offBd54 : BitVec 64 := BitVec.ofNat 64 0xbd54
private abbrev offBdb8 : BitVec 64 := BitVec.ofNat 64 0xbdb8
private abbrev offD618 : BitVec 64 := BitVec.ofNat 64 0xd618
private abbrev offD61c : BitVec 64 := BitVec.ofNat 64 0xd61c
private abbrev offD654 : BitVec 64 := BitVec.ofNat 64 0xd654
abbrev offD6e0 : BitVec 64 := BitVec.ofNat 64 0xd6e0

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xbc6c → 0xbdb4, 0xd618 → 0xd6dc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := rfl
@[simp] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp] private theorem status_orFpsr' (s : State) (f : BitVec 32) :
    (s.orFpsr f).status = s.status := rfl

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

/-! ## 1. Lower-2 `InvNTT` Stages (`len = 2, 4`, `+0xbc6c → +0xbdb8`) -/

private theorem inv8_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offBc94) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (16 + 32 * r)) (hx10 : s.readReg64 .x10 = sp + 28368#64)
    (hx11 : s.readReg64 .x11 = 20159#64) (hx12 : s.readReg64 .x12 = 62209#64)
    (hx13 : s.readReg64 .x13 = 3329#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 1024#16) (hv1 : s.readVReg128 1#5 = dup8x16 0xf2ff#16)
    (hpres : Inv13Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + offBc94 else b + offBd30) s (PolyMem (sp + 28368#64) f ∗ Rest)
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
  have _ : b = blkPl06.base := _hb
  dsimp only [offBc94, offBd30] at hpc ⊢
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

private theorem inv8_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offBc94 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r) →
      s.readReg64 .x9 = BitVec.ofNat 64 (16 + 32 * r) → s.readReg64 .x10 = sp + 28368#64 →
      s.readReg64 .x11 = 20159#64 → s.readReg64 .x12 = 62209#64 → s.readReg64 .x13 = 3329#64 →
      s.readVReg128 0#5 = dup8x16 1024#16 → s.readVReg128 1#5 = dup8x16 0xf2ff#16 →
      Inv13Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (invNttAfterStage2 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offBd30) s
        (PolyMem (sp + 28368#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem (sp + 28368#64) (polyVecNat (invNttAfterStage2 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hv0 hv1 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv8_layer2_iter hb s0 s sp hp (r := 15) (by omega) f Rest
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
    have hiter := inv8_layer2_iter hb s0 s sp hp (by omega) f Rest
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

private theorem inv8_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) {q : Poly16} (hq : q.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offBd54) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r))
    (hx10 : s.readReg64 .x10 = sp + 28368#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv1 : s.readVReg128 1#5 = dup8x16 3329#16)
    (hpres : Inv13Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonInvNttStage16 4 63 false q).1
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + offBd54 else b + offBdb8) s (PolyMem (sp + 28368#64) f ∗ Rest)
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
  have _ : b = blkPl06.base := _hb
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

private theorem inv8_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp : BitVec 64) {q : Poly16} (hq : q.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offBd54 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r) →
      s.readReg64 .x10 = sp + 28368#64 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 1#5 = dup8x16 3329#16 →
      Inv13Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonInvNttStage16 4 63 false q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offBdb8) s
        (PolyMem (sp + 28368#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem (sp + 28368#64) (polyVecNat (neonInvNttStage16 4 63 false q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hv0 hv1 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv8_layer4_iter hb s0 s sp hq (r := 15) (by omega) f Rest
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
    have hiter := inv8_layer4_iter hb s0 s sp hq (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hv0 hv1 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hv0_m, hv1_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hv0_m hv1_m hpres_m hlo' hhi'

private theorem inv8_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + offBc6c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offBdb8) s
      (PolyMem (sp + 28368#64) (polyVecNat dot) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s s' ∧
        P' = (PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  refine sepWP_seq_env hcl hro (mid := b + offBc94)
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
    (inv8_layer2_loop hb s sp hdot Rest 15 0 rfl s1 (polyVecNat dot)
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hv0_1 hv1_1 hpres1
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hpres2, hP2⟩
  subst hP2
  rcases hpres2 with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine sepWP_seq_env hcl2 hro2 (mid := b + offBd54)
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
  exact inv8_layer4_loop hb s sp (invNttAfterStage2_size hdot) Rest 15 0 rfl s3 _
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3 hx9_3 hx10_3 hv0_3 hv1_3 hpres3
    (fun _ h => by omega) (fun _ _ _ => rfl)

/-! ## 2. Symbolic Upper `InvNTT` (`+0xbdb8 → +0xd618`) -/

private theorem noReloc_inv8 : blk06NoRelocInRange 12142 13702 = true := by decide +kernel

private def mkInv8Env (s : State) (f7 : Nat → BitVec 128) (p : Poly16) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn fun i => if i < 7 then f7 i else 0#128
  poly0   := Vec32.ofFn (polyVecNat p)
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_inv8Init {sp : BitVec 64} {s : State} (f7 : Nat → BitVec 128) (p : Poly16)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SymStateMatches sp (mkInv8Env s f7 p) symInitState s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symInitState, SymGprs.ofFn, SymGprs.get, evalSymGpr, mkInv8Env]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

private theorem spill7_eq_initSlice (ptr : BitVec 64) (s : State) (f7 : Nat → BitVec 128) (p : Poly16) :
    VecRangeMem 7 ptr f7 = SpillSliceMem 7 ptr (symInitState.spill.eval (mkInv8Env s f7 p)) :=
  vecRangeMem_congr fun i hi => by
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl
    | _ + 7 => omega

private theorem polyMem_eq_initPoly32 (ptr : BitVec 64) (s : State) (f7 : Nat → BitVec 128) (p : Poly16) :
    PolyMem ptr (polyVecNat p) = Poly32Mem ptr (symInitState.poly.eval (mkInv8Env s f7 p)) := by
  change PolyMem ptr (polyVecNat p) = Poly32Mem ptr (Vec32.ofFn (polyVecNat p))
  rw [poly32Mem_ofFn]

private theorem inv8_upper_ok [MlKemPlacement] {b : BitVec 64}
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (f7 : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offBdb8) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD618) s
      (VecRangeMem 7 (sp + 2320#64) f7 ∗
        PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x0 = sp + 32496#64 ∧ sf.readReg64 .x1 = sp + 28368#64 ∧
        sf.readReg64 .x2 = 512#64 ∧ sf.readReg64 .x19 = sp + 32496#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        ∃ sp40 : Spill40,
          sp40.get 0 = dup8x16 20159#16 ∧ sp40.get 5 = dup8x16 3329#16 ∧
          (Pf ⊢ SpillSliceMem 7 (sp + 2320#64) sp40 ∗
            PolyMem (sp + 28368#64) (polyVecNat (neonInvNttMontgomery16 dot)) ∗ Rest)) := by
  let env := mkInv8Env s f7 (lowerInvNtt16 dot)
  have hpre : VecRangeMem 7 (sp + 2320#64) f7 ∗
      PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ Rest ⊢
      SymSpatial cfgSeg8InvSym sp env symInitState Rest := by
    simp only [SymSpatial, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem, cfgSeg8InvSym,
      Bool.false_eq_true, ↓reduceIte]
    rw [spill7_eq_initSlice (sp + 2320#64) s f7 (lowerInvNtt16 dot),
      polyMem_eq_initPoly32 (sp + 28368#64) s f7 (lowerInvNtt16 dot)]
    sep_frame
  refine SepWP.weaken_pre hpre
    (sepWP_of_runSymRange (wLo := 12142) (wHi := 13702) 1560 12142
      noReloc_inv8 (by decide) (by omega) (by omega) run_seg8_inv1
      (matches_inv8Init f7 (lowerInvNtt16 dot) hsp hspA) hpc hrun ?_)
  intro sf _ _ hmf
  have hgpr := hmf.hgprs
  have hg0 := hgpr 0#5 (by decide)
  have hg1 := hgpr 1#5 (by decide)
  have hg2 := hgpr 2#5 (by decide)
  have hg19 := hgpr 19#5 (by decide)
  have hg22 := hgpr 22#5 (by decide)
  have hg29 := hgpr 29#5 (by decide)
  change sf.readReg64 .x0 = sp + 32496#64 at hg0
  change sf.readReg64 .x1 = sp + 28368#64 at hg1
  change sf.readReg64 .x2 = 512#64 at hg2
  change sf.readReg64 .x19 = sp + 32496#64 at hg19
  change sf.readReg64 .x22 = s.readReg64 .x22 + 0#64 at hg22
  change sf.readReg64 .fp = s.readReg64 .fp + 0#64 at hg29
  refine ⟨hmf.hsp, hmf.hsp_al, hg0, hg1, hg2, hg19,
    by rw [hg22, BitVec.add_zero], by rw [hg29, BitVec.add_zero],
    symSeg8InvSymEnd.spill.eval env, rfl, rfl, ?_⟩
  simp only [SymSpatial, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem, cfgSeg8InvSym,
    Bool.false_eq_true, ↓reduceIte]
  have hpoly_eq := poly_eq_upperInvNtt16 (sp + 28368#64) (lowerInvNtt16_size hdot) env rfl
    symSeg8InvSymEnd.poly seg8_inv_noSpillVreg seg8_inv_ast_eq
  rw [hpoly_eq, upperInvNtt16_lowerInvNtt16]
  sep_frame

/-! ## 3. `B28` `memcpy` + 16-Iter `seg5FinalPoly` Loop (`+0xd618 → +0xd6e0`) -/

private theorem seg8_add_memcpy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) (inv : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offD618) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = sp + 32496#64) (hx1 : s.readReg64 .x1 = sp + 28368#64)
    (hx2 : s.readReg64 .x2 = 512#64) (hx19 : s.readReg64 .x19 = sp + 32496#64)
    (_hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD61c) s
      (memRegion (sp + 32496#64) 512 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.readReg64 .x19 = sp + 32496#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        Pf = (PolyMem (sp + 32496#64) (polyVecNat inv) ∗
          PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest)) := by
  subst hbase
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  generalize hbs_def : vecRangeBytes 32 (polyVecNat inv) = bsInv
  have hbs : bsInv.length = 512 := by rw [← hbs_def, vecRangeBytes_length]
  have hp28368 : PolyMem (sp + 28368#64) (polyVecNat inv) = ((sp + 28368#64) ↦ₛ bsInv) := by
    rw [← hbs_def]; exact vecRangeMem_eq_pointsToBytes 32 _ _
  have hp32496 : ((sp + 32496#64) ↦ₛ bsInv) = PolyMem (sp + 32496#64) (polyVecNat inv) := by
    rw [← hbs_def]; exact (vecRangeMem_eq_pointsToBytes 32 _ _).symm
  rw [hp28368]
  wp_call (blk28_memcpy_06 blkPl06.base) (sp + 32496#64, sp + 28368#64, bsInv)
  rw [← hp28368, hp32496]
  have hsp_sf : sf.sp = sp := by simp [*]
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨hsp_sf, spAligned_of_chk hsp_sf hsp_chk, by simp [*], by simp [*], by simp [*],
      sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg8_add_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) (sp40 : Spill40) (Rest : SepProp)
    (hpc : s.pc = b + offD61c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = sp + 32496#64)
    (hs0 : sp40.get 0 = dup8x16 20159#16) (hs5 : sp40.get 5 = dup8x16 3329#16) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD654) s
      (SpillSliceMem 7 (sp + 2320#64) sp40 ∗ Rest)
      (fun s5 P5 =>
        s5.sp = sp ∧ s5.spAligned = true ∧
        s5.readReg64 .x8 = sp + 32512#64 ∧ s5.readReg64 .x9 = sp + 26336#64 ∧
        s5.readReg64 .x10 = sp + 33024#64 ∧ s5.readReg64 .x11 = 16#64 ∧
        s5.readReg64 .x12 = 1441#64 ∧ s5.readReg64 .x13 = 55457#64 ∧
        s5.readReg64 .x22 = s.readReg64 .x22 ∧ s5.readReg64 .fp = s.readReg64 .fp ∧
        s5.readVReg128 16#5 = dup8x16 3329#16 ∧ s5.readVReg128 17#5 = dup8x16 20159#16 ∧
        s5.readVReg128 18#5 = dup8x16 1024#16 ∧ s5.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P5 = (SpillSliceMem 7 (sp + 2320#64) sp40 ∗ Rest)) := by
  have _ : b = blkPl06.base := _hb
  wp_steps 4
  refine step_ldrQ128 (wb := none) (ea := (sp + 2320#64) + BitVec.ofNat 64 (16 * 0))
    (v := dup8x16 20159#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 7) (k := 0) (by decide) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := (sp + 2320#64) + BitVec.ofNat 64 (16 * 5))
    (v := dup8x16 3329#16) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
    (by simpa [checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (hs5 ▸ SepLoad128.left (SepLoad128.vecRange (n := 7) (k := 5) (by decide) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 8
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp, rfl⟩

private theorem seg8_add_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp : BitVec 64) (inv err2 msgPoly : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offD654) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = sp + 32512#64 + BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (32 * r))
    (hx10 : s.readReg64 .x10 = sp + 33024#64 + BitVec.ofNat 64 (32 * r))
    (hx11 : s.readReg64 .x11 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = 1441#64) (hx13 : s.readReg64 .x13 = 55457#64)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16) (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 1024#16) (hv19 : s.readVReg128 19#5 = dup8x16 0xf2ff#16)
    (hhi0 : f (2 * r) = polyVecNat inv (2 * r))
    (hhi1 : f (2 * r + 1) = polyVecNat inv (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + offD654 else b + offD6e0) s
      (PolyMem (sp + 32496#64) f ∗ PolyMem (sp + 33008#64) (polyVecNat err2) ∗
        PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = sp + 32512#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x10 = sp + 33024#64 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x11 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x12 = 1441#64 ∧ s'.readReg64 .x13 = 55457#64 ∧
        s'.readReg64 .x22 = s.readReg64 .x22 ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 1024#16 ∧ s'.readVReg128 19#5 = dup8x16 0xf2ff#16 ∧
        P' = (PolyMem (sp + 32496#64)
          (Function.update
            (Function.update f (2 * r) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r)))
            (2 * r + 1) (polyVecNat (seg5FinalPoly inv err2 msgPoly) (2 * r + 1))) ∗
          PolyMem (sp + 33008#64) (polyVecNat err2) ∗
          PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ Rest)) := by
  have _ : b = blkPl06.base := _hb
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 32496#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 32496#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat inv (2 * r)) (v2 := polyVecNat inv (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ldpQ128 (wb := none)
    (ea := (sp + 33008#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 33008#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
    (ea := (sp + 26320#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 26320#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
    (ea := (sp + 32496#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 32496#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
        by simp [hx12], by simp [hx13], by simp, by simp,
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19], rfl⟩
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
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx12], by simp [hx13], by simp, by simp,
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv19], rfl⟩

private theorem seg8_add_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (sp x22v fpv : BitVec 64) (inv err2 msgPoly : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 →
    ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offD654 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = sp + 32512#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = sp + 26336#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x10 = sp + 33024#64 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x11 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = 1441#64 → s.readReg64 .x13 = 55457#64 →
      s.readReg64 .x22 = x22v → s.readReg64 .fp = fpv →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 18#5 = dup8x16 1024#16 → s.readVReg128 19#5 = dup8x16 0xf2ff#16 →
      (∀ j, j < 2 * r → f j = polyVecNat (seg5FinalPoly inv err2 msgPoly) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat inv j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offD6e0) s
        (PolyMem (sp + 32496#64) f ∗ PolyMem (sp + 33008#64) (polyVecNat err2) ∗
          PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x22 = x22v ∧ s'.readReg64 .fp = fpv ∧
          P' = (PolyMem (sp + 32496#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
            PolyMem (sp + 33008#64) (polyVecNat err2) ∗
            PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl _hro hx8 hx9 hx10 hx11 hx12 hx13 hx22 hfp hv16 hv17 hv18 hv19 hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hstep := seg8_add_iter hb s sp inv err2 msgPoly (r := 15) (by decide) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hv16 hv17 hv18 hv19
      (hhi 30 (by decide) (by decide)) (hhi 31 (by decide) (by decide))
    simp only [show ¬ (15 < 15) by decide, ↓reduceIte] at hstep
    refine SepWP.mono hstep ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, hx22', hfp', _, _, _, _, hP'⟩
    refine ⟨hsp', hspA', hx22'.trans hx22, hfp'.trans hfp, ?_⟩
    rw [hP', polyMem_congr (update2_split (r := 15) hlo hhi).1]
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx22 hfp hv16 hv17 hv18 hv19 hlo hhi
    have hr_lt : r < 15 := by omega
    have hstep := seg8_add_iter hb s sp inv err2 msgPoly (r := r) (by omega) f Rest
      hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hv16 hv17 hv18 hv19
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr_lt, ↓reduceIte] at hstep
    refine sepWP_seq_env hcl hro hstep ?_
    rintro sm _ hpc' hrun' hcl' hro'
      ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx22', hfp', hv16', hv17', hv18', hv19', rfl⟩
    have ⟨hlo', hhi'⟩ := update2_split (r := r) hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc' hrun' hsp' hspA' hcl' hro'
      hx8' hx9' hx10' hx11' hx12' hx13' (hx22'.trans hx22) (hfp'.trans hfp) hv16' hv17' hv18' hv19' hlo' hhi'

/-- Segment 8 `InvNTT` + `e2` + `msgPoly` (`+0xbc6c → +0xd6e0`): computes
    `seg5FinalPoly (neonInvNttMontgomery16 dot) err2 msgPoly` at `[sp + 32496, sp + 33008)`. -/
theorem seg8_inv_add_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s : State) (sp : BitVec 64) {dot : Poly16} (hdot : dot.size = 256)
    (err2 msgPoly : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offBc6c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let inv := neonInvNttMontgomery16 dot
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offD6e0) s
      (memRegion (sp + 2320#64) 112 ∗ PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗
        PolyMem (sp + 28368#64) (polyVecNat dot) ∗ memRegion (sp + 32496#64) 512 ∗
        PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .fp = s.readReg64 .fp ∧
        (Pf ⊢ memRegion (sp + 2320#64) 112 ∗ memRegion (sp + 26320#64) 512 ∗
          memRegion (sp + 28368#64) 512 ∗
          PolyMem (sp + 32496#64) (polyVecNat (seg5FinalPoly inv err2 msgPoly)) ∗
          memRegion (sp + 33008#64) 512 ∗ Rest)) := by
  intro inv
  set R0 := memRegion (sp + 2320#64) 112 ∗ PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗
    memRegion (sp + 32496#64) 512 ∗ PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest
  have hpre0 : memRegion (sp + 2320#64) 112 ∗ PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗
      PolyMem (sp + 28368#64) (polyVecNat dot) ∗ memRegion (sp + 32496#64) 512 ∗
      PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest ⊢
      PolyMem (sp + 28368#64) (polyVecNat dot) ∗ R0 := by dsimp only [R0]; sep_frame
  refine SepWP.weaken_pre hpre0 (sepWP_seq_env hcl hro
    (inv8_low_ok hb s sp hdot R0 hpc hrun hsp hspA hcl hro) ?_)
  rintro s1 _ hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hpres1, rfl⟩
  rcases hpres1 with ⟨_, _, _, hx22_1, _, _, _, _, _, _, hfp_1⟩
  dsimp only [R0]
  refine SepWP.of_memRegion_vecRangeMem 7 (sp + 2320#64) (by decide) (by sep_focus) fun f7 => ?_
  set R1 := PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ memRegion (sp + 32496#64) 512 ∗
    PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest
  have hpre1 : VecRangeMem 7 (sp + 2320#64) f7 ∗
      (PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗
        (PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ memRegion (sp + 32496#64) 512 ∗
          PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest)) ⊢
      VecRangeMem 7 (sp + 2320#64) f7 ∗
        PolyMem (sp + 28368#64) (polyVecNat (lowerInvNtt16 dot)) ∗ R1 := by dsimp only [R1]; sep_frame
  refine SepWP.weaken_pre hpre1 (sepWP_seq_env hcl1 hro1
    (inv8_upper_ok s1 sp hdot f7 R1 hpc1 hrun1 hsp1 hspA1) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx0_2, hx1_2, hx2_2, hx19_2, hx22_2, hfp_2, sp40, hs0, hs5, hP2⟩
  set R2 := SpillSliceMem 7 (sp + 2320#64) sp40 ∗ PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗
    PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest
  have hpre2 : P2 ⊢ memRegion (sp + 32496#64) 512 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ R2 :=
    Entails.trans hP2 (by dsimp only [R1, R2, inv]; sep_frame)
  refine SepWP.weaken_pre hpre2 (sepWP_seq_env hcl2 hro2
    (seg8_add_memcpy hb hbase s2 sp inv R2 hpc2 hrun2 hsp2 hspA2 hx0_2 hx1_2 hx2_2 hx19_2 hcl2) ?_)
  rintro s3 _ hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx19_3, hx22_3, hfp_3, rfl⟩
  set R3 := PolyMem (sp + 32496#64) (polyVecNat inv) ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗
    PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ PolyMem (sp + 33008#64) (polyVecNat err2) ∗ Rest
  have hpre3 : PolyMem (sp + 32496#64) (polyVecNat inv) ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ R2 ⊢
      SpillSliceMem 7 (sp + 2320#64) sp40 ∗ R3 := by dsimp only [R2, R3]; sep_frame
  refine SepWP.weaken_pre hpre3 (sepWP_seq_env hcl3 hro3
    (seg8_add_setup hb s3 sp sp40 R3 hpc3 hrun3 hsp3 hspA3 hx19_3 hs0 hs5) ?_)
  rintro s4 _ hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx8_4, hx9_4, hx10_4, hx11_4, hx12_4, hx13_4, hx22_4, hfp_4, hv16_4, hv17_4, hv18_4, hv19_4, rfl⟩
  set R4 := SpillSliceMem 7 (sp + 2320#64) sp40 ∗ PolyMem (sp + 28368#64) (polyVecNat inv) ∗ Rest
  have hpre4 : SpillSliceMem 7 (sp + 2320#64) sp40 ∗ R3 ⊢
      PolyMem (sp + 32496#64) (polyVecNat inv) ∗ PolyMem (sp + 33008#64) (polyVecNat err2) ∗
        PolyMem (sp + 26320#64) (polyVecNat msgPoly) ∗ R4 := by dsimp only [R3, R4]; sep_frame
  refine SepWP.weaken_pre hpre4 (SepWP.mono
    (seg8_add_loop hb sp (s.readReg64 .x22) (s.readReg64 .fp) inv err2 msgPoly R4 15 0 rfl
      s4 (polyVecNat inv) hpc4 hrun4 hsp4 hspA4 hcl4 hro4
      (by simpa using hx8_4) (by simpa using hx9_4) (by simpa using hx10_4) (by simpa using hx11_4)
      hx12_4 hx13_4
      (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1)))
      (hfp_4.trans (hfp_3.trans (hfp_2.trans hfp_1)))
      hv16_4 hv17_4 hv18_4 hv19_4 (fun _ hj => by omega) (fun _ _ _ => rfl)) ?_)
  rintro sf Pf _ _ ⟨hsp_f, hspA_f, hx22_f, hfp_f, rfl⟩
  refine ⟨hsp_f, hspA_f, hx22_f, hfp_f, ?_⟩
  dsimp only [R4, PolyMem, SpillSliceMem]
  have hm7 := vecRangeMem_entails_memRegion 7 (sp + 2320#64) sp40.get
  have hm26 := vecRangeMem_entails_memRegion 32 (sp + 26320#64) (polyVecNat msgPoly)
  have hm28 := vecRangeMem_entails_memRegion 32 (sp + 28368#64) (polyVecNat inv)
  have hm33 := vecRangeMem_entails_memRegion 32 (sp + 33008#64) (polyVecNat err2)
  exact entails_sub hm7 (by sep_frame)
    (entails_sub hm26 (by sep_frame) (entails_sub hm28 (by sep_frame) (entails_sub hm33 (by sep_frame) (by sep_frame))))

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8InvAdd
