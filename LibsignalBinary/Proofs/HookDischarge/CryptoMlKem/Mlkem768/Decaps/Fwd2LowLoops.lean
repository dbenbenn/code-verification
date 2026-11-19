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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `decapsulate_compressed_key` (`B04`) — Forward NTT Site 2 Low-Stage Loops (`Fwd2_low`)

Steps `+0x8248 → +0x8334` (`len = 4` then `len = 2` of forward NTT on `rHat[i]`), transforming
`PolyMem polyPtr (polyVecNat p)` into `PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p))` while
preserving `Fwd2Preserved`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Fwd2LowLoops

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 dup4hLow lane64 pack2x64)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ld1r4h_ro step_ldrh16_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_stpQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (buildZetaLayer2)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (bv128_or_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdIns_d1_d0 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7
  svc_simdMul_8h svc_simdOrr_16b svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn2_4s svc_simdZip1_2d svc_simdZip2_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure (
  fwdLayer2RawPair fwdLayer2RawPair_eq_polyVecNat
  fwdLayer4RawPair fwdLayer4RawPair_eq_polyVecNat
  fwdNttAfterStage4 fwdNttAfterStage4_size lowerFwdNtt16)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x8248 → 0x8330]
end

attribute [local irreducible]
  blkPC04 zetaTableAt dup8x16 dup4hLow polyVecNat
  simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h simdTrn1_4s simdTrn2_4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdDup_8h_gpr svc_fmov_s_w
  svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4
  svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7 svc_simdIns_d1_d0
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

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

structure Fwd2Preserved (s0 s : State) : Prop where
  v3  : s.readVReg128 3#5 = s0.readVReg128 3#5
  x0  : s.readReg64 .x0  = s0.readReg64 .x0
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x2  : s.readReg64 .x2  = s0.readReg64 .x2
  x3  : s.readReg64 .x3  = s0.readReg64 .x3
  x4  : s.readReg64 .x4  = s0.readReg64 .x4
  x5  : s.readReg64 .x5  = s0.readReg64 .x5
  x7  : s.readReg64 .x7  = s0.readReg64 .x7
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  fp  : s.readReg64 .fp  = s0.readReg64 .fp

@[simp, arm64_norm, wp_norm]
private theorem fwd2Preserved_orFpsr (s0 s : State) (fl : BitVec 32) :
    Fwd2Preserved s0 (s.orFpsr fl) ↔ Fwd2Preserved s0 s := by
  constructor <;>
    rintro ⟨v3, r0, r1, r2, r3, r4, r5, r7, r9, r10, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, rfp⟩ <;>
    exact ⟨by simpa [State.readVReg128_orFpsr] using v3,
      by simpa [State.readReg64_orFpsr] using r0, by simpa [State.readReg64_orFpsr] using r1,
      by simpa [State.readReg64_orFpsr] using r2, by simpa [State.readReg64_orFpsr] using r3,
      by simpa [State.readReg64_orFpsr] using r4, by simpa [State.readReg64_orFpsr] using r5,
      by simpa [State.readReg64_orFpsr] using r7, by simpa [State.readReg64_orFpsr] using r9,
      by simpa [State.readReg64_orFpsr] using r10, by simpa [State.readReg64_orFpsr] using r12,
      by simpa [State.readReg64_orFpsr] using r13, by simpa [State.readReg64_orFpsr] using r14,
      by simpa [State.readReg64_orFpsr] using r15, by simpa [State.readReg64_orFpsr] using r16,
      by simpa [State.readReg64_orFpsr] using r17, by simpa [State.readReg64_orFpsr] using r18,
      by simpa [State.readReg64_orFpsr] using r19, by simpa [State.readReg64_orFpsr] using r20,
      by simpa [State.readReg64_orFpsr] using r21, by simpa [State.readReg64_orFpsr] using rfp⟩

private theorem fwd2_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x8248#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r))
    (hx6 : s.readReg64 .x6 = polyPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (16 - r))
    (hx1 : s.readReg64 .x1 = 62209#64) (hv3 : s.readVReg128 3#5 = dup8x16 3329#16)
    (hpres : Fwd2Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + 0x8248#64 else b + 0x82ac#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * (r + 1)) ∧
        s'.readReg64 .x6 = polyPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x22 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x1 = 62209#64 ∧ s'.readVReg128 0#5 = dup8x16 62209#16 ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ Fwd2Preserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat (fwdNttAfterStage4 p) (2 * r)))
            (2 * r + 1) (polyVecNat (fwdNttAfterStage4 p) (2 * r + 1))) ∗ Rest)) := by
  let k := 32 + 2 * r
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx6]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_step
  refine step_ld1r4h_ro (k := k + 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k + 1)))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_step
  refine step_ld1r4h_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 17
  have hpair := fwdLayer4RawPair_eq_polyVecNat hp r hr
  dsimp only [fwdLayer4RawPair] at hpair
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (fwdNttAfterStage4 p) (2 * r))
    (v2 := polyVecNat (fwdNttAfterStage4 p) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx6]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [k]; rw [← hpair.1]; simp)
    (by dsimp only [k]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  wp_steps 2
  wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx1], by simp, by simp [hv3],
        ⟨by simp [State.readVReg128_orFpsr, hpres.v3],
          by simp [State.readReg64_orFpsr, hpres.x0], by simp [State.readReg64_orFpsr, hpres.x1],
          by simp [State.readReg64_orFpsr, hpres.x2], by simp [State.readReg64_orFpsr, hpres.x3],
          by simp [State.readReg64_orFpsr, hpres.x4], by simp [State.readReg64_orFpsr, hpres.x5],
          by simp [State.readReg64_orFpsr, hpres.x7], by simp [State.readReg64_orFpsr, hpres.x9],
          by simp [State.readReg64_orFpsr, hpres.x10], by simp [State.readReg64_orFpsr, hpres.x12],
          by simp [State.readReg64_orFpsr, hpres.x13], by simp [State.readReg64_orFpsr, hpres.x14],
          by simp [State.readReg64_orFpsr, hpres.x15], by simp [State.readReg64_orFpsr, hpres.x16],
          by simp [State.readReg64_orFpsr, hpres.x17], by simp [State.readReg64_orFpsr, hpres.x18],
          by simp [State.readReg64_orFpsr, hpres.x19], by simp [State.readReg64_orFpsr, hpres.x20],
          by simp [State.readReg64_orFpsr, hpres.x21], by simp [State.readReg64_orFpsr, hpres.fp]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx1], by simp, by simp [hv3],
        ⟨by simp [State.readVReg128_orFpsr, hpres.v3],
          by simp [State.readReg64_orFpsr, hpres.x0], by simp [State.readReg64_orFpsr, hpres.x1],
          by simp [State.readReg64_orFpsr, hpres.x2], by simp [State.readReg64_orFpsr, hpres.x3],
          by simp [State.readReg64_orFpsr, hpres.x4], by simp [State.readReg64_orFpsr, hpres.x5],
          by simp [State.readReg64_orFpsr, hpres.x7], by simp [State.readReg64_orFpsr, hpres.x9],
          by simp [State.readReg64_orFpsr, hpres.x10], by simp [State.readReg64_orFpsr, hpres.x12],
          by simp [State.readReg64_orFpsr, hpres.x13], by simp [State.readReg64_orFpsr, hpres.x14],
          by simp [State.readReg64_orFpsr, hpres.x15], by simp [State.readReg64_orFpsr, hpres.x16],
          by simp [State.readReg64_orFpsr, hpres.x17], by simp [State.readReg64_orFpsr, hpres.x18],
          by simp [State.readReg64_orFpsr, hpres.x19], by simp [State.readReg64_orFpsr, hpres.x20],
          by simp [State.readReg64_orFpsr, hpres.x21], by simp [State.readReg64_orFpsr, hpres.fp]⟩, rfl⟩

private theorem fwd2_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x8248#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r) →
      s.readReg64 .x6 = polyPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x22 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x1 = 62209#64 → s.readVReg128 3#5 = dup8x16 3329#16 →
      Fwd2Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (fwdNttAfterStage4 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x82ac#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 3#5 = dup8x16 3329#16 ∧
          Fwd2Preserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx6 hx22 hx1 hv3 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := fwd2_layer4_iter hb s0 s sp polyPtr hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx6 hx22 hx1 hv3 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hv0', hv3', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv0', hv3', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx6 hx22 hx1 hv3 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := fwd2_layer4_iter hb s0 s sp polyPtr hp (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx6 hx22 hx1 hv3 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx6_m, hx22_m, hx1_m, _, hv3_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx6_m hx22_m hx1_m hv3_m hpres_m hlo' hhi'

private theorem fwd2_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr r21 r10 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r21 + r10 = polyPtr + 16#64) {r : Nat} (hr : r < 16)
    (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x82b8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx6 : s.readReg64 .x6 = r10 + BitVec.ofNat 64 (32 * r))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (16 - r))
    (hx21 : s.readReg64 .x21 = r21)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv3 : s.readVReg128 3#5 = dup8x16 3329#16)
    (hpres : Fwd2Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonNttStage16 2 64 q).1
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + 0x82b8#64 else b + 0x8334#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x6 = r10 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x22 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x21 = r21 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 3#5 = dup8x16 3329#16 ∧
        Fwd2Preserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat q' (2 * r)))
            (2 * r + 1) (polyVecNat q' (2 * r + 1))) ∗ Rest)) := by
  intro q'
  let k := 64 + 4 * r
  refine step_ldrh16_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k)) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 3
  refine step_ldrh16_ro (k := k + 2) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k + 2)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldrh16_ro (k := k + 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k + 1)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  refine step_ldrh16_ro (k := k + 3) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k + 3)))
    (wb := some (.x8, mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1))))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx8]; refine ⟨by dsimp [k]; clear * - hr; bv_omega, by clear * - hr; bv_omega⟩)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 4
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q (2 * r)) (v2 := polyVecNat q (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hsum hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 15
  have hpair := fwdLayer2RawPair_eq_polyVecNat hq r hr
  dsimp only [fwdLayer2RawPair, buildZetaLayer2] at hpair
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q' (2 * r)) (v2 := polyVecNat q' (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hsum hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [q', k]; rw [← hpair.1]; simp)
    (by dsimp only [q', k]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  wp_step
  wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx21], by simp [hv0], by simp [hv3],
        ⟨by simp [State.readVReg128_orFpsr, hpres.v3],
          by simp [State.readReg64_orFpsr, hpres.x0], by simp [State.readReg64_orFpsr, hpres.x1],
          by simp [State.readReg64_orFpsr, hpres.x2], by simp [State.readReg64_orFpsr, hpres.x3],
          by simp [State.readReg64_orFpsr, hpres.x4], by simp [State.readReg64_orFpsr, hpres.x5],
          by simp [State.readReg64_orFpsr, hpres.x7], by simp [State.readReg64_orFpsr, hpres.x9],
          by simp [State.readReg64_orFpsr, hpres.x10], by simp [State.readReg64_orFpsr, hpres.x12],
          by simp [State.readReg64_orFpsr, hpres.x13], by simp [State.readReg64_orFpsr, hpres.x14],
          by simp [State.readReg64_orFpsr, hpres.x15], by simp [State.readReg64_orFpsr, hpres.x16],
          by simp [State.readReg64_orFpsr, hpres.x17], by simp [State.readReg64_orFpsr, hpres.x18],
          by simp [State.readReg64_orFpsr, hpres.x19], by simp [State.readReg64_orFpsr, hpres.x20],
          by simp [State.readReg64_orFpsr, hpres.x21], by simp [State.readReg64_orFpsr, hpres.fp]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp [hr_eq], by simp [hr_eq], by simp [hx21],
        by simp [hv0], by simp [hv3],
        ⟨by simp [State.readVReg128_orFpsr, hpres.v3],
          by simp [State.readReg64_orFpsr, hpres.x0], by simp [State.readReg64_orFpsr, hpres.x1],
          by simp [State.readReg64_orFpsr, hpres.x2], by simp [State.readReg64_orFpsr, hpres.x3],
          by simp [State.readReg64_orFpsr, hpres.x4], by simp [State.readReg64_orFpsr, hpres.x5],
          by simp [State.readReg64_orFpsr, hpres.x7], by simp [State.readReg64_orFpsr, hpres.x9],
          by simp [State.readReg64_orFpsr, hpres.x10], by simp [State.readReg64_orFpsr, hpres.x12],
          by simp [State.readReg64_orFpsr, hpres.x13], by simp [State.readReg64_orFpsr, hpres.x14],
          by simp [State.readReg64_orFpsr, hpres.x15], by simp [State.readReg64_orFpsr, hpres.x16],
          by simp [State.readReg64_orFpsr, hpres.x17], by simp [State.readReg64_orFpsr, hpres.x18],
          by simp [State.readReg64_orFpsr, hpres.x19], by simp [State.readReg64_orFpsr, hpres.x20],
          by simp [State.readReg64_orFpsr, hpres.x21], by simp [State.readReg64_orFpsr, hpres.fp]⟩, rfl⟩

private theorem fwd2_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp polyPtr r21 r10 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r21 + r10 = polyPtr + 16#64) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x82b8#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x6 = r10 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x22 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x21 = r21 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 3#5 = dup8x16 3329#16 →
      Fwd2Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonNttStage16 2 64 q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x8334#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ Fwd2Preserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (neonNttStage16 2 64 q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx6 hx22 hx21 hv0 hv3 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := fwd2_layer2_iter hb s0 s sp polyPtr r21 r10 hq hsum (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx6 hx22 hx21 hv0 hv3 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx6 hx22 hx21 hv0 hv3 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := fwd2_layer2_iter hb s0 s sp polyPtr r21 r10 hq hsum (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx6 hx22 hx21 hv0 hv3 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx6_m, hx22_m, hx21_m, hv0_m, hv3_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx6_m hx22_m hx21_m hv0_m hv3_m hpres_m hlo' hhi'

theorem fwd2_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + 0x8248#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx2 : s.readReg64 .x2 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx6 : s.readReg64 .x6 = polyPtr + 16#64) (hx22 : s.readReg64 .x22 = 16#64)
    (hx1 : s.readReg64 .x1 = 62209#64)
    (hsum : s.readReg64 .x21 + s.readReg64 .x10 = polyPtr + 16#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 3329#16) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x8334#64) s
      (PolyMem polyPtr (polyVecNat p) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Fwd2Preserved s s' ∧
        P' = (PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p)) ∗ Rest)) := by
  have _ : b = blkPl04.base := hb
  have hpres0 : Fwd2Preserved s s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
     rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine sepWP_seq_env hcl hro
    (fwd2_layer4_loop hb s sp polyPtr hp Rest 15 0 rfl s (polyVecNat p)
      hpc hrun hsp hspA hcl hro hx8 hx6 hx22 hx1 hv3 hpres0
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hv0_1, hv3_1, hpres1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1 (mid := b + 0x82b8#64)
    (post1 := fun s2 P2 =>
      s2.sp = sp ∧ s2.spAligned = true ∧
      s2.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 134#64 ∧
      s2.readReg64 .x6 = s.readReg64 .x10 + BitVec.ofNat 64 0 ∧
      s2.readReg64 .x22 = 16#64 ∧ s2.readReg64 .x21 = s.readReg64 .x21 ∧
      s2.readVReg128 0#5 = dup8x16 62209#16 ∧ s2.readVReg128 3#5 = dup8x16 3329#16 ∧
      Fwd2Preserved s s2 ∧
      P2 = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
        ⟨by simp [hsp1], by simpa [State.spAligned] using hspA1,
          by simp [hpres1.x2, hx2], by simp [hpres1.x10],
          by simp, by simp [hpres1.x21],
          by simp [hv0_1], by simp [hv3_1],
          ⟨by simp [hpres1.v3], by simp [hpres1.x0], by simp [hpres1.x1],
           by simp [hpres1.x2], by simp [hpres1.x3], by simp [hpres1.x4],
           by simp [hpres1.x5], by simp [hpres1.x7], by simp [hpres1.x9],
           by simp [hpres1.x10], by simp [hpres1.x12], by simp [hpres1.x13],
           by simp [hpres1.x14], by simp [hpres1.x15], by simp [hpres1.x16],
           by simp [hpres1.x17], by simp [hpres1.x18], by simp [hpres1.x19],
           by simp [hpres1.x20], by simp [hpres1.x21], by simp [hpres1.fp]⟩, rfl⟩) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx6_2, hx22_2, hx21_2, hv0_2, hv3_2, hpres2, hP2⟩
  subst hP2
  exact fwd2_layer2_loop hb s sp polyPtr (s.readReg64 .x21) (s.readReg64 .x10)
    ((fwdNttAfterStage4_size p).trans hp) hsum Rest 15 0 rfl s2 _
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx6_2 hx22_2 hx21_2 hv0_2 hv3_2 hpres2
    (fun _ h => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Fwd2LowLoops
