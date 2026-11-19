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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `decapsulate_compressed_key` (`B04`) — Site 2 Inverse NTT Low-Stage Loops (`+0x90c0 → +0x91d4`)

Steps the lower 2 stages (`len = 2` then `len = 4`) of `invert_ntt_montgomery` on
`PolyMem polyPtr` at Site 2 (`+0x90c0 → +0x91d4`, inside the 3-iteration `u'` outer loop),
producing `PolyMem polyPtr (polyVecNat (lowerInvNtt16 dot))` while setting `v17 = dup8x16 20159#16`
and preserving `v0, v16, v18, v23, v27` and `Inv2Preserved`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv2LowLoops

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_ro00)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonInvNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMla8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ld1r4h_ro step_ldrh16_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_stpQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (bv128_or_self)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdIns_d1_d0 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4 svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7
  svc_simdMla_8h svc_simdMul_8h svc_simdOrr_16b svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdSshr_8h_11 svc_simdSub_8h svc_simdTrn1_4s svc_simdTrn2_4s
  svc_simdZip1_2d svc_simdZip2_2d)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZetaLayer2 invNttAfterStage2 invNttAfterStage2_size
  layer2RawPair layer2RawPair_eq_polyVecNat
  layer4RawPair layer4RawPair_eq_polyVecNat lowerInvNtt16)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x90c0 → 0x91d0]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem readReg64_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg64 r = s.readReg64 r := State.readReg64_orFpsr s fl r

@[simp, arm64_norm, wp_norm]
private theorem readReg32_orFpsr' (s : State) (fl : BitVec 32) (r : Reg) :
    (s.orFpsr fl).readReg32 r = s.readReg32 r := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem readReg_orFpsr' (s : State) (fl : BitVec 32) (w : Width) (r : Reg) :
    (s.orFpsr fl).readReg w r = s.readReg w r := by cases s; cases w <;> rfl

@[simp, arm64_norm, wp_norm]
private theorem readVReg128_orFpsr' (s : State) (fl : BitVec 32) (r : BitVec 5) :
    (s.orFpsr fl).readVReg128 r = s.readVReg128 r := State.readVReg128_orFpsr s fl r

@[simp, arm64_norm, wp_norm]
private theorem status_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).status = s.status := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem pc_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pc = s.pc := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem sp_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).sp = s.sp := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem spAligned_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).spAligned = s.spAligned := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem pstate_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).pstate = s.pstate := by cases s; rfl

@[simp, arm64_norm, wp_norm]
private theorem mem_orFpsr' (s : State) (fl : BitVec 32) :
    (s.orFpsr fl).mem = s.mem := by cases s; rfl

attribute [local irreducible]
  blkPC04 zetaTableAt dup8x16 dup4hLow polyVecNat
  simdAdd8h simdSub8h simdMul8h simdMla8h simdSqdmulh8h simdSshr8h
  simdTrn1_4s simdTrn2_4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdMla_8h svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSshr_8h_11
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

/-- Outer-loop GPRs and `v0` untouched by `Inv2_low` (`+0x90c0 → +0x91d4`). -/
structure Inv2Preserved (s0 s : State) : Prop where
  x0  : s.readReg64 .x0  = s0.readReg64 .x0
  x3  : s.readReg64 .x3  = s0.readReg64 .x3
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x26 : s.readReg64 .x26 = s0.readReg64 .x26
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5 = s0.readVReg128 0#5

private theorem inv2_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr basePtr off10 : BitVec 64) (hbase : basePtr + off10 = polyPtr + 16#64)
    {p : Poly16} (hp : p.size = 256) {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x90d0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = 20159#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (16 - r))
    (hx12 : s.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r))
    (hx14 : s.readReg64 .x14 = off10 + BitVec.ofNat 64 (32 * r))
    (hx20 : s.readReg64 .x20 = basePtr)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Inv2Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + 0x90d0#64 else b + 0x9164#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x0 = 20159#64 ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * (r + 1)) ∧
        s'.readReg64 .x14 = off10 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x20 = basePtr ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        s'.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat (invNttAfterStage2 p) (2 * r)))
            (2 * r + 1) (polyVecNat (invNttAfterStage2 p) (2 * r + 1))) ∗ Rest)) := by
  rcases hpres with ⟨p0, p3, p8, p9, p10, p11, p13, p15, p16, p17,
    p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp, pv0⟩
  let k := 127 - 4 * r
  refine step_ldrh16_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k)) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx12]; dsimp [k]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hbase hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 6
  refine step_ldrh16_ro (k := k - 2) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 2)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx12]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 6
  refine step_ldrh16_ro (k := k - 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 1)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx12]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
  refine step_ldrh16_ro (k := k - 3) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 3)))
    (wb := none) (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx12]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 14
  have hpair := layer2RawPair_eq_polyVecNat hp r hr
  dsimp only [layer2RawPair, buildZetaLayer2] at hpair
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat (invNttAfterStage2 p) (2 * r))
    (v2 := polyVecNat (invNttAfterStage2 p) (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hbase hr; bv_omega) (by clear * -; bv_omega)
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
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hx0],
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx20],
        by simp [hv16], by simp, by simp [hv18], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
         by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
         by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p26],
         by simp [p27], by simp [p28], by simp [pfp], by simp [pv0]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt; clear * - hne hr hlt; bv_omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hx0],
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq], by simp [hx20],
        by simp [hv16], by simp, by simp [hv18], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
         by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
         by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p26],
         by simp [p27], by simp [p28], by simp [pfp], by simp [pv0]⟩, rfl⟩

private theorem inv2_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp polyPtr basePtr off10 : BitVec 64) (hbase : basePtr + off10 = polyPtr + 16#64)
    {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x90d0#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x0 = 20159#64 →
      s.readReg64 .x2 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (254 - 8 * r) →
      s.readReg64 .x14 = off10 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x20 = basePtr →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 18#5 = dup8x16 62209#16 →
      s.readVReg128 23#5 = dup8x16 0xf2ff#16 → s.readVReg128 27#5 = dup8x16 1024#16 →
      Inv2Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (invNttAfterStage2 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x9164#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
          s'.readVReg128 18#5 = dup8x16 62209#16 ∧ s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
          s'.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (invNttAfterStage2 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx0 hx2 hx12 hx14 hx20 hv16 hv18 hv23 hv27 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv2_layer2_iter hb s0 s sp polyPtr basePtr off10 hbase hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx0 hx2 hx12 hx14 hx20 hv16 hv18 hv23 hv27 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, hv16', hv17', hv18', hv23', hv27', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv16', hv17', hv18', hv23', hv27', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx0 hx2 hx12 hx14 hx20 hv16 hv18 hv23 hv27 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := inv2_layer2_iter hb s0 s sp polyPtr basePtr off10 hbase hp (by omega) f Rest
      hpc hrun hsp hspA hro hx0 hx2 hx12 hx14 hx20 hv16 hv18 hv23 hv27 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx0_m, hx2_m, hx12_m, hx14_m, hx20_m, hv16_m, _hv17_m, hv18_m, hv23_m, hv27_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx0_m hx2_m hx12_m hx14_m hx20_m hv16_m hv18_m hv23_m hv27_m hpres_m hlo' hhi'

private theorem inv2_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {q : Poly16} (hq : q.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x9174#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx12 : s.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r))
    (hx14 : s.readReg64 .x14 = polyPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx18 : s.readReg64 .x18 = BitVec.ofNat 64 (16 - r))
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv17 : s.readVReg128 17#5 = dup8x16 20159#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16)
    (hpres : Inv2Preserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonInvNttStage16 4 63 false q).1
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + 0x9174#64 else b + 0x91d4#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * (r + 1)) ∧
        s'.readReg64 .x14 = polyPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x18 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        s'.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat q' (2 * r)))
            (2 * r + 1) (polyVecNat q' (2 * r + 1))) ∗ Rest)) := by
  intro q'
  rcases hpres with ⟨p0, p3, p8, p9, p10, p11, p13, p15, p16, p17,
    p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp, pv0⟩
  let k := 63 - 2 * r
  wp_step
  refine step_ld1r4h_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [hx12]; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_step
  refine step_ld1r4h_ro (k := k - 1) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (k - 1)))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp; dsimp [k]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q (2 * r)) (v2 := polyVecNat q (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx14]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 16
  have hpair := layer4RawPair_eq_polyVecNat hq r hr
  dsimp only [layer4RawPair] at hpair
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q' (2 * r)) (v2 := polyVecNat q' (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx14]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [q', k]; rw [← hpair.1]; simp) (by dsimp only [q', k]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'; wp_steps 2; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega,
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
         by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
         by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p26],
         by simp [p27], by simp [p28], by simp [pfp], by simp [pv0]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt; clear * - hne hr hlt; bv_omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hv16], by simp [hv17], by simp [hv18], by simp [hv23], by simp [hv27],
        ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
         by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
         by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p26],
         by simp [p27], by simp [p28], by simp [pfp], by simp [pv0]⟩, rfl⟩

private theorem inv2_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp polyPtr : BitVec 64) {q : Poly16} (hq : q.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x9174#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x12 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (126 - 4 * r) →
      s.readReg64 .x14 = polyPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x18 = BitVec.ofNat 64 (16 - r) →
      s.readVReg128 16#5 = dup8x16 3329#16 → s.readVReg128 17#5 = dup8x16 20159#16 →
      s.readVReg128 18#5 = dup8x16 62209#16 → s.readVReg128 23#5 = dup8x16 0xf2ff#16 →
      s.readVReg128 27#5 = dup8x16 1024#16 → Inv2Preserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonInvNttStage16 4 63 false q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x91d4#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
          s'.readVReg128 18#5 = dup8x16 62209#16 ∧ s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
          s'.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (neonInvNttStage16 4 63 false q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx12 hx14 hx18 hv16 hv17 hv18 hv23 hv27 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := inv2_layer4_iter hb s0 s sp polyPtr hq (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx12 hx14 hx18 hv16 hv17 hv18 hv23 hv27 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, hv16', hv17', hv18', hv23', hv27', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv16', hv17', hv18', hv23', hv27', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx12 hx14 hx18 hv16 hv17 hv18 hv23 hv27 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := inv2_layer4_iter hb s0 s sp polyPtr hq (by omega) f Rest
      hpc hrun hsp hspA hro hx12 hx14 hx18 hv16 hv17 hv18 hv23 hv27 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx12_m, hx14_m, hx18_m, hv16_m, hv17_m, hv18_m, hv23_m, hv27_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx12_m hx14_m hx18_m hv16_m hv17_m hv18_m hv23_m hv27_m hpres_m hlo' hhi'

theorem inv2_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s : State) (sp polyPtr basePtr off10 : BitVec 64) (hbase : basePtr + off10 = polyPtr + 16#64)
    {dot : Poly16} (hdot : dot.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + 0x90c0#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = 20159#64) (hx8 : s.readReg64 .x8 = polyPtr + 16#64)
    (hx10 : s.readReg64 .x10 = off10) (hx20 : s.readReg64 .x20 = basePtr)
    (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16)
    (hv23 : s.readVReg128 23#5 = dup8x16 0xf2ff#16)
    (hv27 : s.readVReg128 27#5 = dup8x16 1024#16) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x91d4#64) s
      (PolyMem polyPtr (polyVecNat dot) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 17#5 = dup8x16 20159#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ s'.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
        s'.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s s' ∧
        P' = (PolyMem polyPtr (polyVecNat (lowerInvNtt16 dot)) ∗ Rest)) := by
  have _ : b = blkPl04.base := hb
  refine sepWP_seq_env hcl hro (mid := b + 0x90d0#64)
    (post1 := fun s1 P1 =>
      s1.sp = sp ∧ s1.spAligned = true ∧ s1.readReg64 .x0 = 20159#64 ∧
      s1.readReg64 .x2 = 16#64 ∧ s1.readReg64 .x12 = mlkemMpl.ρ ro00Sym + 254#64 ∧
      s1.readReg64 .x14 = off10 ∧ s1.readReg64 .x20 = basePtr ∧
      s1.readVReg128 16#5 = dup8x16 3329#16 ∧ s1.readVReg128 18#5 = dup8x16 62209#16 ∧
      s1.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧ s1.readVReg128 27#5 = dup8x16 1024#16 ∧
      Inv2Preserved s s1 ∧ P1 = (PolyMem polyPtr (polyVecNat dot) ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
        ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
          by simp [hx0], by simp, by simp, by simp, by simp [hx20],
          by simp [hv16], by simp [hv18], by simp [hv23], by simp [hv27],
          ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp,
           by simp, by simp, by simp, by simp, by simp, by simp, by simp,
           by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩, rfl⟩) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx0_1, hx2_1, hx12_1, hx14_1, hx20_1, hv16_1, hv18_1, hv23_1, hv27_1, hpres1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1
    (inv2_layer2_loop hb s sp polyPtr basePtr off10 hbase hdot Rest 15 0 rfl s1 (polyVecNat dot)
      hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx0_1 hx2_1 (by simpa using hx12_1) (by simpa using hx14_1)
      hx20_1 hv16_1 hv18_1 hv23_1 hv27_1 hpres1
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hv16_2, hv17_2, hv18_2, hv23_2, hv27_2, hpres2, hP2⟩
  subst hP2
  rcases hpres2 with ⟨p0, p3, p8, p9, p10, p11, p13, p15, p16, p17,
    p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp, pv0⟩
  refine sepWP_seq_env hcl2 hro2 (mid := b + 0x9174#64)
    (post1 := fun s3 P3 =>
      s3.sp = sp ∧ s3.spAligned = true ∧
      s3.readReg64 .x12 = mlkemMpl.ρ ro00Sym + 126#64 ∧
      s3.readReg64 .x14 = polyPtr + 16#64 ∧ s3.readReg64 .x18 = 16#64 ∧
      s3.readVReg128 16#5 = dup8x16 3329#16 ∧ s3.readVReg128 17#5 = dup8x16 20159#16 ∧
      s3.readVReg128 18#5 = dup8x16 62209#16 ∧ s3.readVReg128 23#5 = dup8x16 0xf2ff#16 ∧
      s3.readVReg128 27#5 = dup8x16 1024#16 ∧ Inv2Preserved s s3 ∧
      P3 = (PolyMem polyPtr (polyVecNat (invNttAfterStage2 dot)) ∗ Rest))
    (by
      have hx8_2 : s2.readReg64 .x8 = polyPtr + 16#64 := p8.trans hx8
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun2])
        ⟨by simp [hsp2], by simpa [State.spAligned] using hspA2,
          by simp, by simp, by simp,
          by simp [hv16_2], by simp [hv17_2], by simp [hv18_2], by simp [hv23_2], by simp [hv27_2],
          ⟨by simp [p0], by simp [p3], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
           by simp [p13], by simp [p15], by simp [p16], by simp [p17], by simp [p19], by simp [p20],
           by simp [p21], by simp [p22], by simp [p23], by simp [p24], by simp [p25], by simp [p26],
           by simp [p27], by simp [p28], by simp [pfp], by simp [pv0]⟩, rfl⟩) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx12_3, hx14_3, hx18_3, hv16_3, hv17_3, hv18_3, hv23_3, hv27_3, hpres3, hP3⟩
  subst hP3
  exact inv2_layer4_loop hb s sp polyPtr (invNttAfterStage2_size hdot) Rest 15 0 rfl s3 _
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 (by simpa using hx12_3) (by simpa using hx14_3) hx18_3
    hv16_3 hv17_3 hv18_3 hv23_3 hv27_3 hpres3
    (fun _ h => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Inv2LowLoops
