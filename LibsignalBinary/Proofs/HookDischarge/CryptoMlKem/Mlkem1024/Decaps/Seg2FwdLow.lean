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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `kyber_decapsulate` (`B06`) — Segment 2 Forward NTT Low-Stage Loops (`+0x14a8 .. +0x159c`)

Steps the lower 2 stages (`len = 4` then `len = 2`) of forward NTT in `Seg2` (`uHat[0..3]`):
transforms `PolyMem polyPtr (polyVecNat p)` into `PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p))`,
loads `x0 := nextCtA` from `[sp + 2416]`, and preserves `Seg2FwdPreserved`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2FwdLow

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl resolve_ro00)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ld1r4h_ro step_ldrh16_ro)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 polyVecNat step_ldpQ128 step_stpQ128 vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (buildZetaLayer2)
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
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x14a8 → 0x1598]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible]
  blkPC06 zetaTableAt dup8x16 dup4hLow polyVecNat
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

@[expose] def Seg2FwdPreserved (s0 s : State) : Prop :=
  s.readVReg128 8#5 = s0.readVReg128 8#5 ∧
  s.readVReg128 11#5 = s0.readVReg128 11#5 ∧
  s.readReg64 .fp = s0.readReg64 .fp ∧
  s.readReg64 .x19 = s0.readReg64 .x19 ∧ s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧ s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28

@[simp, arm64_norm, wp_norm]
private theorem seg2FwdPreserved_orFpsr (s0 s : State) (fl : BitVec 32) :
    Seg2FwdPreserved s0 (s.orFpsr fl) ↔ Seg2FwdPreserved s0 s := by
  simp [Seg2FwdPreserved]

private theorem seg2_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x14a8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r))
    (hx9 : s.readReg64 .x9 = polyPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 - r))
    (hx28 : s.readReg64 .x28 = 62209#64) (hv11 : s.readVReg128 11#5 = dup8x16 3329#16)
    (hpres : Seg2FwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x14a8#64 else b + 0x150c#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * (r + 1)) ∧
        s'.readReg64 .x9 = polyPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x10 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x28 = 62209#64 ∧ s'.readVReg128 0#5 = dup8x16 62209#16 ∧
        s'.readVReg128 11#5 = dup8x16 3329#16 ∧ Seg2FwdPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat (fwdNttAfterStage4 p) (2 * r)))
            (2 * r + 1) (polyVecNat (fwdNttAfterStage4 p) (2 * r + 1))) ∗ Rest)) := by
  let k := 32 + 2 * r
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
    (by simp [evalAddrMode, hx9]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
        by simp; clear * - hr15; bv_omega, by simp [hx28], by simp, by simp [hv11],
        by simpa [Seg2FwdPreserved] using hpres, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx28], by simp, by simp [hv11],
        by simpa [Seg2FwdPreserved] using hpres, rfl⟩

private theorem seg2_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x14a8#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r) →
      s.readReg64 .x9 = polyPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x10 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x28 = 62209#64 → s.readVReg128 11#5 = dup8x16 3329#16 →
      Seg2FwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (fwdNttAfterStage4 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x150c#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 11#5 = dup8x16 3329#16 ∧
          Seg2FwdPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx28 hv11 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg2_layer4_iter hb s0 s sp polyPtr hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx28 hv11 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hv0', hv11', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv0', hv11', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx28 hv11 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := seg2_layer4_iter hb s0 s sp polyPtr hp (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx28 hv11 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hx28_m, _, hv11_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hx28_m hv11_m hpres_m hlo' hhi'

private theorem seg2_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp polyPtr x0Val r19 r24 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r19 + r24 = polyPtr + 16#64) {r : Nat} (hr : r < 16)
    (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x1520#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = x0Val)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx9 : s.readReg64 .x9 = r24 + BitVec.ofNat 64 (32 * r))
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (16 - r))
    (hx19 : s.readReg64 .x19 = r19)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv11 : s.readVReg128 11#5 = dup8x16 3329#16)
    (hpres : Seg2FwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonNttStage16 2 64 q).1
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x1520#64 else b + 0x159c#64) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x0 = x0Val ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x9 = r24 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x10 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x19 = r19 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 11#5 = dup8x16 3329#16 ∧
        Seg2FwdPreserved s0 s' ∧
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
  rcases hpres with ⟨hp8, hp11, hpfp, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28⟩
  wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hx0],
        by simp, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx19], by simp [hv0], by simp [hv11],
        ⟨by simp [hp8], by simp [hp11], by simp [hpfp], by simp [hp19], by simp [hp20],
          by simp [hp21], by simp [hp22], by simp [hp23], by simp [hp24],
          by simp [hp25], by simp [hp26], by simp [hp27], by simp [hp28]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp [hx0],
        by simp, by simp [hr_eq], by simp [hr_eq], by simp [hx19],
        by simp [hv0], by simp [hv11],
        ⟨by simp [hp8], by simp [hp11], by simp [hpfp], by simp [hp19], by simp [hp20],
          by simp [hp21], by simp [hp22], by simp [hp23], by simp [hp24],
          by simp [hp25], by simp [hp26], by simp [hp27], by simp [hp28]⟩, rfl⟩

private theorem seg2_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp polyPtr x0Val r19 r24 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r19 + r24 = polyPtr + 16#64) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x1520#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x0 = x0Val →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x9 = r24 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x10 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x19 = r19 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 11#5 = dup8x16 3329#16 →
      Seg2FwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonNttStage16 2 64 q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x159c#64) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x0 = x0Val ∧
          Seg2FwdPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (neonNttStage16 2 64 q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx0 hx8 hx9 hx10 hx19 hv0 hv11 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg2_layer2_iter hb s0 s sp polyPtr x0Val r19 r24 hq hsum (r := 15) (by omega)
      f Rest hpc hrun hsp hspA hro hx0 hx8 hx9 hx10 hx19 hv0 hv11 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', hx0', _, _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hx0', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx0 hx8 hx9 hx10 hx19 hv0 hv11 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := seg2_layer2_iter hb s0 s sp polyPtr x0Val r19 r24 hq hsum (by omega) f Rest
      hpc hrun hsp hspA hro hx0 hx8 hx9 hx10 hx19 hv0 hv11 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx0_m, hx8_m, hx9_m, hx10_m, hx19_m, hv0_m, hv11_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx0_m hx8_m hx9_m hx10_m hx19_m hv0_m hv11_m hpres_m hlo' hhi'

open SepProp in
theorem seg2_fwd_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp polyPtr nextCt : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + 0x14a8#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx9 : s.readReg64 .x9 = polyPtr + 16#64) (hx10 : s.readReg64 .x10 = 16#64)
    (hx28 : s.readReg64 .x28 = 62209#64)
    (hsum : s.readReg64 .x19 + s.readReg64 .x24 = polyPtr + 16#64)
    (hv11 : s.readVReg128 11#5 = dup8x16 3329#16) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x159c#64) s
      (PolyMem polyPtr (polyVecNat p) ∗ ((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x0 = nextCt ∧
        Seg2FwdPreserved s s' ∧
        P' = (PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p)) ∗
          ((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  have hpres0 : Seg2FwdPreserved s s :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine sepWP_seq_env hcl hro
    (seg2_layer4_loop hb s sp polyPtr hp (((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest) 15 0 rfl
      s (polyVecNat p) hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx28 hv11 hpres0
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hv0_1, hv11_1, hpres1, hP1⟩
  subst hP1
  rcases hpres1 with ⟨hp8, hp11, hpfp, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28⟩
  refine sepWP_seq_env hcl1 hro1 (mid := b + 0x1520#64)
    (post1 := fun s2 P2 =>
      s2.sp = sp ∧ s2.spAligned = true ∧
      s2.readReg64 .x0 = nextCt ∧
      s2.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 134#64 ∧
      s2.readReg64 .x9 = s.readReg64 .x24 + BitVec.ofNat 64 0 ∧
      s2.readReg64 .x10 = 16#64 ∧ s2.readReg64 .x19 = s.readReg64 .x19 ∧
      s2.readVReg128 0#5 = dup8x16 62209#16 ∧ s2.readVReg128 11#5 = dup8x16 3329#16 ∧
      Seg2FwdPreserved s s2 ∧
      P2 = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗
        ((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun1])
        ⟨by simp [hsp1], by simpa [State.spAligned] using hspA1,
          by simp, by simp, by simp, by simp, by simp [hp19],
          by simp [hv0_1], by simp [hv11_1],
          ⟨by simp [hp8], by simp [hp11], by simp [hpfp], by simp [hp19], by simp [hp20],
            by simp [hp21], by simp [hp22], by simp [hp23], by simp [hp24],
            by simp [hp25], by simp [hp26], by simp [hp27], by simp [hp28]⟩, rfl⟩) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx0_2, hx8_2, hx9_2, hx10_2, hx19_2, hv0_2, hv11_2, hpres2, hP2⟩
  subst hP2
  exact seg2_layer2_loop hb s sp polyPtr nextCt (s.readReg64 .x19) (s.readReg64 .x24)
    ((fwdNttAfterStage4_size p).trans hp) hsum (((sp + 2416#64) ↦₆₄ nextCt) ∗ Rest)
    15 0 rfl s2 _ hpc2 hrun2 hsp2 hspA2 hcl2 hro2
    hx0_2 hx8_2 hx9_2 hx10_2 hx19_2 hv0_2 hv11_2 hpres2
    (fun _ h => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2FwdLow
