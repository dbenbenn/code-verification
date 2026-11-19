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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.FwdLowPure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `generate_keypair_compressed` (`B05`): forward NTT low-stage loops

Steps both `sHat` (`+0x453c → +0x4628`) and `eHat` (`+0x58d8 → +0x59c0`) low-stage (`len = 4` then
`len = 2`) forward NTT loops, transforming `PolyMem polyPtr (polyVecNat p)` into
`PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p))`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow

open Arm64 Arm64.Obj ProofLib
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Ntt (neonNttStage16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16 dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMul8h simdSqdmulh8h simdSshr8h simdSub8h simdTrn1_4s simdTrn2_4s)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)

theorem step_bCond_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = true) (hdst : pc + off = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        simp [wp_norm, arm64_norm, hcond, hdst])
    rfl hnext

theorem step_bCond_not_taken {P : Program} {target_pc pc off dst : BitVec 64}
    {c : CondCode} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : P.fetch pc = some (.bCond c off))
    (hcond : ConditionHolds c s.pstate = false) (hdst : pc + 4#64 = dst)
    (hnext : SepWP P target_pc (s.setPC dst) Pre post oom) :
    SepWP P target_pc s Pre post oom :=
  SepWP.step_pure (s' := s.setPC dst) hpc hrun hfetch
    (by rw [_root_.Arm64.Program.evalInst_of_isSvc0Instr_false _ (.bCond c off) _ rfl]
        cases s; subst hpc; subst hdst
        simp [wp_norm, arm64_norm, hcond, State.advancePC, State.setPC])
    rfl hnext

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x453c → 0x4628, 0x58d8 → 0x59c0]
end

attribute [local irreducible]
  blkPC05 zetaTableAt dup8x16 dup4hLow polyVecNat
  simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h simdTrn1_4s simdTrn2_4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdOrr_16b
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdDup_8h_gpr svc_fmov_s_w
  svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3 svc_simdIns_h4
  svc_simdIns_h5 svc_simdIns_h6 svc_simdIns_h7 svc_simdIns_d1_d0
  svc_simdTrn1_4s svc_simdTrn2_4s svc_simdZip1_2d svc_simdZip2_2d

@[simp, arm64_norm, wp_norm] abbrev offSFwd4   : BitVec 64 := BitVec.ofNat 64 17724
@[simp, arm64_norm, wp_norm] abbrev offSFwdMid : BitVec 64 := BitVec.ofNat 64 17824
@[simp, arm64_norm, wp_norm] abbrev offSFwd2   : BitVec 64 := BitVec.ofNat 64 17836
@[simp, arm64_norm, wp_norm] abbrev offSFwdEnd : BitVec 64 := BitVec.ofNat 64 17960

@[simp, arm64_norm, wp_norm] abbrev offEFwd4   : BitVec 64 := BitVec.ofNat 64 22744
@[simp, arm64_norm, wp_norm] abbrev offEFwdMid : BitVec 64 := BitVec.ofNat 64 22844
@[simp, arm64_norm, wp_norm] abbrev offEFwd2   : BitVec 64 := BitVec.ofNat 64 22852
@[simp, arm64_norm, wp_norm] abbrev offEFwdEnd : BitVec 64 := BitVec.ofNat 64 22976

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
    · by_cases h0 : j = 2 * r
      · subst h0; simp
      · simp [Function.update_of_ne h1, Function.update_of_ne h0, hlo j (by omega)]
  · simp [Function.update_of_ne (by omega : j ≠ 2 * r + 1),
      Function.update_of_ne (by omega : j ≠ 2 * r), hhi j (by omega) hj2]

private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g :=
  vecRangeMem_congr h

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

/-! ## 1. `sHat` Low-Stage Forward NTT (`+0x453c → +0x4628`) -/

structure SHatFwdPreserved (s0 s : State) : Prop where
  v3  : s.readVReg128 3#5 = s0.readVReg128 3#5
  x0  : s.readReg64 .x0 = s0.readReg64 .x0
  x1  : s.readReg64 .x1 = s0.readReg64 .x1
  x2  : s.readReg64 .x2 = s0.readReg64 .x2
  x3  : s.readReg64 .x3 = s0.readReg64 .x3
  x4  : s.readReg64 .x4 = s0.readReg64 .x4
  x5  : s.readReg64 .x5 = s0.readReg64 .x5
  x6  : s.readReg64 .x6 = s0.readReg64 .x6
  x9  : s.readReg64 .x9 = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x20 : s.readReg64 .x20 = s0.readReg64 .x20
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  fp  : s.readReg64 .fp = s0.readReg64 .fp
  lr  : s.readReg64 .lr = s0.readReg64 .lr

private theorem sHatFwdPreserved_refl (s : State) : SHatFwdPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

local macro "prove_sHat_pres " hp:term:arg : tactic => `(tactic|
  exact ⟨by simp [State.readVReg128_orFpsr, ($hp).v3],
    by simp [State.readReg64_orFpsr, ($hp).x0], by simp [State.readReg64_orFpsr, ($hp).x1],
    by simp [State.readReg64_orFpsr, ($hp).x2], by simp [State.readReg64_orFpsr, ($hp).x3],
    by simp [State.readReg64_orFpsr, ($hp).x4], by simp [State.readReg64_orFpsr, ($hp).x5],
    by simp [State.readReg64_orFpsr, ($hp).x6], by simp [State.readReg64_orFpsr, ($hp).x9],
    by simp [State.readReg64_orFpsr, ($hp).x10], by simp [State.readReg64_orFpsr, ($hp).x11],
    by simp [State.readReg64_orFpsr, ($hp).x13], by simp [State.readReg64_orFpsr, ($hp).x14],
    by simp [State.readReg64_orFpsr, ($hp).x15], by simp [State.readReg64_orFpsr, ($hp).x16],
    by simp [State.readReg64_orFpsr, ($hp).x17], by simp [State.readReg64_orFpsr, ($hp).x18],
    by simp [State.readReg64_orFpsr, ($hp).x19], by simp [State.readReg64_orFpsr, ($hp).x20],
    by simp [State.readReg64_orFpsr, ($hp).x21], by simp [State.readReg64_orFpsr, ($hp).fp],
    by simp [State.readReg64_orFpsr, ($hp).lr]⟩)

private theorem sHat_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSFwd4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r))
    (hx7 : s.readReg64 .x7 = polyPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (16 - r))
    (hx2 : s.readReg64 .x2 = 62209#64) (hv3 : s.readVReg128 3#5 = dup8x16 3329#16)
    (hpres : SHatFwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + offSFwd4 else b + offSFwdMid) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * (r + 1)) ∧
        s'.readReg64 .x7 = polyPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x22 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x2 = 62209#64 ∧ s'.readVReg128 0#5 = dup8x16 62209#16 ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ SHatFwdPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat (fwdNttAfterStage4 p) (2 * r)))
            (2 * r + 1) (polyVecNat (fwdNttAfterStage4 p) (2 * r + 1))) ∗ Rest)) := by
  let k := 32 + 2 * r
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx7]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
    (by simp [evalAddrMode, hx7]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx2], by simp, by simp [hv3],
        ?_, rfl⟩
    prove_sHat_pres hpres
  · have hr15 : ¬ r < 15 := by
      intro hlt; have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx2], by simp, by simp [hv3], ?_, rfl⟩
    prove_sHat_pres hpres

private theorem sHat_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSFwd4 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r) →
      s.readReg64 .x7 = polyPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x22 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x2 = 62209#64 → s.readVReg128 3#5 = dup8x16 3329#16 →
      SHatFwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (fwdNttAfterStage4 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + offSFwdMid) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 3#5 = dup8x16 3329#16 ∧
          SHatFwdPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx7 hx22 hx2 hv3 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := sHat_layer4_iter hb s0 s sp polyPtr hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx7 hx22 hx2 hv3 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hv0', hv3', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv0', hv3', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx7 hx22 hx2 hv3 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := sHat_layer4_iter hb s0 s sp polyPtr hp (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx7 hx22 hx2 hv3 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx7_m, hx22_m, hx2_m, _, hv3_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx7_m hx22_m hx2_m hv3_m hpres_m hlo' hhi'

private theorem sHat_layer2_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr r10 r9 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r10 + r9 = polyPtr + 16#64) {r : Nat} (hr : r < 16)
    (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSFwd2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx7 : s.readReg64 .x7 = r9 + BitVec.ofNat 64 (32 * r))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (16 - r))
    (hx10 : s.readReg64 .x10 = r10)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv3 : s.readVReg128 3#5 = dup8x16 3329#16)
    (hpres : SHatFwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonNttStage16 2 64 q).1
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + offSFwd2 else b + offSFwdEnd) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x7 = r9 + BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x22 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x10 = r10 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 3#5 = dup8x16 3329#16 ∧
        SHatFwdPreserved s0 s' ∧
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
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx10], by simp [hv0], by simp [hv3],
        ?_, rfl⟩
    prove_sHat_pres hpres
  · have hr15 : ¬ r < 15 := by
      intro hlt; have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp [hr_eq], by simp [hr_eq], by simp [hx10],
        by simp [hv0], by simp [hv3], ?_, rfl⟩
    prove_sHat_pres hpres

private theorem sHat_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp polyPtr r10 r9 : BitVec 64) {q : Poly16} (hq : q.size = 256)
    (hsum : r10 + r9 = polyPtr + 16#64) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSFwd2 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x7 = r9 + BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x22 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x10 = r10 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 3#5 = dup8x16 3329#16 →
      SHatFwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonNttStage16 2 64 q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + offSFwdEnd) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ SHatFwdPreserved s0 s' ∧
          mlkemMultiLib.CodeLoaded mlkemMpl s'.mem ∧ MlKemRoOk mlkemMpl s'.mem ∧
          P' = (PolyMem polyPtr (polyVecNat (neonNttStage16 2 64 q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx7 hx22 hx10 hv0 hv3 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := sHat_layer2_iter hb s0 s sp polyPtr r10 r9 hq hsum (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx7 hx22 hx10 hv0 hv3 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro s' P' hpc' hrun' hcl' hro' ⟨hsp', hspA', _, _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact SepWP.done hpc' hrun' ⟨hsp', hspA', hpres', hcl', hro',
      hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx7 hx22 hx10 hv0 hv3 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := sHat_layer2_iter hb s0 s sp polyPtr r10 r9 hq hsum (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx7 hx22 hx10 hv0 hv3 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx7_m, hx22_m, hx10_m, hv0_m, hv3_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx7_m hx22_m hx10_m hv0_m hv3_m hpres_m hlo' hhi'

theorem sHat_fwd_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + offSFwd4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx3 : s.readReg64 .x3 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx7 : s.readReg64 .x7 = polyPtr + 16#64) (hx22 : s.readReg64 .x22 = 16#64)
    (hx2 : s.readReg64 .x2 = 62209#64)
    (hsum : s.readReg64 .x10 + s.readReg64 .x9 = polyPtr + 16#64)
    (hv3 : s.readVReg128 3#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offSFwdEnd) s
      (PolyMem polyPtr (polyVecNat p) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ SHatFwdPreserved s s' ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem ∧ MlKemRoOk mlkemMpl s'.mem ∧
        P' = (PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p)) ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  refine sepWP_seq_env hcl hro
    (sHat_layer4_loop hb s sp polyPtr hp Rest 15 0 rfl s (polyVecNat p)
      hpc hrun hsp hspA hcl hro hx8 hx7 hx22 hx2 hv3 (sHatFwdPreserved_refl s)
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hv0_1, hv3_1, hpres1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1 (mid := b + offSFwd2)
    (post1 := fun s2 P2 =>
      s2.sp = sp ∧ s2.spAligned = true ∧
      s2.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 134#64 ∧
      s2.readReg64 .x7 = s.readReg64 .x9 + BitVec.ofNat 64 0 ∧
      s2.readReg64 .x22 = 16#64 ∧ s2.readReg64 .x10 = s.readReg64 .x10 ∧
      s2.readVReg128 0#5 = dup8x16 62209#16 ∧ s2.readVReg128 3#5 = dup8x16 3329#16 ∧
      SHatFwdPreserved s s2 ∧
      P2 = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest))
    (by
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
        ⟨by simp [hsp1], by simpa [State.spAligned] using hspA1,
          by simp [hpres1.x3, hx3], by simp [hpres1.x9],
          by simp, by simp [hpres1.x10],
          by simp [hv0_1], by simp [hv3_1], ?_, rfl⟩
      prove_sHat_pres hpres1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx7_2, hx22_2, hx10_2, hv0_2, hv3_2, hpres2, hP2⟩
  subst hP2
  exact sHat_layer2_loop hb s sp polyPtr (s.readReg64 .x10) (s.readReg64 .x9)
    ((fwdNttAfterStage4_size p).trans hp) hsum Rest 15 0 rfl s2 _
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx7_2 hx22_2 hx10_2 hv0_2 hv3_2 hpres2
    (fun _ h => by omega) (fun _ _ _ => rfl)

/-! ## 2. `eHat` Low-Stage Forward NTT (`+0x58d8 → +0x59c0`) -/

structure EHatFwdPreserved (s0 s : State) : Prop where
  v7  : s.readVReg128 7#5 = s0.readVReg128 7#5
  x0  : s.readReg64 .x0 = s0.readReg64 .x0
  x1  : s.readReg64 .x1 = s0.readReg64 .x1
  x3  : s.readReg64 .x3 = s0.readReg64 .x3
  x9  : s.readReg64 .x9 = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
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
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x27 : s.readReg64 .x27 = s0.readReg64 .x27
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  fp  : s.readReg64 .fp = s0.readReg64 .fp
  lr  : s.readReg64 .lr = s0.readReg64 .lr

private theorem eHatFwdPreserved_refl (s : State) : EHatFwdPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

local macro "prove_eHat_pres " hp:term:arg : tactic => `(tactic|
  exact ⟨by simp [State.readVReg128_orFpsr, ($hp).v7],
    by simp [State.readReg64_orFpsr, ($hp).x0], by simp [State.readReg64_orFpsr, ($hp).x1],
    by simp [State.readReg64_orFpsr, ($hp).x3], by simp [State.readReg64_orFpsr, ($hp).x9],
    by simp [State.readReg64_orFpsr, ($hp).x10], by simp [State.readReg64_orFpsr, ($hp).x11],
    by simp [State.readReg64_orFpsr, ($hp).x12], by simp [State.readReg64_orFpsr, ($hp).x13],
    by simp [State.readReg64_orFpsr, ($hp).x14], by simp [State.readReg64_orFpsr, ($hp).x15],
    by simp [State.readReg64_orFpsr, ($hp).x16], by simp [State.readReg64_orFpsr, ($hp).x17],
    by simp [State.readReg64_orFpsr, ($hp).x18], by simp [State.readReg64_orFpsr, ($hp).x19],
    by simp [State.readReg64_orFpsr, ($hp).x20], by simp [State.readReg64_orFpsr, ($hp).x21],
    by simp [State.readReg64_orFpsr, ($hp).x23], by simp [State.readReg64_orFpsr, ($hp).x27],
    by simp [State.readReg64_orFpsr, ($hp).x28], by simp [State.readReg64_orFpsr, ($hp).fp],
    by simp [State.readReg64_orFpsr, ($hp).lr]⟩)

private theorem eHat_layer4_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offEFwd4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r))
    (hx2 : s.readReg64 .x2 = polyPtr + BitVec.ofNat 64 (16 + 32 * r))
    (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 (16 - r))
    (hx16 : s.readReg64 .x16 = 62209#64) (hv7 : s.readVReg128 7#5 = dup8x16 3329#16)
    (hpres : EHatFwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat p (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat p (2 * r + 1)) :
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + offEFwd4 else b + offEFwdMid) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * (r + 1)) ∧
        s'.readReg64 .x2 = polyPtr + BitVec.ofNat 64 (16 + 32 * (r + 1)) ∧
        s'.readReg64 .x4 = BitVec.ofNat 64 (16 - (r + 1)) ∧
        s'.readReg64 .x16 = 62209#64 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 7#5 = dup8x16 3329#16 ∧
        EHatFwdPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat (fwdNttAfterStage4 p) (2 * r)))
            (2 * r + 1) (polyVecNat (fwdNttAfterStage4 p) (2 * r + 1))) ∗ Rest)) := by
  let k := 32 + 2 * r
  refine step_ldpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat p (2 * r)) (v2 := polyVecNat p (2 * r + 1))
    hpc hrun (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx2]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
    (by simp [evalAddrMode, hx2]; clear * - hr; bv_omega) (by clear * -; bv_omega)
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
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp; clear * - hr15; bv_omega, by simp; clear * - hr15; bv_omega,
        by simp; clear * - hr15; bv_omega, by simp [hx16], by simp, by simp [hv7],
        ?_, rfl⟩
    prove_eHat_pres hpres
  · have hr15 : ¬ r < 15 := by
      intro hlt; have hr_eq : r = 15 := by clear * - hne hlt; bv_omega
      omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hr_eq], by simp [hr_eq], by simp [hr_eq],
        by simp [hx16], by simp, by simp [hv7], ?_, rfl⟩
    prove_eHat_pres hpres

private theorem eHat_layer4_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offEFwd4 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (66 + 4 * r) →
      s.readReg64 .x2 = polyPtr + BitVec.ofNat 64 (16 + 32 * r) →
      s.readReg64 .x4 = BitVec.ofNat 64 (16 - r) →
      s.readReg64 .x16 = 62209#64 → s.readVReg128 7#5 = dup8x16 3329#16 →
      EHatFwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (fwdNttAfterStage4 p) j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat p j) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + offEFwdMid) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 7#5 = dup8x16 3329#16 ∧
          EHatFwdPreserved s0 s' ∧
          P' = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx2 hx4 hx16 hv7 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := eHat_layer4_iter hb s0 s sp polyPtr hp (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx2 hx4 hx16 hv7 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, hv0', hv7', hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact ⟨hsp', hspA', hv0', hv7', hpres', hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx2 hx4 hx16 hv7 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := eHat_layer4_iter hb s0 s sp polyPtr hp (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx2 hx4 hx16 hv7 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx2_m, hx4_m, hx16_m, _, hv7_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx2_m hx4_m hx16_m hv7_m hpres_m hlo' hhi'

private theorem eHat_layer2_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr : BitVec 64) {q : Poly16} (hq : q.size = 256)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offEFwd2) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (32 * r))
    (hx9 : s.readReg64 .x9 = polyPtr + 16#64)
    (hv0 : s.readVReg128 0#5 = dup8x16 62209#16) (hv7 : s.readVReg128 7#5 = dup8x16 3329#16)
    (hpres : EHatFwdPreserved s0 s)
    (hhi0 : f (2 * r) = polyVecNat q (2 * r)) (hhi1 : f (2 * r + 1) = polyVecNat q (2 * r + 1)) :
    let q' := (neonNttStage16 2 64 q).1
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + offEFwd2 else b + offEFwdEnd) s (PolyMem polyPtr f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x9 = polyPtr + 16#64 ∧
        s'.readVReg128 0#5 = dup8x16 62209#16 ∧ s'.readVReg128 7#5 = dup8x16 3329#16 ∧
        EHatFwdPreserved s0 s' ∧
        P' = (PolyMem polyPtr
          (Function.update (Function.update f (2 * r) (polyVecNat q' (2 * r)))
            (2 * r + 1) (polyVecNat q' (2 * r + 1))) ∗ Rest)) := by
  intro q'
  let k := 64 + 4 * r
  refine step_ldrh16_ro (k := k) (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * k)) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx8]; dsimp [k]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2
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
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (hhi0 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (hhi1 ▸ SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  wp_steps 16
  have hpair := fwdLayer2RawPair_eq_polyVecNat hq r hr
  dsimp only [fwdLayer2RawPair, buildZetaLayer2] at hpair
  refine step_stpQ128 (wb := none)
    (ea := polyPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := polyPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat q' (2 * r)) (v2 := polyVecNat q' (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [q', k]; rw [← hpair.1]; simp)
    (by dsimp only [q', k]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  have _ : b = blkPl05.base := hb
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    refine step_bCond_taken (dst := b + offEFwd2)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp; clear * - hr15
          rcases r with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | r <;>
            first | decide | omega)
      (by subst hb; clear * -; dsimp [offEFwd2]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp; clear * - hr15; bv_omega,
        by simp [hx9], by simp [hv0], by simp [hv7], ?_, rfl⟩
    prove_eHat_pres hpres
  · have hr_eq : r = 15 := by omega
    subst hr_eq
    simp only [Nat.lt_irrefl, ↓reduceIte]
    refine step_bCond_not_taken (dst := b + offEFwdEnd)
      (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs)
      (by simp)
      (by subst hb; clear * -; dsimp [offEFwdEnd]; bv_omega) ?_
    refine SepWP.done (by simp [State.setPC]) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp, by simp, by simp [hx9],
        by simp [hv0], by simp [hv7], ?_, rfl⟩
    prove_eHat_pres hpres

private theorem eHat_layer2_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp polyPtr : BitVec 64) {q : Poly16} (hq : q.size = 256) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offEFwd2 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x2 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x9 = polyPtr + 16#64 →
      s.readVReg128 0#5 = dup8x16 62209#16 → s.readVReg128 7#5 = dup8x16 3329#16 →
      EHatFwdPreserved s0 s →
      (∀ j, j < 2 * r → f j = polyVecNat (neonNttStage16 2 64 q).1 j) →
      (∀ j, 2 * r ≤ j → j < 32 → f j = polyVecNat q j) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + offEFwdEnd) s
        (PolyMem polyPtr f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ EHatFwdPreserved s0 s' ∧
          mlkemMultiLib.CodeLoaded mlkemMpl s'.mem ∧ MlKemRoOk mlkemMpl s'.mem ∧
          P' = (PolyMem polyPtr (polyVecNat (neonNttStage16 2 64 q).1) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx2 hx9 hv0 hv7 hpres hlo hhi
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := eHat_layer2_iter hb s0 s sp polyPtr hq (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx2 hx9 hv0 hv7 hpres
      (hhi 30 (by omega) (by omega)) (hhi 31 (by omega) (by omega))
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro s' P' hpc' hrun' hcl' hro' ⟨hsp', hspA', _, _, _, _, _, hpres', hP'⟩
    have ⟨hlo', _⟩ := update2_split hlo hhi
    exact SepWP.done hpc' hrun' ⟨hsp', hspA', hpres', hcl', hro',
      hP'.trans (by rw [polyMem_congr hlo'])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx2 hx9 hv0 hv7 hpres hlo hhi
    have hr15 : r < 15 := by omega
    have hiter := eHat_layer2_iter hb s0 s sp polyPtr hq (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx2 hx9 hv0 hv7 hpres
      (hhi (2 * r) (by omega) (by omega)) (hhi (2 * r + 1) (by omega) (by omega))
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx2_m, hx9_m, hv0_m, hv7_m, hpres_m, hPm⟩
    subst hPm
    have ⟨hlo', hhi'⟩ := update2_split hlo hhi
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx2_m hx9_m hv0_m hv7_m hpres_m hlo' hhi'

theorem eHat_fwd_low_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s : State) (sp polyPtr : BitVec 64) {p : Poly16} (hp : p.size = 256) (Rest : SepProp)
    (hpc : s.pc = b + offEFwd4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 66#64)
    (hx17 : s.readReg64 .x17 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx2 : s.readReg64 .x2 = polyPtr + 16#64) (hx4 : s.readReg64 .x4 = 16#64)
    (hx16 : s.readReg64 .x16 = 62209#64)
    (hx9 : s.readReg64 .x9 = polyPtr + 16#64)
    (hv7 : s.readVReg128 7#5 = dup8x16 3329#16) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + offEFwdEnd) s
      (PolyMem polyPtr (polyVecNat p) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ EHatFwdPreserved s s' ∧
        mlkemMultiLib.CodeLoaded mlkemMpl s'.mem ∧ MlKemRoOk mlkemMpl s'.mem ∧
        P' = (PolyMem polyPtr (polyVecNat (lowerFwdNtt16 p)) ∗ Rest)) := by
  have _ : b = blkPl05.base := hb
  refine sepWP_seq_env hcl hro
    (eHat_layer4_loop hb s sp polyPtr hp Rest 15 0 rfl s (polyVecNat p)
      hpc hrun hsp hspA hcl hro hx8 hx2 hx4 hx16 hv7 (eHatFwdPreserved_refl s)
      (fun _ h => by omega) (fun _ _ _ => rfl)) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hv0_1, hv7_1, hpres1, hP1⟩
  subst hP1
  refine sepWP_seq_env hcl1 hro1 (mid := b + offEFwd2)
    (post1 := fun s2 P2 =>
      s2.sp = sp ∧ s2.spAligned = true ∧
      s2.readReg64 .x8 = mlkemMpl.ρ ro00Sym + 134#64 ∧
      s2.readReg64 .x2 = BitVec.ofNat 64 0 ∧
      s2.readReg64 .x9 = polyPtr + 16#64 ∧
      s2.readVReg128 0#5 = dup8x16 62209#16 ∧ s2.readVReg128 7#5 = dup8x16 3329#16 ∧
      EHatFwdPreserved s s2 ∧
      P2 = (PolyMem polyPtr (polyVecNat (fwdNttAfterStage4 p)) ∗ Rest))
    (by
      wp_steps
      refine SepWP.done (by wp_norm_lhs) (by simp [hrun1])
        ⟨by simp [hsp1], by simpa [State.spAligned] using hspA1,
          by simp [hpres1.x17, hx17], by simp,
          by simp [hpres1.x9, hx9],
          by simp [hv0_1], by simp [hv7_1], ?_, rfl⟩
      prove_eHat_pres hpres1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx2_2, hx9_2, hv0_2, hv7_2, hpres2, hP2⟩
  subst hP2
  exact eHat_layer2_loop hb s sp polyPtr
    ((fwdNttAfterStage4_size p).trans hp) Rest 15 0 rfl s2 _
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx2_2 hx9_2 hv0_2 hv7_2 hpres2
    (fun _ h => by omega) (fun _ _ _ => rfl)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow
