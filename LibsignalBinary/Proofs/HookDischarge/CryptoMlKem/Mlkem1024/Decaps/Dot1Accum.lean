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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `kyber_decapsulate` (`B06`) — Site 1 4-Way Accumulate & Dot Product (`+0x1c8c → +0x1e84`)

Composes `Dot1Mul` (`dot1_init_ok`, `dot1_clear_scratch`, `dot1_ntt_mul_loop`) with the
accumulate tail (`+0x1c8c → +0x1e84`) to prove the full 4-way `sHat · uHat` dot product
(`+0x1970 → +0x1e84`) producing `neonDot4` at `sp + 28368`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Accum

open Arm64 Arm64.Obj ProofLib SepProp
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonPolyNttMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (simdAdd8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (polyAdd16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (
  dot1_clear_scratch dot1_init_ok dot1_ntt_mul_loop neonDot4 ro00Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepLoad128.spill21 SepStore128.spill21 Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (
  AccMidRegs04 AccSpill21 accMidVec32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 poly32Mem_ofFn polyVecNat
  step_ldrQ128 step_strQ128 vec32_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (svc_simdAdd_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  neonDot3 neonPolyNttMul16_size polyAdd16_zero_left polyZero16 simdAdd8h_polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x1c8c → 0x1e80]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem vec32_ofFn_get_simp (f : Nat → BitVec 128) (k : Nat) (hk : k < 32) :
    (Vec32.ofFn f).get k = f k := vec32_ofFn_get f k hk

@[simp, arm64_norm, wp_norm]
private theorem simdAdd8h_polyVecNat_simp (a b : Poly16) (k : Nat) (hk : k < 32) :
    simdAdd8h (polyVecNat b k) (polyVecNat a k) = polyVecNat (polyAdd16 a b) k :=
  simdAdd8h_polyVecNat a b k hk

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

attribute [local irreducible] blkPC06 polyVecNat simdAdd8h
attribute [local wp_norm ↓ high] svc_simdAdd_8h

local macro "s1_ldr0 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.left; apply SepLoad128.spill21 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [AccSpill21, Spill21.get] } }
  { wp_norm_lhs }))

local macro "s1_str0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.spill21 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [AccSpill21, Spill21.set] } }
  { wp_norm_lhs }; intro _))

local macro "s1_str1 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "s1_ldr2 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.left
    apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

private theorem dot1_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (hj : j < 4)
    (t0 : Spill21) (acc prod : Poly16) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1c8c#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1)) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1dd4#64) s
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 3) ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧ s'.readReg64 .x9 = lhsPtr + 512#64 ∧
        s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧ s'.readReg64 .x11 = rhsPtr + 512#64 ∧
        s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 14432#64 ∧
        AccMidRegs04 acc prod s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc') ∗
          Poly32Mem (sp + 28368#64) (accMidVec32 acc' v28368) ∗
          Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  cases v28368
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  s1_ldr2 0; s1_ldr0 20; wp_step; s1_ldr2 1; s1_ldr0 19; wp_step; wp_step
  s1_ldr2 2; s1_ldr0 18; wp_step; s1_ldr2 3; s1_ldr0 17; wp_step; s1_ldr2 4; wp_step; wp_step
  s1_str0 20; s1_ldr2 5; s1_str1 0; s1_ldr0 16; s1_str0 19; s1_str1 1; s1_ldr0 15; wp_step
  s1_ldr2 6; s1_str0 18; wp_step; s1_ldr2 7; s1_str1 2; s1_str0 17; s1_ldr0 14; s1_str1 3; s1_ldr0 13; wp_step
  s1_ldr2 8; s1_str0 16; wp_step; s1_str1 4; s1_ldr0 12; s1_ldr2 9; s1_str0 15; s1_str1 5; s1_ldr0 11; wp_step
  s1_ldr2 10; s1_str0 14; wp_step; s1_ldr2 11; s1_str1 6; s1_str0 13; s1_ldr0 10; s1_str1 7; s1_ldr0 9; wp_step
  s1_ldr2 12; s1_str0 12; wp_step; s1_ldr2 13; s1_str1 8; s1_ldr0 8; s1_str0 11; wp_step
  s1_ldr2 15; s1_str1 9; wp_step; s1_ldr2 14; s1_str0 10; wp_step; s1_ldr2 17; s1_str1 10; wp_step
  s1_ldr2 16; s1_str0 9; wp_step; s1_ldr2 19; s1_str1 11; wp_step; s1_ldr2 18; s1_str0 8; wp_step
  s1_ldr2 21; s1_str1 12
  have hpst : ConditionHolds .NE (AddWithCarry64 (BitVec.ofNat 64 (j + 1)) (~~~4#64) true).2 =
      decide (j < 3) := by
    clear * - hj; rcases j with _ | _ | _ | _ | _ <;> try omega
    all_goals decide
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simpa [subsPState64] using hpst,
      by simp [hx8], by simp, by simp [hx10], by simp, by simp [hx12], by simp [hx13], by simp [hx14],
      ⟨by simp [hv0], by simp [hv1], by simp, by simp,
        by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15],
        by simp, by simp, by simp, by simp, by simp,
        by simp [hv27], by simp, by simp [hv29], by simp [hv30], by simp [hv31]⟩,
      ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
        by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩,
      by simp [AccSpill21, accMidVec32]⟩

private theorem dot1_accum_hi [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp x9v x11v : BitVec 64) {j : Nat}
    (t0 : Spill21) (acc prod : Poly16) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1dd4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 3))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1)) (hx9 : s.readReg64 .x9 = x9v)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = x11v)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hmid : AccMidRegs04 acc prod s) (hpres : Inv13Preserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none))
      (if j < 3 then b + 0x1ad4#64 else b + 0x1e84#64) s
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc') ∗
        Poly32Mem (sp + 28368#64) (accMidVec32 acc' v28368) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = x9v ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = x11v ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 14432#64 ∧ AccRegs acc' s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc') ∗
          Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [accMidVec32]
  cases v28368
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv0, hv1, hv2, hv3, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  wp_step; s1_ldr2 20; s1_str1 13; wp_step; s1_ldr2 23; s1_str1 14
  wp_step; s1_ldr2 22; s1_str1 15; wp_step; s1_ldr2 25; s1_str1 16
  wp_step; s1_ldr2 24; s1_str1 17; wp_step; s1_ldr2 27; s1_str1 18
  wp_step; s1_ldr2 26; s1_str1 19; wp_step; s1_ldr2 29; s1_str1 20
  wp_step; s1_ldr2 28; s1_str1 21; wp_step; s1_ldr2 31; s1_str1 22
  wp_step; s1_ldr2 30; s1_str1 23; wp_step; s1_str1 24; wp_step
  s1_str1 25; s1_str1 26; s1_str1 27; s1_str1 28; s1_str1 29; s1_str1 30; s1_str1 31
  wp_step; wp_if hne
  · have hj3 : j < 3 := by simpa [hpst] using hne
    simp only [hj3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx13], by simp [hx14],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
          by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩,
        by simp [Vec32.ofFn]⟩
  · have hj3 : ¬ j < 3 := by simpa [hpst] using hne
    simp only [hj3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx13], by simp [hx14],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
          by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩,
        by simp [Vec32.ofFn]⟩


private theorem dot1_outer_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (hj : j < 4)
    (t0 : Spill21) (lhs rhs acc : Poly16) (v28368 v14432 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1ad4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none)) (if j < 3 then b + 0x1ad4#64 else b + 0x1e84#64) s
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 14432#64) v14432 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = lhsPtr + 512#64 ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr + 512#64 ∧ s'.readReg64 .x12 = 62209#64 ∧
        s'.readReg64 .x13 = 3329#64 ∧ s'.readReg64 .x14 = sp + 14432#64 ∧
        AccRegs acc' s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc') ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro prod acc'
  rw [show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 14432#64) v14432 ∗ Rest) =
      (Poly32Mem (sp + 14432#64) v14432 ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (dot1_clear_scratch hb s0 s sp lhsPtr rhsPtr hj acc v14432 _
    hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hx14 hacc hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hacc1, hpres1, rfl⟩
  rw [show (Poly32Mem (sp + 14432#64) Vec32.zero ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 14432#64) Vec32.zero.get ∗
        (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) from by
    change (PolyMem (sp + 14432#64) Vec32.zero.get ∗ _) = _; exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (dot1_ntt_mul_loop hb s0 sp lhsPtr rhsPtr _ lhs rhs acc _ 15 0 rfl
    s1 Vec32.zero.get hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hx15_1 hx16_1 hacc1 hpres1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hacc2, hpres2, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (dot1_accum_lo hb s0 s2 sp lhsPtr rhsPtr hj t0 acc prod v28368 _
    hpc2 hrun2 hsp2 hspA2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hacc2 hpres2) ?_
  rintro sm Pm hpcm hrunm
    ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hmidm, hpresm, rfl⟩
  refine SepWP.mono (dot1_accum_hi hb s0 sm sp (lhsPtr + 512#64) (rhsPtr + 512#64) t0 acc prod v28368 _
    hpcm hrunm hspm hspAm hpstm hx8m hx9m hx10m hx11m hx12m hx13m hx14m hmidm hpresm) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', hacc', hpres', rfl⟩
  exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', hacc', hpres',
    sepProp_ext (by sep_frame) (by sep_frame)⟩

theorem dot1_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp lhsBase rhsBase : BitVec 64)
    (t0 : Spill21) (l0 l1 l2 l3 r0 r1 r2 r3 : Poly16) (v28368 v14432 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1ad4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = lhsBase)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsBase)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hacc : AccRegs polyZero16 s) (hpres : Inv13Preserved s0 s) :
    let dot := neonDot4 l0 l1 l2 l3 r0 r1 r2 r3
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1e84#64) s
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 dot) ∗
          PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
          PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
          PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗
          PolyMem (sp + 28368#64) (polyVecNat dot) ∗
          Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l3 r3))) ∗ Rest)) := by
  dsimp only
  let dot := neonDot4 l0 l1 l2 l3 r0 r1 r2 r3
  let p0 := neonPolyNttMul16 l0 r0
  let p1 := neonPolyNttMul16 l1 r1
  let p2 := neonPolyNttMul16 l2 r2
  let acc1 := polyAdd16 p0 p1
  let acc2 := polyAdd16 acc1 p2
  let Rest0 : SepProp := PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
    PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
    PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
    PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗ Rest
  let Rest1 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗
    PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
    PolyMem rhsBase (polyVecNat r0) ∗
    PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗ Rest
  let Rest2 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗
    PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
    PolyMem rhsBase (polyVecNat r0) ∗
    PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗ Rest
  let Rest3 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗
    PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem rhsBase (polyVecNat r0) ∗
    PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Rest
  rw [show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗ PolyMem lhsBase (polyVecNat l0) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 14432#64) v14432 ∗ Rest0) from
    sepProp_ext (by dsimp only [Rest0]; sep_frame) (by dsimp only [Rest0]; sep_frame)]
  have hj0 := dot1_outer_iter hb s0 s sp lhsBase rhsBase (j := 0) (by omega)
    t0 l0 r0 polyZero16 v28368 v14432 Rest0 hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hacc hpres
  dsimp only at hj0
  simp only [show 0 < 3 by omega, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size l0 r0)] at hj0
  refine sepWP_seq_env hcl hro hj0 ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hacc1, hpres1, rfl⟩
  rw [show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 p0) ∗ PolyMem lhsBase (polyVecNat l0) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest0) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 p0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1) from
    sepProp_ext (by dsimp only [Rest0, Rest1]; sep_frame) (by dsimp only [Rest0, Rest1]; sep_frame)]
  have hj1 := dot1_outer_iter hb s0 s1 sp (lhsBase + 512#64) (rhsBase + 512#64) (j := 1) (by omega)
    t0 l1 r1 p0 (Vec32.ofFn (polyVecNat p0)) (Vec32.ofFn (polyVecNat p0)) Rest1
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hacc1 hpres1
  dsimp only at hj1; simp only [show 1 < 3 by omega, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl1 hro1 hj1 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hacc2, hpres2, rfl⟩
  rw [show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc1) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest1) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2) from
    sepProp_ext (by dsimp only [Rest1, Rest2]; sep_frame) (by dsimp only [Rest1, Rest2]; sep_frame)]
  have hj2 := dot1_outer_iter hb s0 s2 sp (lhsBase + 1024#64) (rhsBase + 1024#64) (j := 2) (by omega)
    t0 l2 r2 acc1 (Vec32.ofFn (polyVecNat acc1)) (Vec32.ofFn (polyVecNat p1)) Rest2
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2
    (by simpa [show (lhsBase + 512#64) + 512#64 = lhsBase + 1024#64 by clear * -; bv_omega] using hx9_2)
    hx10_2
    (by simpa [show (rhsBase + 512#64) + 512#64 = rhsBase + 1024#64 by clear * -; bv_omega] using hx11_2)
    hx12_2 hx13_2 hx14_2 hacc2 hpres2
  dsimp only at hj2; simp only [show 2 < 3 by omega, ↓reduceIte] at hj2
  refine sepWP_seq_env hcl2 hro2 hj2 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx13_3, hx14_3, hacc3, hpres3, rfl⟩
  rw [show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc2) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc2)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p2)) ∗ Rest2) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 acc2) ∗ PolyMem (lhsBase + 1536#64) (polyVecNat l3) ∗
        PolyMem (rhsBase + 1536#64) (polyVecNat r3) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc2)) ∗
        Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat p2)) ∗ Rest3) from
    sepProp_ext (by dsimp only [Rest2, Rest3]; sep_frame) (by dsimp only [Rest2, Rest3]; sep_frame)]
  have hj3 := dot1_outer_iter hb s0 s3 sp (lhsBase + 1536#64) (rhsBase + 1536#64) (j := 3) (by omega)
    t0 l3 r3 acc2 (Vec32.ofFn (polyVecNat acc2)) (Vec32.ofFn (polyVecNat p2)) Rest3
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3
    (by simpa [show (lhsBase + 1024#64) + 512#64 = lhsBase + 1536#64 by clear * -; bv_omega] using hx9_3)
    hx10_3
    (by simpa [show (rhsBase + 1024#64) + 512#64 = rhsBase + 1536#64 by clear * -; bv_omega] using hx11_3)
    hx12_3 hx13_3 hx14_3 hacc3 hpres3
  dsimp only at hj3; simp only [Nat.lt_irrefl, ↓reduceIte] at hj3
  refine SepWP.mono hj3 ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, _, hpres', rfl⟩
  refine ⟨hsp', hspA', hpres', ?_⟩
  rw [poly32Mem_ofFn]
  dsimp only [dot, neonDot4, acc2, neonDot3, acc1, p0, p1, p2, Rest3]
  exact sepProp_ext (by sep_frame) (by sep_frame)

theorem dot1_full_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64)
    (t0 : Spill21) (l0 l1 l2 l3 r0 r1 r2 r3 : Poly16) (v28368 v14432 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1970#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpres : Inv13Preserved s0 s) :
    let dot := neonDot4 l0 l1 l2 l3 r0 r1 r2 r3
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1e84#64) s
      (Spill21Mem (sp + 2096#64) t0 ∗
        PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem (sp + 30960#64) (polyVecNat l1) ∗
        PolyMem (sp + 31472#64) (polyVecNat l2) ∗ PolyMem (sp + 31984#64) (polyVecNat l3) ∗
        PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem (sp + 4672#64) (polyVecNat r1) ∗
        PolyMem (sp + 5184#64) (polyVecNat r2) ∗ PolyMem (sp + 5696#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 dot) ∗
          PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem (sp + 30960#64) (polyVecNat l1) ∗
          PolyMem (sp + 31472#64) (polyVecNat l2) ∗ PolyMem (sp + 31984#64) (polyVecNat l3) ∗
          PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem (sp + 4672#64) (polyVecNat r1) ∗
          PolyMem (sp + 5184#64) (polyVecNat r2) ∗ PolyMem (sp + 5696#64) (polyVecNat r3) ∗
          PolyMem (sp + 28368#64) (polyVecNat dot) ∗
          Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l3 r3))) ∗ Rest)) := by
  intro dot
  rw [show (Spill21Mem (sp + 2096#64) t0 ∗
        PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem (sp + 30960#64) (polyVecNat l1) ∗
        PolyMem (sp + 31472#64) (polyVecNat l2) ∗ PolyMem (sp + 31984#64) (polyVecNat l3) ∗
        PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem (sp + 4672#64) (polyVecNat r1) ∗
        PolyMem (sp + 5184#64) (polyVecNat r2) ∗ PolyMem (sp + 5696#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest) =
      (Spill21Mem (sp + 2096#64) t0 ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        (PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem (sp + 30960#64) (polyVecNat l1) ∗
         PolyMem (sp + 31472#64) (polyVecNat l2) ∗ PolyMem (sp + 31984#64) (polyVecNat l3) ∗
         PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem (sp + 4672#64) (polyVecNat r1) ∗
         PolyMem (sp + 5184#64) (polyVecNat r2) ∗ PolyMem (sp + 5696#64) (polyVecNat r3) ∗
         Poly32Mem (sp + 14432#64) v14432 ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (dot1_init_ok hb s0 s sp t0 v28368 _ hpc hrun hsp hspA hcl hro hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hacc1, hpres1, rfl⟩
  have h1 : (sp + 30448#64) + 512#64 = sp + 30960#64 := by clear * -; bv_omega
  have h2 : (sp + 30448#64) + 1024#64 = sp + 31472#64 := by clear * -; bv_omega
  have h3 : (sp + 30448#64) + 1536#64 = sp + 31984#64 := by clear * -; bv_omega
  have h4 : (sp + 4160#64) + 512#64 = sp + 4672#64 := by clear * -; bv_omega
  have h5 : (sp + 4160#64) + 1024#64 = sp + 5184#64 := by clear * -; bv_omega
  have h6 : (sp + 4160#64) + 1536#64 = sp + 5696#64 := by clear * -; bv_omega
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, show (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗
        Poly32Mem (sp + 28368#64) Vec32.zero ∗
        (PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem ((sp + 30448#64) + 512#64) (polyVecNat l1) ∗
         PolyMem ((sp + 30448#64) + 1024#64) (polyVecNat l2) ∗ PolyMem ((sp + 30448#64) + 1536#64) (polyVecNat l3) ∗
         PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem ((sp + 4160#64) + 512#64) (polyVecNat r1) ∗
         PolyMem ((sp + 4160#64) + 1024#64) (polyVecNat r2) ∗ PolyMem ((sp + 4160#64) + 1536#64) (polyVecNat r3) ∗
         Poly32Mem (sp + 14432#64) v14432 ∗ Rest)) =
      (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem (sp + 30448#64) (polyVecNat l0) ∗ PolyMem ((sp + 30448#64) + 512#64) (polyVecNat l1) ∗
        PolyMem ((sp + 30448#64) + 1024#64) (polyVecNat l2) ∗ PolyMem ((sp + 30448#64) + 1536#64) (polyVecNat l3) ∗
        PolyMem (sp + 4160#64) (polyVecNat r0) ∗ PolyMem ((sp + 4160#64) + 512#64) (polyVecNat r1) ∗
        PolyMem ((sp + 4160#64) + 1024#64) (polyVecNat r2) ∗ PolyMem ((sp + 4160#64) + 1536#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) Vec32.zero ∗ Poly32Mem (sp + 14432#64) v14432 ∗ Rest) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.mono (dot1_ok hb s0 s1 sp (sp + 30448#64) (sp + 4160#64) t0 l0 l1 l2 l3 r0 r1 r2 r3
    Vec32.zero v14432 Rest hpc1 hrun1 hsp1 hspA1 hcl1 hro1
    hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hacc1 hpres1) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hpres', rfl⟩
  rw [h1, h2, h3, h4, h5, h6]
  exact ⟨hsp', hspA', hpres', rfl⟩

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Accum
