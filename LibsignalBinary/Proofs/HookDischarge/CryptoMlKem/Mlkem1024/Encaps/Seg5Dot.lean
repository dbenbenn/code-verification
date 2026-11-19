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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure

/-!
# `kyber::encapsulate` (`B07`) — `Seg5Dot`: 4-Way `tHat · rHat` Dot Product (`+0x7f10 → +0x82c0`)

Steps the 4-iteration outer `ntt_multiply` + accumulate loop (`j = 0, 1, 2, 3`) over
`tHat[0..3]` at `[sp + 10752 .. sp + 12800)` (`x19`) and `rHat[0..3]` at
`[sp + 12832 .. sp + 14880)` (`x20`), producing
`PolyMem (sp + 26768#64) (polyVecNat (neonDot4 t0 t1 t2 t3 r0 r1 r2 r3))` at `+0x82c0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Dot

open Arm64 Arm64.Obj ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk zetaTableAt)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16 neonPolyNttMul16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup8x16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdMul8h simdSmlal4s simdSmull4s simdSqdmulh8h simdSshr8h simdSub8h
  simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul (polyAdd16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Spill13 Spill13Mem Vec32 poly32Mem_ofFn polyVecNat
  spill13_ofFn_get spill13_set_get step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128
  vec32_ofFn_get vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdMul_8h svc_simdRev64_4s svc_simdSmlal_4s
  svc_simdSmull_4s svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h svc_simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZeta4 lane16_buildZeta4 neonDot3 neonPolyNttMul16_size nttMulRawPair
  nttMulRawPair_eq_polyVecNat polyAdd16_zero_left polyZero16 simdAdd8h_polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (
  AccRegs AccSpill accSpill_zero)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07_code_eq blk07_tree_size blkLib07 blkPC07 blkPl07 blkPlaceable07 blkTree07)

@[simp, arm64_norm, wp_norm] abbrev offSeg5DotStart : BitVec 64 := BitVec.ofNat 64 32528
@[simp, arm64_norm, wp_norm] abbrev offSeg5DotMul   : BitVec 64 := BitVec.ofNat 64 32668
@[simp, arm64_norm, wp_norm] abbrev offSeg5DotAccLo : BitVec 64 := BitVec.ofNat 64 32968
@[simp, arm64_norm, wp_norm] abbrev offSeg5DotAccHi : BitVec 64 := BitVec.ofNat 64 33296
@[simp, arm64_norm, wp_norm] abbrev offSeg5InvLow   : BitVec 64 := BitVec.ofNat 64 33472

abbrev ro00Sym : String :=
  "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

section
set_option linter.literalFetch false
gen_placed_fetches blkPC07 blkLib07 blkTree07 blk07_code_eq blk07_tree_size
  via_placement blkPl07 blkPlaceable07 [0x7f10 → 0x82bc]
end

@[simp, arm64_norm, wp_norm]
private theorem blkPl07_ρ [MlKemPlacement] (sym : String) :
    blkPl07.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

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
  blkPC07 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdUzp1_4s simdRev64_4s simdSmull4s simdSmlal4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdDup_8h_gpr svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s
  svc_simdUzp1_4s svc_simdRev64_4s svc_simdExt_16b_8 svc_simdSmull_4s svc_simdSmlal_4s
private theorem SepStore128.polyMem {k : Nat} {ea ptr : BitVec 64} {f : Nat → BitVec 128}
    {val : BitVec 128} (hk : k < 32) (ha : ptr + BitVec.ofNat 64 (16 * k) = ea) :
    SepStore128 ea val (PolyMem ptr f) (PolyMem ptr (Function.update f k val)) :=
  SepStore128.vecRange (n := 32) hk ha

private theorem polyMem_congr {ptr : BitVec 64} {f g : Nat → BitVec 128}
    (h : ∀ i, i < 32 → f i = g i) : PolyMem ptr f = PolyMem ptr g := vecRangeMem_congr h

private theorem update2_prefix {f g : Nat → BitVec 128} {r : Nat}
    (hf : ∀ j, j < 2 * r → f j = g j) :
    ∀ j, j < 2 * (r + 1) →
      Function.update (Function.update f (2 * r) (g (2 * r))) (2 * r + 1) (g (2 * r + 1)) j = g j := by
  intro j hj
  by_cases h1 : j = 2 * r + 1
  · subst h1; simp
  · rw [Function.update_of_ne h1]
    by_cases h0 : j = 2 * r
    · subst h0; simp
    · rw [Function.update_of_ne h0]; exact hf j (by omega)

private theorem zext64_trunc16 (z : BitVec 16) : (z.zeroExtend 64).truncate 16 = z := by bv_bits
private theorem neg_zext_trunc16 (z : BitVec 16) :
    ((0#32 - (z.zeroExtend 64).truncate 32).zeroExtend 64).truncate 16 = -z := by bv_bits

@[simp, arm64_norm, wp_norm]
private theorem vec32_ofFn_get_simp (f : Nat → BitVec 128) (k : Nat) (hk : k < 32) :
    (Vec32.ofFn f).get k = f k := vec32_ofFn_get f k hk

@[simp, arm64_norm, wp_norm]
private theorem simdAdd8h_polyVecNat_simp (a b : Poly16) (k : Nat) (hk : k < 32) :
    simdAdd8h (polyVecNat b k) (polyVecNat a k) = polyVecNat (polyAdd16 a b) k :=
  simdAdd8h_polyVecNat a b k hk

local macro "s5_zero_q0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

private theorem seg5_clear_scratch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp lhsPtr rhsPtr fpVal : BitVec 64) {j : Nat} (_hj : j < 4)
    (acc : Poly16) (v28848 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hfp : s.readReg64 .fp = fpVal) (hacc : AccRegs acc s) :
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5DotMul) s
      (Poly32Mem (sp + 28848#64) v28848 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 28848#64 ∧ s'.readReg64 .x13 = 0#64 ∧
        s'.readReg64 .x14 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x19 = lhsPtr ∧ s'.readReg64 .x20 = rhsPtr ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc s' ∧ P' = (Poly32Mem (sp + 28848#64) Vec32.zero ∗ Rest)) := by
  cases v28848
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  wp_steps 3
  s5_zero_q0 31; s5_zero_q0 30; s5_zero_q0 29; s5_zero_q0 28
  s5_zero_q0 27; s5_zero_q0 26; s5_zero_q0 25; s5_zero_q0 24
  s5_zero_q0 23; s5_zero_q0 22; s5_zero_q0 21; s5_zero_q0 20
  s5_zero_q0 19; s5_zero_q0 18; s5_zero_q0 17; s5_zero_q0 16
  s5_zero_q0 15; s5_zero_q0 14; s5_zero_q0 13; s5_zero_q0 12
  s5_zero_q0 11; s5_zero_q0 10; s5_zero_q0 9; s5_zero_q0 8
  s5_zero_q0 7; s5_zero_q0 6; s5_zero_q0 5; s5_zero_q0 4
  s5_zero_q0 3; s5_zero_q0 2; s5_zero_q0 1; s5_zero_q0 0
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp; clear * -; bv_omega, by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp, by simp, by simp [hx19], by simp [hx20], by simp [hfp],
      ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
        by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
        by simp [hv30], by simp [hv31]⟩, rfl⟩
private theorem seg5_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp lhsPtr rhsPtr x8v fpVal : BitVec 64) (lhs rhs acc : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotMul) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64) (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (32 * r))
    (hx14 : s.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hfp : s.readReg64 .fp = fpVal) (hacc : AccRegs acc s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC07.rebase b (fun _ => none))
      (if r < 15 then b + offSeg5DotMul else b + offSeg5DotAccLo) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 28848#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 28848#64 ∧
        s'.readReg64 .x13 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x19 = lhsPtr ∧ s'.readReg64 .x20 = rhsPtr ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 28848#64)
            (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
              (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro prod
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  refine step_ldrh16_ro (k := 64 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (64 + 4 * r))) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx14]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq0
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq0)
  refine step_ldrh16_ro (k := 66 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (66 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx14]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq1
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq1)
  refine step_ldrh16_ro (k := 65 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (65 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx14]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq2
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq2)
  refine step_ldrh16_ro (k := 67 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (67 + 4 * r)))
    (wb := some (.x14, mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1))))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx14]; constructor <;> (clear * - hr; bv_omega))
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq3
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq3)
  wp_steps 3
  refine step_ldpQ128 (wb := none) (ea := lhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := lhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat lhs (2 * r)) (v2 := polyVecNat lhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)) (by wp_norm_lhs) ?_
  wp_step
  refine step_ldpQ128 (wb := none) (ea := rhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := rhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat rhs (2 * r)) (v2 := polyVecNat rhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 55
  have hz20 := lane16_buildZeta4
    ((zetaTableAt (64 + 4 * r)).zeroExtend 64) ((zetaTableAt (66 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (64 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (66 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hz21 := lane16_buildZeta4
    ((zetaTableAt (65 + 4 * r)).zeroExtend 64) ((zetaTableAt (67 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (65 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (67 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hpair := nttMulRawPair_eq_polyVecNat lhs rhs r hr _ _
    (hz20.1.trans (zext64_trunc16 _)) (hz20.2.1.trans (zext64_trunc16 _))
    (hz20.2.2.1.trans (neg_zext_trunc16 _)) (hz20.2.2.2.trans (neg_zext_trunc16 _))
    (hz21.1.trans (zext64_trunc16 _)) (hz21.2.1.trans (zext64_trunc16 _))
    (hz21.2.2.1.trans (neg_zext_trunc16 _)) (hz21.2.2.2.trans (neg_zext_trunc16 _))
  dsimp only [nttMulRawPair, buildZeta4] at hpair
  refine step_stpQ128 (wb := none) (ea := (sp + 28848#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 28848#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat prod (2 * r)) (v2 := polyVecNat prod (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [prod]; rw [← hpair.1]; simp)
    (by dsimp only [prod]; rw [← hpair.2]; simp)
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))))
    (SepStore128.right (SepStore128.right (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))))
    (by wp_norm_lhs) ?_
  intro m'; wp_step; wp_if hne
  · have hr15 : r < 15 := by
      by_contra hge; have hr_eq : r = 15 := by omega
      subst hr_eq; simp at hne
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
        by simp; clear * - hr15; bv_omega, by simp,
        by simp [hx19], by simp [hx20], by simp [hfp],
        ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
          by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
          by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
          by simp [hv30], by simp [hv31]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hbv : BitVec.ofNat 64 (32 * r) + 32#64 = 512#64 := by simpa [hx13] using hne
      have hnat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
        by simp [hr_eq], by simp [hr_eq],
        by simp [hx19], by simp [hx20], by simp [hfp],
        ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
          by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
          by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
          by simp [hv30], by simp [hv31]⟩, rfl⟩
private theorem seg5_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (sp lhsPtr rhsPtr x8v fpVal : BitVec 64) (lhs rhs acc : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSeg5DotMul → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = x8v → s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 →
      s.readReg64 .x10 = 62209#64 → s.readReg64 .x11 = 3329#64 →
      s.readReg64 .x12 = sp + 28848#64 →
      s.readReg64 .x13 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x19 = lhsPtr → s.readReg64 .x20 = rhsPtr → s.readReg64 .fp = fpVal →
      AccRegs acc s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5DotAccLo) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 28848#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
          s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧ s'.readReg64 .x10 = 62209#64 ∧
          s'.readReg64 .x11 = 3329#64 ∧ s'.readReg64 .x12 = sp + 28848#64 ∧
          s'.readReg64 .x19 = lhsPtr ∧ s'.readReg64 .x20 = rhsPtr ∧ s'.readReg64 .fp = fpVal ∧
          AccRegs acc s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
            Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hfp hacc hf
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg5_ntt_mul_iter hb s sp lhsPtr rhsPtr x8v fpVal lhs rhs acc (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hfp hacc
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', _, _, hx19', hx20', hfp', hacc', hP'⟩
    exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hfp', hacc',
      hP'.trans (by rw [polyMem_congr (update2_prefix (r := 15) hf), poly32Mem_ofFn])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hfp hacc hf
    have hr15 : r < 15 := by omega
    have hiter := seg5_ntt_mul_iter hb s sp lhsPtr rhsPtr x8v fpVal lhs rhs acc (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hfp hacc
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hx19_m, hx20_m, hfp_m, hacc_m, hPm⟩
    subst hPm
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx13_m hx14_m hx19_m hx20_m hfp_m hacc_m (update2_prefix hf)
local macro "s5_ldr0 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.left; apply SepLoad128.spill13 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Spill13.get] } }
  { wp_norm_lhs }))

local macro "s5_str0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.spill13 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Spill13.set] } }
  { wp_norm_lhs }; intro _))

local macro "s5_str1 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "s5_ldr2 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.left
    apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

private def AccMidRegs5 (acc prod : Poly16) (s : State) : Prop :=
  let acc' := polyAdd16 acc prod
  s.readVReg128 0#5 = 0#128 ∧ s.readVReg128 1#5 = polyVecNat acc 31 ∧
  s.readVReg128 2#5 = polyVecNat prod 18 ∧ s.readVReg128 3#5 = polyVecNat prod 21 ∧
  s.readVReg128 8#5 = polyVecNat acc 23 ∧ s.readVReg128 9#5 = polyVecNat acc 24 ∧
  s.readVReg128 10#5 = polyVecNat acc 25 ∧ s.readVReg128 11#5 = polyVecNat acc 26 ∧
  s.readVReg128 12#5 = polyVecNat acc 27 ∧ s.readVReg128 13#5 = polyVecNat acc 28 ∧
  s.readVReg128 14#5 = polyVecNat acc 29 ∧ s.readVReg128 15#5 = polyVecNat acc 30 ∧
  s.readVReg128 22#5 = polyVecNat acc' 13 ∧ s.readVReg128 23#5 = polyVecNat acc' 14 ∧
  s.readVReg128 24#5 = polyVecNat acc' 15 ∧ s.readVReg128 25#5 = polyVecNat acc' 16 ∧
  s.readVReg128 26#5 = polyVecNat acc' 17 ∧ s.readVReg128 27#5 = polyVecNat acc 18 ∧
  s.readVReg128 28#5 = polyVecNat acc' 19 ∧ s.readVReg128 29#5 = polyVecNat acc 20 ∧
  s.readVReg128 30#5 = polyVecNat acc 21 ∧ s.readVReg128 31#5 = polyVecNat acc 22

private def accMidVec32 (acc' : Poly16) (v : Vec32) : Vec32 :=
  { v with
    v0 := polyVecNat acc' 0, v1 := polyVecNat acc' 1, v2 := polyVecNat acc' 2,
    v3 := polyVecNat acc' 3, v4 := polyVecNat acc' 4, v5 := polyVecNat acc' 5,
    v6 := polyVecNat acc' 6, v7 := polyVecNat acc' 7, v8 := polyVecNat acc' 8,
    v9 := polyVecNat acc' 9, v10 := polyVecNat acc' 10, v11 := polyVecNat acc' 11,
    v12 := polyVecNat acc' 12 }
private theorem seg5_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp lhsPtr rhsPtr fpVal : BitVec 64) {j : Nat} (hj : j < 4)
    (acc prod : Poly16) (v26768 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotAccLo) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hfp : s.readReg64 .fp = fpVal) (hacc : AccRegs acc s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5DotAccHi) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 26768#64) v26768 ∗
        Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 3) ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 28848#64 ∧
        s'.readReg64 .x19 = lhsPtr + 512#64 ∧ s'.readReg64 .x20 = rhsPtr + 512#64 ∧
        s'.readReg64 .fp = fpVal ∧ AccMidRegs5 acc prod s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
          Poly32Mem (sp + 26768#64) (accMidVec32 acc' v26768) ∗
          Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  cases v26768
  have hacc_mk : AccSpill acc =
      ⟨polyVecNat acc 12, polyVecNat acc 11, polyVecNat acc 10, polyVecNat acc 9,
       polyVecNat acc 8, polyVecNat acc 7, polyVecNat acc 6, polyVecNat acc 5,
       polyVecNat acc 4, polyVecNat acc 3, polyVecNat acc 2, polyVecNat acc 1,
       polyVecNat acc 0⟩ := by simp [AccSpill, Spill13.ofFn]
  rw [hacc_mk]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  s5_ldr2 0; s5_ldr0 12; wp_step; s5_ldr2 1; s5_ldr0 11; wp_steps 2; s5_ldr2 2; s5_ldr0 10
  wp_step; s5_ldr2 3; s5_ldr0 9; wp_step; s5_ldr2 4; wp_steps 2; s5_str0 12; s5_ldr2 5
  s5_str1 0; s5_ldr0 8; s5_str0 11; s5_str1 1; s5_ldr0 7; wp_step; s5_ldr2 6; s5_str0 10
  wp_step; s5_ldr2 7; s5_str1 2; s5_str0 9; s5_ldr0 6; s5_str1 3; s5_ldr0 5; wp_step
  s5_ldr2 8; s5_str0 8; wp_step; s5_str1 4; s5_ldr0 4; s5_ldr2 9; s5_str0 7; s5_str1 5
  s5_ldr0 3; wp_step; s5_ldr2 10; s5_str0 6; wp_step; s5_ldr2 11; s5_str1 6; s5_str0 5
  s5_ldr0 2; s5_str1 7; s5_ldr0 1; wp_step; s5_ldr2 12; s5_str0 4; wp_step; s5_ldr2 13
  s5_str1 8; s5_ldr0 0; s5_str0 3; wp_step; s5_ldr2 15; s5_str1 9; wp_step; s5_ldr2 14
  s5_str0 2; wp_step; s5_ldr2 17; s5_str1 10; wp_step; s5_ldr2 16; s5_str0 1; wp_step
  s5_ldr2 19; s5_str1 11; wp_step; s5_ldr2 18; s5_str0 0; wp_step; s5_ldr2 21; s5_str1 12
  have hpst : ConditionHolds .NE (AddWithCarry64 (BitVec.ofNat 64 (j + 1)) 0xfffffffffffffffb#64 true).2 =
      decide (j < 3) := by
    clear * - hj; rcases j with _ | _ | _ | _ | _ <;> try omega
    all_goals decide
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [subsPState64, hpst],
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
      by simp, by simp, by simp [hfp],
      ⟨by simp [hv0], by simp [hv1], by simp, by simp,
        by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15],
        by simp, by simp, by simp, by simp, by simp,
        by simp [hv27], by simp, by simp [hv29], by simp [hv30], by simp [hv31]⟩,
      by simp [AccSpill, Spill13.ofFn, accMidVec32]⟩
private theorem seg5_accum_hi [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl07 b)
    (s : State) (sp x19v x20v fpVal : BitVec 64) {j : Nat}
    (acc prod : Poly16) (v26768 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotAccHi) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 3))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = x20v)
    (hfp : s.readReg64 .fp = fpVal) (hmid : AccMidRegs5 acc prod s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC07.rebase b (fun _ => none))
      (if j < 3 then b + offSeg5DotStart else b + offSeg5InvLow) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
        Poly32Mem (sp + 26768#64) (accMidVec32 acc' v26768) ∗
        Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 28848#64 ∧
        s'.readReg64 .x19 = x19v ∧ s'.readReg64 .x20 = x20v ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc' s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
          Poly32Mem (sp + 26768#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [accMidVec32]
  cases v26768
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv0, hv1, hv2, hv3, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  wp_step; s5_ldr2 20; s5_str1 13; wp_step; s5_ldr2 23; s5_str1 14; wp_step; s5_ldr2 22
  s5_str1 15; wp_step; s5_ldr2 25; s5_str1 16; wp_step; s5_ldr2 24; s5_str1 17; wp_step
  s5_ldr2 27; s5_str1 18; wp_step; s5_ldr2 26; s5_str1 19; wp_step; s5_ldr2 29; s5_str1 20
  wp_step; s5_ldr2 28; s5_str1 21; wp_step; s5_ldr2 31; s5_str1 22; wp_step; s5_ldr2 30
  s5_str1 23; wp_step; s5_str1 24; wp_step; s5_str1 25; s5_str1 26; s5_str1 27; s5_str1 28
  s5_str1 29; s5_str1 30; s5_str1 31
  by_cases hj3 : j < 3
  · simp only [hj3, ↓reduceIte]
    refine step_bCond_taken (dst := b + offSeg5DotStart)
      (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
      (by simp [hpst, hj3]) (by clear * -; dsimp [offSeg5DotStart]; bv_omega) ?_
    exact SepWP.done rfl (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
        by simp [hx19], by simp [hx20], by simp [hfp],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp,
          by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        by simp [Vec32.ofFn]⟩
  · simp only [hj3, ↓reduceIte]
    refine step_bCond_not_taken (dst := b + offSeg5InvLow)
      (by wp_norm_lhs) (by simp [*]) (by wp_norm_lhs)
      (by simp [hpst, hj3]) (by clear * -; dsimp [offSeg5InvLow]; bv_omega) ?_
    exact SepWP.done rfl (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
        by simp [hx19], by simp [hx20], by simp [hfp],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp,
          by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        by simp [Vec32.ofFn]⟩
private theorem seg5_outer_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp lhsPtr rhsPtr fpVal : BitVec 64) {j : Nat} (hj : j < 4)
    (lhs rhs acc : Poly16) (v26768 v28848 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hfp : s.readReg64 .fp = fpVal) (hacc : AccRegs acc s) :
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC07.rebase b (fun _ => none))
      (if j < 3 then b + offSeg5DotStart else b + offSeg5InvLow) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 26768#64) v26768 ∗
        Poly32Mem (sp + 28848#64) v28848 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 28848#64 ∧
        s'.readReg64 .x19 = lhsPtr + 512#64 ∧ s'.readReg64 .x20 = rhsPtr + 512#64 ∧
        s'.readReg64 .fp = fpVal ∧ AccRegs acc' s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem rhsPtr (polyVecNat rhs) ∗
          Poly32Mem (sp + 26768#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro prod acc'
  rw [show (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 26768#64) v26768 ∗
        Poly32Mem (sp + 28848#64) v28848 ∗ Rest) =
      (Poly32Mem (sp + 28848#64) v28848 ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Spill13Mem (sp + 2224#64) (AccSpill acc) ∗
        Poly32Mem (sp + 26768#64) v26768 ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (seg5_clear_scratch hb s sp lhsPtr rhsPtr fpVal hj acc v28848 _
    hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx19 hx20 hfp hacc) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx19_1, hx20_1, hfp1, hacc1, rfl⟩
  rw [show (Poly32Mem (sp + 28848#64) Vec32.zero ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Spill13Mem (sp + 2224#64) (AccSpill acc) ∗
        Poly32Mem (sp + 26768#64) v26768 ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 28848#64) Vec32.zero.get ∗
        (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 26768#64) v26768 ∗ Rest)) from by
    change (PolyMem (sp + 28848#64) Vec32.zero.get ∗ _) = _; exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (seg5_ntt_mul_loop hb sp lhsPtr rhsPtr _ fpVal lhs rhs acc _ 15 0 rfl
    s1 Vec32.zero.get hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1
    hx13_1 hx14_1 hx19_1 hx20_1 hfp1 hacc1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hfp2, hacc2, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 26768#64) v26768 ∗ Rest)) =
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 26768#64) v26768 ∗
        Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (seg5_accum_lo hb s2 sp lhsPtr rhsPtr fpVal hj acc prod v26768 _
    hpc2 hrun2 hsp2 hspA2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx19_2 hx20_2 hfp2 hacc2) ?_
  rintro sm Pm hpcm hrunm
    ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hx12m, hx19m, hx20m, hfpm, hmidm, rfl⟩
  refine SepWP.mono (seg5_accum_hi hb sm sp (lhsPtr + 512#64) (rhsPtr + 512#64) fpVal
    acc prod v26768 _ hpcm hrunm hspm hspAm hpstm hx8m hx9m hx10m hx11m hx12m hx19m hx20m hfpm hmidm) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hfp', hacc', rfl⟩
  exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hfp', hacc',
    sepProp_ext (by sep_frame) (by sep_frame)⟩
theorem seg5_dot_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl07 b)
    (s : State) (sp fpVal : BitVec 64) (t0 t1 t2 t3 r0 r1 r2 r3 : Poly16)
    (v26768 v28848 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg5DotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 28848#64)
    (hx19 : s.readReg64 .x19 = sp + 10752#64) (hx20 : s.readReg64 .x20 = sp + 12832#64)
    (hfp : s.readReg64 .fp = fpVal) (hacc : AccRegs polyZero16 s) :
    let dot := neonDot4 t0 t1 t2 t3 r0 r1 r2 r3
    SepWP (blkPC07.rebase b (fun _ => none)) (b + offSeg5InvLow) s
      (Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
        PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
        PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12288#64) (polyVecNat t3) ∗
        PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
        PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 26768#64) v26768 ∗ Poly32Mem (sp + 28848#64) v28848 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = fpVal ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill dot) ∗
          PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
          PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12288#64) (polyVecNat t3) ∗
          PolyMem (sp + 12832#64) (polyVecNat r0) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
          PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
          PolyMem (sp + 26768#64) (polyVecNat dot) ∗
          Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 t3 r3))) ∗ Rest)) := by
  dsimp only
  let p0 := neonPolyNttMul16 t0 r0
  let p1 := neonPolyNttMul16 t1 r1
  let p2 := neonPolyNttMul16 t2 r2
  let acc1 := polyAdd16 p0 p1
  let acc2 := polyAdd16 acc1 p2
  let dot := neonDot4 t0 t1 t2 t3 r0 r1 r2 r3
  let Rest0 : SepProp := PolyMem (sp + 11264#64) (polyVecNat t1) ∗ PolyMem (sp + 11776#64) (polyVecNat t2) ∗
    PolyMem (sp + 12288#64) (polyVecNat t3) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
    PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗ Rest
  let Rest1 : SepProp := PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11776#64) (polyVecNat t2) ∗
    PolyMem (sp + 12288#64) (polyVecNat t3) ∗ PolyMem (sp + 12832#64) (polyVecNat r0) ∗
    PolyMem (sp + 13856#64) (polyVecNat r2) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗ Rest
  let Rest2 : SepProp := PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
    PolyMem (sp + 12288#64) (polyVecNat t3) ∗ PolyMem (sp + 12832#64) (polyVecNat r0) ∗
    PolyMem (sp + 13344#64) (polyVecNat r1) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗ Rest
  let Rest3 : SepProp := PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 11264#64) (polyVecNat t1) ∗
    PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 12832#64) (polyVecNat r0) ∗
    PolyMem (sp + 13344#64) (polyVecNat r1) ∗ PolyMem (sp + 13856#64) (polyVecNat r2) ∗ Rest
  refine SepWP.weaken_pre (show _ ⊢ Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
      PolyMem (sp + 10752#64) (polyVecNat t0) ∗ PolyMem (sp + 12832#64) (polyVecNat r0) ∗
      Poly32Mem (sp + 26768#64) v26768 ∗ Poly32Mem (sp + 28848#64) v28848 ∗ Rest0 by
    dsimp only [Rest0]; sep_frame) ?_
  have hj0 := seg5_outer_iter hb s sp (sp + 10752#64) (sp + 12832#64) fpVal (j := 0) (by omega)
    t0 r0 polyZero16 v26768 v28848 Rest0 hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx19 hx20 hfp hacc
  dsimp only at hj0
  simp only [show (0 : Nat) < 3 by decide, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size t0 r0)] at hj0
  refine sepWP_seq_env hcl hro hj0 ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx19_1, hx20_1, hfp1, hacc1, rfl⟩
  refine SepWP.weaken_pre (show _ ⊢ Spill13Mem (sp + 2224#64) (AccSpill p0) ∗
      PolyMem (sp + 11264#64) (polyVecNat t1) ∗ PolyMem (sp + 13344#64) (polyVecNat r1) ∗
      Poly32Mem (sp + 26768#64) (Vec32.ofFn (polyVecNat p0)) ∗
      Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1 by
    dsimp only [Rest0, Rest1]; sep_frame) ?_
  have hj1 := seg5_outer_iter hb s1 sp (sp + 11264#64) (sp + 13344#64) fpVal (j := 1) (by omega)
    t1 r1 p0 (Vec32.ofFn (polyVecNat p0)) (Vec32.ofFn (polyVecNat p0)) Rest1
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1
    (by simpa [show (sp + 10752#64) + 512#64 = sp + 11264#64 by clear * -; bv_omega] using hx19_1)
    (by simpa [show (sp + 12832#64) + 512#64 = sp + 13344#64 by clear * -; bv_omega] using hx20_1)
    hfp1 hacc1
  dsimp only at hj1; simp only [show (1 : Nat) < 3 by decide, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl1 hro1 hj1 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hfp2, hacc2, rfl⟩
  refine SepWP.weaken_pre (show _ ⊢ Spill13Mem (sp + 2224#64) (AccSpill acc1) ∗
      PolyMem (sp + 11776#64) (polyVecNat t2) ∗ PolyMem (sp + 13856#64) (polyVecNat r2) ∗
      Poly32Mem (sp + 26768#64) (Vec32.ofFn (polyVecNat acc1)) ∗
      Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2 by
    dsimp only [Rest1, Rest2]; sep_frame) ?_
  have hj2 := seg5_outer_iter hb s2 sp (sp + 11776#64) (sp + 13856#64) fpVal (j := 2) (by omega)
    t2 r2 acc1 (Vec32.ofFn (polyVecNat acc1)) (Vec32.ofFn (polyVecNat p1)) Rest2
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2
    (by simpa [show (sp + 11264#64) + 512#64 = sp + 11776#64 by clear * -; bv_omega] using hx19_2)
    (by simpa [show (sp + 13344#64) + 512#64 = sp + 13856#64 by clear * -; bv_omega] using hx20_2)
    hfp2 hacc2
  dsimp only at hj2; simp only [show (2 : Nat) < 3 by decide, ↓reduceIte] at hj2
  refine sepWP_seq_env hcl2 hro2 hj2 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hfp3, hacc3, rfl⟩
  refine SepWP.weaken_pre (show _ ⊢ Spill13Mem (sp + 2224#64) (AccSpill acc2) ∗
      PolyMem (sp + 12288#64) (polyVecNat t3) ∗ PolyMem (sp + 14368#64) (polyVecNat r3) ∗
      Poly32Mem (sp + 26768#64) (Vec32.ofFn (polyVecNat acc2)) ∗
      Poly32Mem (sp + 28848#64) (Vec32.ofFn (polyVecNat p2)) ∗ Rest3 by
    dsimp only [Rest2, Rest3]; sep_frame) ?_
  have hj3 := seg5_outer_iter hb s3 sp (sp + 12288#64) (sp + 14368#64) fpVal (j := 3) (by omega)
    t3 r3 acc2 (Vec32.ofFn (polyVecNat acc2)) (Vec32.ofFn (polyVecNat p2)) Rest3
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3 hx9_3 hx10_3 hx11_3 hx12_3
    (by simpa [show (sp + 11776#64) + 512#64 = sp + 12288#64 by clear * -; bv_omega] using hx19_3)
    (by simpa [show (sp + 13856#64) + 512#64 = sp + 14368#64 by clear * -; bv_omega] using hx20_3)
    hfp3 hacc3
  dsimp only at hj3; simp only [Nat.lt_irrefl, ↓reduceIte] at hj3
  refine SepWP.mono hj3 ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, hfp', _, rfl⟩
  refine ⟨hsp', hspA', hfp', ?_⟩
  rw [poly32Mem_ofFn]
  dsimp only [dot, neonDot4, neonDot3, acc2, acc1, p0, p1, p2, Rest3]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5Dot
