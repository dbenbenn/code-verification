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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `kyber_decapsulate` (`B06`) — Segment 8 4-Way NTT Dot Product (`+0xb8bc .. +0xbc6c`)

Proves `seg8_dot3_ok` (`+0xb8bc → +0xbc6c`): 4-iteration outer `ntt_multiply` + accumulate loop
computing `dot = neonDot4 t0 t1 t2 t3 r0 r1 r2 r3` in `PolyMem (sp + 28368#64) (polyVecNat dot)`
and `Spill13Mem (sp + 2224#64) (AccSpill dot)`, preserving `x22 = ctA` and `fp = fpVal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Dot3

open Arm64 Arm64.Obj ProofLib SepProp
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (
  AccMidRegs04 accMidVec32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Spill13 Spill13Mem
  Vec32 VecRangeMem poly32Mem_ofFn polyVecNat spill13_ofFn_get spill13_set_get
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128 vec32_ofFn_get vecRangeMem_congr
  vecRangeMem_entails_memRegion)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs AccSpill)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul (neonDot4 ro00Sym)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0xb8bc → 0xbc68]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg8Dot   : BitVec 64 := BitVec.ofNat 64 47292
@[simp, arm64_norm, wp_norm] abbrev offSeg8Mul   : BitVec 64 := BitVec.ofNat 64 47432
@[simp, arm64_norm, wp_norm] abbrev offSeg8AccLo : BitVec 64 := BitVec.ofNat 64 47732
@[simp, arm64_norm, wp_norm] abbrev offSeg8AccHi : BitVec 64 := BitVec.ofNat 64 48060
@[simp, arm64_norm, wp_norm] abbrev offSeg8Inv   : BitVec 64 := BitVec.ofNat 64 48236

@[simp, arm64_norm, wp_norm]
private theorem blkPl06_ρ [MlKemPlacement] (sym : String) :
    blkPl06.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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
  blkPC06 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdUzp1_4s simdRev64_4s simdSmull4s simdSmlal4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdDup_8h_gpr svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s
  svc_simdUzp1_4s svc_simdRev64_4s svc_simdExt_16b_8 svc_simdSmull_4s svc_simdSmlal_4s

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

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
private theorem accSpill_get_simp (acc : Poly16) (k : Nat) (hk : k < 13) :
    (AccSpill acc).get k = polyVecNat acc (12 - k) := spill13_ofFn_get _ k hk

@[simp, arm64_norm, wp_norm]
private theorem spill13_set_get_simp (t : Spill13) (k : Nat) (x : BitVec 128) (i : Nat)
    (hk : k < 13) (hi : i < 13) :
    (t.set k x).get i = if i = k then x else t.get i := by
  simpa [Function.update] using (spill13_set_get t k x hk i hi).symm

@[simp, arm64_norm, wp_norm]
private theorem simdAdd8h_polyVecNat_simp (a b : Poly16) (k : Nat) (hk : k < 32) :
    simdAdd8h (polyVecNat b k) (polyVecNat a k) = polyVecNat (polyAdd16 a b) k :=
  simdAdd8h_polyVecNat a b k hk

local macro "s8_zero0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "step_zero32_q0" : tactic => `(tactic| (
  s8_zero0 31; s8_zero0 30; s8_zero0 29; s8_zero0 28;
  s8_zero0 27; s8_zero0 26; s8_zero0 25; s8_zero0 24;
  s8_zero0 23; s8_zero0 22; s8_zero0 21; s8_zero0 20;
  s8_zero0 19; s8_zero0 18; s8_zero0 17; s8_zero0 16;
  s8_zero0 15; s8_zero0 14; s8_zero0 13; s8_zero0 12;
  s8_zero0 11; s8_zero0 10; s8_zero0 9; s8_zero0 8;
  s8_zero0 7; s8_zero0 6; s8_zero0 5; s8_zero0 4;
  s8_zero0 3; s8_zero0 2; s8_zero0 1; s8_zero0 0))

private theorem seg8_clear_scratch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp lhsPtr rhsPtr ctA fpVal : BitVec 64) {j : Nat} (_hj : j < 4)
    (acc : Poly16) (v30448 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Dot) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs acc s) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Mul) s
      (Poly32Mem (sp + 30448#64) v30448 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x13 = 0#64 ∧
        s'.readReg64 .x14 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x19 = lhsPtr ∧ s'.readReg64 .x20 = rhsPtr ∧
        s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc s' ∧ P' = (Poly32Mem (sp + 30448#64) Vec32.zero ∗ Rest)) := by
  have _ : blkPl06.base = b := _hb.symm; subst b
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  wp_steps 3; step_zero32_q0
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp; clear * -; bv_omega, by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp, by simp, by simp [hx19], by simp [hx20],
      by simp [hx22], by simp [hfp],
      ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
        by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
        by simp [hv30], by simp [hv31]⟩, rfl⟩

private theorem seg8_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp lhsPtr rhsPtr x8v ctA fpVal : BitVec 64) (lhs rhs acc : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Mul) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 (32 * r))
    (hx14 : s.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs acc s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + offSeg8Mul else b + offSeg8AccLo) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 30448#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧
        s'.readReg64 .x13 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x19 = lhsPtr ∧ s'.readReg64 .x20 = rhsPtr ∧
        s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧ AccRegs acc s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 30448#64)
            (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
              (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro prod
  have _ : blkPl06.base = b := _hb.symm; subst b
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
  refine step_stpQ128 (wb := none) (ea := (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 30448#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
        by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
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
        by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
        ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
          by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
          by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
          by simp [hv30], by simp [hv31]⟩, rfl⟩

private theorem seg8_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (sp lhsPtr rhsPtr x8v ctA fpVal : BitVec 64) (lhs rhs acc : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offSeg8Mul → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = x8v → s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 →
      s.readReg64 .x10 = 62209#64 → s.readReg64 .x11 = 3329#64 →
      s.readReg64 .x12 = sp + 30448#64 →
      s.readReg64 .x13 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x14 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x19 = lhsPtr → s.readReg64 .x20 = rhsPtr →
      s.readReg64 .x22 = ctA → s.readReg64 .fp = fpVal →
      AccRegs acc s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8AccLo) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 30448#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
          s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
          s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
          s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = lhsPtr ∧
          s'.readReg64 .x20 = rhsPtr ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
          AccRegs acc s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
            Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hx22 hfp hacc hf
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg8_ntt_mul_iter hb s sp lhsPtr rhsPtr x8v ctA fpVal lhs rhs acc (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hx22 hfp hacc
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', _, _, hx19', hx20', hx22', hfp', hacc', hP'⟩
    exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hx22', hfp', hacc',
      hP'.trans (by rw [polyMem_congr (update2_prefix (r := 15) hf), poly32Mem_ofFn])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hx22 hfp hacc hf
    have hr15 : r < 15 := by omega
    have hiter := seg8_ntt_mul_iter hb s sp lhsPtr rhsPtr x8v ctA fpVal lhs rhs acc (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx19 hx20 hx22 hfp hacc
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hx19_m, hx20_m, hx22_m, hfp_m, hacc_m, hPm⟩
    subst hPm
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx13_m hx14_m hx19_m hx20_m hx22_m hfp_m hacc_m (update2_prefix hf)

local macro "s8_ldr0 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.left; apply SepLoad128.spill13 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Spill13.get] } }
  { wp_norm_lhs }))

local macro "s8_str0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.spill13 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Spill13.set] } }
  { wp_norm_lhs }; intro _))

local macro "s8_str1 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.right; apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "s8_ldr2 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.right; apply SepLoad128.right; apply SepLoad128.left
    apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

private theorem seg8_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp lhsPtr rhsPtr ctA fpVal : BitVec 64) {j : Nat} (hj : j < 4)
    (acc prod : Poly16) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8AccLo) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs acc s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8AccHi) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 3) ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = lhsPtr + 512#64 ∧
        s'.readReg64 .x20 = rhsPtr + 512#64 ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccMidRegs04 acc prod s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
          Poly32Mem (sp + 28368#64) (accMidVec32 acc' v28368) ∗
          Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  have _ : blkPl06.base = b := _hb.symm; subst b
  cases v28368
  have hacc_mk : AccSpill acc =
      ⟨polyVecNat acc 12, polyVecNat acc 11, polyVecNat acc 10, polyVecNat acc 9,
       polyVecNat acc 8, polyVecNat acc 7, polyVecNat acc 6, polyVecNat acc 5,
       polyVecNat acc 4, polyVecNat acc 3, polyVecNat acc 2, polyVecNat acc 1,
       polyVecNat acc 0⟩ := by simp [AccSpill, Spill13.ofFn]
  rw [hacc_mk]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  s8_ldr2 0; s8_ldr0 12; wp_step; s8_ldr2 1; s8_ldr0 11; wp_step; wp_step
  s8_ldr2 2; s8_ldr0 10; wp_step; s8_ldr2 3; s8_ldr0 9; wp_step; s8_ldr2 4; wp_step; wp_step
  s8_str0 12; s8_ldr2 5; s8_str1 0; s8_ldr0 8; s8_str0 11; s8_str1 1; s8_ldr0 7; wp_step
  s8_ldr2 6; s8_str0 10; wp_step; s8_ldr2 7; s8_str1 2; s8_str0 9; s8_ldr0 6; s8_str1 3; s8_ldr0 5; wp_step
  s8_ldr2 8; s8_str0 8; wp_step; s8_str1 4; s8_ldr0 4; s8_ldr2 9; s8_str0 7; s8_str1 5; s8_ldr0 3; wp_step
  s8_ldr2 10; s8_str0 6; wp_step; s8_ldr2 11; s8_str1 6; s8_str0 5; s8_ldr0 2; s8_str1 7; s8_ldr0 1; wp_step
  s8_ldr2 12; s8_str0 4; wp_step; s8_ldr2 13; s8_str1 8; s8_ldr0 0; s8_str0 3; wp_step
  s8_ldr2 15; s8_str1 9; wp_step; s8_ldr2 14; s8_str0 2; wp_step; s8_ldr2 17; s8_str1 10; wp_step
  s8_ldr2 16; s8_str0 1; wp_step; s8_ldr2 19; s8_str1 11; wp_step; s8_ldr2 18; s8_str0 0; wp_step
  s8_ldr2 21; s8_str1 12
  have hpst : ConditionHolds .NE (AddWithCarry64 (BitVec.ofNat 64 (j + 1)) (~~~4#64) true).2 =
      decide (j < 3) := by
    clear * - hj; rcases j with _ | _ | _ | _ | _ <;> try omega
    all_goals decide
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simpa [subsPState64, hx8] using hpst,
      by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11], by simp [hx12],
      by simp, by simp, by simp [hx22], by simp [hfp],
      ⟨by simp [hv0], by simp [hv1], by simp, by simp,
        by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15],
        by simp, by simp, by simp, by simp, by simp,
        by simp [hv27], by simp, by simp [hv29], by simp [hv30], by simp [hv31]⟩,
      by simp [AccSpill, Spill13.ofFn, accMidVec32]⟩

private theorem seg8_accum_hi [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s : State) (sp x19v x20v ctA fpVal : BitVec 64) {j : Nat}
    (acc prod : Poly16) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8AccHi) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 3))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1))
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = x19v) (hx20 : s.readReg64 .x20 = x20v)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hmid : AccMidRegs04 acc prod s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none))
      (if j < 3 then b + offSeg8Dot else b + offSeg8Inv) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
        Poly32Mem (sp + 28368#64) (accMidVec32 acc' v28368) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = x19v ∧
        s'.readReg64 .x20 = x20v ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc' s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗
          Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [accMidVec32]
  have _ : blkPl06.base = b := _hb.symm; subst b
  cases v28368
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv0, hv1, hv2, hv3, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  wp_step; s8_ldr2 20; s8_str1 13; wp_step; s8_ldr2 23; s8_str1 14
  wp_step; s8_ldr2 22; s8_str1 15; wp_step; s8_ldr2 25; s8_str1 16
  wp_step; s8_ldr2 24; s8_str1 17; wp_step; s8_ldr2 27; s8_str1 18
  wp_step; s8_ldr2 26; s8_str1 19; wp_step; s8_ldr2 29; s8_str1 20
  wp_step; s8_ldr2 28; s8_str1 21; wp_step; s8_ldr2 31; s8_str1 22
  wp_step; s8_ldr2 30; s8_str1 23; wp_step; s8_str1 24; wp_step
  s8_str1 25; s8_str1 26; s8_str1 27; s8_str1 28; s8_str1 29; s8_str1 30; s8_str1 31
  wp_step; wp_if hne
  · have hj3 : j < 3 := by simpa [hpst] using hne
    simp only [hj3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        by simp [Vec32.ofFn]⟩
  · have hj3 : ¬ j < 3 := by simpa [hpst] using hne
    simp only [hj3, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx19], by simp [hx20], by simp [hx22], by simp [hfp],
        ⟨by simp [hv0], by simp,
          by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
          by simp [hv22], by simp [hv23], by simp [hv24], by simp [hv25], by simp [hv26],
          by simp, by simp [hv28], by simp, by simp, by simp⟩,
        by simp [Vec32.ofFn]⟩

private theorem seg8_outer_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp lhsPtr rhsPtr ctA fpVal : BitVec 64) {j : Nat} (hj : j < 4)
    (lhs rhs acc : Poly16) (v28368 v30448 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Dot) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j)
    (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = lhsPtr) (hx20 : s.readReg64 .x20 = rhsPtr)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs acc s) :
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC06.rebase b (fun _ => none)) (if j < 3 then b + offSeg8Dot else b + offSeg8Inv) s
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 30448#64) v30448 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x10 = 62209#64 ∧ s'.readReg64 .x11 = 3329#64 ∧
        s'.readReg64 .x12 = sp + 30448#64 ∧ s'.readReg64 .x19 = lhsPtr + 512#64 ∧
        s'.readReg64 .x20 = rhsPtr + 512#64 ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        AccRegs acc' s' ∧
        P' = (Spill13Mem (sp + 2224#64) (AccSpill acc') ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro prod acc'
  rw [show (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 30448#64) v30448 ∗ Rest) =
      (Poly32Mem (sp + 30448#64) v30448 ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (seg8_clear_scratch hb s sp lhsPtr rhsPtr ctA fpVal hj acc v30448 _
    hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx19 hx20 hx22 hfp hacc) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx19_1, hx20_1, hx22_1, hfp_1, hacc1, rfl⟩
  rw [show (Poly32Mem (sp + 30448#64) Vec32.zero ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 30448#64) Vec32.zero.get ∗
        (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) from by
    change (PolyMem (sp + 30448#64) Vec32.zero.get ∗ _) = _; exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (seg8_ntt_mul_loop hb sp lhsPtr rhsPtr _ ctA fpVal lhs rhs acc _ 15 0 rfl
    s1 Vec32.zero.get hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1
    hx19_1 hx20_1 hx22_1 hfp_1 hacc1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hx22_2, hfp_2, hacc2, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) =
      (Spill13Mem (sp + 2224#64) (AccSpill acc) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (seg8_accum_lo hb s2 sp lhsPtr rhsPtr ctA fpVal hj acc prod v28368 _
    hpc2 hrun2 hsp2 hspA2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx19_2 hx20_2 hx22_2 hfp_2 hacc2) ?_
  rintro sm Pm hpcm hrunm ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hx12m, hx19m, hx20m, hx22m, hfpm, hmidm, rfl⟩
  refine SepWP.mono (seg8_accum_hi hb sm sp (lhsPtr + 512#64) (rhsPtr + 512#64) ctA fpVal acc prod v28368 _
    hpcm hrunm hspm hspAm hpstm hx8m hx9m hx10m hx11m hx12m hx19m hx20m hx22m hfpm hmidm) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hx22', hfp', hacc', rfl⟩
  exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx19', hx20', hx22', hfp', hacc',
    sepProp_ext (by sep_frame) (by sep_frame)⟩

theorem seg8_dot3_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s : State) (sp ctA fpVal : BitVec 64)
    (t0 t1 t2 t3 r0 r1 r2 r3 : Poly16) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offSeg8Dot) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx10 : s.readReg64 .x10 = 62209#64) (hx11 : s.readReg64 .x11 = 3329#64)
    (hx12 : s.readReg64 .x12 = sp + 30448#64)
    (hx19 : s.readReg64 .x19 = sp + 12352#64) (hx20 : s.readReg64 .x20 = sp + 14432#64)
    (hx22 : s.readReg64 .x22 = ctA) (hfp : s.readReg64 .fp = fpVal)
    (hacc : AccRegs polyZero16 s) :
    let dot := neonDot4 t0 t1 t2 t3 r0 r1 r2 r3
    SepWP (blkPC06.rebase b (fun _ => none)) (b + offSeg8Inv) s
      (Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
        PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
        PolyMem (sp + 13376#64) (polyVecNat t2) ∗ PolyMem (sp + 13888#64) (polyVecNat t3) ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ memRegion (sp + 30448#64) 512 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x22 = ctA ∧ s'.readReg64 .fp = fpVal ∧
        (P' ⊢ (Spill13Mem (sp + 2224#64) (AccSpill dot) ∗
          PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
          PolyMem (sp + 13376#64) (polyVecNat t2) ∗ PolyMem (sp + 13888#64) (polyVecNat t3) ∗
          PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
          PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
          PolyMem (sp + 28368#64) (polyVecNat dot) ∗ memRegion (sp + 30448#64) 512 ∗ Rest))) := by
  intro dot
  refine SepWP.of_memRegion_vecRangeMem 32 (sp + 30448#64) (by decide) (by sep_focus) fun f30448 => ?_
  rw [show VecRangeMem 32 (sp + 30448#64) f30448 = Poly32Mem (sp + 30448#64) (Vec32.ofFn f30448) from
    (poly32Mem_ofFn _ _).symm]
  let p0 := neonPolyNttMul16 t0 r0
  let p1 := neonPolyNttMul16 t1 r1
  let p2 := neonPolyNttMul16 t2 r2
  let acc1 := polyAdd16 p0 p1
  let acc2 := polyAdd16 acc1 p2
  let Rest0 : SepProp :=
    PolyMem (sp + 12864#64) (polyVecNat t1) ∗ PolyMem (sp + 13376#64) (polyVecNat t2) ∗
    PolyMem (sp + 13888#64) (polyVecNat t3) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
    PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗ Rest
  let Rest1 : SepProp :=
    PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 13376#64) (polyVecNat t2) ∗
    PolyMem (sp + 13888#64) (polyVecNat t3) ∗ PolyMem (sp + 14432#64) (polyVecNat r0) ∗
    PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗ Rest
  let Rest2 : SepProp :=
    PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
    PolyMem (sp + 13888#64) (polyVecNat t3) ∗ PolyMem (sp + 14432#64) (polyVecNat r0) ∗
    PolyMem (sp + 14944#64) (polyVecNat r1) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗ Rest
  let Rest3 : SepProp :=
    PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
    PolyMem (sp + 13376#64) (polyVecNat t2) ∗ PolyMem (sp + 14432#64) (polyVecNat r0) ∗
    PolyMem (sp + 14944#64) (polyVecNat r1) ∗ PolyMem (sp + 15456#64) (polyVecNat r2) ∗ Rest
  rw [show (Poly32Mem (sp + 30448#64) (Vec32.ofFn f30448) ∗
        (Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗
        PolyMem (sp + 12352#64) (polyVecNat t0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
        PolyMem (sp + 13376#64) (polyVecNat t2) ∗ PolyMem (sp + 13888#64) (polyVecNat t3) ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ PolyMem (sp + 14944#64) (polyVecNat r1) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ PolyMem (sp + 15968#64) (polyVecNat r3) ∗
        Poly32Mem (sp + 28368#64) v28368 ∗ Rest)) =
      (Spill13Mem (sp + 2224#64) (AccSpill polyZero16) ∗ PolyMem (sp + 12352#64) (polyVecNat t0) ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ Poly32Mem (sp + 28368#64) v28368 ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn f30448) ∗ Rest0) from
    sepProp_ext (by dsimp only [Rest0]; sep_frame) (by dsimp only [Rest0]; sep_frame)]
  have hj0 := seg8_outer_iter hb s sp (sp + 12352#64) (sp + 14432#64) ctA fpVal (j := 0) (by omega)
    t0 r0 polyZero16 v28368 (Vec32.ofFn f30448) Rest0
    hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx19 hx20 hx22 hfp hacc
  dsimp only at hj0
  simp only [show 0 < 3 by omega, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size t0 r0)] at hj0
  refine sepWP_seq_env hcl hro hj0 ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx19_1, hx20_1, hx22_1, hfp_1, hacc1, rfl⟩
  rw [show (Spill13Mem (sp + 2224#64) (AccSpill p0) ∗ PolyMem (sp + 12352#64) (polyVecNat t0) ∗
        PolyMem (sp + 14432#64) (polyVecNat r0) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest0) =
      (Spill13Mem (sp + 2224#64) (AccSpill p0) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
        PolyMem (sp + 14944#64) (polyVecNat r1) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1) from
    sepProp_ext (by dsimp only [Rest0, Rest1]; sep_frame) (by dsimp only [Rest0, Rest1]; sep_frame)]
  have hj1 := seg8_outer_iter hb s1 sp (sp + 12864#64) (sp + 14944#64) ctA fpVal (j := 1) (by omega)
    t1 r1 p0 (Vec32.ofFn (polyVecNat p0)) (Vec32.ofFn (polyVecNat p0)) Rest1
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1
    (by simpa [show (sp + 12352#64) + 512#64 = sp + 12864#64 by clear * -; bv_omega] using hx19_1)
    (by simpa [show (sp + 14432#64) + 512#64 = sp + 14944#64 by clear * -; bv_omega] using hx20_1)
    hx22_1 hfp_1 hacc1
  dsimp only at hj1; simp only [show 1 < 3 by omega, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl1 hro1 hj1 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx19_2, hx20_2, hx22_2, hfp_2, hacc2, rfl⟩
  rw [show (Spill13Mem (sp + 2224#64) (AccSpill acc1) ∗ PolyMem (sp + 12864#64) (polyVecNat t1) ∗
        PolyMem (sp + 14944#64) (polyVecNat r1) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest1) =
      (Spill13Mem (sp + 2224#64) (AccSpill acc1) ∗ PolyMem (sp + 13376#64) (polyVecNat t2) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2) from
    sepProp_ext (by dsimp only [Rest1, Rest2]; sep_frame) (by dsimp only [Rest1, Rest2]; sep_frame)]
  have hj2 := seg8_outer_iter hb s2 sp (sp + 13376#64) (sp + 15456#64) ctA fpVal (j := 2) (by omega)
    t2 r2 acc1 (Vec32.ofFn (polyVecNat acc1)) (Vec32.ofFn (polyVecNat p1)) Rest2
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2
    (by simpa [show (sp + 12864#64) + 512#64 = sp + 13376#64 by clear * -; bv_omega] using hx19_2)
    (by simpa [show (sp + 14944#64) + 512#64 = sp + 15456#64 by clear * -; bv_omega] using hx20_2)
    hx22_2 hfp_2 hacc2
  dsimp only at hj2; simp only [show 2 < 3 by omega, ↓reduceIte] at hj2
  refine sepWP_seq_env hcl2 hro2 hj2 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx8_3, hx9_3, hx10_3, hx11_3, hx12_3, hx19_3, hx20_3, hx22_3, hfp_3, hacc3, rfl⟩
  rw [show (Spill13Mem (sp + 2224#64) (AccSpill acc2) ∗ PolyMem (sp + 13376#64) (polyVecNat t2) ∗
        PolyMem (sp + 15456#64) (polyVecNat r2) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc2)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p2)) ∗ Rest2) =
      (Spill13Mem (sp + 2224#64) (AccSpill acc2) ∗ PolyMem (sp + 13888#64) (polyVecNat t3) ∗
        PolyMem (sp + 15968#64) (polyVecNat r3) ∗ Poly32Mem (sp + 28368#64) (Vec32.ofFn (polyVecNat acc2)) ∗
        Poly32Mem (sp + 30448#64) (Vec32.ofFn (polyVecNat p2)) ∗ Rest3) from
    sepProp_ext (by dsimp only [Rest2, Rest3]; sep_frame) (by dsimp only [Rest2, Rest3]; sep_frame)]
  have hj3 := seg8_outer_iter hb s3 sp (sp + 13888#64) (sp + 15968#64) ctA fpVal (j := 3) (by omega)
    t3 r3 acc2 (Vec32.ofFn (polyVecNat acc2)) (Vec32.ofFn (polyVecNat p2)) Rest3
    hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx8_3 hx9_3 hx10_3 hx11_3 hx12_3
    (by simpa [show (sp + 13376#64) + 512#64 = sp + 13888#64 by clear * -; bv_omega] using hx19_3)
    (by simpa [show (sp + 15456#64) + 512#64 = sp + 15968#64 by clear * -; bv_omega] using hx20_3)
    hx22_3 hfp_3 hacc3
  dsimp only at hj3; simp only [Nat.lt_irrefl, ↓reduceIte] at hj3
  refine SepWP.mono hj3 ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, hx22', hfp', _, rfl⟩
  refine ⟨hsp', hspA', hx22', hfp', ?_⟩
  rw [poly32Mem_ofFn, poly32Mem_ofFn]
  dsimp only [dot, neonDot4, acc2, neonDot3, acc1, p0, p1, p2, Rest3]
  have h30 : PolyMem (sp + 30448#64) (polyVecNat (neonPolyNttMul16 t3 r3)) ⊢ memRegion (sp + 30448#64) 512 :=
    vecRangeMem_entails_memRegion 32 (sp + 30448#64) _
  exact entails_sub h30 (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Dot3
