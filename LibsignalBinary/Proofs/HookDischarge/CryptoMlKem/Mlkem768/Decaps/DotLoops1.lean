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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `decapsulate_compressed_key` (`B04`) — Site 1 3-Way `ntt_multiply` + Accumulate (`+0x1b04 → +0x1eb4`)

Steps the 3-iteration outer `ntt_multiply` + accumulate loop (`j = 0, 1, 2`) over `lhsBase`
(`uHat[0..2]`) and `rhsBase` (`sHat[0..2]`), using `Spill21Mem (sp + 1920#64)` slots `8..20`
(preserving slots `0..7`), `Poly32Mem (sp + 11856#64)` as product scratch, and
`Poly32Mem (sp + 20704#64)` as output (`PolyMem (sp + 20704#64) (polyVecNat (neonDot3 l0 l1 l2 r0 r1 r2))`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1

open Arm64 Arm64.Obj ProofLib
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  SepLoad128.spill21 SepStore128.spill21 Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 poly32Mem_ofFn polyVecNat
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128 vec32_ofFn_get vecRangeMem_congr)
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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs)

/-- `Spill21` layout keeping slots `0..7` from `t0` and placing `acc[12..0]` in slots `8..20`. -/
@[expose] def AccSpill21 (t0 : Spill21) (acc : Poly16) : Spill21 :=
  ⟨t0.s0, t0.s1, t0.s2, t0.s3, t0.s4, t0.s5, t0.s6, t0.s7,
   polyVecNat acc 12, polyVecNat acc 11, polyVecNat acc 10, polyVecNat acc 9,
   polyVecNat acc 8, polyVecNat acc 7, polyVecNat acc 6, polyVecNat acc 5,
   polyVecNat acc 4, polyVecNat acc 3, polyVecNat acc 2, polyVecNat acc 1,
   polyVecNat acc 0⟩

theorem accSpill21_zero_iff (t : Spill21) :
    t = AccSpill21 t polyZero16 ↔
      t.s8 = 0#128 ∧ t.s9 = 0#128 ∧ t.s10 = 0#128 ∧ t.s11 = 0#128 ∧ t.s12 = 0#128 ∧
      t.s13 = 0#128 ∧ t.s14 = 0#128 ∧ t.s15 = 0#128 ∧ t.s16 = 0#128 ∧ t.s17 = 0#128 ∧
      t.s18 = 0#128 ∧ t.s19 = 0#128 ∧ t.s20 = 0#128 := by
  cases t; simp [AccSpill21]

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0x1b04 → 0x1eb0]
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
  blkPC04 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdUzp1_4s simdRev64_4s simdSmull4s simdSmlal4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdDup_8h_gpr svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s
  svc_simdUzp1_4s svc_simdRev64_4s svc_simdExt_16b_8 svc_simdSmull_4s svc_simdSmlal_4s

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

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

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

local macro "s1_zero0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "step_zero32_q0" : tactic => `(tactic| (
  s1_zero0 31; s1_zero0 30; s1_zero0 29; s1_zero0 28; s1_zero0 27; s1_zero0 26; s1_zero0 25; s1_zero0 24;
  s1_zero0 23; s1_zero0 22; s1_zero0 21; s1_zero0 20; s1_zero0 19; s1_zero0 18; s1_zero0 17; s1_zero0 16;
  s1_zero0 15; s1_zero0 14; s1_zero0 13; s1_zero0 12; s1_zero0 11; s1_zero0 10; s1_zero0 9; s1_zero0 8;
  s1_zero0 7; s1_zero0 6; s1_zero0 5; s1_zero0 4; s1_zero0 3; s1_zero0 2; s1_zero0 1; s1_zero0 0))

/-! ## 1. Scratch Clear (`+0x1b04 → +0x1b90`) & `ntt_multiply` Loop (`+0x1b90 → +0x1cbc`) -/

private theorem dot1_clear_scratch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (_hj : j < 3)
    (acc : Poly16) (v11856 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1b04#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x1b90#64) s
      (Poly32Mem (sp + 11856#64) v11856 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 11856#64 ∧ s'.readReg64 .x15 = 0#64 ∧
        s'.readReg64 .x16 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
        P' = (Poly32Mem (sp + 11856#64) Vec32.zero ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  wp_steps 3; step_zero32_q0
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp; clear * -; bv_omega, by simp [hx9], by simp [hx10], by simp [hx11],
      by simp [hx12], by simp [hx13], by simp [hx14], by simp, by simp,
      ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
        by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
        by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
        by simp [hv30], by simp [hv31]⟩,
      ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
        by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem dot1_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp lhsPtr rhsPtr x8v : BitVec 64) (lhs rhs acc : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x1b90#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hx15 : s.readReg64 .x15 = BitVec.ofNat 64 (32 * r))
    (hx16 : s.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC04.rebase b (fun _ => none))
      (if r < 15 then b + 0x1b90#64 else b + 0x1cbc#64) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 11856#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
        s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 11856#64 ∧
        s'.readReg64 .x15 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 11856#64)
            (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
              (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro prod
  rcases hacc with ⟨hv0, hv1, hv8, hv9, hv10, hv11, hv12, hv13, hv14, hv15,
    hv22, hv23, hv24, hv25, hv26, hv27, hv28, hv29, hv30, hv31⟩
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine step_ldrh16_ro (k := 64 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (64 + 4 * r))) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx16]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq0
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq0)
  refine step_ldrh16_ro (k := 66 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (66 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx16]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq1
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq1)
  refine step_ldrh16_ro (k := 65 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (65 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx16]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq2
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq2)
  refine step_ldrh16_ro (k := 67 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (67 + 4 * r)))
    (wb := some (.x16, mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1))))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx16]; constructor <;> (clear * - hr; bv_omega))
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
  refine step_stpQ128 (wb := none) (ea := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 11856#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat prod (2 * r)) (v2 := polyVecNat prod (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [prod]; rw [← hpair.1]; simp) (by dsimp only [prod]; rw [← hpair.2]; simp)
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
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx13], by simp [hx14],
        by simp; clear * - hr15; bv_omega, by simp,
        ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
          by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
          by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
          by simp [hv30], by simp [hv31]⟩,
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
        by simp [hx8], by simp [hx9], by simp [hx10], by simp [hx11],
        by simp [hx12], by simp [hx13], by simp [hx14],
        by simp [hr_eq], by simp [hr_eq],
        ⟨by simp [hv0], by simp [hv1], by simp [hv8], by simp [hv9], by simp [hv10], by simp [hv11],
          by simp [hv12], by simp [hv13], by simp [hv14], by simp [hv15], by simp [hv22], by simp [hv23],
          by simp [hv24], by simp [hv25], by simp [hv26], by simp [hv27], by simp [hv28], by simp [hv29],
          by simp [hv30], by simp [hv31]⟩,
        ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
          by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩

private theorem dot1_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 : State) (sp lhsPtr rhsPtr x8v : BitVec 64) (lhs rhs acc : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x1b90#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = x8v → s.readReg64 .x9 = lhsPtr →
      s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 → s.readReg64 .x11 = rhsPtr →
      s.readReg64 .x12 = 62209#64 → s.readReg64 .x13 = 3329#64 →
      s.readReg64 .x14 = sp + 11856#64 →
      s.readReg64 .x15 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      AccRegs acc s → Inv13Preserved s0 s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x1cbc#64) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 11856#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
          s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
          s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
          s'.readReg64 .x14 = sp + 11856#64 ∧ AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
            Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hacc hpres hf
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := dot1_ntt_mul_iter hb s0 s sp lhsPtr rhsPtr x8v lhs rhs acc (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hacc hpres
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', _, _, hacc', hpres', hP'⟩
    exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', hacc', hpres',
      hP'.trans (by rw [polyMem_congr (update2_prefix (r := 15) hf), poly32Mem_ofFn])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hacc hpres hf
    have hr15 : r < 15 := by omega
    have hiter := dot1_ntt_mul_iter hb s0 s sp lhsPtr rhsPtr x8v lhs rhs acc (by omega) f Rest
      hpc hrun hsp hspA hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hacc hpres
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx8_m, hx9_m, hx10_m, hx11_m, hx12_m, hx13_m, hx14_m, hx15_m, hx16_m, hacc_m, hpres_m, hPm⟩
    subst hPm
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx8_m hx9_m hx10_m hx11_m hx12_m hx13_m hx14_m hx15_m hx16_m hacc_m hpres_m (update2_prefix hf)

/-! ## 2. Accumulate Tail (`+0x1cbc → +0x1eb4`) & Outer 3-Way Dot Product (`dot1_ok`) -/

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

/-- Intermediate SIMD register layout at `+0x1e04` (and `+0xb490` in `DotLoops3`). -/
@[expose] def AccMidRegs04 (acc prod : Poly16) (s : State) : Prop :=
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

@[expose] def accMidVec32 (acc' : Poly16) (v : Vec32) : Vec32 :=
  { v with
    v0 := polyVecNat acc' 0, v1 := polyVecNat acc' 1, v2 := polyVecNat acc' 2,
    v3 := polyVecNat acc' 3, v4 := polyVecNat acc' 4, v5 := polyVecNat acc' 5,
    v6 := polyVecNat acc' 6, v7 := polyVecNat acc' 7, v8 := polyVecNat acc' 8,
    v9 := polyVecNat acc' 9, v10 := polyVecNat acc' 10, v11 := polyVecNat acc' 11,
    v12 := polyVecNat acc' 12 }

private theorem dot1_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (hj : j < 3)
    (t0 : Spill21) (acc prod : Poly16) (v20704 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1cbc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1)) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x1e04#64) s
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 2) ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧ s'.readReg64 .x9 = lhsPtr + 512#64 ∧
        s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧ s'.readReg64 .x11 = rhsPtr + 512#64 ∧
        s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 11856#64 ∧
        AccMidRegs04 acc prod s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc') ∗
          Poly32Mem (sp + 20704#64) (accMidVec32 acc' v20704) ∗
          Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  cases v20704
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
  have hpst : ConditionHolds .NE (AddWithCarry64 (BitVec.ofNat 64 (j + 1)) (~~~3#64) true).2 =
      decide (j < 2) := by
    clear * - hj; rcases j with _ | _ | _ | _ <;> try omega
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

private theorem dot1_accum_hi [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp x9v x11v : BitVec 64) {j : Nat}
    (t0 : Spill21) (acc prod : Poly16) (v20704 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1e04#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 2))
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (j + 1)) (hx9 : s.readReg64 .x9 = x9v)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = x11v)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hmid : AccMidRegs04 acc prod s) (hpres : Inv13Preserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC04.rebase b (fun _ => none))
      (if j < 2 then b + 0x1b04#64 else b + 0x1eb4#64) s
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc') ∗
        Poly32Mem (sp + 20704#64) (accMidVec32 acc' v20704) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = x9v ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = x11v ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 11856#64 ∧ AccRegs acc' s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc') ∗
          Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [accMidVec32]
  cases v20704
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
  · have hj2 : j < 2 := by simpa [hpst] using hne
    simp only [hj2, ↓reduceIte]
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
  · have hj2 : ¬ j < 2 := by simpa [hpst] using hne
    simp only [hj2, ↓reduceIte]
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

private theorem dot1_outer_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (hj : j < 3)
    (t0 : Spill21) (lhs rhs acc : Poly16) (v20704 v11856 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1b04#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC04.rebase b (fun _ => none)) (if j < 2 then b + 0x1b04#64 else b + 0x1eb4#64) s
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 20704#64) v20704 ∗
        Poly32Mem (sp + 11856#64) v11856 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = lhsPtr + 512#64 ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr + 512#64 ∧ s'.readReg64 .x12 = 62209#64 ∧
        s'.readReg64 .x13 = 3329#64 ∧ s'.readReg64 .x14 = sp + 11856#64 ∧
        AccRegs acc' s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc') ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro prod acc'
  rw [show (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 20704#64) v20704 ∗
        Poly32Mem (sp + 11856#64) v11856 ∗ Rest) =
      (Poly32Mem (sp + 11856#64) v11856 ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (dot1_clear_scratch hb s0 s sp lhsPtr rhsPtr hj acc v11856 _
    hpc hrun hsp hspA hx8 hx9 hx10 hx11 hx12 hx13 hx14 hacc hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hacc1, hpres1, rfl⟩
  rw [show (Poly32Mem (sp + 11856#64) Vec32.zero ∗ (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 11856#64) Vec32.zero.get ∗
        (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗ Rest)) from by
    change (PolyMem (sp + 11856#64) Vec32.zero.get ∗ _) = _; exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (dot1_ntt_mul_loop hb s0 sp lhsPtr rhsPtr _ lhs rhs acc _ 15 0 rfl
    s1 Vec32.zero.get hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hx15_1 hx16_1 hacc1 hpres1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hacc2, hpres2, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗ Rest)) =
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc) ∗ Poly32Mem (sp + 20704#64) v20704 ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (dot1_accum_lo hb s0 s2 sp lhsPtr rhsPtr hj t0 acc prod v20704 _
    hpc2 hrun2 hsp2 hspA2 hx8_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2 hx14_2 hacc2 hpres2) ?_
  rintro sm Pm hpcm hrunm
    ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hmidm, hpresm, rfl⟩
  refine SepWP.mono (dot1_accum_hi hb s0 sm sp (lhsPtr + 512#64) (rhsPtr + 512#64) t0 acc prod v20704 _
    hpcm hrunm hspm hspAm hpstm hx8m hx9m hx10m hx11m hx12m hx13m hx14m hmidm hpresm) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', hacc', hpres', rfl⟩
  exact ⟨hsp', hspA', hx8', hx9', hx10', hx11', hx12', hx13', hx14', hacc', hpres',
    sepProp_ext (by sep_frame) (by sep_frame)⟩

theorem dot1_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl04 b)
    (s0 s : State) (sp lhsBase rhsBase : BitVec 64)
    (t0 : Spill21) (l0 l1 l2 r0 r1 r2 : Poly16) (v20704 v11856 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1b04#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = 0#64) (hx9 : s.readReg64 .x9 = lhsBase)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsBase)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 11856#64)
    (hacc : AccRegs polyZero16 s) (hpres : Inv13Preserved s0 s) :
    let dot := neonDot3 l0 l1 l2 r0 r1 r2
    SepWP (blkPC04.rebase b (fun _ => none)) (b + 0x1eb4#64) s
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 20704#64) v20704 ∗ Poly32Mem (sp + 11856#64) v11856 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 1920#64) (AccSpill21 t0 dot) ∗
          PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
          PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
          PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
          PolyMem (sp + 20704#64) (polyVecNat dot) ∗
          Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗ Rest)) := by
  dsimp only
  let dot := neonDot3 l0 l1 l2 r0 r1 r2
  let p0 := neonPolyNttMul16 l0 r0
  let p1 := neonPolyNttMul16 l1 r1
  let acc1 := polyAdd16 p0 p1
  let Rest0 : SepProp := PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Rest
  let Rest1 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Rest
  let Rest2 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
    PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Rest
  rw [show (Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 20704#64) v20704 ∗ Poly32Mem (sp + 11856#64) v11856 ∗ Rest) =
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 polyZero16) ∗ PolyMem lhsBase (polyVecNat l0) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ Poly32Mem (sp + 20704#64) v20704 ∗
        Poly32Mem (sp + 11856#64) v11856 ∗ Rest0) from
    sepProp_ext (by dsimp only [Rest0]; sep_frame) (by dsimp only [Rest0]; sep_frame)]
  have hj0 := dot1_outer_iter hb s0 s sp lhsBase rhsBase (j := 0) (by omega)
    t0 l0 r0 polyZero16 v20704 v11856 Rest0 hpc hrun hsp hspA hcl hro hx8 hx9 hx10 hx11 hx12 hx13 hx14 hacc hpres
  dsimp only at hj0
  simp only [Nat.zero_lt_two, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size l0 r0)] at hj0
  refine sepWP_seq_env hcl hro hj0 ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx8_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hacc1, hpres1, rfl⟩
  rw [show (Spill21Mem (sp + 1920#64) (AccSpill21 t0 p0) ∗ PolyMem lhsBase (polyVecNat l0) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest0) =
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 p0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat p0)) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1) from
    sepProp_ext (by dsimp only [Rest0, Rest1]; sep_frame) (by dsimp only [Rest0, Rest1]; sep_frame)]
  have hj1 := dot1_outer_iter hb s0 s1 sp (lhsBase + 512#64) (rhsBase + 512#64) (j := 1) (by omega)
    t0 l1 r1 p0 (Vec32.ofFn (polyVecNat p0)) (Vec32.ofFn (polyVecNat p0)) Rest1
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx8_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1 hx14_1 hacc1 hpres1
  dsimp only at hj1; simp only [Nat.one_lt_two, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl1 hro1 hj1 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx8_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2, hx14_2, hacc2, hpres2, rfl⟩
  rw [show (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc1) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest1) =
      (Spill21Mem (sp + 1920#64) (AccSpill21 t0 acc1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Poly32Mem (sp + 20704#64) (Vec32.ofFn (polyVecNat acc1)) ∗
        Poly32Mem (sp + 11856#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2) from
    sepProp_ext (by dsimp only [Rest1, Rest2]; sep_frame) (by dsimp only [Rest1, Rest2]; sep_frame)]
  have hj2 := dot1_outer_iter hb s0 s2 sp (lhsBase + 1024#64) (rhsBase + 1024#64) (j := 2) (by omega)
    t0 l2 r2 acc1 (Vec32.ofFn (polyVecNat acc1)) (Vec32.ofFn (polyVecNat p1)) Rest2
    hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx8_2
    (by simpa [show (lhsBase + 512#64) + 512#64 = lhsBase + 1024#64 by clear * -; bv_omega] using hx9_2)
    hx10_2
    (by simpa [show (rhsBase + 512#64) + 512#64 = rhsBase + 1024#64 by clear * -; bv_omega] using hx11_2)
    hx12_2 hx13_2 hx14_2 hacc2 hpres2
  dsimp only at hj2; simp only [Nat.lt_irrefl, ↓reduceIte] at hj2
  refine SepWP.mono hj2 ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, _, _, _, _, _, hpres', rfl⟩
  refine ⟨hsp', hspA', hpres', ?_⟩
  rw [poly32Mem_ofFn]
  dsimp only [dot, neonDot3, acc1, p0, p1, Rest2]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1
