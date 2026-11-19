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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `encapsulate1_serialized` (`B03`) — 3-Way `ntt_multiply` + In-Place Accumulate (`+0x4e9c → +0x51fc`)

Steps one outer row (`i < 3`) of the 3-way `ntt_multiply` + in-place accumulate loop over
`lhsBase` (`Âᵀ[i, 0..2]` in `x28`) and `rhsBase` (`rHat[0..2]` in `x14`), accumulating into
`Poly32Mem polyPtr` (`polyPtr = basePtr + BitVec.ofNat 64 (512 * i)` in `x26`) from `Vec32.zero`
to `PolyMem polyPtr (polyVecNat (neonDot3 l0 l1 l2 r0 r1 r2))` while setting `v16 = dup8x16 3329#16`
and `v18 = dup8x16 62209#16`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Dot

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
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

/-- Outer-loop GPRs and SIMD constants untouched across `Seg5Dot` (`+0x4e9c → +0x51fc`). -/
structure Seg5DotPreserved (s0 s : State) : Prop where
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x4  : s.readReg64 .x4  = s0.readReg64 .x4
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  x19 : s.readReg64 .x19 = s0.readReg64 .x19
  x21 : s.readReg64 .x21 = s0.readReg64 .x21
  x22 : s.readReg64 .x22 = s0.readReg64 .x22
  x23 : s.readReg64 .x23 = s0.readReg64 .x23
  x24 : s.readReg64 .x24 = s0.readReg64 .x24
  x25 : s.readReg64 .x25 = s0.readReg64 .x25
  x28 : s.readReg64 .x28 = s0.readReg64 .x28
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5  = s0.readVReg128 0#5
  v23 : s.readVReg128 23#5 = s0.readVReg128 23#5
  v27 : s.readVReg128 27#5 = s0.readVReg128 27#5

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x4e9c → 0x51fc]
end

@[simp, arm64_norm, wp_norm] abbrev offDotStart : BitVec 64 := BitVec.ofNat 64 20124
@[simp, arm64_norm, wp_norm] abbrev offDotClear : BitVec 64 := BitVec.ofNat 64 20144
@[simp, arm64_norm, wp_norm] abbrev offDotMul   : BitVec 64 := BitVec.ofNat 64 20288
@[simp, arm64_norm, wp_norm] abbrev offDotAccLo : BitVec 64 := BitVec.ofNat 64 20592
@[simp, arm64_norm, wp_norm] abbrev offDotAccHi : BitVec 64 := BitVec.ofNat 64 20792
@[simp, arm64_norm, wp_norm] abbrev offDotEnd   : BitVec 64 := BitVec.ofNat 64 20988

@[simp, arm64_norm, wp_norm]
private theorem blkPl03_ρ [MlKemPlacement] (sym : String) :
    blkPl03.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl
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
  blkPC03 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
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

private theorem vec32_ofFn_polyZero16 : Vec32.ofFn (polyVecNat polyZero16) = Vec32.zero := by
  simp [Vec32.ofFn, Vec32.zero]

local macro "s5_zero0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "step_zero32_q0" : tactic => `(tactic| (
  s5_zero0 31; s5_zero0 30; s5_zero0 29; s5_zero0 28; s5_zero0 27; s5_zero0 26; s5_zero0 25; s5_zero0 24;
  s5_zero0 23; s5_zero0 22; s5_zero0 21; s5_zero0 20; s5_zero0 19; s5_zero0 18; s5_zero0 17; s5_zero0 16;
  s5_zero0 15; s5_zero0 14; s5_zero0 13; s5_zero0 12; s5_zero0 11; s5_zero0 10; s5_zero0 9; s5_zero0 8;
  s5_zero0 7; s5_zero0 6; s5_zero0 5; s5_zero0 4; s5_zero0 3; s5_zero0 2; s5_zero0 1; s5_zero0 0))
/-! ## 1. Scratch Clear (`+0x4eb0 → +0x4f40`) & `ntt_multiply` Loop (`+0x4f40 → +0x5070`) -/

private theorem seg5_dot_clear [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr lhsPtr rhsBase x8v x13v : BitVec 64) {j : Nat} (_hj : j < 3)
    (v4272 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotClear) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = lhsPtr)
    (hx13 : s.readReg64 .x13 = x13v) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx26 : s.readReg64 .x26 = polyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (512 * j))
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg5DotPreserved s0 s) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotMul) s
      (Poly32Mem (sp + 4272#64) v4272 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x3 = rhsBase + BitVec.ofNat 64 (512 * j) ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr ∧
        s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x15 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)) ∧ s'.readReg64 .lr = 0#64 ∧
        s'.readVReg128 0#5 = 0#128 ∧ Seg5DotPreserved s0 s' ∧
        P' = (Poly32Mem (sp + 4272#64) Vec32.zero ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p1, p4, p9, p11, p12, p14, p16, p17, p18, p19,
    p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  wp_steps 4; step_zero32_q0
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp, by simp [hx4], by simp [hx8], by simp [hx10], by simp [hx13], by simp [hx14],
      by simp, by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26],
      by simp; clear * -; bv_omega, by simp, by simp [hv0],
      ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
        by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
        by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
        by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
private theorem seg5_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr lhsPtr rhsPtr rhsBase x8v x13v x27v : BitVec 64) (lhs rhs : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + offDotMul) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx3 : s.readReg64 .x3 = rhsPtr) (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = lhsPtr)
    (hx13 : s.readReg64 .x13 = x13v) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx15 : s.readReg64 .x15 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx26 : s.readReg64 .x26 = polyPtr)
    (hx27 : s.readReg64 .x27 = x27v) (hlr : s.readReg64 .lr = BitVec.ofNat 64 (32 * r))
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg5DotPreserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC03.rebase b (fun _ => none))
      (if r < 15 then b + offDotMul else b + offDotAccLo) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 4272#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x3 = rhsPtr ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr ∧
        s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x15 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readReg64 .x27 = x27v ∧ s'.readReg64 .lr = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 16#5 = dup8x16 3329#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ Seg5DotPreserved s0 s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 4272#64)
            (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
              (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro prod
  rcases hpres with ⟨p1, p4, p9, p11, p12, p14, p16, p17, p18, p19,
    p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  refine step_ldrh16_ro (k := 64 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (64 + 4 * r))) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx15]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq0
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq0)
  refine step_ldrh16_ro (k := 66 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (66 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx15]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq1
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq1)
  refine step_ldrh16_ro (k := 65 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (65 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx15]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq2
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq2)
  refine step_ldrh16_ro (k := 67 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (67 + 4 * r)))
    (wb := some (.x15, mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1))))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx15]; constructor <;> (clear * - hr; bv_omega))
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq3
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq3)
  wp_steps 2
  refine step_ldrQ128 (wb := none) (ea := rhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (v := polyVecNat rhs (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx3, hlr]; clear * - hr; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  refine step_ldpQ128 (wb := none) (ea := lhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := lhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat lhs (2 * r)) (v2 := polyVecNat lhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)) (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := rhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v := polyVecNat rhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  wp_steps 57
  have hz19 := lane16_buildZeta4
    ((zetaTableAt (64 + 4 * r)).zeroExtend 64) ((zetaTableAt (66 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (64 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (66 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hz20 := lane16_buildZeta4
    ((zetaTableAt (65 + 4 * r)).zeroExtend 64) ((zetaTableAt (67 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (65 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (67 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hpair := nttMulRawPair_eq_polyVecNat lhs rhs r hr _ _
    (hz19.1.trans (zext64_trunc16 _)) (hz19.2.1.trans (zext64_trunc16 _))
    (hz19.2.2.1.trans (neg_zext_trunc16 _)) (hz19.2.2.2.trans (neg_zext_trunc16 _))
    (hz20.1.trans (zext64_trunc16 _)) (hz20.2.1.trans (zext64_trunc16 _))
    (hz20.2.2.1.trans (neg_zext_trunc16 _)) (hz20.2.2.2.trans (neg_zext_trunc16 _))
  dsimp only [nttMulRawPair, buildZeta4] at hpair
  refine step_stpQ128 (wb := none) (ea := (sp + 4272#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 4272#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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
        by simp [hx3], by simp [hx4], by simp [hx8], by simp [hx10], by simp [hx13], by simp [hx14],
        by simp, by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26], by simp [hx27],
        by simp; clear * - hr15; bv_omega, by simp [hv0], by simp, by simp,
        ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
          by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
          by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
  · have hr15 : ¬ r < 15 := by
      intro hlt
      have hbv : BitVec.ofNat 64 (32 * r) + 32#64 = 512#64 := by simpa using hne
      have hnat := congrArg BitVec.toNat hbv
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat; omega
    have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx3], by simp [hx4], by simp [hx8], by simp [hx10], by simp [hx13], by simp [hx14],
        by simp [hr_eq], by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26], by simp [hx27],
        by simp [hr_eq], by simp [hv0], by simp, by simp,
        ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
          by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
          by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩
private theorem seg5_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 : State) (sp polyPtr lhsPtr rhsPtr rhsBase x8v x13v x27v : BitVec 64) (lhs rhs : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + offDotMul → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x3 = rhsPtr → s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 →
      s.readReg64 .x8 = x8v → s.readReg64 .x10 = lhsPtr →
      s.readReg64 .x13 = x13v → s.readReg64 .x14 = rhsBase →
      s.readReg64 .x15 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      s.readReg64 .x16 = 62209#64 → s.readReg64 .x17 = 3329#64 →
      s.readReg64 .x18 = sp + 4272#64 → s.readReg64 .x26 = polyPtr →
      s.readReg64 .x27 = x27v → s.readReg64 .lr = BitVec.ofNat 64 (32 * r) →
      s.readVReg128 0#5 = 0#128 → Seg5DotPreserved s0 s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotAccLo) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 4272#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
          s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr ∧
          s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
          s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
          s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
          s'.readReg64 .x27 = x27v ∧ s'.readVReg128 0#5 = 0#128 ∧
          s'.readVReg128 16#5 = dup8x16 3329#16 ∧ s'.readVReg128 18#5 = dup8x16 62209#16 ∧
          Seg5DotPreserved s0 s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
            Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx3 hx4 hx8 hx10 hx13 hx14 hx15 hx16 hx17 hx18 hx26 hx27 hlr hv0 hpres hf
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg5_ntt_mul_iter hb s0 s sp polyPtr lhsPtr rhsPtr rhsBase x8v x13v x27v lhs rhs (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx3 hx4 hx8 hx10 hx13 hx14 hx15 hx16 hx17 hx18 hx26 hx27 hlr hv0 hpres
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', _, hx4', hx8', hx10', hx13', hx14', _, hx16', hx17', hx18', hx26', hx27', _, hv0', hv16', hv18', hpres', hP'⟩
    exact ⟨hsp', hspA', hx4', hx8', hx10', hx13', hx14', hx16', hx17', hx18', hx26', hx27', hv0', hv16', hv18', hpres',
      hP'.trans (by rw [polyMem_congr (update2_prefix (r := 15) hf), poly32Mem_ofFn])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx3 hx4 hx8 hx10 hx13 hx14 hx15 hx16 hx17 hx18 hx26 hx27 hlr hv0 hpres hf
    have hr15 : r < 15 := by omega
    have hiter := seg5_ntt_mul_iter hb s0 s sp polyPtr lhsPtr rhsPtr rhsBase x8v x13v x27v lhs rhs (by omega) f Rest
      hpc hrun hsp hspA hro hx3 hx4 hx8 hx10 hx13 hx14 hx15 hx16 hx17 hx18 hx26 hx27 hlr hv0 hpres
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx3_m, hx4_m, hx8_m, hx10_m, hx13_m, hx14_m, hx15_m, hx16_m, hx17_m, hx18_m, hx26_m, hx27_m, hlr_m, hv0_m, _, _, hpres_m, hPm⟩
    subst hPm
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx3_m hx4_m hx8_m hx10_m hx13_m hx14_m hx15_m hx16_m hx17_m hx18_m hx26_m hx27_m hlr_m hv0_m hpres_m (update2_prefix hf)
/-! ## 2. In-Place Accumulate (`+0x5070 → +0x51fc`) & Outer 3-Way Dot Product (`seg5_dot_ok`) -/

local macro "s5_ldp0 " k1:num k2:num : tactic => `(tactic| (
  apply step_ldpQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { rfl }
  { wp_norm_lhs }; { rfl }
  { apply SepLoad128.left; apply SepLoad128.vec32 (k := $k1); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { apply SepLoad128.left; apply SepLoad128.vec32 (k := $k2); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

local macro "s5_stp0 " k1:num k2:num : tactic => `(tactic| (
  apply step_stpQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { rfl }
  { wp_norm_lhs }; { rfl }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k1); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.set] } }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k2); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "s5_ldr1 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.right; apply SepLoad128.left
    apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

private def Seg5DotMidRegs (acc prod : Poly16) (s : State) : Prop :=
  s.readVReg128 0#5 = 0#128 ∧
  s.readVReg128 2#5 = polyVecNat acc 15 ∧ s.readVReg128 3#5 = polyVecNat prod 15 ∧
  s.readVReg128 6#5 = polyVecNat acc 14 ∧ s.readVReg128 7#5 = polyVecNat prod 14 ∧
  s.readVReg128 16#5 = dup8x16 3329#16 ∧ s.readVReg128 17#5 = polyVecNat acc 28 ∧
  s.readVReg128 18#5 = dup8x16 62209#16 ∧ s.readVReg128 19#5 = polyVecNat acc 29 ∧
  s.readVReg128 20#5 = polyVecNat prod 28 ∧ s.readVReg128 21#5 = polyVecNat prod 29

private def seg5DotMidVec32 (acc acc' : Poly16) : Vec32 :=
  { (Vec32.ofFn (polyVecNat acc)) with
    v0 := polyVecNat acc' 0, v1 := polyVecNat acc' 1, v2 := polyVecNat acc' 2,
    v3 := polyVecNat acc' 3, v4 := polyVecNat acc' 4, v5 := polyVecNat acc' 5,
    v6 := polyVecNat acc' 6, v7 := polyVecNat acc' 7, v8 := polyVecNat acc' 8,
    v9 := polyVecNat acc' 9, v10 := polyVecNat acc' 10, v11 := polyVecNat acc' 11,
    v12 := polyVecNat acc' 12, v13 := polyVecNat acc' 13 }
private theorem seg5_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr lhsPtr rhsBase x8v x13v : BitVec 64) {j : Nat} (hj : j < 3)
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offDotAccLo) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = lhsPtr)
    (hx13 : s.readReg64 .x13 = x13v) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx26 : s.readReg64 .x26 = polyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)))
    (hv0 : s.readVReg128 0#5 = 0#128) (hv16 : s.readVReg128 16#5 = dup8x16 3329#16)
    (hv18 : s.readVReg128 18#5 = dup8x16 62209#16) (hpres : Seg5DotPreserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotAccHi) s
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 2) ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr + 512#64 ∧
        s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        Seg5DotMidRegs acc prod s' ∧ Seg5DotPreserved s0 s' ∧
        P' = (Poly32Mem polyPtr (seg5DotMidVec32 acc acc') ∗
          Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p1, p4, p9, p11, p12, p14, p16, p17, p18, p19,
    p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  s5_ldp0 0 1; wp_step; s5_ldr1 0; s5_ldr1 1; wp_step; s5_ldr1 3; s5_ldr1 4; s5_ldr1 28
  wp_step; wp_step; s5_ldr1 2; s5_ldp0 2 3; s5_ldr1 29; s5_stp0 0 1
  s5_ldp0 4 5; wp_step; wp_step; s5_ldr1 5; wp_step; s5_ldr1 6; s5_stp0 2 3
  wp_step; s5_ldr1 7; s5_ldp0 6 7; s5_ldp0 28 29; s5_stp0 4 5
  wp_step; wp_step; s5_ldr1 8; s5_ldp0 8 9; s5_ldr1 9; s5_stp0 6 7
  wp_step; wp_step; s5_ldr1 10; s5_ldp0 10 11; s5_ldr1 11; s5_stp0 8 9
  wp_step; wp_step; s5_ldr1 12; s5_ldp0 12 13; s5_ldr1 13; s5_stp0 10 11
  wp_step; wp_step; s5_ldr1 14; s5_ldp0 14 15; s5_ldr1 15; s5_stp0 12 13
  have hpst : ConditionHolds .NE
      (AddWithCarry64 (BitVec.ofNat 64 (512 * (j + 1))) (~~~1536#64) true).2 = decide (j < 2) := by
    clear * - hj; rcases j with _ | _ | _ | _ <;> try omega
    all_goals decide
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simpa [subsPState64] using hpst,
      by simp [hx4], by simp [hx8], by simp, by simp [hx13], by simp [hx14],
      by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26], by simp [hx27],
      ⟨by simp [hv0], by simp, by simp, by simp, by simp,
        by simp [hv16], by simp, by simp [hv18], by simp, by simp, by simp⟩,
      ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
        by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
        by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
        by simp [pv0], by simp [pv23], by simp [pv27]⟩,
      by simp [seg5DotMidVec32, Vec32.ofFn]⟩

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
private theorem seg5_accum_hi [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr lhsPtr rhsBase x8v x13v : BitVec 64) {j : Nat}
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offDotAccHi) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 2))
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = lhsPtr)
    (hx13 : s.readReg64 .x13 = x13v) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx26 : s.readReg64 .x26 = polyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)))
    (hmid : Seg5DotMidRegs acc prod s) (hpres : Seg5DotPreserved s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC03.rebase b (fun _ => none))
      (if j < 2 then b + offDotClear else b + offDotEnd) s
      (Poly32Mem polyPtr (seg5DotMidVec32 acc acc') ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr ∧
        s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 16#5 = dup8x16 3329#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ Seg5DotPreserved s0 s' ∧
        P' = (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [seg5DotMidVec32]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv0, hv2, hv3, hv6, hv7, hv16, hv17, hv18, hv19, hv20, hv21⟩
  rcases hpres with ⟨p1, p4, p9, p11, p12, p14, p16, p17, p18, p19,
    p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  wp_step; wp_step; s5_ldr1 16; s5_ldp0 16 17; s5_ldr1 17; s5_stp0 14 15
  wp_step; wp_step; s5_ldr1 18; s5_ldp0 18 19; s5_ldr1 19; s5_stp0 16 17
  wp_step; wp_step; s5_ldr1 20; s5_ldp0 20 21; s5_ldr1 21; s5_stp0 18 19
  wp_step; wp_step; s5_ldr1 22; s5_ldp0 22 23; s5_ldr1 23; s5_stp0 20 21
  s5_ldr1 25; wp_step; s5_ldp0 24 25; wp_step; s5_ldr1 24; wp_step; wp_step; s5_ldr1 26; s5_stp0 22 23
  s5_ldp0 26 27; s5_ldr1 27; wp_step; s5_stp0 24 25; s5_ldr1 30; wp_step; wp_step; s5_ldr1 31; wp_step
  s5_stp0 26 27; s5_ldp0 30 31; s5_stp0 28 29; wp_step; wp_step; s5_stp0 30 31
  wp_step; wp_if hne
  · have hj2 : j < 2 := by simpa [hpst] using hne
    simp only [hj2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx4], by simp [hx8], by simp [hx10], by simp [hx13], by simp [hx14],
        by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26], by simp [hx27],
        by simp [hv0], by simp [hv16], by simp [hv18],
        ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
          by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
          by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩,
        by simp [Vec32.ofFn]⟩
  · have hj2 : ¬ j < 2 := by simpa [hpst] using hne
    simp only [hj2, ↓reduceIte]
    exact SepWP.done (by wp_norm_lhs) (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx4], by simp [hx8], by simp [hx10], by simp [hx13], by simp [hx14],
        by simp [hx16], by simp [hx17], by simp [hx18], by simp [hx26], by simp [hx27],
        by simp [hv0], by simp [hv16], by simp [hv18],
        ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
          by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
          by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
          by simp [pv0], by simp [pv23], by simp [pv27]⟩,
        by simp [Vec32.ofFn]⟩

private theorem seg5_dot_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp polyPtr lhsPtr rhsBase x8v x13v : BitVec 64) {j : Nat} (hj : j < 3)
    (lhs rhs acc : Poly16) (v4272 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotClear) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = x8v) (hx10 : s.readReg64 .x10 = lhsPtr)
    (hx13 : s.readReg64 .x13 = x13v) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx26 : s.readReg64 .x26 = polyPtr)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (512 * j))
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg5DotPreserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC03.rebase b (fun _ => none))
      (if j < 2 then b + offDotClear else b + offDotEnd) s
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem (rhsBase + BitVec.ofNat 64 (512 * j)) (polyVecNat rhs) ∗
        Poly32Mem (sp + 4272#64) v4272 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = x8v ∧ s'.readReg64 .x10 = lhsPtr + 512#64 ∧
        s'.readReg64 .x13 = x13v ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readReg64 .x27 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 16#5 = dup8x16 3329#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ Seg5DotPreserved s0 s' ∧
        P' = (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc')) ∗
          PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem (rhsBase + BitVec.ofNat 64 (512 * j)) (polyVecNat rhs) ∗
          Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro prod acc'
  let rhsPtr := rhsBase + BitVec.ofNat 64 (512 * j)
  rw [show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 4272#64) v4272 ∗ Rest) =
      (Poly32Mem (sp + 4272#64) v4272 ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (seg5_dot_clear hb s0 s sp polyPtr lhsPtr rhsBase x8v x13v hj v4272 _
    hpc hrun hsp hspA hx4 hx8 hx10 hx13 hx14 hx16 hx17 hx18 hx26 hx27 hv0 hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx3_1, hx4_1, hx8_1, hx10_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1,
      hx18_1, hx26_1, hx27_1, hlr_1, hv0_1, hpres1, rfl⟩
  rw [show (Poly32Mem (sp + 4272#64) Vec32.zero ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 4272#64) Vec32.zero.get ∗
        (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) from by
    change (PolyMem (sp + 4272#64) Vec32.zero.get ∗ _) = _
    exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (seg5_ntt_mul_loop hb s0 sp polyPtr lhsPtr rhsPtr rhsBase x8v x13v
    (BitVec.ofNat 64 (512 * (j + 1))) lhs rhs _ 15 0 rfl s1 Vec32.zero.get
    hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx3_1 hx4_1 hx8_1 hx10_1 hx13_1 hx14_1 hx15_1
    hx16_1 hx17_1 hx18_1 hx26_1 hx27_1 hlr_1 hv0_1 hpres1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2
    ⟨hsp2, hspA2, hx4_2, hx8_2, hx10_2, hx13_2, hx14_2, hx16_2, hx17_2,
      hx18_2, hx26_2, hx27_2, hv0_2, hv16_2, hv18_2, hpres2, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (seg5_accum_lo hb s0 s2 sp polyPtr lhsPtr rhsBase x8v x13v hj acc prod _
    hpc2 hrun2 hsp2 hspA2 hx4_2 hx8_2 hx10_2 hx13_2 hx14_2 hx16_2 hx17_2 hx18_2 hx26_2 hx27_2
    hv0_2 hv16_2 hv18_2 hpres2) ?_
  rintro sm Pm hpcm hrunm
    ⟨hspm, hspAm, hpstm, hx4m, hx8m, hx10m, hx13m, hx14m, hx16m, hx17m, hx18m, hx26m, hx27m,
      hmidm, hpresm, rfl⟩
  refine SepWP.mono (seg5_accum_hi hb s0 sm sp polyPtr (lhsPtr + 512#64) rhsBase x8v x13v acc prod _
    hpcm hrunm hspm hspAm hpstm hx4m hx8m hx10m hx13m hx14m hx16m hx17m hx18m hx26m hx27m
    hmidm hpresm) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx4', hx8', hx10', hx13', hx14', hx16', hx17', hx18', hx26', hx27',
    hv0', hv16', hv18', hpres', rfl⟩
  exact ⟨hsp', hspA', hx4', hx8', hx10', hx13', hx14', hx16', hx17', hx18', hx26', hx27',
    hv0', hv16', hv18', hpres', sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg5_dot_head [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp basePtr lhsBase rhsBase : BitVec 64) {i : Nat} (hi : i < 3) (P : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (1536 * i))
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 i) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx19 : s.readReg64 .x19 = basePtr)
    (hx28 : s.readReg64 .x28 = lhsBase)
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg5DotPreserved s0 s) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotClear) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (1536 * (i + 1)) ∧
        s'.readReg64 .x10 = lhsBase ∧
        s'.readReg64 .x13 = BitVec.ofNat 64 (i + 1) ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧
        s'.readReg64 .x26 = basePtr + BitVec.ofNat 64 (512 * i) ∧
        s'.readReg64 .x27 = 0#64 ∧ s'.readVReg128 0#5 = 0#128 ∧
        Seg5DotPreserved s0 s' ∧ P' = P) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p1, p4, p9, p11, p12, p14, p16, p17, p18, p19,
    p21, p22, p23, p24, p25, p28, pfp, pv0, pv23, pv27⟩
  have hshl : (BitVec.ofNat 64 i) <<< 9 = BitVec.ofNat 64 (512 * i) := by
    clear * - hi; rcases i with _ | _ | _ | _ <;> try omega
    all_goals decide
  wp_steps 5
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp [hx4], by simp; clear * -; bv_omega, by simp,
      by simp; clear * -; bv_omega, by simp [hx14],
      by simp [hx16], by simp [hx17], by simp [hx18],
      by simp [← hshl], by simp, by simp [hv0],
      ⟨by simp [p1], by simp [p4], by simp [p9], by simp [p11], by simp [p12], by simp [p14],
        by simp [p16], by simp [p17], by simp [p18], by simp [p19], by simp [p21], by simp [p22],
        by simp [p23], by simp [p24], by simp [p25], by simp [p28], by simp [pfp],
        by simp [pv0], by simp [pv23], by simp [pv27]⟩, rfl⟩

theorem seg5_dot_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl03 b)
    (s0 s : State) (sp basePtr lhsBase rhsBase : BitVec 64) {i : Nat} (hi : i < 3)
    (l0 l1 l2 r0 r1 r2 : Poly16) (v4272 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + offDotStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx4 : s.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (1536 * i))
    (hx13 : s.readReg64 .x13 = BitVec.ofNat 64 i) (hx14 : s.readReg64 .x14 = rhsBase)
    (hx16 : s.readReg64 .x16 = 62209#64) (hx17 : s.readReg64 .x17 = 3329#64)
    (hx18 : s.readReg64 .x18 = sp + 4272#64) (hx19 : s.readReg64 .x19 = basePtr)
    (hx28 : s.readReg64 .x28 = lhsBase)
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg5DotPreserved s0 s) :
    let polyPtr := basePtr + BitVec.ofNat 64 (512 * i)
    let dot := neonDot3 l0 l1 l2 r0 r1 r2
    SepWP (blkPC03.rebase b (fun _ => none)) (b + offDotEnd) s
      (PolyMem polyPtr (fun _ => 0#128) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 4272#64) v4272 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x4 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x8 = BitVec.ofNat 64 (1536 * (i + 1)) ∧
        s'.readReg64 .x13 = BitVec.ofNat 64 (i + 1) ∧ s'.readReg64 .x14 = rhsBase ∧
        s'.readReg64 .x16 = 62209#64 ∧ s'.readReg64 .x17 = 3329#64 ∧
        s'.readReg64 .x18 = sp + 4272#64 ∧ s'.readReg64 .x26 = polyPtr ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 16#5 = dup8x16 3329#16 ∧
        s'.readVReg128 18#5 = dup8x16 62209#16 ∧ Seg5DotPreserved s0 s' ∧
        P' = (PolyMem polyPtr (polyVecNat dot) ∗
          PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
          PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
          PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
          Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗ Rest)) := by
  intro polyPtr dot
  let p0 := neonPolyNttMul16 l0 r0
  let p1 := neonPolyNttMul16 l1 r1
  let acc1 := polyAdd16 p0 p1
  let Rest0 : SepProp := PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Rest
  let Rest1 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗ Rest
  let Rest2 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
    PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗ Rest
  have hzero_mem : PolyMem polyPtr (fun _ => 0#128) = Poly32Mem polyPtr (Vec32.ofFn (polyVecNat polyZero16)) := by
    rw [vec32_ofFn_polyZero16]; rfl
  refine sepWP_seq_env hcl hro (seg5_dot_head hb s0 s sp basePtr lhsBase rhsBase hi _
    hpc hrun hsp hspA hx4 hx8 hx13 hx14 hx16 hx17 hx18 hx19 hx28 hv0 hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx4_1, hx8_1, hx10_1, hx13_1, hx14_1, hx16_1, hx17_1, hx18_1, hx26_1, hx27_1, hv0_1, hpres1, rfl⟩
  rw [hzero_mem, show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat polyZero16)) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem rhsBase (polyVecNat r0) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 4272#64) v4272 ∗ Rest) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat polyZero16)) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (rhsBase + 0#64) (polyVecNat r0) ∗
        Poly32Mem (sp + 4272#64) v4272 ∗ Rest0) from by
    rw [BitVec.add_zero]; exact sepProp_ext (by dsimp only [Rest0]; sep_frame) (by dsimp only [Rest0]; sep_frame)]
  have hj0 := seg5_dot_iter hb s0 s1 sp polyPtr lhsBase rhsBase _ _ (j := 0) (by omega)
    l0 r0 polyZero16 v4272 Rest0 hpc1 hrun1 hsp1 hspA1 hcl1 hro1
    hx4_1 hx8_1 hx10_1 hx13_1 hx14_1 hx16_1 hx17_1 hx18_1 hx26_1 hx27_1 hv0_1 hpres1
  dsimp only at hj0
  simp only [Nat.zero_lt_two, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size l0 r0)] at hj0
  refine sepWP_seq_env hcl1 hro1 hj0 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hx4_2, hx8_2, hx10_2, hx13_2, hx14_2, hx16_2, hx17_2, hx18_2, hx26_2, hx27_2, _, _, _, hpres2, rfl⟩
  rw [BitVec.add_zero, show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat p0)) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem rhsBase (polyVecNat r0) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest0) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat p0)) ∗
        PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1) from
    sepProp_ext (by dsimp only [Rest0, Rest1]; sep_frame) (by dsimp only [Rest0, Rest1]; sep_frame)]
  have hj1 := seg5_dot_iter hb s0 s2 sp polyPtr (lhsBase + 512#64) rhsBase _ _ (j := 1) (by omega)
    l1 r1 p0 (Vec32.ofFn (polyVecNat p0)) Rest1 hpc2 hrun2 hsp2 hspA2 hcl2 hro2
    hx4_2 hx8_2 hx10_2 hx13_2 hx14_2 hx16_2 hx17_2 hx18_2 hx26_2 hx27_2 (by assumption) hpres2
  dsimp only at hj1; simp only [Nat.one_lt_two, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl2 hro2 hj1 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hx4_3, hx8_3, hx10_3, hx13_3, hx14_3, hx16_3, hx17_3, hx18_3, hx26_3, hx27_3, hv0_3, _, _, hpres3, rfl⟩
  rw [show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc1)) ∗
        PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (rhsBase + 512#64) (polyVecNat r1) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest1) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc1)) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗ PolyMem (rhsBase + 1024#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 4272#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2) from
    sepProp_ext (by dsimp only [Rest1, Rest2]; sep_frame) (by dsimp only [Rest1, Rest2]; sep_frame)]
  have hj2 := seg5_dot_iter hb s0 s3 sp polyPtr (lhsBase + 1024#64) rhsBase _ _ (j := 2) (by omega)
    l2 r2 acc1 (Vec32.ofFn (polyVecNat p1)) Rest2 hpc3 hrun3 hsp3 hspA3 hcl3 hro3
    hx4_3 hx8_3 (by simpa [show (lhsBase + 512#64) + 512#64 = lhsBase + 1024#64 by clear * -; bv_omega] using hx10_3)
    hx13_3 hx14_3 hx16_3 hx17_3 hx18_3 hx26_3 hx27_3 hv0_3 hpres3
  dsimp only at hj2; simp only [Nat.lt_irrefl, ↓reduceIte] at hj2
  refine SepWP.mono hj2 ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx4', hx8', _, hx13', hx14', hx16', hx17', hx18', hx26', _, hv0', hv16', hv18', hpres', rfl⟩
  refine ⟨hsp', hspA', hx4', hx8', hx13', hx14', hx16', hx17', hx18', hx26', hv0', hv16', hv18', hpres', ?_⟩
  rw [poly32Mem_ofFn]
  dsimp only [dot, neonDot3, acc1, p0, p1, Rest2]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg5Dot
