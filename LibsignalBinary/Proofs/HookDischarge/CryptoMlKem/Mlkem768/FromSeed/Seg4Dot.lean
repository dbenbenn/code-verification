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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.NttMul
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc

/-!
# `generate_keypair_compressed` (`B05`) — Segment 4 Setup & 3-Way NTT Dot Product (`Seg4Dot`)

Steps `+0x5c60 → +0x5cb0` (`seg4_setup`) and one outer row `+0x5cb0 → +0x605c` (`seg4_row_dot`)
computing `neonDot3 l0 l1 l2 r0 r1 r2` into `PolyMem (sp + 2208 + 512 * i)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4Dot

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 poly32Mem_ofFn polyVecNat
  step_ldpQ128 step_ldrQ128 step_stpQ128 step_strQ128 vec32_ofFn_get vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdMovi_8h_1024 svc_simdMul_8h
  svc_simdMvni_8h_f2ff svc_simdRev64_4s svc_simdSmlal_4s svc_simdSmull_4s
  svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h svc_simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZeta4 lane16_buildZeta4 neonDot3 neonPolyNttMul16_size nttMulRawPair
  nttMulRawPair_eq_polyVecNat polyAdd16_zero_left polyZero16 simdAdd8h_polyVecNat)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Base (
  blk05_code_eq blk05_tree_size blkLib05 blkPC05 blkPl05 blkPlaceable05 blkTree05)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3FwdLow (
  ro00Sym step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg3 (off5c60)

/-- Outer-loop GPRs and SIMD constants untouched across `+0x5d04 → +0x605c`. -/
structure Seg4InnerPres (s0 s : State) : Prop where
  x0  : s.readReg64 .x0  = s0.readReg64 .x0
  x1  : s.readReg64 .x1  = s0.readReg64 .x1
  x8  : s.readReg64 .x8  = s0.readReg64 .x8
  x9  : s.readReg64 .x9  = s0.readReg64 .x9
  x10 : s.readReg64 .x10 = s0.readReg64 .x10
  x11 : s.readReg64 .x11 = s0.readReg64 .x11
  x12 : s.readReg64 .x12 = s0.readReg64 .x12
  x13 : s.readReg64 .x13 = s0.readReg64 .x13
  x14 : s.readReg64 .x14 = s0.readReg64 .x14
  x15 : s.readReg64 .x15 = s0.readReg64 .x15
  x16 : s.readReg64 .x16 = s0.readReg64 .x16
  x17 : s.readReg64 .x17 = s0.readReg64 .x17
  x18 : s.readReg64 .x18 = s0.readReg64 .x18
  fp  : s.readReg64 .fp  = s0.readReg64 .fp
  v0  : s.readVReg128 0#5 = s0.readVReg128 0#5
  v1  : s.readVReg128 1#5 = s0.readVReg128 1#5
  v2  : s.readVReg128 2#5 = s0.readVReg128 2#5

section
set_option linter.literalFetch false
gen_placed_fetches blkPC05 blkLib05 blkTree05 blk05_code_eq blk05_tree_size
  via_placement blkPl05 blkPlaceable05 [0x5c64 → 0x6058]
end

@[simp, arm64_norm, wp_norm] abbrev off5cb0 : BitVec 64 := BitVec.ofNat 64 23728
@[simp, arm64_norm, wp_norm] abbrev off5d04 : BitVec 64 := BitVec.ofNat 64 23812
@[simp, arm64_norm, wp_norm] abbrev off5d98 : BitVec 64 := BitVec.ofNat 64 23960
@[simp, arm64_norm, wp_norm] abbrev off5ed0 : BitVec 64 := BitVec.ofNat 64 24272
@[simp, arm64_norm, wp_norm] abbrev off5f98 : BitVec 64 := BitVec.ofNat 64 24472
@[simp, arm64_norm, wp_norm] abbrev off605c : BitVec 64 := BitVec.ofNat 64 24668

@[simp, arm64_norm, wp_norm]
private theorem blkPl05_ρ [MlKemPlacement] (sym : String) :
    blkPl05.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

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

@[simp, arm64_norm, wp_norm]
private theorem svc_simdMovi_2d_0 {svc : State → State} (rd : BitVec 5) (s : State) :
    execInstWithSvc svc (.simdImmShift true true 0#4 0#3 0b11100#5 0#5 rd) s =
      (s.writeVReg128 rd 0#128).advancePC := rfl

attribute [local irreducible]
  blkPC05 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdUzp1_4s simdRev64_4s simdSmull4s simdSmlal4s

attribute [local wp_norm ↓ high]
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdMovi_8h_1024 svc_simdMvni_8h_f2ff svc_simdMovi_2d_0
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

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

private theorem vec32_ofFn_polyZero16 : Vec32.ofFn (polyVecNat polyZero16) = Vec32.zero := by
  simp [Vec32.ofFn, Vec32.zero]

/-- Pre-loop setup (`+0x5c60 → +0x5cb0`, `20` insns). -/
theorem seg4_setup [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (hbase : blkPl05.base = b) (s : State) (sp : BitVec 64) (P : SepProp)
    (hpc : s.pc = b + off5c60) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5cb0) s P
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x0 = 6144#64 ∧ s'.readReg64 .x1 = 0#64 ∧
        s'.readReg64 .x8 = 16#64 ∧ s'.readReg64 .x9 = 1536#64 ∧
        s'.readReg64 .x10 = sp + 17392#64 ∧
        s'.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x12 = sp + 2208#64 ∧ s'.readReg64 .x13 = 62209#64 ∧
        s'.readReg64 .x14 = 3329#64 ∧ s'.readReg64 .x15 = sp + 9984#64 ∧
        s'.readReg64 .x16 = 1353#64 ∧ s'.readReg64 .x17 = 20553#64 ∧
        s'.readReg64 .x18 = 20159#64 ∧ s'.readVReg128 0#5 = 0#128 ∧
        s'.readVReg128 1#5 = dup8x16 1024#16 ∧ s'.readVReg128 2#5 = dup8x16 0xf2ff#16 ∧
        P' = P) := by
  have _ : b = blkPl05.base := hbase.symm
  wp_steps
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp,
      by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp, rfl⟩

local macro "s4_zero_stp " k1:num k2:num : tactic => `(tactic| (
  apply step_stpQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { rfl }
  { wp_norm_lhs }; { rfl }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k1); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k2); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "step_zero16_stp_q0" : tactic => `(tactic| (
  s4_zero_stp 0 1; s4_zero_stp 2 3; s4_zero_stp 4 5; s4_zero_stp 6 7;
  s4_zero_stp 8 9; s4_zero_stp 10 11; s4_zero_stp 12 13; s4_zero_stp 14 15;
  s4_zero_stp 16 17; s4_zero_stp 18 19; s4_zero_stp 20 21; s4_zero_stp 22 23;
  s4_zero_stp 24 25; s4_zero_stp 26 27; s4_zero_stp 28 29; s4_zero_stp 30 31))

local macro "s4_zero0 " k:num : tactic => `(tactic| (
  apply step_strQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "step_zero32_q0" : tactic => `(tactic| (
  s4_zero0 31; s4_zero0 30; s4_zero0 29; s4_zero0 28; s4_zero0 27; s4_zero0 26; s4_zero0 25; s4_zero0 24;
  s4_zero0 23; s4_zero0 22; s4_zero0 21; s4_zero0 20; s4_zero0 19; s4_zero0 18; s4_zero0 17; s4_zero0 16;
  s4_zero0 15; s4_zero0 14; s4_zero0 13; s4_zero0 12; s4_zero0 11; s4_zero0 10; s4_zero0 9; s4_zero0 8;
  s4_zero0 7; s4_zero0 6; s4_zero0 5; s4_zero0 4; s4_zero0 3; s4_zero0 2; s4_zero0 1; s4_zero0 0))

private theorem seg4_row_head [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s : State) (sp : BitVec 64) {i : Nat} (hi : i < 3) (vInit : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off5cb0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 1)))
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hv0 : s.readVReg128 0#5 = 0#128) :
    let polyPtr := sp + 2208#64 + BitVec.ofNat 64 (512 * i)
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5d04) s
      (Poly32Mem polyPtr vInit ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x1 = BitVec.ofNat 64 (i + 1) ∧ s'.readReg64 .x2 = 0#64 ∧
        s'.readReg64 .x3 = polyPtr ∧
        s'.readReg64 .x4 = BitVec.ofNat 64 (1536 * (i + 1)) ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 2)) ∧
        (∀ r : BitVec 5, r ≠ 1#5 → r ≠ 2#5 → r ≠ 3#5 → r ≠ 4#5 → r ≠ 9#5 → r ≠ 31#5 →
          s'.readReg64 (.gpr r) = s.readReg64 (.gpr r)) ∧
        s'.readReg64 .fp = s.readReg64 .fp ∧ s'.vregs = s.vregs ∧
        P' = (Poly32Mem polyPtr Vec32.zero ∗ Rest)) := by
  dsimp only
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  have hshl : (BitVec.ofNat 64 i) <<< 9 = BitVec.ofNat 64 (512 * i) := by
    clear * - hi; rcases i with _ | _ | _ | _ <;> try omega
    all_goals decide
  rw [← hshl]
  wp_steps 5; step_zero16_stp_q0
  refine SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp; clear * -; bv_omega, by simp, by simp; exact hshl.symm,
      by simp, by simp; clear * -; bv_omega, ?_, by simp, rfl, rfl⟩
  intro r h1 h2 h3 h4 h9 h31
  simp [h31, show Reg.gpr r ≠ .x1 by intro h; cases h; exact h1 rfl,
    show Reg.gpr r ≠ .x2 by intro h; cases h; exact h2 rfl,
    show Reg.gpr r ≠ .x3 by intro h; cases h; exact h3 rfl,
    show Reg.gpr r ≠ .x4 by intro h; cases h; exact h4 rfl,
    show Reg.gpr r ≠ .x9 by intro h; cases h; exact h9 rfl]

private theorem seg4_dot_clear [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x4v : BitVec 64) {j : Nat} (_hj : j < 3)
    (vScr : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off5d04) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (512 * j))
    (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hx11 : s.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg4InnerPres s0 s) :
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5d98) s
      (Poly32Mem (sp + 9984#64) vScr ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        s'.readReg64 .x5 = 0#64 ∧
        s'.readReg64 .x6 = sp + 2208#64 + BitVec.ofNat 64 (512 * j) ∧
        s'.readReg64 .x7 = sp + 2208#64 + x4v ∧
        s'.readReg64 .x19 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem (sp + 9984#64) Vec32.zero ∗ Rest)) := by
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  wp_steps 5; step_zero32_q0
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simp; clear * -; bv_omega, by simp [hx3], by simp [hx4], by simp,
      by simp, by simp, by simp,
      ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
        by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
        by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩, rfl⟩

@[simp, arm64_norm, wp_norm] abbrev off5de4 : BitVec 64 := BitVec.ofNat 64 24036

private theorem seg4_ntt_mul_loads [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr lhsPtr x2v x4v x6v : BitVec 64) (lhs rhs : Poly16)
    {r : Nat} (hr : r < 16) (Rest : SepProp)
    (hpc : s.pc = b + off5d98) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr)
    (hx4 : s.readReg64 .x4 = x4v) (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 (32 * r))
    (hx6 : s.readReg64 .x6 = x6v) (hx7 : s.readReg64 .x7 = lhsPtr)
    (hx19 : s.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hpres : Seg4InnerPres s0 s) :
    let rhsPtr := x6v + 6208#64
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5de4) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        s'.readReg64 .x5 = BitVec.ofNat 64 (32 * r) ∧
        s'.readReg64 .x6 = x6v ∧ s'.readReg64 .x7 = lhsPtr ∧
        s'.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readReg64 .x20 = (zetaTableAt (64 + 4 * r)).zeroExtend 64 ∧
        s'.readReg64 .x21 = (zetaTableAt (66 + 4 * r)).zeroExtend 64 ∧
        s'.readReg64 .x22 = (zetaTableAt (67 + 4 * r)).zeroExtend 64 ∧
        s'.readReg64 .x23 = (zetaTableAt (65 + 4 * r)).zeroExtend 64 ∧
        s'.readVReg128 4#5 = polyVecNat lhs (2 * r) ∧
        s'.readVReg128 5#5 = polyVecNat lhs (2 * r + 1) ∧
        s'.readVReg128 6#5 = polyVecNat rhs (2 * r) ∧
        s'.readVReg128 7#5 = polyVecNat rhs (2 * r + 1) ∧
        Seg4InnerPres s0 s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) := by
  intro rhsPtr
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  refine step_ldrh16_ro (k := 64 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (64 + 4 * r))) (wb := none)
    hpc hrun (by wp_norm_lhs) rfl (by simp [evalAddrMode, hx19]; clear * - hr; bv_omega)
    hro.zetaTable (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq0
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq0)
  refine step_ldrh16_ro (k := 66 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (66 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx19]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq1
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq1)
  refine step_ldrh16_ro (k := 65 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (65 + 4 * r))) (wb := none)
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx19]; clear * - hr; bv_omega)
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq2
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq2)
  refine step_ldrh16_ro (k := 67 + 4 * r)
    (ea := mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (2 * (67 + 4 * r)))
    (wb := some (.x19, mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1))))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, hx19]; constructor <;> (clear * - hr; bv_omega))
    (by simpa using hro.zetaTable) (by omega) rfl (by wp_norm_lhs) ?_
  wp_steps 2; wp_if heq3
  · exact False.elim (zetaTableAt_zext32_ne_32768 _ (by omega) heq3)
  wp_steps 3
  refine step_ldrQ128 (wb := none) (ea := lhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (v := polyVecNat lhs (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode, extendVal, hx7, hx5]; clear * - hr; bv_omega)
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := lhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v := polyVecNat lhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega)
    (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := rhsPtr + BitVec.ofNat 64 (16 * (2 * r)))
    (v := polyVecNat rhs (2 * r))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; dsimp only [rhsPtr]; clear * - hr; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  refine step_ldrQ128 (wb := none) (ea := rhsPtr + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v := polyVecNat rhs (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; dsimp only [rhsPtr]; clear * - hr; bv_omega)
    (SepLoad128.right (SepLoad128.left (SepLoad128.vecRange (n := 32) (k := 2 * r + 1) (by omega) rfl)))
    (by wp_norm_lhs) ?_
  exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
      by simp [hx2], by simp [hx3], by simp [hx4], by simp [hx5], by simp [hx6], by simp [hx7],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
        by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
        by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩, rfl⟩

set_option maxRecDepth 200000 in
private theorem seg4_ntt_mul_simd [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr lhsPtr x2v x4v x6v : BitVec 64) (lhs rhs : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off5de4) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr)
    (hx4 : s.readReg64 .x4 = x4v) (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 (32 * r))
    (hx6 : s.readReg64 .x6 = x6v) (hx7 : s.readReg64 .x7 = lhsPtr)
    (hx13 : s.readReg64 .x13 = 62209#64) (hx14 : s.readReg64 .x14 = 3329#64)
    (hx15 : s.readReg64 .x15 = sp + 9984#64)
    (hx19 : s.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)))
    (hx20 : s.readReg64 .x20 = (zetaTableAt (64 + 4 * r)).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = (zetaTableAt (66 + 4 * r)).zeroExtend 64)
    (hx22 : s.readReg64 .x22 = (zetaTableAt (67 + 4 * r)).zeroExtend 64)
    (hx23 : s.readReg64 .x23 = (zetaTableAt (65 + 4 * r)).zeroExtend 64)
    (hv4 : s.readVReg128 4#5 = polyVecNat lhs (2 * r))
    (hv5 : s.readVReg128 5#5 = polyVecNat lhs (2 * r + 1))
    (hv6 : s.readVReg128 6#5 = polyVecNat rhs (2 * r))
    (hv7 : s.readVReg128 7#5 = polyVecNat rhs (2 * r + 1))
    (hpres : Seg4InnerPres s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + off5d98 else b + off5ed0) s
      (PolyMem (sp + 9984#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        s'.readReg64 .x5 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x6 = x6v ∧ s'.readReg64 .x7 = lhsPtr ∧
        s'.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ s'.readVReg128 18#5 = dup8x16 62209#16 ∧
        Seg4InnerPres s0 s' ∧
        P' = (PolyMem (sp + 9984#64)
          (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
            (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro prod
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  wp_steps 57
  have hz21 := lane16_buildZeta4
    ((zetaTableAt (64 + 4 * r)).zeroExtend 64) ((zetaTableAt (66 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (64 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (66 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hz22 := lane16_buildZeta4
    ((zetaTableAt (65 + 4 * r)).zeroExtend 64) ((zetaTableAt (67 + 4 * r)).zeroExtend 64)
    ((0#32 - ((zetaTableAt (65 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
    ((0#32 - ((zetaTableAt (67 + 4 * r)).zeroExtend 64).truncate 32).zeroExtend 64)
  have hpair := nttMulRawPair_eq_polyVecNat lhs rhs r hr _ _
    (hz21.1.trans (zext64_trunc16 _)) (hz21.2.1.trans (zext64_trunc16 _))
    (hz21.2.2.1.trans (neg_zext_trunc16 _)) (hz21.2.2.2.trans (neg_zext_trunc16 _))
    (hz22.1.trans (zext64_trunc16 _)) (hz22.2.1.trans (zext64_trunc16 _))
    (hz22.2.2.1.trans (neg_zext_trunc16 _)) (hz22.2.2.2.trans (neg_zext_trunc16 _))
  dsimp only [nttMulRawPair, buildZeta4] at hpair
  refine step_stpQ128 (wb := none) (ea := (sp + 9984#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 9984#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
    (v1 := polyVecNat prod (2 * r)) (v2 := polyVecNat prod (2 * r + 1))
    (by wp_norm_lhs) (by simp [hrun]) (by wp_norm_lhs) rfl
    (by simp [evalAddrMode]; clear * - hr; bv_omega) (by clear * -; bv_omega)
    (by dsimp only [prod]; rw [← hpair.1]; simp)
    (by dsimp only [prod]; rw [← hpair.2]; simp)
    (SepStore128.left (SepStore128.polyMem (k := 2 * r) (by omega) rfl))
    (SepStore128.left (SepStore128.polyMem (k := 2 * r + 1) (by omega) rfl))
    (by wp_norm_lhs) ?_
  intro m'
  have hcnd : ConditionHolds .NE
      (AddWithCarry64 (BitVec.ofNat 64 (32 * r) + 32#64) (~~~512#64) true).2 = decide (r < 15) := by
    clear * - hr
    rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
        r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases hr15 : r < 15
  · simp only [hr15, ↓reduceIte]
    refine step_bCond_taken (pc := b + BitVec.ofNat 64 24268) (dst := b + off5d98)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [_hb]; wp_norm_lhs)
      (by simpa [subsPState64, hr15] using hcnd)
      (by dsimp only [off5d98]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx2], by simp [hx3], by simp [hx4], by simp; clear * - hr15; bv_omega,
        by simp [hx6], by simp [hx7], by simp [hx19], by simp, by simp,
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩, rfl⟩
  · have hr_eq : r = 15 := by omega
    simp only [hr15, ↓reduceIte]
    refine step_bCond_not_taken (pc := b + BitVec.ofNat 64 24268) (dst := b + off5ed0)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [_hb]; wp_norm_lhs)
      (by simpa [subsPState64, hr15] using hcnd)
      (by dsimp only [off5ed0]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [hrun])
      ⟨by simp [hsp], by simpa [State.spAligned] using hspA,
        by simp [hx2], by simp [hx3], by simp [hx4], by simp [hr_eq],
        by simp [hx6], by simp [hx7], by simp [hx19], by simp, by simp,
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩, rfl⟩

private theorem seg4_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr lhsPtr x2v x4v x6v : BitVec 64) (lhs rhs : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + off5d98) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr)
    (hx4 : s.readReg64 .x4 = x4v) (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 (32 * r))
    (hx6 : s.readReg64 .x6 = x6v) (hx7 : s.readReg64 .x7 = lhsPtr)
    (hx13 : s.readReg64 .x13 = 62209#64) (hx14 : s.readReg64 .x14 = 3329#64)
    (hx15 : s.readReg64 .x15 = sp + 9984#64)
    (hx19 : s.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hpres : Seg4InnerPres s0 s) :
    let rhsPtr := x6v + 6208#64
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC05.rebase b (fun _ => none))
      (if r < 15 then b + off5d98 else b + off5ed0) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 9984#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        s'.readReg64 .x5 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x6 = x6v ∧ s'.readReg64 .x7 = lhsPtr ∧
        s'.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ s'.readVReg128 18#5 = dup8x16 62209#16 ∧
        Seg4InnerPres s0 s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 9984#64)
            (Function.update (Function.update f (2 * r) (polyVecNat prod (2 * r)))
              (2 * r + 1) (polyVecNat prod (2 * r + 1))) ∗ Rest)) := by
  intro rhsPtr prod
  refine SepWP.seq (seg4_ntt_mul_loads hb s0 s sp polyPtr lhsPtr x2v x4v x6v lhs rhs hr
    (PolyMem (sp + 9984#64) f ∗ Rest) hpc hrun hsp hspA hro hx2 hx3 hx4 hx5 hx6 hx7 hx19 hpres) ?_
  rintro s1 P1 hpc1 hrun1
    ⟨hsp1, hspA1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1,
      hv4_1, hv5_1, hv6_1, hv7_1, hpres1, rfl⟩
  rw [show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        (PolyMem (sp + 9984#64) f ∗ Rest)) =
      (PolyMem (sp + 9984#64) f ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.mono (seg4_ntt_mul_simd hb s0 s1 sp polyPtr lhsPtr x2v x4v x6v lhs rhs hr f _
    hpc1 hrun1 hsp1 hspA1 hx2_1 hx3_1 hx4_1 hx5_1 hx6_1 hx7_1
    (hpres1.x13.trans (hpres.x13.symm.trans hx13))
    (hpres1.x14.trans (hpres.x14.symm.trans hx14))
    (hpres1.x15.trans (hpres.x15.symm.trans hx15))
    hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hv4_1 hv5_1 hv6_1 hv7_1 hpres1) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx2', hx3', hx4', hx5', hx6', hx7', hx19', hv3', hv18', hpres', rfl⟩
  exact ⟨hsp', hspA', hx2', hx3', hx4', hx5', hx6', hx7', hx19', hv3', hv18', hpres',
    sepProp_ext (by sep_frame) (by sep_frame)⟩

private theorem seg4_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 : State) (sp polyPtr lhsPtr x2v x4v x6v : BitVec 64) (lhs rhs : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + off5d98 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x2 = x2v → s.readReg64 .x3 = polyPtr → s.readReg64 .x4 = x4v →
      s.readReg64 .x5 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x6 = x6v → s.readReg64 .x7 = lhsPtr →
      s.readReg64 .x13 = 62209#64 → s.readReg64 .x14 = 3329#64 →
      s.readReg64 .x15 = sp + 9984#64 →
      s.readReg64 .x19 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      Seg4InnerPres s0 s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC05.rebase b (fun _ => none)) (b + off5ed0) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem (x6v + 6208#64) (polyVecNat rhs) ∗
          PolyMem (sp + 9984#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧
          s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
          s'.readVReg128 3#5 = dup8x16 3329#16 ∧ Seg4InnerPres s0 s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem (x6v + 6208#64) (polyVecNat rhs) ∗
            Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
  intro rem; induction rem with
  | zero =>
    intro r hrem s f hpc hrun hsp hspA _hcl hro hx2 hx3 hx4 hx5 hx6 hx7 hx13 hx14 hx15 hx19 hpres hf
    have hr15 : r = 15 := by omega
    subst hr15
    have hiter := seg4_ntt_mul_iter hb s0 s sp polyPtr lhsPtr x2v x4v x6v lhs rhs (r := 15) (by omega) f Rest
      hpc hrun hsp hspA hro hx2 hx3 hx4 hx5 hx6 hx7 hx13 hx14 hx15 hx19 hpres
    dsimp only at hiter; simp only [Nat.lt_irrefl, ↓reduceIte] at hiter
    refine SepWP.mono hiter ?_
    rintro s' P' _ _ ⟨hsp', hspA', hx2', hx3', hx4', _, _, _, _, hv3', _, hpres', hP'⟩
    exact ⟨hsp', hspA', hx2', hx3', hx4', hv3', hpres',
      hP'.trans (by rw [polyMem_congr (update2_prefix (r := 15) hf), poly32Mem_ofFn])⟩
  | succ rem ih =>
    intro r hrem s f hpc hrun hsp hspA hcl hro hx2 hx3 hx4 hx5 hx6 hx7 hx13 hx14 hx15 hx19 hpres hf
    have hr15 : r < 15 := by omega
    have hiter := seg4_ntt_mul_iter hb s0 s sp polyPtr lhsPtr x2v x4v x6v lhs rhs (by omega) f Rest
      hpc hrun hsp hspA hro hx2 hx3 hx4 hx5 hx6 hx7 hx13 hx14 hx15 hx19 hpres
    dsimp only at hiter; simp only [hr15, ↓reduceIte] at hiter
    refine sepWP_seq_env hcl hro hiter ?_
    rintro sm Pm hpc_m hrun_m hcl_m hro_m
      ⟨hsp_m, hspA_m, hx2_m, hx3_m, hx4_m, hx5_m, hx6_m, hx7_m, hx19_m, _, _, hpres_m, hPm⟩
    subst hPm
    exact ih (r + 1) (by omega) sm _ hpc_m hrun_m hsp_m hspA_m hcl_m hro_m
      hx2_m hx3_m hx4_m hx5_m hx6_m hx7_m (hpres_m.x13.trans (hpres.x13.symm.trans hx13))
      (hpres_m.x14.trans (hpres.x14.symm.trans hx14)) (hpres_m.x15.trans (hpres.x15.symm.trans hx15))
      hx19_m hpres_m (update2_prefix hf)

@[simp, arm64_norm, wp_norm] abbrev off5fe0 : BitVec 64 := BitVec.ofNat 64 24544

local macro "s4_ldp0 " k1:num k2:num : tactic => `(tactic| (
  apply step_ldpQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { rfl }
  { wp_norm_lhs }; { rfl }
  { apply SepLoad128.left; apply SepLoad128.vec32 (k := $k1); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { apply SepLoad128.left; apply SepLoad128.vec32 (k := $k2); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

local macro "s4_stp0 " k1:num k2:num : tactic => `(tactic| (
  apply step_stpQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { rfl }
  { wp_norm_lhs }; { rfl }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k1); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.set] } }
  { apply SepStore128.left; apply SepStore128.vec32 (k := $k2); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.set] } }
  { wp_norm_lhs }; intro _))

local macro "s4_ldr1 " k:num : tactic => `(tactic| (
  apply step_ldrQ128
  { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }; { wp_norm_lhs }
  { apply SepLoad128.right; apply SepLoad128.left
    apply SepLoad128.vec32 (k := $k); { decide }; { clear * -; bv_omega }; { dsimp only [Vec32.ofFn, Vec32.get] } }
  { wp_norm_lhs }))

private def Seg4MidRegs (idx : Nat) (acc prod : Poly16) (s : State) : Prop :=
  s.readVReg128 3#5 = dup8x16 3329#16 ∧
  s.readVReg128 5#5 = polyVecNat acc (idx + 1) ∧ s.readVReg128 6#5 = polyVecNat prod (idx + 1) ∧
  s.readVReg128 17#5 = polyVecNat acc idx ∧ s.readVReg128 18#5 = polyVecNat prod idx ∧
  s.readVReg128 19#5 = polyVecNat acc 28 ∧ s.readVReg128 20#5 = polyVecNat acc 29 ∧
  s.readVReg128 21#5 = polyVecNat prod 28 ∧ s.readVReg128 22#5 = polyVecNat prod 29

private def seg4Mid14 (acc acc' : Poly16) : Vec32 :=
  { (Vec32.ofFn (polyVecNat acc)) with
    v0 := polyVecNat acc' 0, v1 := polyVecNat acc' 1, v2 := polyVecNat acc' 2,
    v3 := polyVecNat acc' 3, v4 := polyVecNat acc' 4, v5 := polyVecNat acc' 5,
    v6 := polyVecNat acc' 6, v7 := polyVecNat acc' 7, v8 := polyVecNat acc' 8,
    v9 := polyVecNat acc' 9, v10 := polyVecNat acc' 10, v11 := polyVecNat acc' 11,
    v12 := polyVecNat acc' 12, v13 := polyVecNat acc' 13 }

private def seg4Mid20 (acc acc' : Poly16) : Vec32 :=
  { seg4Mid14 acc acc' with
    v14 := polyVecNat acc' 14, v15 := polyVecNat acc' 15, v16 := polyVecNat acc' 16,
    v17 := polyVecNat acc' 17, v18 := polyVecNat acc' 18, v19 := polyVecNat acc' 19 }

private theorem seg4_accum_lo [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x4v : BitVec 64) {j : Nat} (hj : j < 3)
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off5ed0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (512 * (j + 1)))
    (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hv3 : s.readVReg128 3#5 = dup8x16 3329#16) (hpres : Seg4InnerPres s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5f98) s
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 2) ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v + 512#64 ∧
        Seg4MidRegs 14 acc prod s' ∧ Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem polyPtr (seg4Mid14 acc acc') ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  s4_ldp0 0 1; wp_step; s4_ldr1 0; s4_ldr1 1; wp_step; s4_ldr1 3; s4_ldr1 4; s4_ldr1 28
  wp_step; wp_step; s4_ldr1 2; s4_ldp0 2 3; s4_ldr1 29; s4_stp0 0 1
  s4_ldp0 4 5; wp_step; wp_step; s4_ldr1 5; wp_step; s4_ldr1 6; s4_stp0 2 3
  wp_step; s4_ldr1 7; s4_ldp0 6 7; s4_ldp0 28 29; s4_stp0 4 5
  wp_step; wp_step; s4_ldr1 8; s4_ldp0 8 9; s4_ldr1 9; s4_stp0 6 7
  wp_step; wp_step; s4_ldr1 10; s4_ldp0 10 11; s4_ldr1 11; s4_stp0 8 9
  wp_step; wp_step; s4_ldr1 12; s4_ldp0 12 13; s4_ldr1 13; s4_stp0 10 11
  wp_step; wp_step; s4_ldr1 14; s4_ldp0 14 15; s4_ldr1 15; s4_stp0 12 13
  have hpst : ConditionHolds .NE
      (AddWithCarry64 (BitVec.ofNat 64 (512 * (j + 1))) (~~~1536#64) true).2 = decide (j < 2) := by
    clear * - hj; rcases j with _ | _ | _ | _ <;> try omega
    all_goals decide
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
      by simpa [subsPState64] using hpst,
      by simp [hx2], by simp [hx3], by simp,
      ⟨by simp [hv3], by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
        by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
        by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩,
      by simp [seg4Mid14, Vec32.ofFn]⟩

private theorem seg4_accum_mid [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x2v x4v : BitVec 64) {j : Nat}
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off5f98) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 2))
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hmid : Seg4MidRegs 14 acc prod s) (hpres : Seg4InnerPres s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off5fe0) s
      (Poly32Mem polyPtr (seg4Mid14 acc acc') ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 2) ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        Seg4MidRegs 20 acc prod s' ∧ Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem polyPtr (seg4Mid20 acc acc') ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [seg4Mid14]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv3, hv5, hv6, hv17, hv18, hv19, hv20, hv21, hv22⟩
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  wp_step; wp_step; s4_ldr1 16; s4_ldp0 16 17; s4_ldr1 17; s4_stp0 14 15
  wp_step; wp_step; s4_ldr1 18; s4_ldp0 18 19; s4_ldr1 19; s4_stp0 16 17
  wp_step; wp_step; s4_ldr1 20; s4_ldp0 20 21; s4_ldr1 21; s4_stp0 18 19
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], by simpa using hpst,
      by simp [hx2], by simp [hx3], by simp [hx4],
      ⟨by simp [hv3], by simp, by simp, by simp, by simp,
        by simp [hv19], by simp [hv20], by simp [hv21], by simp [hv22]⟩,
      ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
        by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
        by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩,
      by simp [seg4Mid20, seg4Mid14, Vec32.ofFn]⟩

@[simp, arm64_norm, wp_norm] abbrev off601c : BitVec 64 := BitVec.ofNat 64 24604

private def seg4Mid24 (acc acc' : Poly16) : Vec32 :=
  { seg4Mid20 acc acc' with
    v20 := polyVecNat acc' 20, v21 := polyVecNat acc' 21,
    v22 := polyVecNat acc' 22, v23 := polyVecNat acc' 23 }

private def Seg4HiRegs (acc acc' prod : Poly16) (s : State) : Prop :=
  s.readVReg128 3#5 = dup8x16 3329#16 ∧
  s.readVReg128 4#5 = polyVecNat acc' 25 ∧ s.readVReg128 6#5 = polyVecNat acc' 24 ∧
  s.readVReg128 17#5 = polyVecNat prod 26 ∧
  s.readVReg128 19#5 = polyVecNat acc 28 ∧ s.readVReg128 20#5 = polyVecNat acc 29 ∧
  s.readVReg128 21#5 = polyVecNat prod 28 ∧ s.readVReg128 22#5 = polyVecNat prod 29

private theorem seg4_accum_hi1 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x2v x4v : BitVec 64) {j : Nat}
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off5fe0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 2))
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hmid : Seg4MidRegs 20 acc prod s) (hpres : Seg4InnerPres s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off601c) s
      (Poly32Mem polyPtr (seg4Mid20 acc acc') ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ ConditionHolds .NE s'.pstate = decide (j < 2) ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        Seg4HiRegs acc acc' prod s' ∧ Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem polyPtr (seg4Mid24 acc acc') ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [seg4Mid20, seg4Mid14]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hmid with ⟨hv3, hv5, hv6, hv17, hv18, hv19, hv20, hv21, hv22⟩
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  wp_step; wp_step; s4_ldr1 22; s4_ldp0 22 23; s4_ldr1 23; s4_stp0 20 21
  s4_ldr1 25; wp_step; s4_ldp0 24 25; wp_step; s4_ldr1 24; wp_step; wp_step; s4_ldr1 26; s4_stp0 22 23
  exact SepWP.done (by wp_norm_lhs) (by simp [*])
    ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk], by simpa using hpst,
      by simp [hx2], by simp [hx3], by simp [hx4],
      ⟨by simp [hv3], by simp, by simp, by simp,
        by simp [hv19], by simp [hv20], by simp [hv21], by simp [hv22]⟩,
      ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
        by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
        by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩,
      by simp [seg4Mid24, seg4Mid20, seg4Mid14, Vec32.ofFn]⟩
set_option maxRecDepth 200000 in
private theorem seg4_accum_hi2 [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x2v x4v : BitVec 64) {j : Nat}
    (acc prod : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off601c) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hpst : ConditionHolds .NE s.pstate = decide (j < 2))
    (hx2 : s.readReg64 .x2 = x2v) (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hhi : Seg4HiRegs acc (polyAdd16 acc prod) prod s) (hpres : Seg4InnerPres s0 s) :
    let acc' := polyAdd16 acc prod
    SepWP (blkPC05.rebase b (fun _ => none))
      (if j < 2 then b + off5d04 else b + off605c) s
      (Poly32Mem polyPtr (seg4Mid24 acc acc') ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = x2v ∧ s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc')) ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  dsimp only [seg4Mid24, seg4Mid20, seg4Mid14]
  have hsp_chk : (sp &&& 15#64 == 0#64) = true := by simpa [State.spAligned, hsp] using hspA
  rcases hhi with ⟨hv3, hv4, hv6, hv17, hv19, hv20, hv21, hv22⟩
  rcases hpres with ⟨p0, p1, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, pfp, pv0, pv1, pv2⟩
  s4_ldp0 26 27; s4_ldr1 27; wp_step; s4_stp0 24 25; s4_ldr1 30; wp_step; wp_step; s4_ldr1 31; wp_step
  s4_stp0 26 27; s4_ldp0 30 31; s4_stp0 28 29; wp_step; wp_step; s4_stp0 30 31
  by_cases hj2 : j < 2
  · simp only [hj2, ↓reduceIte]
    refine step_bCond_taken (pc := b + BitVec.ofNat 64 24664) (dst := b + off5d04)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [_hb]; wp_norm_lhs)
      (by simpa [hj2] using hpst) (by dsimp only [off5d04]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx2], by simp [hx3], by simp [hx4], by simp [hv3],
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩,
        by simp [Vec32.ofFn]⟩
  · simp only [hj2, ↓reduceIte]
    refine step_bCond_not_taken (pc := b + BitVec.ofNat 64 24664) (dst := b + off605c)
      (by wp_norm_lhs) (by simp [hrun]) (by rw [_hb]; wp_norm_lhs)
      (by simpa [hj2] using hpst) (by dsimp only [off605c]; clear * -; bv_omega) ?_
    exact SepWP.done rfl (by simp [*])
      ⟨by simp [hsp], by simp [State.spAligned, hsp, hsp_chk],
        by simp [hx2], by simp [hx3], by simp [hx4], by simp [hv3],
        ⟨by simp [p0], by simp [p1], by simp [p8], by simp [p9], by simp [p10], by simp [p11],
          by simp [p12], by simp [p13], by simp [p14], by simp [p15], by simp [p16],
          by simp [p17], by simp [p18], by simp [pfp], by simp [pv0], by simp [pv1], by simp [pv2]⟩,
        by simp [Vec32.ofFn]⟩

private theorem seg4_dot_iter [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s0 s : State) (sp polyPtr x4v : BitVec 64) {j : Nat} (hj : j < 3)
    (lhs rhs acc : Poly16) (vScr : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off5d04) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (512 * j))
    (hx3 : s.readReg64 .x3 = polyPtr) (hx4 : s.readReg64 .x4 = x4v)
    (hx11 : s.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hx13 : s.readReg64 .x13 = 62209#64) (hx14 : s.readReg64 .x14 = 3329#64)
    (hx15 : s.readReg64 .x15 = sp + 9984#64)
    (hv0 : s.readVReg128 0#5 = 0#128) (hpres : Seg4InnerPres s0 s) :
    let lhsPtr := sp + 2208#64 + x4v
    let rhsPtr := sp + 8416#64 + BitVec.ofNat 64 (512 * j)
    let prod := neonPolyNttMul16 lhs rhs
    let acc' := polyAdd16 acc prod
    SepWP (blkPC05.rebase b (fun _ => none))
      (if j < 2 then b + off5d04 else b + off605c) s
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 9984#64) vScr ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x2 = BitVec.ofNat 64 (512 * (j + 1)) ∧
        s'.readReg64 .x3 = polyPtr ∧ s'.readReg64 .x4 = x4v + 512#64 ∧
        s'.readVReg128 3#5 = dup8x16 3329#16 ∧ Seg4InnerPres s0 s' ∧
        P' = (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc')) ∗
          PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗ Rest)) := by
  intro lhsPtr rhsPtr prod acc'
  have hrhs_eq : (sp + 2208#64 + BitVec.ofNat 64 (512 * j)) + 6208#64 = rhsPtr := by
    dsimp only [rhsPtr]; clear * -; bv_omega
  rw [show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem rhsPtr (polyVecNat rhs) ∗ Poly32Mem (sp + 9984#64) vScr ∗ Rest) =
      (Poly32Mem (sp + 9984#64) vScr ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl hro (seg4_dot_clear hb s0 s sp polyPtr x4v hj vScr _
    hpc hrun hsp hspA hx2 hx3 hx4 hx11 hx12 hv0 hpres) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx19_1, hpres1, rfl⟩
  rw [← hrhs_eq, show (Poly32Mem (sp + 9984#64) Vec32.zero ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗
          PolyMem ((sp + 2208#64 + BitVec.ofNat 64 (512 * j)) + 6208#64) (polyVecNat rhs) ∗
          Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) =
      (PolyMem lhsPtr (polyVecNat lhs) ∗
        PolyMem ((sp + 2208#64 + BitVec.ofNat 64 (512 * j)) + 6208#64) (polyVecNat rhs) ∗
        PolyMem (sp + 9984#64) Vec32.zero.get ∗
        (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) from by
    change (PolyMem (sp + 9984#64) Vec32.zero.get ∗ _) = _
    exact sepProp_ext (by sep_frame) (by sep_frame)]
  refine sepWP_seq_env hcl1 hro1 (seg4_ntt_mul_loop hb s0 sp polyPtr lhsPtr
    (BitVec.ofNat 64 (512 * (j + 1))) x4v (sp + 2208#64 + BitVec.ofNat 64 (512 * j)) lhs rhs _
    15 0 rfl s1 Vec32.zero.get hpc1 hrun1 hsp1 hspA1 hcl1 hro1
    hx2_1 hx3_1 hx4_1 hx5_1 hx6_1 hx7_1
    (hpres1.x13.trans (hpres.x13.symm.trans hx13))
    (hpres1.x14.trans (hpres.x14.symm.trans hx14))
    (hpres1.x15.trans (hpres.x15.symm.trans hx15))
    hx19_1 hpres1 (by omega)) ?_
  rintro s2 P2 hpc2 hrun2 _hcl2 _hro2 ⟨hsp2, hspA2, hx2_2, hx3_2, hx4_2, hv3_2, hpres2, rfl⟩
  rw [hrhs_eq, show (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗ Rest)) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc)) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat prod)) ∗
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ Rest)) from
    sepProp_ext (by sep_frame) (by sep_frame)]
  refine SepWP.seq (seg4_accum_lo hb s0 s2 sp polyPtr x4v hj acc prod _
    hpc2 hrun2 hsp2 hspA2 hx2_2 hx3_2 hx4_2 hv3_2 hpres2) ?_
  rintro sm1 Pm1 hpcm1 hrunm1 ⟨hspm1, hspAm1, hpstm1, hx2m1, hx3m1, hx4m1, hmid1, hpresm1, rfl⟩
  refine SepWP.seq (seg4_accum_mid hb s0 sm1 sp polyPtr _ (x4v + 512#64) acc prod _
    hpcm1 hrunm1 hspm1 hspAm1 hpstm1 hx2m1 hx3m1 hx4m1 hmid1 hpresm1) ?_
  rintro sm2 Pm2 hpcm2 hrunm2 ⟨hspm2, hspAm2, hpstm2, hx2m2, hx3m2, hx4m2, hmid2, hpresm2, rfl⟩
  refine SepWP.seq (seg4_accum_hi1 hb s0 sm2 sp polyPtr _ (x4v + 512#64) acc prod _
    hpcm2 hrunm2 hspm2 hspAm2 hpstm2 hx2m2 hx3m2 hx4m2 hmid2 hpresm2) ?_
  rintro sm3 Pm3 hpcm3 hrunm3 ⟨hspm3, hspAm3, hpstm3, hx2m3, hx3m3, hx4m3, hhi3, hpresm3, rfl⟩
  refine SepWP.mono (seg4_accum_hi2 hb s0 sm3 sp polyPtr _ (x4v + 512#64) acc prod _
    hpcm3 hrunm3 hspm3 hspAm3 hpstm3 hx2m3 hx3m3 hx4m3 hhi3 hpresm3) ?_
  rintro s' P' _ _ ⟨hsp', hspA', hx2', hx3', hx4', hv3', hpres', rfl⟩
  exact ⟨hsp', hspA', hx2', hx3', hx4', hv3', hpres', sepProp_ext (by sep_frame) (by sep_frame)⟩

theorem seg4_row_dot [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl05 b)
    (s : State) (sp : BitVec 64) {i : Nat} (hi : i < 3)
    (l0 l1 l2 r0 r1 r2 : Poly16) (vInit vScr : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + off5cb0) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx0 : s.readReg64 .x0 = 6144#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 1)))
    (hx11 : s.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64)
    (hx12 : s.readReg64 .x12 = sp + 2208#64)
    (hx13 : s.readReg64 .x13 = 62209#64) (hx14 : s.readReg64 .x14 = 3329#64)
    (hx15 : s.readReg64 .x15 = sp + 9984#64)
    (hv0 : s.readVReg128 0#5 = 0#128) :
    let polyPtr := sp + 2208#64 + BitVec.ofNat 64 (512 * i)
    let lhsBase := sp + 3744#64 + BitVec.ofNat 64 (1536 * i)
    let dot := neonDot3 l0 l1 l2 r0 r1 r2
    SepWP (blkPC05.rebase b (fun _ => none)) (b + off605c) s
      (Poly32Mem polyPtr vInit ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗
        Poly32Mem (sp + 9984#64) vScr ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .fp = s.readReg64 .fp ∧
        s'.readReg64 .x0 = 6144#64 ∧ s'.readReg64 .x1 = BitVec.ofNat 64 (i + 1) ∧
        s'.readReg64 .x8 = s.readReg64 .x8 ∧
        s'.readReg64 .x9 = BitVec.ofNat 64 (1536 * (i + 2)) ∧
        s'.readReg64 .x10 = s.readReg64 .x10 ∧
        s'.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x12 = sp + 2208#64 ∧ s'.readReg64 .x13 = 62209#64 ∧
        s'.readReg64 .x14 = 3329#64 ∧ s'.readReg64 .x15 = sp + 9984#64 ∧
        s'.readReg64 .x16 = s.readReg64 .x16 ∧ s'.readReg64 .x17 = s.readReg64 .x17 ∧
        s'.readReg64 .x18 = s.readReg64 .x18 ∧
        s'.readVReg128 0#5 = 0#128 ∧ s'.readVReg128 1#5 = s.readVReg128 1#5 ∧
        s'.readVReg128 2#5 = s.readVReg128 2#5 ∧ s'.readVReg128 3#5 = dup8x16 3329#16 ∧
        P' = (PolyMem polyPtr (polyVecNat dot) ∗
          PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
          PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
          PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
          PolyMem (sp + 9440#64) (polyVecNat r2) ∗
          Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 l2 r2))) ∗ Rest)) := by
  intro polyPtr lhsBase dot
  let p0 := neonPolyNttMul16 l0 r0
  let p1 := neonPolyNttMul16 l1 r1
  let acc1 := polyAdd16 p0 p1
  let Rest0 : SepProp := PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem (sp + 8928#64) (polyVecNat r1) ∗ PolyMem (sp + 9440#64) (polyVecNat r2) ∗ Rest
  let Rest1 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
    PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 9440#64) (polyVecNat r2) ∗ Rest
  let Rest2 : SepProp := PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
    PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗ Rest
  refine sepWP_seq_env hcl hro
    (seg4_row_head hb s sp hi vInit _ hpc hrun hsp hspA hx1 hx9 hx12 hv0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hx1_1, hx2_1, hx3_1, hx4_1, hx9_1, hgpr1, hfp1, hvregs1, rfl⟩
  have hpres1 : Seg4InnerPres s1 s1 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hv1 (r : BitVec 5) : s1.readVReg128 r = s.readVReg128 r := by
    simp [State.readVReg128, hvregs1]
  have hx11_1 : s1.readReg64 .x11 = mlkemMpl.ρ ro00Sym + 134#64 :=
    (hgpr1 11#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11
  have hx12_1 : s1.readReg64 .x12 = sp + 2208#64 :=
    (hgpr1 12#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx12
  have hx13_1 : s1.readReg64 .x13 = 62209#64 :=
    (hgpr1 13#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13
  have hx14_1 : s1.readReg64 .x14 = 3329#64 :=
    (hgpr1 14#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14
  have hx15_1 : s1.readReg64 .x15 = sp + 9984#64 :=
    (hgpr1 15#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15
  have hv0_1 : s1.readVReg128 0#5 = 0#128 := (hv1 0#5).trans hv0
  have hlhs0 : sp + 2208#64 + BitVec.ofNat 64 (1536 * (i + 1)) = lhsBase := by
    dsimp only [lhsBase]; clear * -; bv_omega
  have hlhs1 : BitVec.ofNat 64 (1536 * (i + 1)) + 512#64 = BitVec.ofNat 64 (1536 * (i + 1) + 512) := by
    clear * -; bv_omega
  rw [ ← vec32_ofFn_polyZero16, show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat polyZero16)) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (lhsBase + 512#64) (polyVecNat l1) ∗
        PolyMem (lhsBase + 1024#64) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64) (polyVecNat r0) ∗ PolyMem (sp + 8928#64) (polyVecNat r1) ∗
        PolyMem (sp + 9440#64) (polyVecNat r2) ∗ Poly32Mem (sp + 9984#64) vScr ∗ Rest) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat polyZero16)) ∗
        PolyMem (sp + 2208#64 + BitVec.ofNat 64 (1536 * (i + 1))) (polyVecNat l0) ∗
        PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 0)) (polyVecNat r0) ∗
        Poly32Mem (sp + 9984#64) vScr ∗ Rest0) from by
    rw [hlhs0, show sp + 8416#64 + BitVec.ofNat 64 (512 * 0) = sp + 8416#64 by clear * -; bv_omega]
    exact sepProp_ext (by dsimp only [Rest0]; sep_frame) (by dsimp only [Rest0]; sep_frame)]
  have hj0 := seg4_dot_iter hb s1 s1 sp polyPtr (BitVec.ofNat 64 (1536 * (i + 1))) (j := 0) (by decide)
    l0 r0 polyZero16 vScr Rest0 hpc1 hrun1 hsp1 hspA1 hcl1 hro1
    hx2_1 hx3_1 hx4_1 hx11_1 hx12_1 hx13_1 hx14_1 hx15_1 hv0_1 hpres1
  dsimp only at hj0
  simp only [Nat.zero_lt_two, ↓reduceIte, polyAdd16_zero_left (neonPolyNttMul16_size l0 r0)] at hj0
  refine sepWP_seq_env hcl1 hro1 hj0 ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hx2_2, hx3_2, hx4_2, _, hpres2, rfl⟩
  rw [hlhs0, show sp + 8416#64 + BitVec.ofNat 64 (512 * 0) = sp + 8416#64 by clear * -; bv_omega,
      show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat p0)) ∗
        PolyMem lhsBase (polyVecNat l0) ∗ PolyMem (sp + 8416#64) (polyVecNat r0) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest0) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat p0)) ∗
        PolyMem (sp + 2208#64 + (BitVec.ofNat 64 (1536 * (i + 1)) + 512#64)) (polyVecNat l1) ∗
        PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 1)) (polyVecNat r1) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat p0)) ∗ Rest1) from by
    rw [show sp + 2208#64 + (BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) = lhsBase + 512#64 by
          dsimp only [lhsBase]; clear * -; bv_omega,
        show sp + 8416#64 + BitVec.ofNat 64 (512 * 1) = sp + 8928#64 by clear * -; bv_omega]
    exact sepProp_ext (by dsimp only [Rest0, Rest1]; sep_frame) (by dsimp only [Rest0, Rest1]; sep_frame)]
  have hj1 := seg4_dot_iter hb s1 s2 sp polyPtr (BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) (j := 1) (by decide)
    l1 r1 p0 (Vec32.ofFn (polyVecNat p0)) Rest1 hpc2 hrun2 hsp2 hspA2 hcl2 hro2
    hx2_2 hx3_2 hx4_2 (hpres2.x11.trans hx11_1) (hpres2.x12.trans hx12_1)
    (hpres2.x13.trans hx13_1) (hpres2.x14.trans hx14_1) (hpres2.x15.trans hx15_1)
    (hpres2.v0.trans hv0_1) hpres2
  dsimp only at hj1; simp only [Nat.one_lt_two, ↓reduceIte] at hj1
  refine sepWP_seq_env hcl2 hro2 hj1 ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hx2_3, hx3_3, hx4_3, _, hpres3, rfl⟩
  rw [show (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc1)) ∗
        PolyMem (sp + 2208#64 + (BitVec.ofNat 64 (1536 * (i + 1)) + 512#64)) (polyVecNat l1) ∗
        PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 1)) (polyVecNat r1) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest1) =
      (Poly32Mem polyPtr (Vec32.ofFn (polyVecNat acc1)) ∗
        PolyMem (sp + 2208#64 + ((BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) + 512#64)) (polyVecNat l2) ∗
        PolyMem (sp + 8416#64 + BitVec.ofNat 64 (512 * 2)) (polyVecNat r2) ∗
        Poly32Mem (sp + 9984#64) (Vec32.ofFn (polyVecNat p1)) ∗ Rest2) from by
    rw [show sp + 2208#64 + (BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) = lhsBase + 512#64 by
          dsimp only [lhsBase]; clear * -; bv_omega,
        show sp + 2208#64 + ((BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) + 512#64) = lhsBase + 1024#64 by
          dsimp only [lhsBase]; clear * -; bv_omega,
        show sp + 8416#64 + BitVec.ofNat 64 (512 * 1) = sp + 8928#64 by clear * -; bv_omega,
        show sp + 8416#64 + BitVec.ofNat 64 (512 * 2) = sp + 9440#64 by clear * -; bv_omega]
    exact sepProp_ext (by dsimp only [Rest1, Rest2]; sep_frame) (by dsimp only [Rest1, Rest2]; sep_frame)]
  have hj2 := seg4_dot_iter hb s1 s3 sp polyPtr ((BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) + 512#64) (j := 2) (by decide)
    l2 r2 acc1 (Vec32.ofFn (polyVecNat p1)) Rest2 hpc3 hrun3 hsp3 hspA3 hcl3 hro3
    hx2_3 hx3_3 hx4_3 (hpres3.x11.trans hx11_1) (hpres3.x12.trans hx12_1)
    (hpres3.x13.trans hx13_1) (hpres3.x14.trans hx14_1) (hpres3.x15.trans hx15_1)
    (hpres3.v0.trans hv0_1) hpres3
  dsimp only at hj2; simp only [Nat.lt_irrefl, ↓reduceIte] at hj2
  refine SepWP.mono hj2 ?_
  rintro s' P' _ _ ⟨hsp', hspA', _, _, _, hv3', hpres', rfl⟩
  refine ⟨hsp', hspA', hpres'.fp.trans hfp1,
    hpres'.x0.trans ((hgpr1 0#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx0),
    hpres'.x1.trans hx1_1,
    hpres'.x8.trans (hgpr1 8#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hpres'.x9.trans hx9_1,
    hpres'.x10.trans (hgpr1 10#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hpres'.x11.trans hx11_1, hpres'.x12.trans hx12_1, hpres'.x13.trans hx13_1,
    hpres'.x14.trans hx14_1, hpres'.x15.trans hx15_1,
    hpres'.x16.trans (hgpr1 16#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hpres'.x17.trans (hgpr1 17#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hpres'.x18.trans (hgpr1 18#5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),
    hpres'.v0.trans hv0_1, hpres'.v1.trans (hv1 1#5), hpres'.v2.trans (hv1 2#5), hv3', ?_⟩
  rw [poly32Mem_ofFn,
    show sp + 2208#64 + ((BitVec.ofNat 64 (1536 * (i + 1)) + 512#64) + 512#64) = lhsBase + 1024#64 by
      dsimp only [lhsBase]; clear * -; bv_omega,
    show sp + 8416#64 + BitVec.ofNat 64 (512 * 2) = sp + 9440#64 by clear * -; bv_omega]
  dsimp only [dot, neonDot3, acc1, p0, p1, Rest2]
  exact sepProp_ext (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.FromSeed.Seg4Dot
