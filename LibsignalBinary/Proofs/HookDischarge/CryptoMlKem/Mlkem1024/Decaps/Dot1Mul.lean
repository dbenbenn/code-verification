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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1InitSym

/-!
# `kyber_decapsulate` (`B06`) — Site 1 Init & `ntt_multiply` Loop (`+0x1970 → +0x1c8c`)

Steps the zero-initialization (`+0x1970 → +0x1ad4`), per-iteration scratch clear
(`+0x1ad4 → +0x1b60`), and 16-iteration `ntt_multiply` loop (`+0x1b60 → +0x1c8c`) of Site 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul

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
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  blk06_code_eq blk06_tree_size blkLib06 blkPC06 blkPl06 blkPlaceable06 blkTree06)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.SpillMem (
  Spill21 Spill21Mem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.InvLowLoops (Inv13Preserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.DotLoops1 (AccSpill21)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env step_ldrh16_ro zetaTableAt_zext32_ne_32768)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  Poly32Mem PolyMem SepLoad128 SepStore128 Vec32 poly32Mem_ofFn polyVecNat
  step_ldpQ128 step_stpQ128 step_strQ128 vec32_ofFn_get vecRangeMem_congr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Simd (
  simdRev64_4s simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_fmov_s_w svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8 svc_simdIns_h1
  svc_simdIns_h2 svc_simdIns_h3 svc_simdMul_8h svc_simdRev64_4s svc_simdSmlal_4s
  svc_simdSmull_4s svc_simdSqdmulh_8h svc_simdSshr_8h_1 svc_simdSub_8h
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h svc_simdUzp1_4s)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3Pure (
  buildZeta4 lane16_buildZeta4 neonDot3 neonDot3_size neonPolyNttMul16_size nttMulRawPair
  nttMulRawPair_eq_polyVecNat polyAdd16_size polyVecNat_polyZero16 polyZero16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3a (AccRegs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (
  Spill40 SpillSliceMem SymEnv SymGprs SymVRegs SymVec32 evalSExpr spill40_ofFn_get)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymBridge (
  SymSpatial SymStateMatches blk06NoRelocInRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySym (
  sepWP_of_runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (exec_simdMovi_2d_0)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1InitSym (
  cfgDot1Init run_dot1_init symDot1InitEnd symDot1InitStart)

/-- 4-way NEON NTT dot product (`((l0*r0 + l1*r1) + l2*r2) + l3*r3`). -/
@[expose] def neonDot4 (l0 l1 l2 l3 r0 r1 r2 r3 : Poly16) : Poly16 :=
  polyAdd16 (neonDot3 l0 l1 l2 r0 r1 r2) (neonPolyNttMul16 l3 r3)

theorem neonDot4_size (l0 l1 l2 l3 r0 r1 r2 r3 : Poly16) :
    (neonDot4 l0 l1 l2 l3 r0 r1 r2 r3).size = 256 :=
  polyAdd16_size _ _

abbrev ro00Sym : String := "libcrux_ml_kem:.rodata..Lanon.93aaf077219c190cad3ae4a83c9f0f14.0"

section
set_option linter.literalFetch false
gen_placed_fetches blkPC06 blkLib06 blkTree06 blk06_code_eq blk06_tree_size
  via_placement blkPl06 blkPlaceable06 [0x1970 → 0x198c, 0x1ad4 → 0x1c88]
end

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

private theorem noReloc_dot1_init : blk06NoRelocInRange 1636 1717 = true := by rfl_kernel

private theorem dup8x16_zero : dup8x16 0x0000#16 = 0#128 := by decide

private theorem polyZero16_vec_eq_zero (k : Nat) (_hk : k < 32) :
    polyVecNat polyZero16 k = 0#128 := polyVecNat_polyZero16 k

attribute [local irreducible]
  blkPC06 zetaTableAt dup8x16 polyVecNat simdAdd8h simdSub8h simdMul8h simdSqdmulh8h simdSshr8h
  simdTrn1_8h simdTrn2_8h simdTrn1_4s simdTrn2_4s simdUzp1_4s simdRev64_4s simdSmull4s simdSmlal4s

attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0
  svc_simdAdd_8h svc_simdSub_8h svc_simdMul_8h svc_simdSqdmulh_8h svc_simdSshr_8h_1
  svc_simdDup_8h_gpr svc_fmov_s_w svc_simdIns_h1 svc_simdIns_h2 svc_simdIns_h3
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s
  svc_simdUzp1_4s svc_simdRev64_4s svc_simdExt_16b_8 svc_simdSmull_4s svc_simdSmlal_4s

@[simp, arm64_norm, wp_norm]
private theorem checkAddrSPAligned_offset_sp (s : State) (off : BitVec 64) :
    checkAddrSPAligned s (.Offset .sp off) = s.spAligned := rfl

private def mkDot1Env (s : State) (t0 : Spill21) (v28368 : Vec32) : SymEnv where
  vreg0   := fun r => s.readVReg128 (BitVec.ofNat 5 r)
  spill0  := Spill40.ofFn t0.get
  poly0   := v28368
  src0    := Vec32.zero
  gpr0    := fun r => s.readReg64 (.gpr r)
  pstate0 := s.pstate

private theorem matches_dot1InitStart {sp : BitVec 64} {s : State}
    (t0 : Spill21) (v28368 : Vec32)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hv0 : s.readVReg128 0#5 = 0#128) :
    SymStateMatches sp (mkDot1Env s t0 v28368) symDot1InitStart s := by
  refine ⟨hsp, hspA, rfl, fun r => ?_, fun r hr => ?_⟩
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 => exact hv0.trans dup8x16_zero.symm
    | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 => rfl
    | _ + 32 => omega
  · rcases r with ⟨rv, hrv⟩
    match rv with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
    | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 =>
      simp [symDot1InitStart, SymGprs.get, PolySymDefs.evalSymGpr, mkDot1Env]
    | 31 => exact absurd rfl hr
    | _ + 32 => omega

theorem dot1_init_ok [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp : BitVec 64) (t0 : Spill21) (v28368 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1970#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem)
    (hpres : Inv13Preserved s0 s) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1ad4#64) s
      (Spill21Mem (sp + 2096#64) t0 ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x8 = 0#64 ∧ s'.readReg64 .x9 = sp + 30448#64 ∧
        s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧ s'.readReg64 .x11 = sp + 4160#64 ∧
        s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 14432#64 ∧
        AccRegs polyZero16 s' ∧ Inv13Preserved s0 s' ∧
        P' = (Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) ∗
          Poly32Mem (sp + 28368#64) Vec32.zero ∗ Rest)) := by
  have _ : b = blkPl06.base := hb
  rcases hpres with ⟨p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, pfp⟩
  refine sepWP_seq_env hcl hro (mid := b + 0x1990#64)
    (post1 := fun s1 P1 =>
      s1.sp = sp ∧ s1.spAligned = true ∧ s1.readVReg128 0#5 = 0#128 ∧
      s1.readReg64 .x8 = 0#64 ∧ s1.readReg64 .x9 = sp + 30448#64 ∧
      s1.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
      s1.readReg64 .x11 = sp + 4096#64 ∧ s1.readReg64 .x14 = sp + 12288#64 ∧
      Inv13Preserved s0 s1 ∧
      P1 = (Spill21Mem (sp + 2096#64) t0 ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest))
    (by
      wp_steps
      exact SepWP.done (by wp_norm_lhs) (by simp [hrun])
        ⟨by simp [hsp], by simpa [State.spAligned] using hspA, by simp,
          by simp, by simp,
          by simp, by simp, by simp,
          ⟨by simp [p19], by simp [p20], by simp [p21], by simp [p22], by simp [p23], by simp [p24],
           by simp [p25], by simp [p26], by simp [p27], by simp [p28], by simp [pfp]⟩, rfl⟩) ?_
  rintro s1 P1 hpc1 hrun1 _hcl1 _hro1
    ⟨hsp1, hspA1, hv0_1, hx8_1, hx9_1, hx10_1, hx11_1, hx14_1, hpres1, rfl⟩
  rcases hpres1 with ⟨q19, q20, q21, q22, q23, q24, q25, q26, q27, q28, qfp⟩
  set env := mkDot1Env s1 t0 v28368
  have hP1 : Spill21Mem (sp + 2096#64) t0 ∗ Poly32Mem (sp + 28368#64) v28368 ∗ Rest =
      SymSpatial cfgDot1Init sp env symDot1InitStart Rest := by
    simp only [SymSpatial, cfgDot1Init, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem,
      Bool.false_eq_true, ↓reduceIte]
    have hsp21 : Spill21Mem (sp + 2096#64) t0 =
        SpillSliceMem 21 (sp + 2096#64) (symDot1InitStart.spill.eval env) :=
      vecRangeMem_congr fun i hi => by
        interval_cases i <;> rfl
    have hp32 : v28368 = symDot1InitStart.poly.eval env := by
      cases v28368; rfl
    rw [hsp21, ← hp32]
    exact sepProp_ext (by sep_frame) (by sep_frame)
  rw [hP1]
  refine SepWP.mono
    (sepWP_of_runSymRange (cfg := cfgDot1Init) (env := env) (F := Rest)
      81 1636 noReloc_dot1_init (by decide) (by decide) (by decide)
      run_dot1_init (matches_dot1InitStart t0 v28368 hsp1 hspA1 hv0_1) hpc1 hrun1
      (post := fun s' P' => SymStateMatches sp env symDot1InitEnd s' ∧
        P' = SymSpatial cfgDot1Init sp env symDot1InitEnd Rest)
      (fun _ _ _ hm => ⟨hm, rfl⟩)) ?_
  rintro s' P' _ _ ⟨hm', rfl⟩
  have hz128 : ∀ k, k < 32 → dup8x16 0x0000#16 = polyVecNat polyZero16 k :=
    fun k hk => dup8x16_zero.trans (polyZero16_vec_eq_zero k hk).symm
  have hacc' : AccRegs polyZero16 s' :=
    ⟨(hm'.hvregs 0#5).trans dup8x16_zero,
     (hm'.hvregs 1#5).trans (hz128 31 (by decide)),
     (hm'.hvregs 8#5).trans (hz128 23 (by decide)),
     (hm'.hvregs 9#5).trans (hz128 24 (by decide)),
     (hm'.hvregs 10#5).trans (hz128 25 (by decide)),
     (hm'.hvregs 11#5).trans (hz128 26 (by decide)),
     (hm'.hvregs 12#5).trans (hz128 27 (by decide)),
     (hm'.hvregs 13#5).trans (hz128 28 (by decide)),
     (hm'.hvregs 14#5).trans (hz128 29 (by decide)),
     (hm'.hvregs 15#5).trans (hz128 30 (by decide)),
     (hm'.hvregs 22#5).trans (hz128 13 (by decide)),
     (hm'.hvregs 23#5).trans (hz128 14 (by decide)),
     (hm'.hvregs 24#5).trans (hz128 15 (by decide)),
     (hm'.hvregs 25#5).trans (hz128 16 (by decide)),
     (hm'.hvregs 26#5).trans (hz128 17 (by decide)),
     (hm'.hvregs 27#5).trans (hz128 18 (by decide)),
     (hm'.hvregs 28#5).trans (hz128 19 (by decide)),
     (hm'.hvregs 29#5).trans (hz128 20 (by decide)),
     (hm'.hvregs 30#5).trans (hz128 21 (by decide)),
     (hm'.hvregs 31#5).trans (hz128 22 (by decide))⟩
  have hpres' : Inv13Preserved s0 s' :=
    ⟨(hm'.hgprs 19#5 (by decide)).trans ((BitVec.add_zero _).trans q19),
     (hm'.hgprs 20#5 (by decide)).trans ((BitVec.add_zero _).trans q20),
     (hm'.hgprs 21#5 (by decide)).trans ((BitVec.add_zero _).trans q21),
     (hm'.hgprs 22#5 (by decide)).trans ((BitVec.add_zero _).trans q22),
     (hm'.hgprs 23#5 (by decide)).trans ((BitVec.add_zero _).trans q23),
     (hm'.hgprs 24#5 (by decide)).trans ((BitVec.add_zero _).trans q24),
     (hm'.hgprs 25#5 (by decide)).trans ((BitVec.add_zero _).trans q25),
     (hm'.hgprs 26#5 (by decide)).trans ((BitVec.add_zero _).trans q26),
     (hm'.hgprs 27#5 (by decide)).trans ((BitVec.add_zero _).trans q27),
     (hm'.hgprs 28#5 (by decide)).trans ((BitVec.add_zero _).trans q28),
     (hm'.hgprs 29#5 (by decide)).trans ((BitVec.add_zero _).trans qfp)⟩
  refine ⟨hm'.hsp, hm'.hsp_al,
    (hm'.hgprs 8#5 (by decide)).trans ((BitVec.add_zero _).trans hx8_1),
    (hm'.hgprs 9#5 (by decide)).trans ((BitVec.add_zero _).trans hx9_1),
    (hm'.hgprs 10#5 (by decide)).trans ((BitVec.add_zero _).trans hx10_1),
    (hm'.hgprs 11#5 (by decide)).trans (by change s1.readReg64 .x11 + 64#64 = _; rw [hx11_1]; clear * -; bv_omega),
    hm'.hgprs 12#5 (by decide),
    hm'.hgprs 13#5 (by decide),
    (hm'.hgprs 14#5 (by decide)).trans (by change s1.readReg64 .x14 + 2144#64 = _; rw [hx14_1]; clear * -; bv_omega),
    hacc', hpres', ?_⟩
  simp only [SymSpatial, cfgDot1Init, PolySymBridge.polyPtr, PolySymBridge.SrcOptMem,
    Bool.false_eq_true, ↓reduceIte]
  have hsp_end : SpillSliceMem 21 (sp + 2096#64) (symDot1InitEnd.spill.eval env) =
      Spill21Mem (sp + 2096#64) (AccSpill21 t0 polyZero16) :=
    vecRangeMem_congr fun i hi => by
      interval_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      all_goals exact hz128 _ (by decide)
  have hp_end : symDot1InitEnd.poly.eval env = Vec32.zero := by
    simp only [SymVec32.eval, SymVec32.get, symDot1InitEnd, evalSExpr, Vec32.zero, Vec32.ofFn,
      dup8x16_zero]
  rw [hsp_end, hp_end]
  exact sepProp_ext (by sep_frame) (by sep_frame)


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

/-! ## Scratch Clear (`+0x1ad4 → +0x1b60`) & `ntt_multiply` Loop (`+0x1b60 → +0x1c8c`) -/

theorem dot1_clear_scratch [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp lhsPtr rhsPtr : BitVec 64) {j : Nat} (_hj : j < 4)
    (acc : Poly16) (v14432 : Vec32) (Rest : SepProp)
    (hpc : s.pc = b + 0x1ad4#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 j) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1b60#64) s
      (Poly32Mem (sp + 14432#64) v14432 ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = BitVec.ofNat 64 (j + 1) ∧
        s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 14432#64 ∧ s'.readReg64 .x15 = 0#64 ∧
        s'.readReg64 .x16 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
        P' = (Poly32Mem (sp + 14432#64) Vec32.zero ∗ Rest)) := by
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

private theorem dot1_ntt_mul_iter [MlKemPlacement] {b : BitVec 64} (_hb : MlKemBase blkPl06 b)
    (s0 s : State) (sp lhsPtr rhsPtr x8v : BitVec 64) (lhs rhs acc : Poly16)
    {r : Nat} (hr : r < 16) (f : Nat → BitVec 128) (Rest : SepProp)
    (hpc : s.pc = b + 0x1b60#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hro : MlKemRoOk mlkemMpl s.mem)
    (hx8 : s.readReg64 .x8 = x8v) (hx9 : s.readReg64 .x9 = lhsPtr)
    (hx10 : s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64) (hx11 : s.readReg64 .x11 = rhsPtr)
    (hx12 : s.readReg64 .x12 = 62209#64) (hx13 : s.readReg64 .x13 = 3329#64)
    (hx14 : s.readReg64 .x14 = sp + 14432#64)
    (hx15 : s.readReg64 .x15 = BitVec.ofNat 64 (32 * r))
    (hx16 : s.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r))
    (hacc : AccRegs acc s) (hpres : Inv13Preserved s0 s) :
    let prod := neonPolyNttMul16 lhs rhs
    SepWP (blkPC06.rebase b (fun _ => none))
      (if r < 15 then b + 0x1b60#64 else b + 0x1c8c#64) s
      (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
        PolyMem (sp + 14432#64) f ∗ Rest)
      (fun s' P' =>
        s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
        s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
        s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
        s'.readReg64 .x14 = sp + 14432#64 ∧
        s'.readReg64 .x15 = BitVec.ofNat 64 (32 * (r + 1)) ∧
        s'.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * (r + 1)) ∧
        AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
        P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
          PolyMem (sp + 14432#64)
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
  refine step_stpQ128 (wb := none) (ea := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r)))
    (ea16 := (sp + 14432#64) + BitVec.ofNat 64 (16 * (2 * r + 1)))
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

theorem dot1_ntt_mul_loop [MlKemPlacement] {b : BitVec 64} (hb : MlKemBase blkPl06 b)
    (s0 : State) (sp lhsPtr rhsPtr x8v : BitVec 64) (lhs rhs acc : Poly16) (Rest : SepProp) :
    ∀ rem r, rem + r = 15 → ∀ (s : State) (f : Nat → BitVec 128),
      s.pc = b + 0x1b60#64 → s.status = .Running → s.sp = sp → s.spAligned = true →
      mlkemMultiLib.CodeLoaded mlkemMpl s.mem → MlKemRoOk mlkemMpl s.mem →
      s.readReg64 .x8 = x8v → s.readReg64 .x9 = lhsPtr →
      s.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 → s.readReg64 .x11 = rhsPtr →
      s.readReg64 .x12 = 62209#64 → s.readReg64 .x13 = 3329#64 →
      s.readReg64 .x14 = sp + 14432#64 →
      s.readReg64 .x15 = BitVec.ofNat 64 (32 * r) →
      s.readReg64 .x16 = mlkemMpl.ρ ro00Sym + BitVec.ofNat 64 (134 + 8 * r) →
      AccRegs acc s → Inv13Preserved s0 s →
      (∀ k, k < 2 * r → f k = polyVecNat (neonPolyNttMul16 lhs rhs) k) →
      SepWP (blkPC06.rebase b (fun _ => none)) (b + 0x1c8c#64) s
        (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗ PolyMem (sp + 14432#64) f ∗ Rest)
        (fun s' P' =>
          s'.sp = sp ∧ s'.spAligned = true ∧ s'.readReg64 .x8 = x8v ∧
          s'.readReg64 .x9 = lhsPtr ∧ s'.readReg64 .x10 = mlkemMpl.ρ ro00Sym + 134#64 ∧
          s'.readReg64 .x11 = rhsPtr ∧ s'.readReg64 .x12 = 62209#64 ∧ s'.readReg64 .x13 = 3329#64 ∧
          s'.readReg64 .x14 = sp + 14432#64 ∧ AccRegs acc s' ∧ Inv13Preserved s0 s' ∧
          P' = (PolyMem lhsPtr (polyVecNat lhs) ∗ PolyMem rhsPtr (polyVecNat rhs) ∗
            Poly32Mem (sp + 14432#64) (Vec32.ofFn (polyVecNat (neonPolyNttMul16 lhs rhs))) ∗ Rest)) := by
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

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1Mul
