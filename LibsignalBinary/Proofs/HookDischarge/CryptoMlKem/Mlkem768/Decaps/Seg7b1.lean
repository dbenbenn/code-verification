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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a

/-!
# `decapsulate_compressed_key` (`B04`) — Segment 7b, Part 1 (`+0xa968 .. +0xabd8`)

Helper lemmas for the 3-polynomial `compress_and_serialize_10` outer/inner loops in Segment 7b:
20-byte cell decomposition, scalar SIMD store helpers, header (`+0xa968 → +0xa9c4`), outer-loop
stage preparation (`+0xa9c4 → +0xaa84`), and inner-loop `compress_10` steps (completed in `Seg7b`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b1

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement mlkemMpl seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Poly Poly16 indCpaEncryptWith sampleNtt sha3_512List shake256List zeroPoly)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 lane32 lane64 lane8 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdExt16b simdSli2d simdSli4s simdSqdmulh4s
  simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  neonSerialize10Bytes neonSerialize10Mix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem VecRangeMem
  polyVecNat step_ldpQ128 step_ldrQ128 step_strQ128 vecRangeBytes vecRangeBytes_length
  vecRangeMem_entails_memRegion vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_simdAdd_4s exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDup_4s
  exec_simdSqdmulh_4s exec_simdUshr_4s_4 sqdmulh4sFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (sha3_512List_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd (
  cells20_eq_neonSerialize10Bytes exec_simdBic_4s_fc24 exec_simdBic_8h_fc8
  exec_simdDupScalar_b12 exec_simdDupScalar_b4 exec_simdMovi_2d_0 exec_simdShl_4s_10
  exec_simdSli_2d_20 exec_simdSli_4s_10 exec_simdUshr_4s_6 neonCompressSerialize10Poly
  neonCompressSerialize10Poly_eq neonCompressSerialize10Poly_length
  seg6_compress10_eq seg6_serialize10_mix_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk04_code_eq blk04_tree_size blkLib04 blkPC04 blkPl04 blkPlaceable04 blkTree04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg1a (blk28_memcpy_04)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6b (rHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7a (
  offSeg7SerStart polyMem3_eq_pointsToBytes uVecPoly16 uVecPoly16_spec)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xa968 → 0xab0c]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Outer    : BitVec 64 := BitVec.ofNat 64 43460
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Zero     : BitVec 64 := BitVec.ofNat 64 43544
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Inner    : BitVec 64 := BitVec.ofNat 64 43652
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Store    : BitVec 64 := BitVec.ofNat 64 43840
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Bounce   : BitVec 64 := BitVec.ofNat 64 43908
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7RhatCopy : BitVec 64 := BitVec.ofNat 64 43960
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Mix      : BitVec 64 := BitVec.ofNat 64 43792
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg7Mul      : BitVec 64 := BitVec.ofNat 64 43744
end Simp
export Simp (offSeg7Outer offSeg7Zero offSeg7Inner offSeg7Store
  offSeg7Bounce offSeg7RhatCopy offSeg7Mix offSeg7Mul)
open scoped Simp

@[simp, arm64_norm, wp_norm]
private theorem blkPl04_ρ [MlKemPlacement] (sym : String) :
    blkPl04.ρ sym = mlkemMultiLib.resolve mlkemMpl sym := rfl

attribute [local irreducible] blkPC04
attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdBic_4s_fc24 exec_simdBic_8h_fc8
  exec_simdShl_4s_10 exec_simdUshr_4s_6 exec_simdSli_4s_10 exec_simdSli_2d_20
  exec_simdDupScalar_b4 exec_simdDupScalar_b12
  exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdAdd_4s exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s

/-! ## 1. 20-Byte Cell Decomposition & Scalar SIMD Store Helpers -/

theorem sepWP_elim_cell4 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 32, SepWP prog target s ((a ↦₃₂ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 4 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

theorem sepWP_elim_cell1 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 8, SepWP prog target s ((a ↦₈ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 1 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

theorem sepWP_elim_region5 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w : BitVec 32) (u : BitVec 8),
      SepWP prog target s ((a ↦₃₂ w) ∗ ((a + 4#64) ↦₈ u) ∗ R0) post) :
    SepWP prog target s (memRegion a 5 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 4#64) (n := 4) (k := (1 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_cell4; intro w
  refine SepWP.weaken_pre (show (a ↦₃₂ w) ∗ (memRegion (a + 4#64) 1 ∗ R0) ⊢
      memRegion (a + 4#64) 1 ∗ ((a ↦₃₂ w) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_cell1; intro u
  exact SepWP.weaken_pre (by sep_frame) (h w u)

theorem sepWP_elim_region10 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 8) (w2 : BitVec 32) (u3 : BitVec 8),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗ ((a + 9#64) ↦₈ u3) ∗ R0) post) :
    SepWP prog target s (memRegion a 10 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 5#64) (n := 5) (k := (5 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_region5; intro w0 u1
  refine SepWP.weaken_pre (show (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ (memRegion (a + 5#64) 5 ∗ R0) ⊢
      memRegion (a + 5#64) 5 ∗ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_region5; intro w2 u3
  refine SepWP.weaken_pre ?_ (h w0 u1 w2 u3)
  rw [show a + 5#64 + 4#64 = a + 9#64 by bv_omega]; sep_frame

theorem sepWP_elim_region20 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 8) (w2 : BitVec 32) (u3 : BitVec 8)
        (w4 : BitVec 32) (u5 : BitVec 8) (w6 : BitVec 32) (u7 : BitVec 8),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗ ((a + 9#64) ↦₈ u3) ∗
         ((a + 10#64) ↦₃₂ w4) ∗ ((a + 14#64) ↦₈ u5) ∗ ((a + 15#64) ↦₃₂ w6) ∗
         ((a + 19#64) ↦₈ u7) ∗ R0) post) :
    SepWP prog target s (memRegion a 20 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 10#64) (n := 10) (k := (10 : Nat)) rfl (by bv_omega) (by decide), sepConj_assoc]
  apply sepWP_elim_region10; intro w0 u1 w2 u3
  refine SepWP.weaken_pre (show (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗
        ((a + 9#64) ↦₈ u3) ∗ (memRegion (a + 10#64) 10 ∗ R0) ⊢
      memRegion (a + 10#64) 10 ∗ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗
        ((a + 9#64) ↦₈ u3) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_region10; intro w4 u5 w6 u7
  refine SepWP.weaken_pre ?_ (h w0 u1 w2 u3 w4 u5 w6 u7)
  rw [show a + 10#64 + 4#64 = a + 14#64 by bv_omega,
      show a + 10#64 + 5#64 = a + 15#64 by bv_omega,
      show a + 10#64 + 9#64 = a + 19#64 by bv_omega]; sep_frame

namespace Simp
@[scoped simp, arm64_norm, wp_norm] theorem sp_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).sp = s.sp := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) :
    (s.writeVReg128 v w).pstate = s.pstate := rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_writeVReg128' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) :
    (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem pc_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pc = s.pc := rfl
@[scoped simp, arm64_norm, wp_norm] theorem sp_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := rfl
@[scoped simp, arm64_norm, wp_norm] theorem status_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := rfl
@[scoped simp, arm64_norm, wp_norm] theorem mem_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) :
    (s.orFpsr f).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) :
    (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[scoped simp, arm64_norm, wp_norm] theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) :
    (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_setMem' (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_setPState' (s : State) (p : PState) : (s.setPState p).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem spA_writeGPR' (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).spAligned = s.spAligned := rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).pstate = s.pstate := rfl
@[scoped simp, arm64_norm, wp_norm] theorem pstate_writeGPR' (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).pstate = s.pstate := rfl
@[scoped simp] theorem setWidth8_zext128 (x : BitVec 8) :
    (x.zeroExtend 128).setWidth 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
@[scoped simp] theorem low32_eq_lane64_0 (v : BitVec 128) :
    v.extractLsb' 0 32 = (lane64 v 0).truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [lane64, hi]
end Simp
export Simp (sp_writeVReg128' spA_writeVReg128' pstate_writeVReg128' readReg64_writeVReg128'
  pc_orFpsr' sp_orFpsr' spA_orFpsr' pstate_orFpsr' status_orFpsr' mem_orFpsr'
  readReg64_orFpsr' readVReg128_orFpsr' readReg64_setPC' readReg64_setMem'
  readVReg128_setMem' spA_setPC' spA_setMem' spA_setPState' spA_writeGPR'
  pstate_setPC' pstate_writeGPR' setWidth8_zext128 low32_eq_lane64_0)
open scoped Simp

theorem step_strS32_off {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff off : Nat) (vt : BitVec 5) (ptrReg : Reg) (v : BitVec 32)
    (hptr : ptrReg ≠ .sp) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .S32 vt (.Offset ptrReg (BitVec.ofNat 64 off))))
    (hea : s.readReg64 ptrReg = ea) (hv : (s.readVReg128 vt).extractLsb' 0 32 = v)
    (hstore : SepStore32 (ea + BitVec.ofNat 64 off) v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact SepWP.step_strSimd32 (wb := none) hpc hrun hfetch
    (by cases ptrReg <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned])
    (by simp [evalAddrMode, hea]) hv hstore (by simp [applyWriteback, hpc']) hnext

theorem step_strB8_off {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop}
    (b ea : BitVec 64) (pcOff nextOff off : Nat) (vt : BitVec 5) (ptrReg : Reg) (v : BitVec 8)
    (hptr : ptrReg ≠ .sp) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .B8 vt (.Offset ptrReg (BitVec.ofNat 64 off))))
    (hea : s.readReg64 ptrReg = ea) (hv : (s.readVReg128 vt).truncate 8 = v)
    (hstore : SepStore8 (ea + BitVec.ofNat 64 off) v P P') (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m') P' post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strSimd8 (wb := none) hpc hrun hfetch
    (by cases ptrReg <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned])
    (by simp [evalAddrMode, hea]) hv hstore (by simp [applyWriteback, hpc']) hnext

/-! ## 2. Prefix Chunk Helpers & Header (`+0xa968 → +0xa9c4`) -/

@[expose] def ser10Chunk (u : Poly16) (c : Nat) : List (BitVec 8) :=
  neonSerialize10Bytes (neonCompress8h 10 (polyVecNat u (2 * c)))
    (neonCompress8h 10 (polyVecNat u (2 * c + 1)))

@[expose] def ser10Prefix (u : Poly16) (c : Nat) : List (BitVec 8) :=
  ((List.range c).map (ser10Chunk u)).flatten

theorem ser10Chunk_length (u : Poly16) (c : Nat) : (ser10Chunk u c).length = 20 := by
  simp [ser10Chunk, neonSerialize10Bytes, Poly.Serialize.EncodeHigh.neonSerialize10Half]

theorem ser10Prefix_zero (u : Poly16) : ser10Prefix u 0 = [] := rfl

theorem ser10Prefix_succ (u : Poly16) (c : Nat) :
    ser10Prefix u (c + 1) = ser10Prefix u c ++ ser10Chunk u c := by
  simp [ser10Prefix, List.range_succ, List.flatten_append]

theorem ser10Prefix_length (u : Poly16) (c : Nat) : (ser10Prefix u c).length = 20 * c := by
  induction c with
  | zero => rfl
  | succ n ih =>
    rw [ser10Prefix_succ, List.length_append, ih, ser10Chunk_length]; omega

theorem ser10Prefix_sixteen (u : Poly16) :
    ser10Prefix u 16 = neonCompressSerialize10Poly u := rfl

@[expose] def c10321340Vec : BitVec 128 := pack4x32 fun _ => 10321340#32
@[expose] def c1664Vec     : BitVec 128 := pack4x32 fun _ => 1664#32
@[expose] def c67107840Vec : BitVec 128 := pack4x32 fun _ => 67107840#32
@[expose] def c3329Vec     : BitVec 128 := dup8x16 3329#16

@[expose] def serConstFn : Nat → BitVec 128
  | 0 => c10321340Vec
  | 1 => c1664Vec
  | 2 => c67107840Vec
  | _ => c3329Vec

theorem sepWP_elim_cell8 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 64, SepWP prog target s ((a ↦₆₄ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 8 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_eight, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

theorem step_strQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5) (val : BitVec 128)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.strSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off)
    (hval : s.readVReg128 vt = val) (hnextOff : pcOff + 4 = nextOff)
    (hnext : ∀ m' : Memory, SepWP prog target_pc
      ((s.setPC (b + BitVec.ofNat 64 nextOff)).setMem m')
      (VecRangeMem n base (Function.update f k val) ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_strQ128 (wb := none) hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp]) hval
    (SepStore128.left (SepStore128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

theorem step_ldrQ128_sp_vecRange {prog : Program} {target_pc : BitVec 64}
    {s : State} {Rest : SepProp} {post : State → SepProp → Prop}
    (b sp base : BitVec 64) (pcOff nextOff off n k : Nat) (vt : BitVec 5)
    (f : Nat → BitVec 128)
    (hk : k < n) (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.ldrSimd .Q128 vt (.Offset .sp (BitVec.ofNat 64 off))))
    (hea : base + BitVec.ofNat 64 (16 * k) = sp + BitVec.ofNat 64 off) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 vt (f k)).setPC (b + BitVec.ofNat 64 nextOff))
      (VecRangeMem n base f ∗ Rest) post) :
    SepWP prog target_pc s (VecRangeMem n base f ∗ Rest) post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  exact step_ldrQ128 (wb := none) hpc hrun hfetch
    (by simpa [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned] using hspA)
    (by simp [evalAddrMode, hsp])
    (SepLoad128.left (SepLoad128.vecRange hk hea))
    (by simp [applyWriteback, hpc']) hnext

theorem cell_entails_memRegion8 (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 :=
  Encaps2.Base.cell_entails_memRegion8 a v

theorem seg7b_header [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7SerStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) (hx20 : s.readReg64 .x20 = sp + 11872#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Outer) s
      (memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 11864#64) 8 ∗
        memRegion (sp + 13408#64) 8 ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = true ∧
        s1.readReg64 .fp = fpVal ∧
        s1.readReg64 .x19 = sp + 22400#64 ∧
        s1.readReg64 .x20 = sp + 11872#64 ∧
        s1.readReg64 .x22 = 0#64 ∧
        s1.readReg64 .x23 = sp + 24448#64 ∧
        s1.readReg64 .x24 = sp + 25296#64 ∧
        s1.readReg64 .x25 = sp + 18032#64 ∧
        (P1 ⊢ VecRangeMem 4 (sp + 2192#64) serConstFn ∗
          memRegion (sp + 11864#64) 8 ∗ memRegion (sp + 13408#64) 8 ∗ Rest)) := by
  subst hbase
  apply SepWP.of_memRegion_vecRangeMem 4 (sp + 2192#64) (by decide) (by sep_focus); intro fc
  refine SepWP.weaken_pre
    (show VecRangeMem 4 (sp + 2192#64) fc ∗ (memRegion (sp + 11864#64) 8 ∗ memRegion (sp + 13408#64) 8 ∗ Rest) ⊢
      memRegion (sp + 11864#64) 8 ∗ (memRegion (sp + 13408#64) 8 ∗ (VecRangeMem 4 (sp + 2192#64) fc ∗ Rest)) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w1
  refine SepWP.weaken_pre (show ((sp + 11864#64) ↦₆₄ w1) ∗ (memRegion (sp + 13408#64) 8 ∗
      (VecRangeMem 4 (sp + 2192#64) fc ∗ Rest)) ⊢
      memRegion (sp + 13408#64) 8 ∗ (((sp + 11864#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2192#64) fc ∗ Rest) by
      sep_frame) ?_
  apply sepWP_elim_cell8; intro w2
  refine SepWP.weaken_pre
    (show ((sp + 13408#64) ↦₆₄ w2) ∗ (((sp + 11864#64) ↦₆₄ w1) ∗ VecRangeMem 4 (sp + 2192#64) fc ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2192#64) fc ∗ (((sp + 11864#64) ↦₆₄ w1) ∗ ((sp + 13408#64) ↦₆₄ w2) ∗ Rest) by
      sep_frame) ?_
  wp_steps 12
  refine step_strQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43416 43420 2240 4 3 0#5 c3329Vec fc
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c3329Vec]) rfl ?_; intro m1
  wp_steps 5
  refine step_strQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43440 43444 2224 4 2 0#5 c67107840Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c67107840Vec]) rfl ?_; intro m2
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43448 43452 2208 4 1 0#5 c1664Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c1664Vec]) rfl ?_; intro m3
  wp_steps 1
  refine step_strQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43456 43460 2192 4 0 0#5 c10321340Vec _
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) (by simp [c10321340Vec]) rfl ?_; intro m4
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp], by simp [hx19], by simp [hx20],
      by simp, by simp, by simp, by simp, ?_⟩
  have hvc : VecRangeMem 4 (sp + 2192#64)
      (Function.update (Function.update (Function.update (Function.update fc 3 c3329Vec) 2 c67107840Vec) 1 c1664Vec) 0 c10321340Vec) =
      VecRangeMem 4 (sp + 2192#64) serConstFn := by
    apply Encaps2.VecMem.vecRangeMem_congr; intro i hi
    rcases i with _ | _ | _ | _ | n <;> try omega
    all_goals simp [serConstFn, Function.update]
  rw [hvc]
  exact entails_sub (cell_entails_memRegion8 (sp + 11864#64) 3#64) (by sep_frame)
    (entails_sub (cell_entails_memRegion8 (sp + 13408#64) 0#64) (by sep_frame) (by sep_frame))

/-! ## 3. Outer-Loop Stage Preparation (`+0xa9c4 → +0xaa84`) -/

theorem seg7b_prep_poly [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) (hx20 : s.readReg64 .x20 = sp + 11872#64)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 idx)
    (hx23 : s.readReg64 .x23 = sp + 24448#64) (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hx25 : s.readReg64 .x25 = sp + 18032#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (11872 + 512 * idx)
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Zero) s
      (PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 24448#64) 520 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧ sf.readReg64 .x20 = sp + 11872#64 ∧
        sf.readReg64 .x21 = BitVec.ofNat 64 (320 * idx) ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x23 = sp + 24448#64 ∧ sf.readReg64 .x24 = sp + 25296#64 ∧
        sf.readReg64 .x25 = sp + 18032#64 ∧
        (Pf ⊢ PolyMem uPtr (polyVecNat u) ∗
          PolyMem (sp + 22400#64) (polyVecNat u) ∗
          memRegion (sp + 22912#64) 8 ∗ memRegion (sp + 24448#64) 520 ∗ Rest)) := by
  subst hbase
  intro uPtr
  set bsU := vecRangeBytes 32 (polyVecNat u)
  have hbsU : bsU.length = 512 := vecRangeBytes_length 32 (polyVecNat u)
  have hm520a : memRegion (sp + 22400#64) 520 = memRegion (sp + 22400#64) 8 ∗ memRegion (sp + 22408#64) 512 :=
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22408#64) (n := 8) (k := (512 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm520b : memRegion (sp + 22400#64) 520 = memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 8 :=
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22912#64) (n := 512) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  rw [hm520a]
  refine SepWP.weaken_pre (show PolyMem uPtr (polyVecNat u) ∗ ((memRegion (sp + 22400#64) 8 ∗ memRegion (sp + 22408#64) 512) ∗
      memRegion (sp + 24448#64) 520 ∗ Rest) ⊢
      memRegion (sp + 22400#64) 8 ∗ ((uPtr ↦ₛ bsU) ∗ memRegion (sp + 22408#64) 512 ∗ memRegion (sp + 24448#64) 520 ∗ Rest) by
      dsimp only [PolyMem]; rw [← vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u)]; sep_frame) ?_
  apply sepWP_elim_cell8; intro w0
  have huPtr : (sp + 11872#64) + (BitVec.ofNat 64 idx <<< 9) = uPtr := by
    dsimp only [uPtr]; rcases idx with _ | _ | _ | n <;> try omega
    all_goals (clear * -; bv_omega)
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 22408#64, uPtr, bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have h19_1 : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := ‹_›
  have h20_1 : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := ‹_›
  have h22_1 : sf.readReg64 (.gpr 22#5) = BitVec.ofNat 64 idx + 1#64 := ‹_›
  have h23_1 : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := ‹_›
  have h24_1 : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := ‹_›
  have h25_1 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := ‹_›
  have h26_1 : sf.readReg64 (.gpr 26#5) = BitVec.ofNat 64 idx := ‹_›
  have hjoin1 : ((sp + 22400#64) ↦₆₄ w0) ∗ ((sp + 22408#64) ↦ₛ bsU) =
      ((sp + 22400#64) ↦ₛ (unpack64 w0 ++ bsU)) := by
    have ha8 : (sp + 22400#64) + 8#64 = sp + 22408#64 := by clear * -; bv_omega
    rw [pointsTo64_eq_pointsToBytes, pointsToBytes_append, unpack64_length, ha8]
  have h520len : (unpack64 w0 ++ bsU).length = 520 := by
    simp [List.length_append, unpack64_length, hbsU]
  refine SepWP.weaken_pre
    (P' := ((sp + 22400#64) ↦ₛ (unpack64 w0 ++ bsU)) ∗ memRegion (sp + 24448#64) 520 ∗
      ((uPtr ↦ₛ bsU) ∗ Rest))
    (by dsimp only [bsU, uPtr] at hjoin1 ⊢; rw [← hjoin1]; sep_frame) ?_
  have hsp1 : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl1)
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 24448#64, sp + 22400#64, unpack64 w0 ++ bsU)
  apply SepWP.done (by assumption) (by assumption); intro hcl2
  have hsp2 : sf_1.sp = sp := hsp_sf_1.trans hsp1
  have hspA2 : sf_1.spAligned = true := spAligned_of_sp_eq hspA1 hsp1 hsp2
  have h19_2 : sf_1.readReg64 (.gpr 19#5) = sf.readReg64 (.gpr 19#5) := ‹_›
  have h20_2 : sf_1.readReg64 (.gpr 20#5) = sf.readReg64 (.gpr 20#5) := ‹_›
  have h22_2 : sf_1.readReg64 (.gpr 22#5) = sf.readReg64 (.gpr 22#5) := ‹_›
  have h23_2 : sf_1.readReg64 (.gpr 23#5) = sf.readReg64 (.gpr 23#5) := ‹_›
  have h24_2 : sf_1.readReg64 (.gpr 24#5) = sf.readReg64 (.gpr 24#5) := ‹_›
  have h25_2 : sf_1.readReg64 (.gpr 25#5) = sf.readReg64 (.gpr 25#5) := ‹_›
  have h26_2 : sf_1.readReg64 (.gpr 26#5) = sf.readReg64 (.gpr 26#5) := ‹_›
  have hsplit24448 : ((sp + 24448#64) ↦ₛ (unpack64 w0 ++ bsU)) =
      ((sp + 24448#64) ↦ₛ unpack64 w0) ∗ ((sp + 24456#64) ↦ₛ bsU) := by
    rw [pointsToBytes_append, unpack64_length, show (sp + 24448#64) + 8#64 = sp + 24456#64 by clear * -; bv_omega]
  have hm22400 : ((sp + 22400#64) ↦ₛ (unpack64 w0 ++ bsU)) ⊢
      memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 8 := by
    rw [← hm520b, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 22400#64) (unpack64 w0 ++ bsU)
  refine SepWP.weaken_pre
    (P' := ((sp + 24456#64) ↦ₛ bsU) ∗ memRegion (sp + 22400#64) 512 ∗
      (((sp + 24448#64) ↦ₛ unpack64 w0) ∗ memRegion (sp + 22912#64) 8 ∗ (uPtr ↦ₛ bsU) ∗ Rest))
    (by rw [hsplit24448]; exact entails_sub hm22400 (by sep_frame) (by sep_frame)) ?_
  wp_steps 4; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl2)
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 22400#64, sp + 24456#64, bsU)
  apply SepWP.done (by assumption) (by assumption); intro _
  have hsp3 : sf_2.sp = sp := hsp_sf_2.trans hsp2
  have hspA3 : sf_2.spAligned = true := spAligned_of_sp_eq hspA2 hsp2 hsp3
  have h19_3 : sf_2.readReg64 (.gpr 19#5) = sf_1.readReg64 (.gpr 19#5) := ‹_›
  have h20_3 : sf_2.readReg64 (.gpr 20#5) = sf_1.readReg64 (.gpr 20#5) := ‹_›
  have h22_3 : sf_2.readReg64 (.gpr 22#5) = sf_1.readReg64 (.gpr 22#5) := ‹_›
  have h23_3 : sf_2.readReg64 (.gpr 23#5) = sf_1.readReg64 (.gpr 23#5) := ‹_›
  have h24_3 : sf_2.readReg64 (.gpr 24#5) = sf_1.readReg64 (.gpr 24#5) := ‹_›
  have h25_3 : sf_2.readReg64 (.gpr 25#5) = sf_1.readReg64 (.gpr 25#5) := ‹_›
  have h26_3 : sf_2.readReg64 (.gpr 26#5) = sf_1.readReg64 (.gpr 26#5) := ‹_›
  wp_steps 3
  refine step_bCond_not_taken (c := .EQ) (dst := blkPl04.base + offSeg7Zero)
    (by wp_norm_lhs) (by simp [hrun_sf_2]) (by simp only [arm64_norm]; rfl)
    (by simp only [wp_norm, arm64_norm]; clear * - hidx; rcases idx with _ | _ | _ | n <;> first | decide | omega)
    (by dsimp only [offSeg7Zero]; clear * -; bv_omega) ?_
  refine SepWP.done rfl (by simp [hrun_sf_2])
    ⟨by simp [hsp3], spAligned_of_sp_eq hspA3 hsp3 (by simp [hsp3]),
      by simp [Reg.fp] at hfp ⊢; rw [hcs_sf_2, hcs_sf_1, hcs_sf, hfp],
      by simp [Reg.x19] at hx19 ⊢; rw [h19_3, h19_2, h19_1, hx19],
      by simp [Reg.x20] at hx20 ⊢; rw [h20_3, h20_2, h20_1, hx20],
      by simp only [wp_norm, arm64_norm]
         clear * - hidx; rcases idx with _ | _ | _ | n <;> first | decide | omega,
      by simp [Reg.x22]; rw [h22_3, h22_2, h22_1]
         clear * - hidx; rcases idx with _ | _ | _ | n <;> first | decide | omega,
      by simp [Reg.x23] at hx23 ⊢; rw [h23_3, h23_2, h23_1, hx23],
      by simp [Reg.x24] at hx24 ⊢; rw [h24_3, h24_2, h24_1, hx24],
      by simp [Reg.x25] at hx25 ⊢; rw [h25_3, h25_2, h25_1, hx25], ?_⟩
  have hm24448 : ((sp + 24448#64) ↦ₛ unpack64 w0) ∗ ((sp + 24456#64) ↦ₛ bsU) ⊢
      memRegion (sp + 24448#64) 520 := by
    rw [← hsplit24448, ← h520len]; exact pointsToBytes_entails_memRegion (sp + 24448#64) (unpack64 w0 ++ bsU)
  dsimp only [PolyMem]
  rw [← vecRangeMem_eq_pointsToBytes 32 uPtr (polyVecNat u),
      ← vecRangeMem_eq_pointsToBytes 32 (sp + 22400#64) (polyVecNat u)]
  exact entails_sub hm24448 (by sep_frame) (by sep_frame)

local macro "step_zero_q " sp:term:arg hrun:term:arg hsp:term:arg hspA:term:arg
    pcOff:num nextOff:num spOff:num k:num : tactic => `(tactic|
  (refine step_strQ128_sp_vecRange blkPl04.base $sp ($sp + 25296#64) $pcOff $nextOff $spOff 20 $k 0#5 0#128 _
      (by decide) (by wp_norm_lhs) (by simp [$hrun:term]) (by simp [$hsp:term])
      (spAligned_of_sp_eq $hspA $hsp (by simp [$hsp:term]))
      (by simp) (by clear * -; bv_omega) (by simp) rfl ?_;
   intro _))

theorem seg7b_zero_load [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Zero) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Inner) s
      (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ memRegion (sp + 25296#64) 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x8 = 0xfffffffffffffec0#64 ∧
        sf.readReg64 .x9 = sp + 22416#64 ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readVReg128 5#5 = c3329Vec ∧ sf.readVReg128 6#5 = c67107840Vec ∧
        sf.readVReg128 7#5 = c1664Vec ∧ sf.readVReg128 16#5 = c10321340Vec ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2192#64) serConstFn ∗ memRegion (sp + 25296#64) 320 ∗ Rest)) := by
  subst hbase
  refine SepWP.weaken_pre (show VecRangeMem 4 (sp + 2192#64) serConstFn ∗ (memRegion (sp + 25296#64) 320 ∗ Rest) ⊢
      memRegion (sp + 25296#64) 320 ∗ (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ Rest) by sep_frame) ?_
  apply SepWP.of_memRegion_vecRangeMem 20 (sp + 25296#64) (by decide) (by sep_focus); intro fz
  refine SepWP.weaken_pre (show VecRangeMem 20 (sp + 25296#64) fz ∗ (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ Rest) ⊢
      VecRangeMem 4 (sp + 2192#64) serConstFn ∗ (VecRangeMem 20 (sp + 25296#64) fz ∗ Rest) by sep_frame) ?_
  wp_steps 1
  refine step_ldrQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43548 43552 2240 4 3 5#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43552 43556 2224 4 2 6#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43556 43560 2208 4 1 7#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  refine step_ldrQ128_sp_vecRange blkPl04.base sp (sp + 2192#64) 43560 43564 2192 4 0 16#5 serConstFn
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp [hsp]) (spAligned_of_sp_eq hspA hsp (by simp [hsp]))
    (by simp) (by clear * -; bv_omega) rfl ?_
  wp_steps 2
  refine SepWP.weaken_pre (P' := VecRangeMem 20 (sp + 25296#64) fz ∗ (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ Rest))
    (by sep_frame) ?_
  step_zero_q sp hrun hsp hspA 43572 43576 25600 19; step_zero_q sp hrun hsp hspA 43576 43580 25584 18
  step_zero_q sp hrun hsp hspA 43580 43584 25568 17; step_zero_q sp hrun hsp hspA 43584 43588 25552 16
  step_zero_q sp hrun hsp hspA 43588 43592 25536 15; step_zero_q sp hrun hsp hspA 43592 43596 25520 14
  step_zero_q sp hrun hsp hspA 43596 43600 25504 13; step_zero_q sp hrun hsp hspA 43600 43604 25488 12
  step_zero_q sp hrun hsp hspA 43604 43608 25472 11; step_zero_q sp hrun hsp hspA 43608 43612 25456 10
  step_zero_q sp hrun hsp hspA 43612 43616 25440 9;  step_zero_q sp hrun hsp hspA 43616 43620 25424 8
  step_zero_q sp hrun hsp hspA 43620 43624 25408 7;  step_zero_q sp hrun hsp hspA 43624 43628 25392 6
  step_zero_q sp hrun hsp hspA 43628 43632 25376 5;  step_zero_q sp hrun hsp hspA 43632 43636 25360 4
  step_zero_q sp hrun hsp hspA 43636 43640 25344 3;  step_zero_q sp hrun hsp hspA 43640 43644 25328 2
  step_zero_q sp hrun hsp hspA 43644 43648 25312 1;  step_zero_q sp hrun hsp hspA 43648 43652 25296 0
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun])
    ⟨by simp [hsp], spAligned_of_sp_eq hspA hsp (by simp [hsp]), by simp [hfp],
      by simp, by simp, by simp [hx19], by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [serConstFn], by simp [serConstFn], by simp [serConstFn], by simp [serConstFn], ?_⟩
  exact entails_sub (vecRangeMem_entails_memRegion 20 (sp + 25296#64) _) (by sep_frame) (by sep_frame)

/-! ## 4. 16-Iteration `compress_10` + `serialize_10` Inner Loop (`+0xaa84 → +0xab84`) -/

theorem inner_addr_ldp (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + 22400#64) + BitVec.ofNat 64 (16 * (2 * c)) =
      (sp + BitVec.ofNat 64 (22416 + 32 * c)) + 0xfffffffffffffff0#64 := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

theorem inner_addr_x8 {c : Nat} (hc : c < 16) :
    (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) + 20#64 =
      0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals decide

theorem inner_addr_x9 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + BitVec.ofNat 64 (22416 + 32 * c)) + 32#64 = sp + BitVec.ofNat 64 (22416 + 32 * (c + 1)) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

theorem inner_addr_x10 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + 25296#64) + (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) =
      sp + BitVec.ofNat 64 (24976 + 20 * c) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

theorem inner_addr_x11 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + BitVec.ofNat 64 (24976 + 20 * c)) + 330#64 = sp + BitVec.ofNat 64 (25306 + 20 * c) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

theorem seg7b_compress_eq (vn : BitVec 128) :
    let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
    let evIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) k +
        lane32 c1664Vec k
    let odIn := pack4x32 fun k =>
      lane32 ((pack4x32 fun j => lane32 u0 j >>> 6) &&& c67107840Vec) k + lane32 c1664Vec k
    let evOut := pack4x32 fun k => lane32 (simdSqdmulh4s evIn c10321340Vec) k >>> 4
    let odOut := pack4x32 fun k => lane32 (simdSqdmulh4s odIn c10321340Vec) k >>> 4
    simdTrn1_8h evOut odOut &&& dup8x16 0x03ff#16 = neonCompress8h 10 vn := by
  dsimp only [c3329Vec, c1664Vec, c67107840Vec, c10321340Vec]
  exact seg6_compress10_eq vn

section InnerCompress
attribute [local irreducible]
  c10321340Vec c1664Vec c67107840Vec c3329Vec polyVecNat neonCompress8h
  dup8x16 pack4x32 lane32 simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h

theorem step_vreg1 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rd : BitVec 5) (val : BitVec 128)
    {inst : Instr} (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some inst)
    (hexec : execInstWithSvc (evalSvc prog.svc) inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      ((s.setPC (b + BitVec.ofNat 64 pcOff)).writeVReg128 rd val).advancePC)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      ((s.writeVReg128 rd val).setPC (b + BitVec.ofNat 64 nextOff)) P post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hev : prog.evalInst inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      (s.writeVReg128 rd val).setPC (b + BitVec.ofNat 64 nextOff) := by
    unfold Program.evalInst; rw [hexec]
    cases s; simp [State.setPC, State.writeVReg128, State.advancePC, hpc']
  exact SepWP.step_pure hpc hrun hfetch hev rfl hnext

private theorem step_sqdmulh4s {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rm rn rd : BitVec 5) (vn vm : BitVec 128)
    (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) =
      some (.simdThreeSame true false 0b10#2 rm 0b10110#5 rn rd))
    (hvn : s.readVReg128 rn = vn) (hvm : s.readVReg128 rm = vm) (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 rd (simdSqdmulh4s vn vm)).orFpsr (sqdmulh4sFlags vn vm)).setPC
        (b + BitVec.ofNat 64 nextOff)) P post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hvns : (s.setPC (b + BitVec.ofNat 64 pcOff)).readVReg128 rn = vn := hvn
  have hvms : (s.setPC (b + BitVec.ofNat 64 pcOff)).readVReg128 rm = vm := hvm
  have hev : prog.evalInst (.simdThreeSame true false 0b10#2 rm 0b10110#5 rn rd)
      (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      (((s.writeVReg128 rd (simdSqdmulh4s vn vm)).orFpsr (sqdmulh4sFlags vn vm)).setPC
        (b + BitVec.ofNat 64 nextOff)) := by
    unfold Program.evalInst; rw [exec_simdSqdmulh_4s, hvns, hvms]
    cases s; simp [State.setPC, State.writeVReg128, State.orFpsr, State.advancePC, hpc']
  exact SepWP.step_pure hpc hrun hfetch hev rfl hnext

@[expose] def compressEvIn (vn : BitVec 128) : BitVec 128 :=
  let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
  pack4x32 fun k =>
    lane32 ((pack4x32 fun j => lane32 u0 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) k +
      lane32 c1664Vec k

@[expose] def compressOdIn (vn : BitVec 128) : BitVec 128 :=
  let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
  pack4x32 fun k =>
    lane32 ((pack4x32 fun j => lane32 u0 j >>> 6) &&& c67107840Vec) k + lane32 c1664Vec k

theorem seg7b_inner_pre [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * c))
    (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Mul) s
      (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = s.spAligned ∧
        sm.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        sm.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        sm.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * (c + 1)) ∧
        sm.readReg64 .x10 = sp + BitVec.ofNat 64 (24976 + 20 * c) ∧
        sm.readReg64 .x11 = sp + BitVec.ofNat 64 (25306 + 20 * c) ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → sm.readReg64 r = s.readReg64 r) ∧
        sm.readVReg128 2#5 = compressEvIn (polyVecNat u (2 * c)) ∧
        sm.readVReg128 0#5 = compressOdIn (polyVecNat u (2 * c)) ∧
        sm.readVReg128 3#5 = compressEvIn (polyVecNat u (2 * c + 1)) ∧
        sm.readVReg128 1#5 = compressOdIn (polyVecNat u (2 * c + 1)) ∧
        sm.readVReg128 5#5 = c3329Vec ∧ sm.readVReg128 6#5 = c67107840Vec ∧
        sm.readVReg128 7#5 = c1664Vec ∧ sm.readVReg128 16#5 = c10321340Vec ∧
        Pm = (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)) := by
  subst hbase
  have ha_ldp := inner_addr_ldp sp hc
  have ha_ldp1 : (sp + 22400#64) + BitVec.ofNat 64 (16 * (2 * c + 1)) =
      ((sp + BitVec.ofNat 64 (22416 + 32 * c)) + 0xfffffffffffffff0#64) + 16#64 := by
    rw [← ha_ldp]; rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
    all_goals simp [BitVec.add_assoc]
  refine step_ldpQ128
    (s' := ((s.writeVReg128 0#5 (polyVecNat u (2 * c))).writeVReg128 1#5
      (polyVecNat u (2 * c + 1))).setPC (blkPl04.base + BitVec.ofNat 64 43656))
    (vt1 := 0#5) (vt2 := 1#5) (addr := .Offset .x9 0xfffffffffffffff0#64) (wb := none)
    hpc hrun (by simp only [arm64_norm]; rfl) rfl (by simp [evalAddrMode, hx9]) rfl
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c < 32) ha_ldp))
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c + 1 < 32) ha_ldp1))
    (by simp [applyWriteback, offSeg7Inner]) ?_
  let w0 := polyVecNat u (2 * c)
  let w1 := polyVecNat u (2 * c + 1)
  let u0 := simdAdd8h (simdCmltZero8h w0 &&& c3329Vec) w0
  let u1 := simdAdd8h (simdCmltZero8h w1 &&& c3329Vec) w1
  wp_steps 4
  refine step_vreg1 blkPl04.base 43672 43676 2#5 (simdCmltZero8h w0) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdCmltZero_8h]; simp [w0]) rfl ?_
  refine step_vreg1 blkPl04.base 43676 43680 3#5 (simdCmltZero8h w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdCmltZero_8h]; simp [w1]) rfl ?_
  refine step_vreg1 blkPl04.base 43680 43684 2#5 (simdCmltZero8h w0 &&& c3329Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv5]) rfl ?_
  refine step_vreg1 blkPl04.base 43684 43688 3#5 (simdCmltZero8h w1 &&& c3329Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv5]) rfl ?_
  refine step_vreg1 blkPl04.base 43688 43692 0#5 u0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdAdd_8h]; simp [u0, w0]) rfl ?_
  refine step_vreg1 blkPl04.base 43692 43696 1#5 u1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdAdd_8h]; simp [u1, w1]) rfl ?_
  refine step_vreg1 blkPl04.base 43696 43700 2#5 (pack4x32 fun j => lane32 u0 j <<< 10) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdShl_4s_10]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43700 43704 0#5 (pack4x32 fun j => lane32 u0 j >>> 6) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_6]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43704 43708 3#5 (pack4x32 fun j => lane32 u1 j <<< 10) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdShl_4s_10]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43708 43712 1#5 (pack4x32 fun j => lane32 u1 j >>> 6) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_6]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43712 43716 2#5 ((pack4x32 fun j => lane32 u0 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_4s_fc24]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43716 43720 0#5 ((pack4x32 fun j => lane32 u0 j >>> 6) &&& c67107840Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv6]) rfl ?_
  refine step_vreg1 blkPl04.base 43720 43724 3#5 ((pack4x32 fun j => lane32 u1 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_4s_fc24]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43724 43728 1#5 ((pack4x32 fun j => lane32 u1 j >>> 6) &&& c67107840Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv6]) rfl ?_
  refine step_vreg1 blkPl04.base 43728 43732 2#5 (compressEvIn w0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressEvIn, u0]) rfl ?_
  refine step_vreg1 blkPl04.base 43732 43736 0#5 (compressOdIn w0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressOdIn, u0]) rfl ?_
  refine step_vreg1 blkPl04.base 43736 43740 3#5 (compressEvIn w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressEvIn, u1]) rfl ?_
  refine step_vreg1 blkPl04.base 43740 43744 1#5 (compressOdIn w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressOdIn, u1]) rfl ?_
  refine SepWP.done rfl (by simp [hrun]) ⟨by simp [hsp], ?_, by simp,
    by simp [inner_addr_x8 hc], by simp [inner_addr_x9 sp hc],
    by simp [inner_addr_x10 sp hc],
    by simp [inner_addr_x10 sp hc, inner_addr_x11 sp hc],
    fun r h8 h9 h10 h11 => ?_,
    by simp [w0], by simp [w0], by simp [w1], by simp [w1],
    by simp [hv5], by simp [hv6], by simp [hv7], by simp [hv16], rfl⟩
  · simp only [spA_setPC', spA_writeVReg128', spA_setPState', spA_writeGPR']
  · simp only [readReg64_setPC', readReg64_writeVReg128']
    cases r with
    | gpr idx =>
      have i8 : idx ≠ 8#5 := fun h => h8 (h ▸ rfl)
      have i9 : idx ≠ 9#5 := fun h => h9 (h ▸ rfl)
      have i10 : idx ≠ 10#5 := fun h => h10 (h ▸ rfl)
      have i11 : idx ≠ 11#5 := fun h => h11 (h ▸ rfl)
      simp [i8, i9, i10, i11]
    | xzr => simp
    | sp => simp

attribute [local irreducible] compressEvIn compressOdIn

theorem seg7b_inner_mul [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (ev0 od0 ev1 od1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + offSeg7Mul) (hrun : s.status = .Running)
    (hv2 : s.readVReg128 2#5 = ev0) (hv0 : s.readVReg128 0#5 = od0)
    (hv3 : s.readVReg128 3#5 = ev1) (hv1 : s.readVReg128 1#5 = od1)
    (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Mix) s P
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        (∀ r : Reg, s2.readReg64 r = s.readReg64 r) ∧
        s2.readVReg128 0#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s ev0 c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s od0 c10321340Vec) k >>> 4) &&& dup8x16 0x03ff#16) ∧
        s2.readVReg128 1#5 = (simdTrn1_8h
          (pack4x32 fun k => lane32 (simdSqdmulh4s ev1 c10321340Vec) k >>> 4)
          (pack4x32 fun k => lane32 (simdSqdmulh4s od1 c10321340Vec) k >>> 4) &&& dup8x16 0x03ff#16) ∧
        s2.readVReg128 5#5 = s.readVReg128 5#5 ∧ s2.readVReg128 6#5 = s.readVReg128 6#5 ∧
        s2.readVReg128 7#5 = s.readVReg128 7#5 ∧ s2.readVReg128 16#5 = c10321340Vec ∧
        P2 = P) := by
  subst hbase
  let m2 := pack4x32 fun k => lane32 (simdSqdmulh4s ev0 c10321340Vec) k >>> 4
  let m0 := pack4x32 fun k => lane32 (simdSqdmulh4s od0 c10321340Vec) k >>> 4
  let m3 := pack4x32 fun k => lane32 (simdSqdmulh4s ev1 c10321340Vec) k >>> 4
  let m1 := pack4x32 fun k => lane32 (simdSqdmulh4s od1 c10321340Vec) k >>> 4
  refine step_sqdmulh4s blkPl04.base 43744 43748 16#5 2#5 2#5 ev0 c10321340Vec
    hpc hrun (by simp only [arm64_norm]) hv2 hv16 rfl ?_
  refine step_sqdmulh4s blkPl04.base 43748 43752 16#5 0#5 0#5 od0 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv0]) (by simp [hv16]) rfl ?_
  refine step_sqdmulh4s blkPl04.base 43752 43756 16#5 3#5 3#5 ev1 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv3]) (by simp [hv16]) rfl ?_
  refine step_sqdmulh4s blkPl04.base 43756 43760 16#5 1#5 1#5 od1 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv1]) (by simp [hv16]) rfl ?_
  refine step_vreg1 blkPl04.base 43760 43764 2#5 m2 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m2]) rfl ?_
  refine step_vreg1 blkPl04.base 43764 43768 0#5 m0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m0]) rfl ?_
  refine step_vreg1 blkPl04.base 43768 43772 3#5 m3 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m3]) rfl ?_
  refine step_vreg1 blkPl04.base 43772 43776 1#5 m1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m1]) rfl ?_
  refine step_vreg1 blkPl04.base 43776 43780 0#5 (simdTrn1_8h m2 m0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43780 43784 1#5 (simdTrn1_8h m3 m1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43784 43788 0#5 (simdTrn1_8h m2 m0 &&& dup8x16 0x03ff#16) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_8h_fc8]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43788 43792 1#5 (simdTrn1_8h m3 m1 &&& dup8x16 0x03ff#16) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_8h_fc8]; simp) rfl ?_
  exact SepWP.done rfl (by simp [hrun])
    ⟨by simp, by simp only [spA_setPC', spA_writeVReg128', spA_orFpsr'], by simp,
      fun r => by simp only [readReg64_setPC', readReg64_writeVReg128', readReg64_orFpsr'],
      by simp [m2, m0], by simp [m3, m1], by simp, by simp, by simp, by simp [hv16], rfl⟩

end InnerCompress

theorem seg7b_compress_evod_eq (vn : BitVec 128) :
    simdTrn1_8h
      (pack4x32 fun k => lane32 (simdSqdmulh4s (compressEvIn vn) c10321340Vec) k >>> 4)
      (pack4x32 fun k => lane32 (simdSqdmulh4s (compressOdIn vn) c10321340Vec) k >>> 4) &&&
      dup8x16 0x03ff#16 = neonCompress8h 10 vn :=
  seg7b_compress_eq vn

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b1
