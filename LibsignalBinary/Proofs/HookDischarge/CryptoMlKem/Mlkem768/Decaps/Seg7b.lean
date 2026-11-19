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
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b1
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
# `decapsulate_compressed_key` (`B04`) — Segment 7b (`+0xa968 .. +0xabd8`)

Executes the 3-polynomial `compress_and_serialize_10` outer/inner loops writing the `960`-byte
re-encrypted ciphertext `c₁'` at `[sp + 18032, sp + 18992)`, then copies `1,536` bytes of `r̂[0..2]`
from `[sp + 19168, sp + 20704)` to `[sp + 11856, sp + 13392)` via `B28` `memcpy`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b

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
  lane64_simdExt16b_8_0 neonSerialize10Bytes neonSerialize10Mix)
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

open scoped LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b1.Simp
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b1 (
  c10321340Vec c1664Vec c3329Vec c67107840Vec cell_entails_memRegion8
  compressEvIn compressOdIn inner_addr_x10 inner_addr_x11 inner_addr_x8 inner_addr_x9
  offSeg7Bounce offSeg7Inner offSeg7Mix offSeg7Mul offSeg7Outer offSeg7RhatCopy
  offSeg7Store offSeg7Zero seg7b_compress_evod_eq seg7b_header
  seg7b_inner_mul seg7b_inner_pre seg7b_prep_poly seg7b_zero_load
  sepWP_elim_cell8 sepWP_elim_region20 ser10Chunk ser10Chunk_length ser10Prefix
  ser10Prefix_length ser10Prefix_sixteen ser10Prefix_succ ser10Prefix_zero
  serConstFn step_strB8_off step_strS32_off step_vreg1 low32_eq_lane64_0)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC04 blkLib04 blkTree04 blk04_code_eq blk04_tree_size
  via_placement blkPl04 blkPlaceable04 [0xab10 → 0xabd4]
end

namespace Simp
@[scoped simp, arm64_norm, wp_norm] abbrev offSeg8Start : BitVec 64 := BitVec.ofNat 64 43992
end Simp
export Simp (offSeg8Start)
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


section InnerSimd
attribute [local irreducible] c10321340Vec c1664Vec c67107840Vec c3329Vec
  polyVecNat neonSerialize10Mix neonCompress8h compressEvIn compressOdIn
  simdExt16b simdTrn1_8h simdTrn2_8h simdSli4s simdTrn1_4s simdTrn2_4s simdSli2d

private theorem seg7b_inner_compress [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * c))
    (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Mix) s
      (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        s1.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        s1.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * (c + 1)) ∧
        s1.readReg64 .x10 = sp + BitVec.ofNat 64 (24976 + 20 * c) ∧
        s1.readReg64 .x11 = sp + BitVec.ofNat 64 (25306 + 20 * c) ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s1.readReg64 r = s.readReg64 r) ∧
        s1.readVReg128 0#5 = neonCompress8h 10 (polyVecNat u (2 * c)) ∧
        s1.readVReg128 1#5 = neonCompress8h 10 (polyVecNat u (2 * c + 1)) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c67107840Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)) := by
  refine SepWP.seq
    (seg7b_inner_pre hb hbase s sp hc u Rest hpc hrun hsp hx8 hx9 hx24 hv5 hv6 hv7 hv16) ?_
  rintro sm Pm hpcm hrunm ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hregsm,
    hv2m, hv0m, hv3m, hv1m, hv5m, hv6m, hv7m, hv16m, hPm⟩
  refine SepWP.mono (seg7b_inner_mul hb hbase sm _ _ _ _ Pm hpcm hrunm hv2m hv0m hv3m hv1m hv16m) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv0_1, hv1_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  exact ⟨hsp1.trans hspm, hspA1.trans hspAm, hpst1.trans hpstm,
    (hregs1 .x8).trans hx8m, (hregs1 .x9).trans hx9m,
    (hregs1 .x10).trans hx10m, (hregs1 .x11).trans hx11m,
    fun r h8 h9 h10 h11 => (hregs1 r).trans (hregsm r h8 h9 h10 h11),
    hv0_1.trans (seg7b_compress_evod_eq _), hv1_1.trans (seg7b_compress_evod_eq _),
    hv5_1.trans hv5m, hv6_1.trans hv6m, hv7_1.trans hv7m, hv16_1, hP1.trans hPm⟩

private theorem seg7b_inner_mix [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (v0 v1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + offSeg7Mix) (hrun : s.status = .Running)
    (hv0 : s.readVReg128 0#5 = neonCompress8h 10 v0)
    (hv1 : s.readVReg128 1#5 = neonCompress8h 10 v1) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Store) s P
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        (∀ r : Reg, s2.readReg64 r = s.readReg64 r) ∧
        s2.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 v0) ∧
        s2.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 v1) ∧
        s2.readVReg128 5#5 = s.readVReg128 5#5 ∧ s2.readVReg128 6#5 = s.readVReg128 6#5 ∧
        s2.readVReg128 7#5 = s.readVReg128 7#5 ∧ s2.readVReg128 16#5 = s.readVReg128 16#5 ∧
        P2 = P) := by
  subst hbase
  let c0 := neonCompress8h 10 v0
  let c1 := neonCompress8h 10 v1
  let a0 := simdSli4s (simdTrn1_8h c0 c0) (simdTrn2_8h c0 c0) 10
  let a1 := simdSli4s (simdTrn1_8h c1 c1) (simdTrn2_8h c1 c1) 10
  let m0 := simdSli2d (simdTrn1_4s a0 a0) (simdTrn2_4s a0 a0) 20
  let m1 := simdSli2d (simdTrn1_4s a1 a1) (simdTrn2_4s a1 a1) 20
  refine step_vreg1 blkPl04.base 43792 43796 2#5 (simdTrn1_8h c0 c0) hpc hrun (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp [hv0, c0]) rfl ?_
  refine step_vreg1 blkPl04.base 43796 43800 0#5 (simdTrn2_8h c0 c0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn2_8h]; simp [hv0, c0]) rfl ?_
  refine step_vreg1 blkPl04.base 43800 43804 3#5 (simdTrn1_8h c1 c1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp [hv1, c1]) rfl ?_
  refine step_vreg1 blkPl04.base 43804 43808 1#5 (simdTrn2_8h c1 c1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn2_8h]; simp [hv1, c1]) rfl ?_
  refine step_vreg1 blkPl04.base 43808 43812 2#5 a0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdSli_4s_10]; simp [a0]) rfl ?_
  refine step_vreg1 blkPl04.base 43812 43816 3#5 a1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdSli_4s_10]; simp [a1]) rfl ?_
  refine step_vreg1 blkPl04.base 43816 43820 0#5 (simdTrn1_4s a0 a0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_4s]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43820 43824 1#5 (simdTrn2_4s a0 a0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn2_4s]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43824 43828 2#5 (simdTrn1_4s a1 a1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_4s]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43828 43832 3#5 (simdTrn2_4s a1 a1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn2_4s]; simp) rfl ?_
  refine step_vreg1 blkPl04.base 43832 43836 0#5 m0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdSli_2d_20]; simp [m0]) rfl ?_
  refine step_vreg1 blkPl04.base 43836 43840 2#5 m1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdSli_2d_20]; simp [m1]) rfl ?_
  exact SepWP.done rfl (by simp [hrun])
    ⟨by simp, by simp only [Seg7b1.spA_setPC', Seg7b1.spA_writeVReg128'], by simp,
      fun r => by simp only [Seg7b1.readReg64_setPC', Seg7b1.readReg64_writeVReg128'],
      by simp [m0, a0, c0]; exact seg6_serialize10_mix_eq v0,
      by simp [m1, a1, c1]; exact seg6_serialize10_mix_eq v1,
      by simp, by simp, by simp, by simp, rfl⟩

private theorem seg7b_inner_simd [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Inner) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * c))
    (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Store) s
      (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        s1.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        s1.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * (c + 1)) ∧
        s1.readReg64 .x10 = sp + BitVec.ofNat 64 (24976 + 20 * c) ∧
        s1.readReg64 .x11 = sp + BitVec.ofNat 64 (25306 + 20 * c) ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s1.readReg64 r = s.readReg64 r) ∧
        s1.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c))) ∧
        s1.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c + 1))) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c67107840Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest)) := by
  refine SepWP.seq
    (seg7b_inner_compress hb hbase s sp hc u Rest hpc hrun hsp hx8 hx9 hx24 hv5 hv6 hv7 hv16) ?_
  rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hx11_1, hregs1,
    hv0_1, hv1_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  refine SepWP.mono (seg7b_inner_mix hb hbase s1 (polyVecNat u (2 * c)) (polyVecNat u (2 * c + 1))
    P1 hpc1 hrun1 hv0_1 hv1_1) ?_
  rintro s2 P2 _ _ ⟨hsp2, hspA2, hpst2, hregs2, hv0_2, hv2_2, hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  exact ⟨hsp2.trans hsp1, hspA2.trans hspA1, hpst2.trans hpst1,
    (hregs2 .x8).trans hx8_1, (hregs2 .x9).trans hx9_1,
    (hregs2 .x10).trans hx10_1, (hregs2 .x11).trans hx11_1,
    fun r h8 h9 h10 h11 => (hregs2 r).trans (hregs1 r h8 h9 h10 h11),
    hv0_2, hv2_2, hv5_2.trans hv5_1, hv6_2.trans hv6_1, hv7_2.trans hv7_1, hv16_2.trans hv16_1,
    hP2.trans hP1⟩

end InnerSimd

@[simp] private theorem ext8_self_low32 (m : BitVec 128) :
    (lane64 (m.truncate 64 ++ m.extractLsb' 64 64) 0).truncate 32 =
      (lane64 (simdExt16b m m 8) 0).truncate 32 := by
  rw [lane64_simdExt16b_8_0]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [lane64, show i < 64 by omega, hi]

private theorem ser10Prefix_append_chunk (dst : BitVec 64) (u : Poly16) (c : Nat) :
    (dst ↦ₛ ser10Prefix u c) ∗ ((dst + BitVec.ofNat 64 (20 * c)) ↦ₛ ser10Chunk u c) =
      (dst ↦ₛ ser10Prefix u (c + 1)) := by
  rw [ser10Prefix_succ, pointsToBytes_append, ser10Prefix_length]

section InnerStore
attribute [local irreducible] neonSerialize10Mix neonCompress8h polyVecNat simdExt16b lane8 lane64

private theorem seg7b_inner_store [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Store) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hpst : s.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64)
    (hx10 : s.readReg64 .x10 = sp + BitVec.ofNat 64 (24976 + 20 * c))
    (hx11 : s.readReg64 .x11 = sp + BitVec.ofNat 64 (25306 + 20 * c))
    (hv0 : s.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c))))
    (hv2 : s.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c + 1)))) :
    let nextPc := if c < 15 then b + offSeg7Inner else b + offSeg7Bounce
    SepWP (blkPC04.rebase b (fun _ => none)) nextPc s
      (((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (25296 + 20 * c)) (320 - 20 * c) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = s.spAligned ∧
        (∀ r : Reg, r ≠ .x11 → sf.readReg64 r = s.readReg64 r) ∧
        sf.readVReg128 5#5 = s.readVReg128 5#5 ∧ sf.readVReg128 6#5 = s.readVReg128 6#5 ∧
        sf.readVReg128 7#5 = s.readVReg128 7#5 ∧ sf.readVReg128 16#5 = s.readVReg128 16#5 ∧
        (Pf ⊢ ((sp + 25296#64) ↦ₛ ser10Prefix u (c + 1)) ∗
          memRegion (sp + BitVec.ofNat 64 (25296 + 20 * (c + 1))) (320 - 20 * (c + 1)) ∗ Rest)) := by
  subst hbase
  intro nextPc
  let ea := sp + BitVec.ofNat 64 (25296 + 20 * c)
  let x10v := sp + BitVec.ofNat 64 (24976 + 20 * c)
  let m0 := neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c)))
  let m1 := neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c + 1)))
  have hsplit : memRegion ea (320 - 20 * c) =
      memRegion ea 20 ∗ memRegion (sp + BitVec.ofNat 64 (25296 + 20 * (c + 1))) (320 - 20 * (c + 1)) :=
    memRegion_split' (b := ea) (b' := sp + BitVec.ofNat 64 (25296 + 20 * (c + 1)))
      (n := 20) (k := (320 - 20 * (c + 1) : Nat)) (by omega)
      (by dsimp only [ea]; clear * - hc; bv_omega) (by omega)
  have hx10_ea (k : Nat) (hk : k < 20) : ea + BitVec.ofNat 64 k = x10v + BitVec.ofNat 64 (320 + k) := by
    dsimp only [x10v, ea]; clear * - hc hk; bv_omega
  have hx10_ea0 : ea = x10v + 320#64 := by simpa using hx10_ea 0 (by decide)
  have hx11_ea10 : s.readReg64 .x11 = ea + 10#64 := by
    rw [hx11]; dsimp only [ea]; clear * - hc; bv_omega
  have hx10_ea5 : x10v + 325#64 = ea + 5#64 := (hx10_ea 5 (by decide)).symm
  have hx10_ea15 : x10v + 335#64 = ea + 15#64 := (hx10_ea 15 (by decide)).symm
  have hea2 : ea = (sp + 25296#64) + BitVec.ofNat 64 (20 * c) := by
    dsimp only [ea]; clear * - hc; bv_omega
  refine SepWP.weaken_pre
    (show ((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗ (memRegion ea (320 - 20 * c) ∗ Rest) ⊢
      memRegion ea 20 ∗ (((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (25296 + 20 * (c + 1))) (320 - 20 * (c + 1)) ∗ Rest) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region20; intro w0 u1 w2 u3 w4 u5 w6 u7
  let e0 := m0.truncate 64 ++ m0.extractLsb' 64 64
  let e1 := m1.truncate 64 ++ m1.extractLsb' 64 64
  refine step_vreg1 blkPl04.base 43840 43844 1#5 ((lane8 m0 4).zeroExtend 128) hpc hrun (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b4]; simp [hv0]; rfl) rfl ?_
  refine step_vreg1 blkPl04.base 43844 43848 4#5 e0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdExt_16b_8]; simp [hv0]; rfl) rfl ?_
  refine step_vreg1 blkPl04.base 43848 43852 3#5 ((lane8 m0 12).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b12]; simp [hv0]; rfl) rfl ?_
  refine step_strS32_off blkPl04.base x10v 43852 43856 320 0#5 .x10 ((lane64 m0 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, x10v])
    (by simp [hv0, low32_eq_lane64_0]; rfl) (SepStore32.left (SepStore32.here hx10_ea0)) rfl ?_; intro m_1
  refine step_vreg1 blkPl04.base 43856 43860 0#5 ((lane8 m1 4).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b4]; simp [hv2]; rfl) rfl ?_
  refine step_strS32_off blkPl04.base (ea + 10#64) 43860 43864 0 2#5 .x11 ((lane64 m1 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm])
    (by simp [hx11_ea10]) (by simp [hv2, low32_eq_lane64_0]; rfl)
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega)))))))
    rfl ?_; intro m_2
  wp_step
  refine step_strB8_off blkPl04.base x10v 43868 43872 324 1#5 .x10 (lane8 m0 4)
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, x10v])
    (by simp) (SepStore8.right (SepStore8.left (SepStore8.here (hx10_ea 4 (by decide))))) rfl ?_; intro m_3
  refine step_vreg1 blkPl04.base 43872 43876 1#5 ((lane8 m1 12).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b12]; simp [hv2]; rfl) rfl ?_
  refine step_vreg1 blkPl04.base 43876 43880 2#5 e1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdExt_16b_8]; simp [hv2]; rfl) rfl ?_
  refine step_strS32_off blkPl04.base (ea + 5#64) 43880 43884 0 4#5 .x11 ((lane64 (simdExt16b m0 m0 8) 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm])
    (by simp [x10v, hx10_ea5]) (by simp [e0, low32_eq_lane64_0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega))))) rfl ?_; intro m_4
  wp_step
  refine step_strB8_off blkPl04.base x10v 43888 43892 329 3#5 .x10 (lane8 m0 12)
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, x10v])
    (by simp) (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (hx10_ea 9 (by decide))))))) rfl ?_; intro m_5
  refine step_strB8_off blkPl04.base x10v 43892 43896 334 0#5 .x10 (lane8 m1 4)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, x10v])
    (by simp) (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (hx10_ea 14 (by decide))))))))) rfl ?_; intro m_6
  refine step_strB8_off blkPl04.base x10v 43896 43900 339 1#5 .x10 (lane8 m1 12)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, x10v])
    (by simp) (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (hx10_ea 19 (by decide))))))))))) rfl ?_; intro m_7
  refine step_strS32_off blkPl04.base (ea + 15#64) 43900 43904 0 2#5 .x11 ((lane64 (simdExt16b m1 m1 8) 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm])
    (by simp [x10v, hx10_ea15]) (by simp [e1, low32_eq_lane64_0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega))))))))) rfl ?_; intro m_8
  have hcells := cells20_eq_neonSerialize10Bytes ea (neonCompress8h 10 (polyVecNat u (2 * c))) (neonCompress8h 10 (polyVecNat u (2 * c + 1)))
  have hpost :
      (ea ↦₃₂ (lane64 m0 0).truncate 32) ∗ ((ea + 4#64) ↦₈ lane8 m0 4) ∗
      ((ea + 5#64) ↦₃₂ (lane64 (simdExt16b m0 m0 8) 0).truncate 32) ∗ ((ea + 9#64) ↦₈ lane8 m0 12) ∗
      ((ea + 10#64) ↦₃₂ (lane64 m1 0).truncate 32) ∗ ((ea + 14#64) ↦₈ lane8 m1 4) ∗
      ((ea + 15#64) ↦₃₂ (lane64 (simdExt16b m1 m1 8) 0).truncate 32) ∗ ((ea + 19#64) ↦₈ lane8 m1 12) ∗
      (((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗ memRegion (sp + BitVec.ofNat 64 (25296 + 20 * (c + 1))) (320 - 20 * (c + 1)) ∗ Rest) ⊢
      ((sp + 25296#64) ↦ₛ ser10Prefix u (c + 1)) ∗ memRegion (sp + BitVec.ofNat 64 (25296 + 20 * (c + 1))) (320 - 20 * (c + 1)) ∗ Rest := by
    have hch := ser10Prefix_append_chunk (sp + 25296#64) u c
    dsimp only [m0, m1, ser10Chunk] at hcells hch ⊢
    rw [← hch, ← hea2, ← hcells]; sep_frame
  by_cases hc15 : c < 15
  · refine step_bCond_taken (pc := blkPl04.base + BitVec.ofNat 64 43904)
      (off := 0xffffffffffffff04#64) (dst := blkPl04.base + offSeg7Inner) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpst]; clear * - hc15
          rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> first | decide | omega)
      (by dsimp only [offSeg7Inner]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp [hc15]) (by simp [hrun])
      ⟨by simp [hsp], by simp [State.spAligned],
        fun r hr => by cases r with
          | gpr idx => have hne : idx ≠ 11#5 := fun h => hr (h ▸ rfl); simp [hne]
          | xzr => simp
          | sp => simp,
        by simp, by simp, by simp, by simp, hpost⟩
  · have hce : c = 15 := by omega
    subst hce
    refine step_bCond_not_taken (pc := blkPl04.base + BitVec.ofNat 64 43904)
      (off := 0xffffffffffffff04#64) (dst := blkPl04.base + offSeg7Bounce) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm, hpst])
      (by dsimp only [offSeg7Bounce]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp) (by simp [hrun])
      ⟨by simp [hsp], by simp [State.spAligned],
        fun r hr => by cases r with
          | gpr idx => have hne : idx ≠ 11#5 := fun h => hr (h ▸ rfl); simp [hne]
          | xzr => simp
          | sp => simp,
        by simp, by simp, by simp, by simp, hpost⟩

end InnerStore

/-! ## 5. Full 16-Iteration Inner Loop, Outer Bounce, `r̂` Copy, & `seg7b_ok` -/

private theorem seg7b_inner_from [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (c : Nat) (hc : c ≤ 16) (s : State) (sp : BitVec 64) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = if c < 16 then b + offSeg7Inner else b + offSeg7Bounce)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * c))
    (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg7Bounce) s
      (PolyMem (sp + 22400#64) (polyVecNat u) ∗
        ((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗
        memRegion (sp + BitVec.ofNat 64 (25296 + 20 * c)) (320 - 20 * c) ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = s.spAligned ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → sf.readReg64 r = s.readReg64 r) ∧
        (Pf ⊢ PolyMem (sp + 22400#64) (polyVecNat u) ∗
          ((sp + 25296#64) ↦ₛ neonCompressSerialize10Poly u) ∗ Rest)) := by
  by_cases hc16 : c < 16
  · have hpc' : s.pc = b + offSeg7Inner := by simpa [hc16] using hpc
    refine SepWP.seq (seg7b_inner_simd hb hbase s sp hc16 u _ hpc' hrun hsp hx8 hx9 hx24 hv5 hv6 hv7 hv16) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hsp1, hspA1, hpst1, hx8_1, hx9_1, hx10_1, hx11_1, hregs1, hv0_1, hv2_1,
      hv5_1, hv6_1, hv7_1, hv16_1, rfl⟩
    refine SepWP.weaken_pre (show PolyMem (sp + 22400#64) (polyVecNat u) ∗
          (((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗
            memRegion (sp + BitVec.ofNat 64 (25296 + 20 * c)) (320 - 20 * c) ∗ Rest) ⊢
        ((sp + 25296#64) ↦ₛ ser10Prefix u c) ∗
          memRegion (sp + BitVec.ofNat 64 (25296 + 20 * c)) (320 - 20 * c) ∗
          (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest) by sep_frame) ?_
    refine SepWP.seq (seg7b_inner_store hb hbase s1 sp hc16 u
        (PolyMem (sp + 22400#64) (polyVecNat u) ∗ Rest) hpc1 hrun1 hsp1 hpst1 hx10_1 hx11_1 hv0_1 hv2_1) ?_
    rintro s2 P2 hpc2 hrun2 ⟨hsp2, hspA2, hregs2, hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
    have hpc2' : s2.pc = if c + 1 < 16 then b + offSeg7Inner else b + offSeg7Bounce := by
      have heq : (c < 15) = (c + 1 < 16) := propext ⟨by omega, by omega⟩
      simpa [heq] using hpc2
    have hx8_2 : s2.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) :=
      (hregs2 .x8 (by decide)).trans hx8_1
    have hx9_2 : s2.readReg64 .x9 = sp + BitVec.ofNat 64 (22416 + 32 * (c + 1)) :=
      (hregs2 .x9 (by decide)).trans hx9_1
    have hx24_2 : s2.readReg64 .x24 = sp + 25296#64 :=
      ((hregs2 .x24 (by decide)).trans (hregs1 .x24 (by decide) (by decide) (by decide) (by decide))).trans hx24
    refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
      (SepWP.mono (seg7b_inner_from hb hbase (c + 1) (by omega) s2 sp u Rest
        hpc2' hrun2 hsp2 hx8_2 hx9_2 hx24_2
        (hv5_2.trans hv5_1) (hv6_2.trans hv6_1) (hv7_2.trans hv7_1) (hv16_2.trans hv16_1)) ?_)
    intro sf Pf _ _ ⟨hsp_f, hspA_f, hregs_f, hPf⟩
    refine ⟨hsp_f, hspA_f.trans (hspA2.trans hspA1), fun r h8 h9 h10 h11 => ?_, hPf⟩
    exact (hregs_f r h8 h9 h10 h11).trans ((hregs2 r h11).trans (hregs1 r h8 h9 h10 h11))
  · have hce : c = 16 := by omega
    subst hce
    refine SepWP.done (by simpa using hpc) hrun ⟨hsp, rfl, fun _ _ _ _ _ => rfl, ?_⟩
    rw [ser10Prefix_sixteen]
    simp only [show 320 - 20 * 16 = 0 from rfl, memRegion_zero]
    sep_frame
termination_by 16 - c

private theorem seg7b_bounce [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Bounce) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) (hx20 : s.readReg64 .x20 = sp + 11872#64)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (320 * idx))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (idx + 1))
    (hx23 : s.readReg64 .x23 = sp + 24448#64) (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hx25 : s.readReg64 .x25 = sp + 18032#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    let outPtr := sp + BitVec.ofNat 64 (18032 + 320 * idx)
    let nextPc := if idx < 2 then b + offSeg7Outer else b + offSeg7RhatCopy
    SepWP (blkPC04.rebase b (fun _ => none)) nextPc s
      (((sp + 25296#64) ↦ₛ neonCompressSerialize10Poly u) ∗
        memRegion (sp + 24976#64) 320 ∗ memRegion outPtr 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧ sf.readReg64 .x20 = sp + 11872#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x23 = sp + 24448#64 ∧ sf.readReg64 .x24 = sp + 25296#64 ∧
        sf.readReg64 .x25 = sp + 18032#64 ∧
        (Pf ⊢ (outPtr ↦ₛ neonCompressSerialize10Poly u) ∗
          memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 ∗ Rest)) := by
  subst hbase
  intro outPtr nextPc
  set bsC := neonCompressSerialize10Poly u
  have hbsC : bsC.length = 320 := neonCompressSerialize10Poly_length u
  wp_steps 5; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 24976#64, sp + 25296#64, bsC)
  apply SepWP.done (by assumption) (by assumption); intro hcl1
  have hsp1' : sf.sp = sp := hsp_sf.trans hsp
  have hspA1 : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp1'
  have h19_1 : sf.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) := ‹_›
  have h20_1 : sf.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) := ‹_›
  have h21_1 : sf.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) := ‹_›
  have h22_1 : sf.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) := ‹_›
  have h23_1 : sf.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) := ‹_›
  have h24_1 : sf.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) := ‹_›
  have h25_1 : sf.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) := ‹_›
  have houtPtr : (sp + 18032#64) + BitVec.ofNat 64 (320 * idx) = outPtr := by
    dsimp only [outPtr]; clear * - hidx; bv_omega
  have hx0_eq : sf.readReg64 .x25 + sf.readReg64 .x21 = outPtr := by
    change sf.readReg64 (.gpr 25#5) + sf.readReg64 (.gpr 21#5) = outPtr
    rw [h25_1, h21_1]; simpa [Reg.x25, Reg.x21, hx25, hx21] using houtPtr
  refine SepWP.weaken_pre (P' := ((sp + 24976#64) ↦ₛ bsC) ∗ memRegion outPtr 320 ∗
      (((sp + 25296#64) ↦ₛ bsC) ∗ Rest)) (by sep_frame) ?_
  wp_steps 4; wp_step
  apply seq_codeLoaded_lr (by simpa using hcl1)
  wp_call (blk28_memcpy_04 blkPl04.base) (outPtr, sp + 24976#64, bsC)
  apply SepWP.done (by assumption) (by assumption); intro _
  have hsp2' : sf_1.sp = sp := hsp_sf_1.trans hsp1'
  have hspA2 : sf_1.spAligned = true := spAligned_of_sp_eq hspA1 hsp1' hsp2'
  have h19_2 : sf_1.readReg64 (.gpr 19#5) = sf.readReg64 (.gpr 19#5) := ‹_›
  have h20_2 : sf_1.readReg64 (.gpr 20#5) = sf.readReg64 (.gpr 20#5) := ‹_›
  have h22_2 : sf_1.readReg64 (.gpr 22#5) = sf.readReg64 (.gpr 22#5) := ‹_›
  have h23_2 : sf_1.readReg64 (.gpr 23#5) = sf.readReg64 (.gpr 23#5) := ‹_›
  have h24_2 : sf_1.readReg64 (.gpr 24#5) = sf.readReg64 (.gpr 24#5) := ‹_›
  have h25_2 : sf_1.readReg64 (.gpr 25#5) = sf.readReg64 (.gpr 25#5) := ‹_›
  have hx22_f : sf_1.readReg64 (.gpr 22#5) = BitVec.ofNat 64 (idx + 1) := by
    rw [h22_2, h22_1]; exact hx22
  have hm24976 : ((sp + 24976#64) ↦ₛ bsC) ⊢ memRegion (sp + 24976#64) 320 := by
    simpa [hbsC] using pointsToBytes_entails_memRegion (sp + 24976#64) bsC
  have hm25296 : ((sp + 25296#64) ↦ₛ bsC) ⊢ memRegion (sp + 25296#64) 320 := by
    simpa [hbsC] using pointsToBytes_entails_memRegion (sp + 25296#64) bsC
  have hpostP : (outPtr ↦ₛ bsC) ∗ ((sp + 24976#64) ↦ₛ bsC) ∗ (((sp + 25296#64) ↦ₛ bsC) ∗ Rest) ⊢
      (outPtr ↦ₛ bsC) ∗ memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 ∗ Rest :=
    entails_sub hm24976 (by sep_frame) (entails_sub hm25296 (by sep_frame) (by sep_frame))
  wp_steps 1
  by_cases hidx2 : idx < 2
  · refine step_bCond_taken (pc := blkPl04.base + BitVec.ofNat 64 43956)
      (off := 0xfffffffffffffe10#64) (dst := blkPl04.base + offSeg7Outer) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm]; clear * - hidx2; rcases idx with _ | _ | n <;> first | decide | omega)
      (by dsimp only [offSeg7Outer]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp [hidx2]) (by simp [hrun_sf_1])
      ⟨by simp [hsp2'], spAligned_of_sp_eq hspA2 hsp2' (by simp [hsp2']),
        by simp [Reg.fp] at hfp ⊢; rw [hcs_sf_1, hcs_sf, hfp],
        by simp [Reg.x19] at hx19 ⊢; rw [h19_2, h19_1, hx19],
        by simp [Reg.x20] at hx20 ⊢; rw [h20_2, h20_1, hx20],
        by simp [Reg.x22]; exact hx22_f,
        by simp [Reg.x23] at hx23 ⊢; rw [h23_2, h23_1, hx23],
        by simp [Reg.x24] at hx24 ⊢; rw [h24_2, h24_1, hx24],
        by simp [Reg.x25] at hx25 ⊢; rw [h25_2, h25_1, hx25], hpostP⟩
  · have hidxe : idx = 2 := by omega
    subst hidxe
    refine step_bCond_not_taken (pc := blkPl04.base + BitVec.ofNat 64 43956)
      (off := 0xfffffffffffffe10#64) (dst := blkPl04.base + offSeg7RhatCopy) (c := .NE)
      (by wp_norm_lhs) (by simp [hrun_sf_1]) (by simp only [arm64_norm]; rfl)
      (by simp only [wp_norm, arm64_norm])
      (by dsimp only [offSeg7RhatCopy]; clear * -; bv_omega) ?_
    refine SepWP.done (by dsimp [nextPc]; simp) (by simp [hrun_sf_1])
      ⟨by simp [hsp2'], spAligned_of_sp_eq hspA2 hsp2' (by simp [hsp2']),
        by simp [Reg.fp] at hfp ⊢; rw [hcs_sf_1, hcs_sf, hfp],
        by simp [Reg.x19] at hx19 ⊢; rw [h19_2, h19_1, hx19],
        by simp [Reg.x20] at hx20 ⊢; rw [h20_2, h20_1, hx20],
        by simp [Reg.x22]; exact hx22_f,
        by simp [Reg.x23] at hx23 ⊢; rw [h23_2, h23_1, hx23],
        by simp [Reg.x24] at hx24 ⊢; rw [h24_2, h24_1, hx24],
        by simp [Reg.x25] at hx25 ⊢; rw [h25_2, h25_1, hx25], hpostP⟩


private theorem seg7b_outer_iter [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) {idx : Nat} (hidx : idx < 3) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7Outer) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) (hx20 : s.readReg64 .x20 = sp + 11872#64)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 idx)
    (hx23 : s.readReg64 .x23 = sp + 24448#64) (hx24 : s.readReg64 .x24 = sp + 25296#64)
    (hx25 : s.readReg64 .x25 = sp + 18032#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let uPtr := sp + BitVec.ofNat 64 (11872 + 512 * idx)
    let outPtr := sp + BitVec.ofNat 64 (18032 + 320 * idx)
    let nextPc := if idx < 2 then b + offSeg7Outer else b + offSeg7RhatCopy
    SepWP (blkPC04.rebase b (fun _ => none)) nextPc s
      (VecRangeMem 4 (sp + 2192#64) serConstFn ∗
        PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 24448#64) 520 ∗
        memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 ∗
        memRegion outPtr 320 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 22400#64 ∧ sf.readReg64 .x20 = sp + 11872#64 ∧
        sf.readReg64 .x22 = BitVec.ofNat 64 (idx + 1) ∧
        sf.readReg64 .x23 = sp + 24448#64 ∧ sf.readReg64 .x24 = sp + 25296#64 ∧
        sf.readReg64 .x25 = sp + 18032#64 ∧
        (Pf ⊢ VecRangeMem 4 (sp + 2192#64) serConstFn ∗
          PolyMem uPtr (polyVecNat u) ∗
          memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 24448#64) 520 ∗
          memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 ∗
          (outPtr ↦ₛ neonCompressSerialize10Poly u) ∗ Rest)) := by
  intro uPtr outPtr nextPc
  have hm520b : memRegion (sp + 22400#64) 520 = memRegion (sp + 22400#64) 512 ∗ memRegion (sp + 22912#64) 8 :=
    memRegion_split' (b := sp + 22400#64) (b' := sp + 22912#64) (n := 512) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  refine SepWP.weaken_pre (P' := PolyMem uPtr (polyVecNat u) ∗
      memRegion (sp + 22400#64) 520 ∗ memRegion (sp + 24448#64) 520 ∗
      (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ memRegion (sp + 24976#64) 320 ∗
        memRegion (sp + 25296#64) 320 ∗ memRegion outPtr 320 ∗ Rest)) (by sep_frame) ?_
  refine sepWP_seq_env hcl hro
    (seg7b_prep_poly hb hbase s sp fpVal hidx u _ hpc hrun hsp hspA hfp hx19 hx20 hx22 hx23 hx24 hx25 hcl) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hP1⟩
  refine SepWP.weaken_pre (Entails.trans hP1 (show _ ⊢ VecRangeMem 4 (sp + 2192#64) serConstFn ∗
      memRegion (sp + 25296#64) 320 ∗
      (PolyMem uPtr (polyVecNat u) ∗ PolyMem (sp + 22400#64) (polyVecNat u) ∗
        memRegion (sp + 22912#64) 8 ∗ memRegion (sp + 24448#64) 520 ∗
        memRegion (sp + 24976#64) 320 ∗ memRegion outPtr 320 ∗ Rest) by sep_frame)) ?_
  refine sepWP_seq_env hcl1 hro1
    (seg7b_zero_load hb hbase s1 sp fpVal _ hpc1 hrun1 hsp1 hspA1 hfp1 hx19_1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2
    ⟨hsp2, hspA2, hfp2, hx8_2, hx9_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2,
      hv5_2, hv6_2, hv7_2, hv16_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (show _ ⊢ PolyMem (sp + 22400#64) (polyVecNat u) ∗
      ((sp + 25296#64) ↦ₛ ser10Prefix u 0) ∗ memRegion (sp + BitVec.ofNat 64 (25296 + 20 * 0)) (320 - 20 * 0) ∗
      (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
        memRegion (sp + 22912#64) 8 ∗ memRegion (sp + 24448#64) 520 ∗
        memRegion (sp + 24976#64) 320 ∗ memRegion outPtr 320 ∗ Rest) by
      rw [ser10Prefix_zero, pointsToBytes_nil]; sep_frame)) ?_
  refine sepWP_seq_env hcl2 hro2
    (seg7b_inner_from hb hbase 0 (by decide) s2 sp u _ (by simpa using hpc2) hrun2 hsp2
      (by simpa using hx8_2) (by simpa using hx9_2) (hx24_2.trans hx24_1)
      hv5_2 hv6_2 hv7_2 hv16_2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hsp3, hspA3_eq, hgpr3, hP3⟩
  have hspA3 : s3.spAligned = true := hspA3_eq.trans hspA2
  refine SepWP.weaken_pre (Entails.trans hP3 (show _ ⊢ ((sp + 25296#64) ↦ₛ neonCompressSerialize10Poly u) ∗
      memRegion (sp + 24976#64) 320 ∗ memRegion outPtr 320 ∗
      (VecRangeMem 4 (sp + 2192#64) serConstFn ∗ PolyMem uPtr (polyVecNat u) ∗
        PolyMem (sp + 22400#64) (polyVecNat u) ∗ memRegion (sp + 22912#64) 8 ∗
        memRegion (sp + 24448#64) 520 ∗ Rest) by sep_frame)) ?_
  refine SepWP.mono
    (seg7b_bounce hb hbase s3 sp fpVal hidx u _ hpc3 hrun3 hsp3 hspA3
      ((hgpr3 .fp (by decide) (by decide) (by decide) (by decide)).trans hfp2)
      ((hgpr3 .x19 (by decide) (by decide) (by decide) (by decide)).trans hx19_2)
      ((hgpr3 .x20 (by decide) (by decide) (by decide) (by decide)).trans (hx20_2.trans hx20_1))
      ((hgpr3 .x21 (by decide) (by decide) (by decide) (by decide)).trans (hx21_2.trans hx21_1))
      ((hgpr3 .x22 (by decide) (by decide) (by decide) (by decide)).trans (hx22_2.trans hx22_1))
      ((hgpr3 .x23 (by decide) (by decide) (by decide) (by decide)).trans (hx23_2.trans hx23_1))
      ((hgpr3 .x24 (by decide) (by decide) (by decide) (by decide)).trans (hx24_2.trans hx24_1))
      ((hgpr3 .x25 (by decide) (by decide) (by decide) (by decide)).trans (hx25_2.trans hx25_1))
      hcl3) ?_
  rintro sf Pf _ _ ⟨hspf, hspAf, hfpf, hx19f, hx20f, hx22f, hx23f, hx24f, hx25f, hPf⟩
  refine ⟨hspf, hspAf, hfpf, hx19f, hx20f, hx22f, hx23f, hx24f, hx25f, Entails.trans hPf ?_⟩
  have hm22400 : PolyMem (sp + 22400#64) (polyVecNat u) ∗ memRegion (sp + 22912#64) 8 ⊢
      memRegion (sp + 22400#64) 520 := by
    rw [hm520b]; exact sepConj_mono_left (vecRangeMem_entails_memRegion 32 (sp + 22400#64) (polyVecNat u))
  exact entails_sub hm22400 (by sep_frame) (by sep_frame)

private theorem seg7b_rhat_copy [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (r0 r1 r2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7RhatCopy) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8Start) s
      (PolyMem (sp + 19168#64) (polyVecNat r0) ∗
        PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗
        memRegion (sp + 11856#64) 1536 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 11856#64 ∧
        (Pf ⊢ PolyMem (sp + 11856#64) (polyVecNat r0) ∗
          PolyMem (sp + 12368#64) (polyVecNat r1) ∗
          PolyMem (sp + 12880#64) (polyVecNat r2) ∗
          PolyMem (sp + 19168#64) (polyVecNat r0) ∗
          PolyMem (sp + 19680#64) (polyVecNat r1) ∗
          PolyMem (sp + 20192#64) (polyVecNat r2) ∗ Rest)) := by
  subst hbase
  have ha1 : sp + 19680#64 = (sp + 19168#64) + 512#64 := by clear * -; bv_omega
  have ha2 : sp + 20192#64 = (sp + 19168#64) + 1024#64 := by clear * -; bv_omega
  have hb1 : (sp + 11856#64) + 512#64 = sp + 12368#64 := by clear * -; bv_omega
  have hb2 : (sp + 11856#64) + 1024#64 = sp + 12880#64 := by clear * -; bv_omega
  set bs := vecRangeBytes 32 (polyVecNat r0) ++
    (vecRangeBytes 32 (polyVecNat r1) ++ vecRangeBytes 32 (polyVecNat r2))
  have hbs : bs.length = 1536 := by
    simp [bs, List.length_append, vecRangeBytes_length]
  refine SepWP.weaken_pre
    (P' := ((sp + 19168#64) ↦ₛ bs) ∗ memRegion (sp + 11856#64) 1536 ∗ Rest)
    (by rw [← polyMem3_eq_pointsToBytes (sp + 19168#64), ← ha1, ← ha2]; sep_frame) ?_
  wp_steps 7; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_04 blkPl04.base) (sp + 11856#64, sp + 19168#64, bs)
  apply SepWP.done (by assumption) (by assumption); intro _
  have h19 : sf.readReg64 (.gpr 19#5) = _ := ‹_›
  refine SepWP.done hpc_sf hrun_sf
    ⟨hsp_sf.trans hsp, spAligned_of_sp_eq hspA hsp (hsp_sf.trans hsp),
      by simp [Reg.fp] at hfp ⊢; rw [hcs_sf, hfp],
      by simp [Reg.x19, h19], ?_⟩
  have h1 : ((sp + 11856#64) ↦ₛ bs) =
      PolyMem (sp + 11856#64) (polyVecNat r0) ∗
      PolyMem (sp + 12368#64) (polyVecNat r1) ∗
      PolyMem (sp + 12880#64) (polyVecNat r2) := by
    rw [← hb1, ← hb2, polyMem3_eq_pointsToBytes]
  have h2 : ((sp + 19168#64) ↦ₛ bs) =
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗
      PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) := by
    rw [ha1, ha2, polyMem3_eq_pointsToBytes]
  rw [h1, h2]; sep_frame

section PureCt1
attribute [local irreducible] sha3_512List sampleNtt Spec.polyNtt Spec.polyInvNtt Spec.sampleVecCbd2

theorem decapsCt1_eq {pk m coins : List (BitVec 8)}
    (hpk : pk.length = 1184) (hcoins : coins.length = 32) :
    let rho := (pk.drop 1152).take 32
    neonCompressSerialize10Poly (uVecPoly16 rho coins 0) ++
      (neonCompressSerialize10Poly (uVecPoly16 rho coins 1) ++
        neonCompressSerialize10Poly (uVecPoly16 rho coins 2)) =
      (indCpaEncryptWith sampleNtt 3 10 4 pk m coins).1 := by
  dsimp only [indCpaEncryptWith]
  have hrho : ((pk.drop 1152).take 32).length = 32 := by simp [List.length_take, List.length_drop, hpk]
  obtain ⟨hb0, hr0⟩ := uVecPoly16_spec hrho hcoins (by decide : 0 < 3)
  obtain ⟨hb1, hr1⟩ := uVecPoly16_spec hrho hcoins (by decide : 1 < 3)
  obtain ⟨hb2, hr2⟩ := uVecPoly16_spec hrho hcoins (by decide : 2 < 3)
  have hrng : List.range 3 = [0, 1, 2] := by decide
  simp only [hrng, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil]
  have hg (row : Nat) (h : row < 3) (f : Fin 3 → Poly) :
      (Array.ofFn f).getD row zeroPoly = f ⟨row, h⟩ := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]; simp [h]
  rw [hg 0 (by decide), hg 1 (by decide), hg 2 (by decide),
    neonCompressSerialize10Poly_eq hb0 hr0,
    neonCompressSerialize10Poly_eq hb1 hr1,
    neonCompressSerialize10Poly_eq hb2 hr2]

end PureCt1

theorem seg7b_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl04 b) (hbase : blkPl04.base = b)
    (s : State) (sp fpVal : BitVec 64) (u0 u1 u2 r0 r1 r2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg7SerStart) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true) (hfp : s.readReg64 .fp = fpVal)
    (hx19 : s.readReg64 .x19 = sp + 22400#64) (hx20 : s.readReg64 .x20 = sp + 11872#64)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) (hro : MlKemRoOk mlkemMpl s.mem) :
    let ct1Out := neonCompressSerialize10Poly u0 ++
      (neonCompressSerialize10Poly u1 ++ neonCompressSerialize10Poly u2)
    SepWP (blkPC04.rebase b (fun _ => none)) (b + offSeg8Start) s
      (memRegion (sp + 2192#64) 64 ∗
        memRegion (sp + 11856#64) 16 ∗
        PolyMem (sp + 11872#64) (polyVecNat u0) ∗
        PolyMem (sp + 12384#64) (polyVecNat u1) ∗
        PolyMem (sp + 12896#64) (polyVecNat u2) ∗
        memRegion (sp + 13408#64) 8 ∗
        memRegion (sp + 18032#64) 960 ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗
        PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗
        memRegion (sp + 22400#64) 520 ∗
        memRegion (sp + 24448#64) 1168 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .fp = fpVal ∧
        sf.readReg64 .x19 = sp + 11856#64 ∧
        mlkemMultiLib.CodeLoaded mlkemMpl sf.mem ∧ MlKemRoOk mlkemMpl sf.mem ∧
        (Pf ⊢ memRegion (sp + 2192#64) 64 ∗
          PolyMem (sp + 11856#64) (polyVecNat r0) ∗
          PolyMem (sp + 12368#64) (polyVecNat r1) ∗
          PolyMem (sp + 12880#64) (polyVecNat r2) ∗
          memRegion (sp + 13392#64) 24 ∗
          ((sp + 18032#64) ↦ₛ ct1Out) ∗
          PolyMem (sp + 19168#64) (polyVecNat r0) ∗
          PolyMem (sp + 19680#64) (polyVecNat r1) ∗
          PolyMem (sp + 20192#64) (polyVecNat r2) ∗
          memRegion (sp + 22400#64) 520 ∗
          memRegion (sp + 24448#64) 1168 ∗ Rest)) := by
  intro ct1Out
  have hm16 : memRegion (sp + 11856#64) 16 = memRegion (sp + 11856#64) 8 ∗ memRegion (sp + 11864#64) 8 :=
    memRegion_split' (b := sp + 11856#64) (b' := sp + 11864#64) (n := 8) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)
  have hm960 : memRegion (sp + 18032#64) 960 =
      memRegion (sp + 18032#64) 320 ∗ memRegion (sp + 18352#64) 320 ∗ memRegion (sp + 18672#64) 320 := by
    rw [memRegion_split' (b := sp + 18032#64) (b' := sp + 18352#64) (n := 320) (k := (640 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 18352#64) (b' := sp + 18672#64) (n := 320) (k := (320 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  have hm1168 : memRegion (sp + 24448#64) 1168 =
      memRegion (sp + 24448#64) 520 ∗ memRegion (sp + 24968#64) 8 ∗
      memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 := by
    rw [memRegion_split' (b := sp + 24448#64) (b' := sp + 24968#64) (n := 520) (k := (648 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 24968#64) (b' := sp + 24976#64) (n := 8) (k := (640 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 24976#64) (b' := sp + 25296#64) (n := 320) (k := (320 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
  refine SepWP.weaken_pre (P' := memRegion (sp + 2192#64) 64 ∗ memRegion (sp + 11864#64) 8 ∗
      memRegion (sp + 13408#64) 8 ∗
      (memRegion (sp + 11856#64) 8 ∗ PolyMem (sp + 11872#64) (polyVecNat u0) ∗
        PolyMem (sp + 12384#64) (polyVecNat u1) ∗ PolyMem (sp + 12896#64) (polyVecNat u2) ∗
        memRegion (sp + 18032#64) 320 ∗ memRegion (sp + 18352#64) 320 ∗ memRegion (sp + 18672#64) 320 ∗
        PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
        PolyMem (sp + 20192#64) (polyVecNat r2) ∗ memRegion (sp + 22400#64) 520 ∗
        memRegion (sp + 24448#64) 520 ∗ memRegion (sp + 24968#64) 8 ∗
        memRegion (sp + 24976#64) 320 ∗ memRegion (sp + 25296#64) 320 ∗ Rest))
    (by rw [hm16, hm960, hm1168]; sep_frame) ?_
  refine sepWP_seq_env hcl hro (seg7b_header hb hbase s sp fpVal _ hpc hrun hsp hspA hfp hx19 hx20) ?_
  rintro s0 P0 hpc0 hrun0 hcl0 hro0 ⟨hsp0, hspA0, hfp0, hx19_0, hx20_0, hx22_0, hx23_0, hx24_0, hx25_0, hP0⟩
  have hi0 := seg7b_outer_iter hb hbase s0 sp fpVal (idx := 0) (by decide) u0
    (memRegion (sp + 11856#64) 8 ∗ memRegion (sp + 11864#64) 8 ∗ memRegion (sp + 13408#64) 8 ∗
      PolyMem (sp + 12384#64) (polyVecNat u1) ∗ PolyMem (sp + 12896#64) (polyVecNat u2) ∗
      memRegion (sp + 18352#64) 320 ∗ memRegion (sp + 18672#64) 320 ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗ memRegion (sp + 24968#64) 8 ∗ Rest)
    hpc0 hrun0 hsp0 hspA0 hfp0 hx19_0 hx20_0 hx22_0 hx23_0 hx24_0 hx25_0 hcl0 hro0
  dsimp only at hi0
  refine sepWP_seq_env hcl0 hro0 (SepWP.weaken_pre (Entails.trans hP0 (by
    simp only [show BitVec.ofNat 64 (11872 + 512 * 0) = 11872#64 from rfl,
      show BitVec.ofNat 64 (18032 + 320 * 0) = 18032#64 from rfl]; sep_frame)) hi0) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx22_1, hx23_1, hx24_1, hx25_1, hP1⟩
  have hi1 := seg7b_outer_iter hb hbase s1 sp fpVal (idx := 1) (by decide) u1
    (memRegion (sp + 11856#64) 8 ∗ memRegion (sp + 11864#64) 8 ∗ memRegion (sp + 13408#64) 8 ∗
      PolyMem (sp + 11872#64) (polyVecNat u0) ∗ PolyMem (sp + 12896#64) (polyVecNat u2) ∗
      ((sp + 18032#64) ↦ₛ neonCompressSerialize10Poly u0) ∗ memRegion (sp + 18672#64) 320 ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗ memRegion (sp + 24968#64) 8 ∗ Rest)
    (by simpa using hpc1) hrun1 hsp1 hspA1 hfp1 hx19_1 hx20_1 hx22_1 hx23_1 hx24_1 hx25_1 hcl1 hro1
  dsimp only at hi1
  refine sepWP_seq_env hcl1 hro1 (SepWP.weaken_pre (Entails.trans hP1 (by
    simp only [show BitVec.ofNat 64 (11872 + 512 * 0) = 11872#64 from rfl,
      show BitVec.ofNat 64 (18032 + 320 * 0) = 18032#64 from rfl,
      show BitVec.ofNat 64 (11872 + 512 * 1) = 12384#64 from rfl,
      show BitVec.ofNat 64 (18032 + 320 * 1) = 18352#64 from rfl]; sep_frame)) hi1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, hx19_2, hx20_2, hx22_2, hx23_2, hx24_2, hx25_2, hP2⟩
  have hi2 := seg7b_outer_iter hb hbase s2 sp fpVal (idx := 2) (by decide) u2
    (memRegion (sp + 11856#64) 8 ∗ memRegion (sp + 11864#64) 8 ∗ memRegion (sp + 13408#64) 8 ∗
      PolyMem (sp + 11872#64) (polyVecNat u0) ∗ PolyMem (sp + 12384#64) (polyVecNat u1) ∗
      ((sp + 18032#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
      ((sp + 18352#64) ↦ₛ neonCompressSerialize10Poly u1) ∗
      PolyMem (sp + 19168#64) (polyVecNat r0) ∗ PolyMem (sp + 19680#64) (polyVecNat r1) ∗
      PolyMem (sp + 20192#64) (polyVecNat r2) ∗ memRegion (sp + 24968#64) 8 ∗ Rest)
    (by simpa using hpc2) hrun2 hsp2 hspA2 hfp2 hx19_2 hx20_2 hx22_2 hx23_2 hx24_2 hx25_2 hcl2 hro2
  dsimp only at hi2
  refine sepWP_seq_env hcl2 hro2 (SepWP.weaken_pre (Entails.trans hP2 (by
    simp only [show BitVec.ofNat 64 (11872 + 512 * 1) = 12384#64 from rfl,
      show BitVec.ofNat 64 (18032 + 320 * 1) = 18352#64 from rfl,
      show BitVec.ofNat 64 (11872 + 512 * 2) = 12896#64 from rfl,
      show BitVec.ofNat 64 (18032 + 320 * 2) = 18672#64 from rfl]; sep_frame)) hi2) ?_
  rintro s3 P3 hpc3 hrun3 hcl3 hro3 ⟨hsp3, hspA3, hfp3, _, _, _, _, _, _, hP3⟩
  simp only [show BitVec.ofNat 64 (11872 + 512 * 2) = 12896#64 from rfl,
    show BitVec.ofNat 64 (18032 + 320 * 2) = 18672#64 from rfl] at hP3
  have hm1560 : memRegion (sp + 11856#64) 8 ∗ memRegion (sp + 11864#64) 8 ∗
      PolyMem (sp + 11872#64) (polyVecNat u0) ∗ PolyMem (sp + 12384#64) (polyVecNat u1) ∗
      PolyMem (sp + 12896#64) (polyVecNat u2) ∗ memRegion (sp + 13408#64) 8 ⊢
      memRegion (sp + 11856#64) 1536 ∗ memRegion (sp + 13392#64) 24 := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono
      (vecRangeMem_entails_memRegion 32 _ _)
      (sepConj_mono (vecRangeMem_entails_memRegion 32 _ _)
        (sepConj_mono_left (vecRangeMem_entails_memRegion 32 _ _)))))) ?_
    simp only [show 16 * 32 = 512 from rfl]
    rw [memRegion_split' (b := sp + 11856#64) (b' := sp + 11864#64) (n := 8) (k := (1528 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 11864#64) (b' := sp + 11872#64) (n := 8) (k := (1520 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 11872#64) (b' := sp + 12384#64) (n := 512) (k := (1008 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 12384#64) (b' := sp + 12896#64) (n := 512) (k := (496 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 12896#64) (b' := sp + 13392#64) (n := 496) (k := (16 : Nat)) rfl (by clear * -; bv_omega) (by decide),
      memRegion_split' (b := sp + 13392#64) (b' := sp + 13408#64) (n := 16) (k := (8 : Nat)) rfl (by clear * -; bv_omega) (by decide)]
    sep_frame
  refine sepWP_seq_env hcl3 hro3
    (SepWP.weaken_pre (Entails.trans hP3 (entails_sub hm1560 (by sep_frame) (by sep_frame)))
      (seg7b_rhat_copy hb hbase s3 sp fpVal r0 r1 r2 _ (by simpa using hpc3) hrun3 hsp3 hspA3 hfp3 hcl3)) ?_
  rintro sf Pf hpcf hrunf hclf hrof ⟨hspf, hspAf, hfpf, hx19f, hPf⟩
  refine SepWP.done hpcf hrunf ⟨hspf, hspAf, hfpf, hx19f, hclf, hrof, Entails.trans hPf ?_⟩
  have hct1 : ((sp + 18032#64) ↦ₛ ct1Out) =
      ((sp + 18032#64) ↦ₛ neonCompressSerialize10Poly u0) ∗
      ((sp + 18352#64) ↦ₛ neonCompressSerialize10Poly u1) ∗
      ((sp + 18672#64) ↦ₛ neonCompressSerialize10Poly u2) := by
    dsimp only [ct1Out]
    rw [pointsToBytes_append, neonCompressSerialize10Poly_length,
      show (sp + 18032#64) + 320#64 = sp + 18352#64 by clear * -; bv_omega,
      pointsToBytes_append, neonCompressSerialize10Poly_length,
      show (sp + 18352#64) + 320#64 = sp + 18672#64 by clear * -; bv_omega]
  rw [hct1, hm1168]
  exact entails_sub (vecRangeMem_entails_memRegion 4 (sp + 2192#64) serConstFn) (by sep_frame) (by sep_frame)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7b
