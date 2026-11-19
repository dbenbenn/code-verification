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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd -- proof-setup: allow-public-import
public meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps
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

/-!
# `encapsulate1_serialized` (`B03`) — Segment 6a `ct1` `compress_and_serialize_10` (`+0x6a78 .. +0x6cd8`)

Setup (`seg6_setup`), inner NEON compression/serialization (`seg6_inner_simd`), and 20-byte chunk
store (`step_ser10_tail16`) lemmas for 10-bit `ct1` encoding.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 100000

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser

open Arm64 Arm64.Obj ProofLib SepProp BitVec
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemPlacement add_off_reloc_cancel mbase mlkemBlockPlacement_ρ
  mlkemCall_of_blockOk mlkemMpl resolve_blk28 seq_codeLoaded_lr)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (mlkemMemcpySpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.MemOps (blk28_memcpy_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.SimdSteps (step_strSimd8)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (
  dup8x16 lane32 lane64 lane8 pack4x32)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SimdOps (
  simdAdd8h simdCmltZero8h simdExt16b simdSli2d simdSli4s simdSqdmulh4s
  simdTrn1_4s simdTrn1_8h simdTrn2_4s simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Compress (neonCompress8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Serialize.EncodeHigh (
  lane64_simdExt16b_8_0 neonSerialize10Bytes neonSerialize10Half neonSerialize10Mix)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem SepLoad128 SepStore128 SepWP.of_memRegion_vecRangeMem Vec128At VecRangeMem
  polyVecNat pointsToBytes_eq_vecRangeMem step_ldrQ128 step_ldpQ128 step_strQ128
  vecRangeBytes vecRangeBytes_length vecRangeMem_congr vecRangeMem_entails_memRegion
  vecRangeMem_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (
  entails_sub sepWP_elim_cell8 spAligned_of_sp_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg3SimdSvc (
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8
  svc_simdTrn1_4s svc_simdTrn1_8h svc_simdTrn2_4s svc_simdTrn2_8h)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg5Simd (
  exec_simdAdd_4s exec_simdAnd_16b exec_simdCmltZero_8h exec_simdDup_4s
  exec_simdSqdmulh_4s exec_simdUshr_4s_4 sqdmulh4sFlags)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Base (
  blk03_code_eq blk03_tree_size blkLib03 blkPC03 blkPl03 blkPlaceable03 blkTree03)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg1a (blkPl03_ρ)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg3Cbd (
  sepWP_elim_byte step_bCond_not_taken step_bCond_taken)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Simd (
  cells20_eq_neonSerialize10Bytes exec_simdBic_4s_fc24 exec_simdBic_8h_fc8
  exec_simdDupScalar_b12 exec_simdDupScalar_b4 exec_simdMovi_2d_0 exec_simdShl_4s_10
  exec_simdSli_2d_20 exec_simdSli_4s_10 exec_simdUshr_4s_6 neonCompressSerialize10Poly
  neonCompressSerialize10Poly_length seg6_compress10_eq seg6_serialize10_mix_eq)

section
set_option linter.literalFetch false
gen_placed_fetches blkPC03 blkLib03 blkTree03 blk03_code_eq blk03_tree_size
  via_placement blkPl03 blkPlaceable03 [0x6a78 → 0x6cd4]
end

@[simp, arm64_norm, wp_norm] abbrev offSeg6Start : BitVec 64 := BitVec.ofNat 64 27256
@[simp, arm64_norm, wp_norm] abbrev off6aec      : BitVec 64 := BitVec.ofNat 64 27372
@[simp, arm64_norm, wp_norm] abbrev off6b04      : BitVec 64 := BitVec.ofNat 64 27396
@[simp, arm64_norm, wp_norm] abbrev off6b18      : BitVec 64 := BitVec.ofNat 64 27416
@[simp, arm64_norm, wp_norm] abbrev off6b28      : BitVec 64 := BitVec.ofNat 64 27432
@[simp, arm64_norm, wp_norm] abbrev off6b38      : BitVec 64 := BitVec.ofNat 64 27448
@[simp, arm64_norm, wp_norm] abbrev off6ba4      : BitVec 64 := BitVec.ofNat 64 27556
@[simp, arm64_norm, wp_norm] abbrev off6bb8      : BitVec 64 := BitVec.ofNat 64 27576
@[simp, arm64_norm, wp_norm] abbrev off6c60      : BitVec 64 := BitVec.ofNat 64 27744
@[simp, arm64_norm, wp_norm] abbrev off6ca0      : BitVec 64 := BitVec.ofNat 64 27808
@[simp, arm64_norm, wp_norm] abbrev off6ca4      : BitVec 64 := BitVec.ofNat 64 27812
@[simp, arm64_norm, wp_norm] abbrev off6cbc      : BitVec 64 := BitVec.ofNat 64 27836
@[simp, arm64_norm, wp_norm] abbrev off6cd0      : BitVec 64 := BitVec.ofNat 64 27856
@[simp, arm64_norm, wp_norm] abbrev offSeg6SerEnd : BitVec 64 := BitVec.ofNat 64 27864

theorem blk28_memcpy_03 [MlKemPlacement] (b : BitVec 64) :
    subroutine_ok (blkPC03.rebase b (fun _ => none)) (mlkemMpl.base 28)
      (mlkemMultiLib.withCodeLoaded mlkemMpl mlkemMemcpySpec) :=
  mlkemCall_of_blockOk (blkPC03.rebase b (fun _ => none)) blk28_memcpy_ok

attribute [local irreducible] blkPC03
attribute [local wp_norm ↓ high]
  exec_simdMovi_2d_0 exec_simdBic_4s_fc24 exec_simdBic_8h_fc8
  exec_simdShl_4s_10 exec_simdUshr_4s_6 exec_simdSli_4s_10 exec_simdSli_2d_20
  exec_simdDupScalar_b4 exec_simdDupScalar_b12
  exec_simdAnd_16b exec_simdDup_4s exec_simdCmltZero_8h
  exec_simdUshr_4s_4 exec_simdAdd_4s exec_simdSqdmulh_4s
  svc_simdAdd_8h svc_simdDup_8h_gpr svc_simdExt_16b_8
  svc_simdTrn1_8h svc_simdTrn2_8h svc_simdTrn1_4s svc_simdTrn2_4s

@[expose] def ser10Chunk20 (re : Poly16) (c : Nat) : List (BitVec 8) :=
  neonSerialize10Bytes (neonCompress8h 10 (polyVecNat re (2 * c)))
    (neonCompress8h 10 (polyVecNat re (2 * c + 1)))

@[expose] def ser10PolyPrefix (re : Poly16) (k : Nat) : List (BitVec 8) :=
  ((List.range k).map (ser10Chunk20 re)).flatten

@[simp] theorem ser10PolyPrefix_zero (re : Poly16) : ser10PolyPrefix re 0 = [] := rfl

theorem ser10PolyPrefix_succ (re : Poly16) (k : Nat) :
    ser10PolyPrefix re (k + 1) = ser10PolyPrefix re k ++ ser10Chunk20 re k := by
  unfold ser10PolyPrefix; rw [List.range_succ, List.map_append, List.flatten_append]; simp

@[simp] theorem ser10Chunk20_length (re : Poly16) (c : Nat) :
    (ser10Chunk20 re c).length = 20 := by
  simp [ser10Chunk20, neonSerialize10Bytes, neonSerialize10Half]

@[simp] theorem ser10PolyPrefix_length (re : Poly16) :
    ∀ k : Nat, (ser10PolyPrefix re k).length = 20 * k
  | 0 => rfl
  | k + 1 => by rw [ser10PolyPrefix_succ, List.length_append, ser10PolyPrefix_length re k,
      ser10Chunk20_length]; omega

theorem ser10PolyPrefix_16 (re : Poly16) :
    ser10PolyPrefix re 16 = neonCompressSerialize10Poly re := rfl

private theorem ser10_prefix_append_chunk (dst : BitVec 64) (re : Poly16) (c : Nat) :
    (dst ↦ₛ ser10PolyPrefix re c) ∗
      ((dst + BitVec.ofNat 64 (20 * c)) ↦ₛ ser10Chunk20 re c) =
      (dst ↦ₛ ser10PolyPrefix re (c + 1)) := by
  rw [ser10PolyPrefix_succ, pointsToBytes_append, ser10PolyPrefix_length]

private theorem step_vreg1_sat {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    (b : BitVec 64) (pcOff nextOff : Nat) (rd : BitVec 5) (val : BitVec 128) (fl : BitVec 32)
    {inst : Instr} (hpc : s.pc = b + BitVec.ofNat 64 pcOff) (hrun : s.status = .Running)
    (hfetch : prog.fetch (b + BitVec.ofNat 64 pcOff) = some inst)
    (hexec : execInstWithSvc (evalSvc prog.svc) inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      (((s.setPC (b + BitVec.ofNat 64 pcOff)).writeVReg128 rd val).orFpsr fl).advancePC)
    (hnextOff : pcOff + 4 = nextOff)
    (hnext : SepWP prog target_pc
      (((s.writeVReg128 rd val).orFpsr fl).setPC (b + BitVec.ofNat 64 nextOff)) P post) :
    SepWP prog target_pc s P post := by
  have hpc' : b + BitVec.ofNat 64 pcOff + 4#64 = b + BitVec.ofNat 64 nextOff := by
    subst hnextOff; bv_omega
  have hev : prog.evalInst inst (s.setPC (b + BitVec.ofNat 64 pcOff)) =
      ((s.writeVReg128 rd val).orFpsr fl).setPC (b + BitVec.ofNat 64 nextOff) := by
    unfold Program.evalInst; rw [hexec]
    cases s; simp [State.setPC, State.writeVReg128, State.orFpsr, State.advancePC, hpc']
  exact SepWP.step_pure hpc hrun hfetch hev (by simp [State.orFpsr]) hnext

private theorem sepWP_elim_cell4 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ v : BitVec 32, SepWP prog target s ((a ↦₃₂ v) ∗ R0) post) :
    SepWP prog target s (memRegion a 4 ∗ R0) post := by
  unfold SepWP at h ⊢; intro R hm
  rw [memRegion_four, sepExists_sepConj_left, sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨v, hv⟩ := hm
  exact h v R (by simpa only [sepConj_assoc] using hv)

private theorem sepWP_elim_region5 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w : BitVec 32) (u : BitVec 8),
      SepWP prog target s ((a ↦₃₂ w) ∗ ((a + 4#64) ↦₈ u) ∗ R0) post) :
    SepWP prog target s (memRegion a 5 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 4#64) (n := 4) (k := (1 : Nat)) rfl (by bv_omega) (by decide),
    sepConj_assoc]
  apply sepWP_elim_cell4; intro w
  refine SepWP.weaken_pre (show (a ↦₃₂ w) ∗ (memRegion (a + 4#64) 1 ∗ R0) ⊢
      memRegion (a + 4#64) 1 ∗ ((a ↦₃₂ w) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_byte; intro u
  exact SepWP.weaken_pre (by sep_frame) (h w u)

private theorem sepWP_elim_region10 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 8) (w2 : BitVec 32) (u3 : BitVec 8),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗ ((a + 9#64) ↦₈ u3) ∗ R0) post) :
    SepWP prog target s (memRegion a 10 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 5#64) (n := 5) (k := (5 : Nat)) rfl (by bv_omega) (by decide),
    sepConj_assoc]
  apply sepWP_elim_region5; intro w0 u1
  refine SepWP.weaken_pre (show (a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ (memRegion (a + 5#64) 5 ∗ R0) ⊢
      memRegion (a + 5#64) 5 ∗ ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ R0) by sep_frame) ?_
  apply sepWP_elim_region5; intro w2 u3
  refine SepWP.weaken_pre ?_ (h w0 u1 w2 u3)
  rw [show a + 5#64 + 4#64 = a + 9#64 by bv_omega]; sep_frame

private theorem sepWP_elim_region20 {prog : Program} {target : BitVec 64} {s : State}
    {a : BitVec 64} {R0 : SepProp} {post : State → SepProp → Prop}
    (h : ∀ (w0 : BitVec 32) (u1 : BitVec 8) (w2 : BitVec 32) (u3 : BitVec 8)
        (w4 : BitVec 32) (u5 : BitVec 8) (w6 : BitVec 32) (u7 : BitVec 8),
      SepWP prog target s
        ((a ↦₃₂ w0) ∗ ((a + 4#64) ↦₈ u1) ∗ ((a + 5#64) ↦₃₂ w2) ∗ ((a + 9#64) ↦₈ u3) ∗
         ((a + 10#64) ↦₃₂ w4) ∗ ((a + 14#64) ↦₈ u5) ∗ ((a + 15#64) ↦₃₂ w6) ∗
         ((a + 19#64) ↦₈ u7) ∗ R0) post) :
    SepWP prog target s (memRegion a 20 ∗ R0) post := by
  rw [memRegion_split' (b' := a + 10#64) (n := 10) (k := (10 : Nat)) rfl (by bv_omega) (by decide),
    sepConj_assoc]
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

private theorem step_vreg1 {prog : Program} {target_pc : BitVec 64}
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

@[simp] private theorem setWidth8_zext128 (x : BitVec 8) :
    (x.zeroExtend 128).setWidth 8 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

@[simp] private theorem low32_eq_lane64_0 (v : BitVec 128) :
    v.extractLsb' 0 32 = (lane64 v 0).truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [lane64, hi]

@[simp] private theorem ext8_self_low32 (m : BitVec 128) :
    (lane64 (m.truncate 64 ++ m.extractLsb' 64 64) 0).truncate 32 =
      (lane64 (simdExt16b m m 8) 0).truncate 32 := by
  rw [lane64_simdExt16b_8_0]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [lane64, show i < 64 by omega, hi]

private theorem step_strS32_off {prog : Program} {target_pc : BitVec 64}
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

private theorem step_strB8_off {prog : Program} {target_pc : BitVec 64}
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
  have hsp : checkAddrSPAligned s (.Offset ptrReg (BitVec.ofNat 64 off)) = true := by
    cases ptrReg <;> simp_all [checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned]
  exact step_strSimd8 (wb := none) hpc hrun hfetch hsp (by simp [evalAddrMode, hea]) hv hstore
    (by simp [applyWriteback, hpc']) hnext

@[simp, arm64_norm, wp_norm] private theorem sp_writeV' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).sp = s.sp := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_writeV' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_writeV' (s : State) (v : BitVec 5) (w : BitVec 128) : (s.writeVReg128 v w).pstate = s.pstate := rfl
@[simp, arm64_norm, wp_norm] private theorem readReg64_writeV' (s : State) (v : BitVec 5) (w : BitVec 128) (r : Reg) : (s.writeVReg128 v w).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp, arm64_norm, wp_norm] private theorem pc_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pc = s.pc := rfl
@[simp, arm64_norm, wp_norm] private theorem sp_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).sp = s.sp := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).pstate = s.pstate := rfl
@[simp, arm64_norm, wp_norm] private theorem status_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := rfl
@[simp, arm64_norm, wp_norm] private theorem mem_orFpsr' (s : State) (f : BitVec 32) : (s.orFpsr f).mem = s.mem := rfl
@[simp, arm64_norm, wp_norm] private theorem readReg64_orFpsr' (s : State) (f : BitVec 32) (r : Reg) : (s.orFpsr f).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp, arm64_norm, wp_norm] private theorem readVReg128_orFpsr' (s : State) (f : BitVec 32) (v : BitVec 5) : (s.orFpsr f).readVReg128 v = s.readVReg128 v := rfl
@[simp, arm64_norm, wp_norm] private theorem readReg64_setPC' (s : State) (pc : BitVec 64) (r : Reg) : (s.setPC pc).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp, arm64_norm, wp_norm] private theorem readReg64_setMem' (s : State) (m : Memory) (r : Reg) : (s.setMem m).readReg64 r = s.readReg64 r := by cases r <;> rfl
@[simp, arm64_norm, wp_norm] private theorem readVReg128_setMem' (s : State) (m : Memory) (v : BitVec 5) : (s.setMem m).readVReg128 v = s.readVReg128 v := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_setMem' (s : State) (m : Memory) : (s.setMem m).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_setPState' (s : State) (p : PState) : (s.setPState p).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem spA_writeGPR' (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).spAligned = s.spAligned := rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_setPC' (s : State) (pc : BitVec 64) : (s.setPC pc).pstate = s.pstate := rfl
@[simp, arm64_norm, wp_norm] private theorem pstate_writeGPR' (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeReg64 (.gpr i) v).pstate = s.pstate := rfl

@[expose] def Seg6ConstsMem (sp : BitVec 64) : SepProp :=
  Vec128At (sp + 2128#64) (pack4x32 fun _ => 10321340#32) ∗
  Vec128At (sp + 2144#64) (pack4x32 fun _ => 1664#32) ∗
  Vec128At (sp + 2160#64) (pack4x32 fun _ => 67107840#32) ∗
  Vec128At (sp + 2176#64) (dup8x16 3329#16)

theorem seg6ConstsMem_entails_memRegion (sp : BitVec 64) :
    Seg6ConstsMem sp ⊢ memRegion (sp + 2128#64) 64 := by
  have h : Seg6ConstsMem sp = VecRangeMem 4 (sp + 2128#64)
      (fun i => match i with
        | 0 => pack4x32 fun _ => 10321340#32
        | 1 => pack4x32 fun _ => 1664#32
        | 2 => pack4x32 fun _ => 67107840#32
        | _ => dup8x16 3329#16) := by
    dsimp only [Seg6ConstsMem, VecRangeMem]
    simp only [show (sp + 2128#64) + 16#64 = sp + 2144#64 by bv_omega,
      show (sp + 2144#64) + 16#64 = sp + 2160#64 by bv_omega,
      show (sp + 2160#64) + 16#64 = sp + 2176#64 by bv_omega, sepConj_emp]
  rw [h]; simpa using vecRangeMem_entails_memRegion 4 (sp + 2128#64) _

theorem poly3_eq_pointsToBytes (ptr : BitVec 64) (p0 p1 p2 : Poly16) :
    PolyMem ptr (polyVecNat p0) ∗
      PolyMem (ptr + 512#64) (polyVecNat p1) ∗
      PolyMem (ptr + 1024#64) (polyVecNat p2) =
      (ptr ↦ₛ (vecRangeBytes 32 (polyVecNat p0) ++
        vecRangeBytes 32 (polyVecNat p1) ++
        vecRangeBytes 32 (polyVecNat p2))) := by
  dsimp only [PolyMem]
  rw [pointsToBytes_append, pointsToBytes_append, ← sepConj_assoc,
    vecRangeBytes_length, List.length_append, vecRangeBytes_length, vecRangeBytes_length,
    show ptr + BitVec.ofNat 64 (16 * 32) = ptr + 512#64 by bv_omega,
    show ptr + BitVec.ofNat 64 (16 * 32 + 16 * 32) = ptr + 1024#64 by bv_omega,
    ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes, ← vecRangeMem_eq_pointsToBytes,
    sepConj_assoc]

@[expose] def Seg6OuterRegs (sp : BitVec 64) (row : Nat) (s : State) : Prop :=
  s.readReg64 .x19 = sp + 2192#64 ∧
  s.readReg64 .x20 = BitVec.ofNat 64 row ∧
  s.readReg64 .x21 = sp + 15680#64 ∧
  s.readReg64 .x22 = sp + 16528#64 ∧
  s.readReg64 .x23 = sp + 4288#64 ∧
  s.readReg64 (.gpr 25#5) = sp + 11440#64

theorem seg6_setup [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) (u0 u1 u2 : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + offSeg6Start) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hspA : s.spAligned = true)
    (hcl : mlkemMultiLib.CodeLoaded mlkemMpl s.mem) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6aec) s
      (memRegion (sp + 2128#64) 64 ∗
        PolyMem (sp + 2192#64) (polyVecNat u0) ∗
        PolyMem (sp + 2704#64) (polyVecNat u1) ∗
        PolyMem (sp + 3216#64) (polyVecNat u2) ∗
        memRegion (sp + 4288#64) 1544 ∗ Rest)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧ Seg6OuterRegs sp 0 sf ∧
        (Pf ⊢ Seg6ConstsMem sp ∗ memRegion (sp + 2192#64) 1536 ∗
          PolyMem (sp + 4288#64) (polyVecNat u0) ∗
          PolyMem (sp + 4800#64) (polyVecNat u1) ∗
          PolyMem (sp + 5312#64) (polyVecNat u2) ∗
          memRegion (sp + 5824#64) 8 ∗ Rest)) := by
  subst hbase
  let uBytes := vecRangeBytes 32 (polyVecNat u0) ++ vecRangeBytes 32 (polyVecNat u1) ++
    vecRangeBytes 32 (polyVecNat u2)
  have hu_len : uBytes.length = 1536 := by simp [uBytes]
  have hp_src := poly3_eq_pointsToBytes (sp + 2192#64) u0 u1 u2
  have hp_dst := poly3_eq_pointsToBytes (sp + 4288#64) u0 u1 u2
  simp only [show (sp + 2192#64) + 512#64 = sp + 2704#64 by bv_omega,
    show (sp + 2192#64) + 1024#64 = sp + 3216#64 by bv_omega] at hp_src
  simp only [show (sp + 4288#64) + 512#64 = sp + 4800#64 by bv_omega,
    show (sp + 4288#64) + 1024#64 = sp + 5312#64 by bv_omega] at hp_dst
  rw [memRegion_split' (b := sp + 4288#64) (b' := sp + 5824#64) (n := 1536) (k := (8 : Nat))
        rfl (by bv_omega) (by decide)]
  have hp_src' :
      PolyMem (sp + 2192#64) (polyVecNat u0) ∗ PolyMem (sp + 2704#64) (polyVecNat u1) ∗
        PolyMem (sp + 3216#64) (polyVecNat u2) ⊢ (sp + 2192#64) ↦ₛ uBytes := by
    rw [hp_src]; exact Entails.refl _
  refine SepWP.weaken_pre (show _ ⊢ ((sp + 2192#64) ↦ₛ uBytes) ∗
      memRegion (sp + 4288#64) uBytes.length ∗
      (memRegion (sp + 2128#64) 64 ∗ memRegion (sp + 5824#64) 8 ∗ Rest) by
      rw [hu_len]; exact entails_sub hp_src' (by sep_frame) (by sep_frame)) ?_
  wp_steps 7; wp_step
  apply seq_codeLoaded_lr ‹_›
  wp_call (blk28_memcpy_03 blkPl03.base) (sp + 4288#64, sp + 2192#64, uBytes)
  apply SepWP.done (by assumption) (by assumption); intro _
  have hsp_sf' : sf.sp = sp := hsp_sf.trans hsp
  have hspA_sf : sf.spAligned = true := spAligned_of_sp_eq hspA hsp hsp_sf'
  refine SepWP.of_memRegion_vecRangeMem 4 (sp + 2128#64) (by decide) (by sep_focus) fun fc => ?_
  dsimp only [VecRangeMem, Vec128At]
  simp only [show (sp + 2128#64) + 16#64 = sp + 2144#64 by bv_omega,
    show (sp + 2144#64) + 16#64 = sp + 2160#64 by bv_omega,
    show (sp + 2160#64) + 16#64 = sp + 2176#64 by bv_omega,
    show (sp + 2128#64) + 8#64 = sp + 2136#64 by bv_omega,
    show (sp + 2144#64) + 8#64 = sp + 2152#64 by bv_omega,
    show (sp + 2160#64) + 8#64 = sp + 2168#64 by bv_omega,
    show (sp + 2176#64) + 8#64 = sp + 2184#64 by bv_omega, sepConj_emp]
  sep_frame_apply (sepWP_elim_cell8 (a := sp + 5824#64)); intro w5824
  wp_steps 21
  refine SepWP.done (by wp_norm_lhs) (by simp [hrun_sf])
    ⟨by simp [hsp_sf'], by simpa [State.spAligned, hsp_sf'] using hspA_sf,
      ⟨by simp [‹sf.readReg64 .x19 = _›], by simp,
       by simp, by simp,
       by simp [‹sf.readReg64 .x23 = _›],
       by simp⟩, ?_⟩
  have hm_u : ((sp + 2192#64) ↦ₛ uBytes) ⊢ memRegion (sp + 2192#64) 1536 := by
    simpa [hu_len] using pointsToBytes_entails_memRegion (sp + 2192#64) uBytes
  have hm_8 : ((sp + 5824#64) ↦₆₄ 0#64) ⊢ memRegion (sp + 5824#64) 8 := by
    rw [pointsTo64_eq_pointsToBytes]; simpa using pointsToBytes_entails_memRegion (sp + 5824#64) (unpack64 0#64)
  dsimp only [Seg6ConstsMem, Vec128At]
  simp only [show (sp + 2128#64) + 8#64 = sp + 2136#64 by bv_omega,
    show (sp + 2144#64) + 8#64 = sp + 2152#64 by bv_omega,
    show (sp + 2160#64) + 8#64 = sp + 2168#64 by bv_omega,
    show (sp + 2176#64) + 8#64 = sp + 2184#64 by bv_omega]
  have hd_ent : ((sp + 4288#64) ↦ₛ uBytes) ⊢
      PolyMem (sp + 4288#64) (polyVecNat u0) ∗ PolyMem (sp + 4800#64) (polyVecNat u1) ∗
        PolyMem (sp + 5312#64) (polyVecNat u2) := by
    rw [hp_dst]; exact Entails.refl _
  exact entails_sub hm_u (by sep_frame)
    (entails_sub hm_8 (by sep_frame)
      (entails_sub hd_ent (by sep_frame) (by sep_frame)))

@[expose] def c10321340Vec : BitVec 128 := pack4x32 fun _ => 10321340#32
@[expose] def c1664Vec     : BitVec 128 := pack4x32 fun _ => 1664#32
@[expose] def c67107840Vec : BitVec 128 := pack4x32 fun _ => 67107840#32
@[expose] def c3329Vec     : BitVec 128 := dup8x16 3329#16

@[simp, arm64_norm, wp_norm] private abbrev off6c30 : BitVec 64 := BitVec.ofNat 64 27696

private theorem seg6_compress_eq (vn : BitVec 128) :
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

private theorem inner_addr_ldp (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + 2192#64) + BitVec.ofNat 64 (16 * (2 * c)) =
      (sp + BitVec.ofNat 64 (2208 + 32 * c)) + 0xfffffffffffffff0#64 := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

private theorem inner_addr_ldp1 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + 2192#64) + BitVec.ofNat 64 (16 * (2 * c + 1)) =
      ((sp + BitVec.ofNat 64 (2208 + 32 * c)) + 0xfffffffffffffff0#64) + 16#64 := by
  rw [← inner_addr_ldp sp hc]
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

private theorem inner_addr_x8 {c : Nat} (hc : c < 16) :
    (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) + 20#64 =
      0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals decide

private theorem inner_addr_x9 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + BitVec.ofNat 64 (2208 + 32 * c)) + 32#64 = sp + BitVec.ofNat 64 (2208 + 32 * (c + 1)) := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals simp [BitVec.add_assoc]

private theorem inner_addr_x10 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    (sp + 16528#64) + (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) =
      (sp + 16528#64) + BitVec.ofNat 64 (20 * c) - 320#64 := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals (clear * -; bv_omega)

private theorem inner_addr_x11 (sp : BitVec 64) {c : Nat} (hc : c < 16) :
    ((sp + 16528#64) + (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))) + 330#64 =
      (sp + 16528#64) + BitVec.ofNat 64 (20 * c) + 10#64 := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> try omega
  all_goals (clear * -; bv_omega)

section InnerCompress
attribute [local irreducible]
  c10321340Vec c1664Vec c67107840Vec c3329Vec polyVecNat neonCompress8h
  dup8x16 pack4x32 lane32 simdAdd8h simdCmltZero8h simdSqdmulh4s simdTrn1_8h

@[simp, arm64_norm, wp_norm] private abbrev off6c00 : BitVec 64 := BitVec.ofNat 64 27648

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

private def compressEvIn (vn : BitVec 128) : BitVec 128 :=
  let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
  pack4x32 fun k =>
    lane32 ((pack4x32 fun j => lane32 u0 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) k +
      lane32 c1664Vec k

private def compressOdIn (vn : BitVec 128) : BitVec 128 :=
  let u0 := simdAdd8h (simdCmltZero8h vn &&& c3329Vec) vn
  pack4x32 fun k =>
    lane32 ((pack4x32 fun j => lane32 u0 j >>> 6) &&& c67107840Vec) k + lane32 c1664Vec k

private theorem seg6_inner_pre [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6ba4) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * c))
    (hx22 : s.readReg64 .x22 = sp + 16528#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6c00) s
      (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.spAligned = s.spAligned ∧
        sm.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        sm.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        sm.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * (c + 1)) ∧
        sm.readReg64 .x10 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) - 320#64 ∧
        sm.readReg64 .x11 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) + 10#64 ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → sm.readReg64 r = s.readReg64 r) ∧
        sm.readVReg128 2#5 = compressEvIn (polyVecNat u (2 * c)) ∧
        sm.readVReg128 0#5 = compressOdIn (polyVecNat u (2 * c)) ∧
        sm.readVReg128 3#5 = compressEvIn (polyVecNat u (2 * c + 1)) ∧
        sm.readVReg128 1#5 = compressOdIn (polyVecNat u (2 * c + 1)) ∧
        sm.readVReg128 5#5 = c3329Vec ∧ sm.readVReg128 6#5 = c67107840Vec ∧
        sm.readVReg128 7#5 = c1664Vec ∧ sm.readVReg128 16#5 = c10321340Vec ∧
        Pm = (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)) := by
  subst hbase
  refine step_ldpQ128
    (s' := ((s.writeVReg128 0#5 (polyVecNat u (2 * c))).writeVReg128 1#5
      (polyVecNat u (2 * c + 1))).setPC (blkPl03.base + BitVec.ofNat 64 27560))
    (vt1 := 0#5) (vt2 := 1#5) (addr := .Offset .x9 0xfffffffffffffff0#64) (wb := none)
    hpc hrun (by simp only [arm64_norm]; rfl) rfl (by simp [evalAddrMode, hx9]) rfl
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c < 32) (inner_addr_ldp sp hc)))
    (SepLoad128.left (SepLoad128.vecRange (by omega : 2 * c + 1 < 32) (inner_addr_ldp1 sp hc)))
    (by simp [applyWriteback, off6ba4]) ?_
  let w0 := polyVecNat u (2 * c)
  let w1 := polyVecNat u (2 * c + 1)
  let u0 := simdAdd8h (simdCmltZero8h w0 &&& c3329Vec) w0
  let u1 := simdAdd8h (simdCmltZero8h w1 &&& c3329Vec) w1
  wp_steps 4
  refine step_vreg1 blkPl03.base 27576 27580 2#5 (simdCmltZero8h w0) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdCmltZero_8h]; simp [w0]) rfl ?_
  refine step_vreg1 blkPl03.base 27580 27584 3#5 (simdCmltZero8h w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdCmltZero_8h]; simp [w1]) rfl ?_
  refine step_vreg1 blkPl03.base 27584 27588 2#5 (simdCmltZero8h w0 &&& c3329Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv5]) rfl ?_
  refine step_vreg1 blkPl03.base 27588 27592 3#5 (simdCmltZero8h w1 &&& c3329Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv5]) rfl ?_
  refine step_vreg1 blkPl03.base 27592 27596 0#5 u0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdAdd_8h]; simp [u0, w0]) rfl ?_
  refine step_vreg1 blkPl03.base 27596 27600 1#5 u1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdAdd_8h]; simp [u1, w1]) rfl ?_
  refine step_vreg1 blkPl03.base 27600 27604 2#5 (pack4x32 fun j => lane32 u0 j <<< 10) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdShl_4s_10]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27604 27608 0#5 (pack4x32 fun j => lane32 u0 j >>> 6) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_6]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27608 27612 3#5 (pack4x32 fun j => lane32 u1 j <<< 10) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdShl_4s_10]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27612 27616 1#5 (pack4x32 fun j => lane32 u1 j >>> 6) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_6]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27616 27620 2#5 ((pack4x32 fun j => lane32 u0 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_4s_fc24]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27620 27624 0#5 ((pack4x32 fun j => lane32 u0 j >>> 6) &&& c67107840Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv6]) rfl ?_
  refine step_vreg1 blkPl03.base 27624 27628 3#5 ((pack4x32 fun j => lane32 u1 j <<< 10) &&& 0x03ffffff03ffffff03ffffff03ffffff#128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_4s_fc24]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27628 27632 1#5 ((pack4x32 fun j => lane32 u1 j >>> 6) &&& c67107840Vec) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAnd_16b]; simp [hv6]) rfl ?_
  refine step_vreg1 blkPl03.base 27632 27636 2#5 (compressEvIn w0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressEvIn, u0]) rfl ?_
  refine step_vreg1 blkPl03.base 27636 27640 0#5 (compressOdIn w0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressOdIn, u0]) rfl ?_
  refine step_vreg1 blkPl03.base 27640 27644 3#5 (compressEvIn w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressEvIn, u1]) rfl ?_
  refine step_vreg1 blkPl03.base 27644 27648 1#5 (compressOdIn w1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdAdd_4s]; simp [hv7, compressOdIn, u1]) rfl ?_
  refine SepWP.done rfl (by simp [hrun]) ⟨by simp [hsp], ?_, by simp,
    by simp [inner_addr_x8 hc], by simp [inner_addr_x9 sp hc],
    by simp [inner_addr_x10 sp hc], by simp [inner_addr_x11 sp hc],
    fun r h8 h9 h10 h11 => ?_,
    by simp [w0], by simp [w0], by simp [w1], by simp [w1],
    by simp [hv5], by simp [hv6], by simp [hv7], by simp [hv16], rfl⟩
  · simp only [spA_setPC', spA_writeV', spA_setPState', spA_writeGPR']
  · simp only [readReg64_setPC', readReg64_writeV']
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

private theorem seg6_inner_mul [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (ev0 od0 ev1 od1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + off6c00) (hrun : s.status = .Running)
    (hv2 : s.readVReg128 2#5 = ev0) (hv0 : s.readVReg128 0#5 = od0)
    (hv3 : s.readVReg128 3#5 = ev1) (hv1 : s.readVReg128 1#5 = od1)
    (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6c30) s P
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
  refine step_sqdmulh4s blkPl03.base 27648 27652 16#5 2#5 2#5 ev0 c10321340Vec
    hpc hrun (by simp only [arm64_norm]) hv2 hv16 rfl ?_
  refine step_sqdmulh4s blkPl03.base 27652 27656 16#5 0#5 0#5 od0 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv0]) (by simp [hv16]) rfl ?_
  refine step_sqdmulh4s blkPl03.base 27656 27660 16#5 3#5 3#5 ev1 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv3]) (by simp [hv16]) rfl ?_
  refine step_sqdmulh4s blkPl03.base 27660 27664 16#5 1#5 1#5 od1 c10321340Vec
    rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hv1]) (by simp [hv16]) rfl ?_
  refine step_vreg1 blkPl03.base 27664 27668 2#5 m2 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m2]) rfl ?_
  refine step_vreg1 blkPl03.base 27668 27672 0#5 m0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m0]) rfl ?_
  refine step_vreg1 blkPl03.base 27672 27676 3#5 m3 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m3]) rfl ?_
  refine step_vreg1 blkPl03.base 27676 27680 1#5 m1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdUshr_4s_4]; simp [m1]) rfl ?_
  refine step_vreg1 blkPl03.base 27680 27684 0#5 (simdTrn1_8h m2 m0) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27684 27688 1#5 (simdTrn1_8h m3 m1) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdTrn1_8h]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27688 27692 0#5 (simdTrn1_8h m2 m0 &&& dup8x16 0x03ff#16) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_8h_fc8]; simp) rfl ?_
  refine step_vreg1 blkPl03.base 27692 27696 1#5 (simdTrn1_8h m3 m1 &&& dup8x16 0x03ff#16) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdBic_8h_fc8]; simp) rfl ?_
  exact SepWP.done rfl (by simp [hrun])
    ⟨by simp, by simp only [spA_setPC', spA_writeV', spA_orFpsr'], by simp,
      fun r => by simp only [readReg64_setPC', readReg64_writeV', readReg64_orFpsr'],
      by simp [m2, m0], by simp [m3, m1], by simp, by simp, by simp, by simp [hv16], rfl⟩

end InnerCompress

private theorem seg6_compress_evod_eq (vn : BitVec 128) :
    simdTrn1_8h
      (pack4x32 fun k => lane32 (simdSqdmulh4s (compressEvIn vn) c10321340Vec) k >>> 4)
      (pack4x32 fun k => lane32 (simdSqdmulh4s (compressOdIn vn) c10321340Vec) k >>> 4) &&&
      dup8x16 0x03ff#16 = neonCompress8h 10 vn :=
  seg6_compress_eq vn

section Tail16
attribute [local irreducible]
  c10321340Vec c1664Vec c67107840Vec c3329Vec neonCompress8h neonSerialize10Mix
  polyVecNat simdExt16b compressEvIn compressOdIn
  simdTrn1_8h simdTrn2_8h simdSli4s simdTrn1_4s simdTrn2_4s simdSli2d

private theorem seg6_inner_compress [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6ba4) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * c))
    (hx22 : s.readReg64 .x22 = sp + 16528#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6c30) s
      (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        s1.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        s1.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * (c + 1)) ∧
        s1.readReg64 .x10 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) - 320#64 ∧
        s1.readReg64 .x11 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) + 10#64 ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s1.readReg64 r = s.readReg64 r) ∧
        s1.readVReg128 0#5 = neonCompress8h 10 (polyVecNat u (2 * c)) ∧
        s1.readVReg128 1#5 = neonCompress8h 10 (polyVecNat u (2 * c + 1)) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c67107840Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)) := by
  refine SepWP.seq
    (seg6_inner_pre hb hbase s sp hc u Rest hpc hrun hsp hx8 hx9 hx22 hv5 hv6 hv7 hv16) ?_
  rintro sm Pm hpcm hrunm ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hregsm,
    hv2m, hv0m, hv3m, hv1m, hv5m, hv6m, hv7m, hv16m, hPm⟩
  refine SepWP.mono (seg6_inner_mul hb hbase sm _ _ _ _ Pm hpcm hrunm hv2m hv0m hv3m hv1m hv16m) ?_
  rintro s1 P1 _ _ ⟨hsp1, hspA1, hpst1, hregs1, hv0_1, hv1_1, hv5_1, hv6_1, hv7_1, hv16_1, hP1⟩
  exact ⟨hsp1.trans hspm, hspA1.trans hspAm, hpst1.trans hpstm,
    (hregs1 .x8).trans hx8m, (hregs1 .x9).trans hx9m,
    (hregs1 .x10).trans hx10m, (hregs1 .x11).trans hx11m,
    fun r h8 h9 h10 h11 => (hregs1 r).trans (hregsm r h8 h9 h10 h11),
    hv0_1.trans (seg6_compress_evod_eq _), hv1_1.trans (seg6_compress_evod_eq _),
    hv5_1.trans hv5m, hv6_1.trans hv6m, hv7_1.trans hv7m, hv16_1, hP1.trans hPm⟩

private theorem seg6_inner_mix [MlKemPlacement] {b : BitVec 64}
    (_hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (v0 v1 : BitVec 128) (P : SepProp)
    (hpc : s.pc = b + off6c30) (hrun : s.status = .Running)
    (hc0 : s.readVReg128 0#5 = neonCompress8h 10 v0)
    (hc1 : s.readVReg128 1#5 = neonCompress8h 10 v1) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6c60) s P
      (fun s2 P2 =>
        s2.sp = s.sp ∧ s2.spAligned = s.spAligned ∧ s2.pstate = s.pstate ∧
        (∀ r : Reg, s2.readReg64 r = s.readReg64 r) ∧
        s2.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 v0) ∧
        s2.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 v1) ∧
        s2.readVReg128 5#5 = s.readVReg128 5#5 ∧ s2.readVReg128 6#5 = s.readVReg128 6#5 ∧
        s2.readVReg128 7#5 = s.readVReg128 7#5 ∧ s2.readVReg128 16#5 = s.readVReg128 16#5 ∧
        P2 = P) := by
  subst hbase
  wp_steps 12
  exact SepWP.done (by wp_norm_lhs)
    (by conv => lhs; simp only [wp_norm, arm64_norm]
        exact hrun)
    ⟨by conv => lhs; simp only [wp_norm, arm64_norm],
      by simp only [spA_setPC', spA_writeV'],
      by conv => lhs; simp only [wp_norm, arm64_norm],
      fun r => by simp only [readReg64_setPC', readReg64_writeV'],
      by conv => lhs; simp only [wp_norm, arm64_norm, hc0]
         exact seg6_serialize10_mix_eq v0,
      by conv => lhs; simp only [wp_norm, arm64_norm, hc1]
         exact seg6_serialize10_mix_eq v1,
      by conv => lhs; simp only [wp_norm, arm64_norm],
      by conv => lhs; simp only [wp_norm, arm64_norm],
      by conv => lhs; simp only [wp_norm, arm64_norm],
      by conv => lhs; simp only [wp_norm, arm64_norm], rfl⟩

theorem seg6_inner_simd [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl03 b) (hbase : blkPl03.base = b)
    (s : State) (sp : BitVec 64) {c : Nat} (hc : c < 16) (u : Poly16) (Rest : SepProp)
    (hpc : s.pc = b + off6ba4) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx8 : s.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c))
    (hx9 : s.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * c))
    (hx22 : s.readReg64 .x22 = sp + 16528#64)
    (hv5 : s.readVReg128 5#5 = c3329Vec) (hv6 : s.readVReg128 6#5 = c67107840Vec)
    (hv7 : s.readVReg128 7#5 = c1664Vec) (hv16 : s.readVReg128 16#5 = c10321340Vec) :
    SepWP (blkPC03.rebase b (fun _ => none)) (b + off6c60) s
      (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)
      (fun s1 P1 =>
        s1.sp = sp ∧ s1.spAligned = s.spAligned ∧
        s1.pstate = addsPState64 (0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * c)) 20#64 ∧
        s1.readReg64 .x8 = 0xfffffffffffffec0#64 + BitVec.ofNat 64 (20 * (c + 1)) ∧
        s1.readReg64 .x9 = sp + BitVec.ofNat 64 (2208 + 32 * (c + 1)) ∧
        s1.readReg64 .x10 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) - 320#64 ∧
        s1.readReg64 .x11 = (sp + 16528#64) + BitVec.ofNat 64 (20 * c) + 10#64 ∧
        (∀ r : Reg, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s1.readReg64 r = s.readReg64 r) ∧
        s1.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c))) ∧
        s1.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat u (2 * c + 1))) ∧
        s1.readVReg128 5#5 = c3329Vec ∧ s1.readVReg128 6#5 = c67107840Vec ∧
        s1.readVReg128 7#5 = c1664Vec ∧ s1.readVReg128 16#5 = c10321340Vec ∧
        P1 = (PolyMem (sp + 2192#64) (polyVecNat u) ∗ Rest)) := by
  refine SepWP.seq
    (seg6_inner_compress hb hbase s sp hc u Rest hpc hrun hsp hx8 hx9 hx22 hv5 hv6 hv7 hv16) ?_
  rintro sm Pm hpcm hrunm ⟨hspm, hspAm, hpstm, hx8m, hx9m, hx10m, hx11m, hregsm, hc0, hc1,
    hv5m, hv6m, hv7m, hv16m, rfl⟩
  refine SepWP.mono (seg6_inner_mix hb hbase sm _ _ _ hpcm hrunm hc0 hc1) ?_
  rintro sf Pf _ _ ⟨hspf, hspAf, hpstf, hregsf, hv0f, hv2f, hv5f, hv6f, hv7f, hv16f, rfl⟩
  exact ⟨hspf.trans hspm, hspAf.trans hspAm, hpstf.trans hpstm,
    (hregsf .x8).trans hx8m, (hregsf .x9).trans hx9m,
    (hregsf .x10).trans hx10m, (hregsf .x11).trans hx11m,
    fun r h8 h9 h10 h11 => (hregsf r).trans (hregsm r h8 h9 h10 h11),
    hv0f, hv2f, hv5f.trans hv5m, hv6f.trans hv6m, hv7f.trans hv7m, hv16f.trans hv16m, rfl⟩

theorem step_ser10_tail16 [MlKemPlacement] {b target_pc dst : BitVec 64}
    {s : State} {re : Poly16} {F : SepProp} {post : State → SepProp → Prop}
    (c : Nat) (hc16 : c < 16)
    (hpc : s.pc = b + off6c60) (hrun : s.status = .Running)
    (hx10 : s.readReg64 .x10 = dst + BitVec.ofNat 64 (20 * c) - 320#64)
    (hx11 : s.readReg64 .x11 = dst + BitVec.ofNat 64 (20 * c) + 10#64)
    (hv0 : s.readVReg128 0#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat re (2 * c))))
    (hv2 : s.readVReg128 2#5 = neonSerialize10Mix (neonCompress8h 10 (polyVecNat re (2 * c + 1))))
    (hnext : ∀ s' : State,
      s'.pc = b + off6ca0 → s'.status = .Running →
      s'.sp = s.sp ∧ s'.spAligned = s.spAligned ∧ s'.pstate = s.pstate →
      (∀ r : Reg, r ≠ .x11 → s'.readReg64 r = s.readReg64 r) →
      s'.readVReg128 5#5 = s.readVReg128 5#5 ∧ s'.readVReg128 6#5 = s.readVReg128 6#5 ∧
      s'.readVReg128 7#5 = s.readVReg128 7#5 ∧ s'.readVReg128 16#5 = s.readVReg128 16#5 →
      SepWP (blkPC03.rebase b (fun _ => none)) target_pc s'
        ((dst ↦ₛ ser10PolyPrefix re (c + 1)) ∗
          memRegion (dst + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) ∗ F) post) :
    SepWP (blkPC03.rebase b (fun _ => none)) target_pc s
      ((dst ↦ₛ ser10PolyPrefix re c) ∗
        memRegion (dst + BitVec.ofNat 64 (20 * c)) (320 - 20 * c) ∗ F) post := by
  let ea := dst + BitVec.ofNat 64 (20 * c)
  let c0 := neonCompress8h 10 (polyVecNat re (2 * c))
  let c1 := neonCompress8h 10 (polyVecNat re (2 * c + 1))
  let m0 := neonSerialize10Mix c0; let m1 := neonSerialize10Mix c1
  let e0 := m0.truncate 64 ++ m0.extractLsb' 64 64
  let e1 := m1.truncate 64 ++ m1.extractLsb' 64 64
  have hsplit : memRegion ea (320 - 20 * c) =
      memRegion ea 20 ∗ memRegion (dst + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) := by
    have hm := memRegion_split ea 20 (320 - 20 * (c + 1)) (by omega)
    have ha : ea + BitVec.ofNat 64 20 = dst + BitVec.ofNat 64 (20 * (c + 1)) := by
      dsimp only [ea]; clear * -; bv_omega
    rw [show 20 + (320 - 20 * (c + 1)) = 320 - 20 * c by omega, ha] at hm; exact hm
  refine SepWP.weaken_pre
    (show (dst ↦ₛ ser10PolyPrefix re c) ∗ memRegion ea (320 - 20 * c) ∗ F ⊢
      memRegion ea 20 ∗ ((dst ↦ₛ ser10PolyPrefix re c) ∗
        memRegion (dst + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) ∗ F) by
      rw [hsplit]; sep_frame) ?_
  apply sepWP_elim_region20; intro w0 u1 w2 u3 w4 u5 w6 u7
  refine step_vreg1 b 27744 27748 1#5 ((lane8 m0 4).zeroExtend 128) hpc hrun (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b4]; simp [hv0, m0, c0]) rfl ?_
  refine step_vreg1 b 27748 27752 4#5 e0 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdExt_16b_8]; simp [hv0, e0, m0, c0]) rfl ?_
  refine step_vreg1 b 27752 27756 3#5 ((lane8 m0 12).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b12]; simp [hv0, m0, c0]) rfl ?_
  refine step_strS32_off b (ea - 320#64) 27756 27760 320 0#5 .x10 ((lane64 m0 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, ea]) (by simp [hv0, m0, c0, low32_eq_lane64_0])
    (SepStore32.left (SepStore32.here (by clear * -; bv_omega))) rfl ?_; intro mem1
  refine step_vreg1 b 27760 27764 0#5 ((lane8 m1 4).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b4]; simp [hv2, m1, c1]) rfl ?_
  refine step_strS32_off b (ea + 10#64) 27764 27768 0 2#5 .x11 ((lane64 m1 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx11, ea]) (by simp [hv2, m1, c1, low32_eq_lane64_0])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega)))))))
    rfl ?_; intro mem2
  wp_step
  refine step_strB8_off b (ea - 320#64) 27772 27776 324 1#5 .x10 (lane8 m0 4)
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, ea]) (by simp)
    (SepStore8.right (SepStore8.left (SepStore8.here (by clear * -; bv_omega)))) rfl ?_; intro mem3
  refine step_vreg1 b 27776 27780 1#5 ((lane8 m1 12).zeroExtend 128) rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [exec_simdDupScalar_b12]; simp [hv2, m1, c1]) rfl ?_
  refine step_vreg1 b 27780 27784 2#5 e1 rfl (by simp [hrun]) (by simp only [arm64_norm]; rfl) (by rw [svc_simdExt_16b_8]; simp [hv2, e1, m1, c1]) rfl ?_
  refine step_strS32_off b (ea + 5#64) 27784 27788 0 4#5 .x11 ((lane64 (simdExt16b m0 m0 8) 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [ea]) (by simp [e0, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega))))) rfl ?_; intro mem4
  wp_step
  refine step_strB8_off b (ea - 320#64) 27792 27796 329 3#5 .x10 (lane8 m0 12)
    (by decide) (by wp_norm_lhs) (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, ea]) (by simp)
    (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (by clear * -; bv_omega)))))) rfl ?_; intro mem5
  refine step_strB8_off b (ea - 320#64) 27796 27800 334 0#5 .x10 (lane8 m1 4)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, ea]) (by simp)
    (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (by clear * -; bv_omega)))))))) rfl ?_; intro mem6
  refine step_strB8_off b (ea - 320#64) 27800 27804 339 1#5 .x10 (lane8 m1 12)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [hx10, ea]) (by simp)
    (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.right (SepStore8.left (SepStore8.here (by clear * -; bv_omega)))))))))) rfl ?_; intro mem7
  refine step_strS32_off b (ea + 15#64) 27804 27808 0 2#5 .x11 ((lane64 (simdExt16b m1 m1 8) 0).truncate 32)
    (by decide) rfl (by simp [hrun]) (by simp only [arm64_norm]) (by simp [ea]) (by simp [e1, ext8_self_low32])
    (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.right (SepStore32.left (SepStore32.here (by clear * -; bv_omega))))))))) rfl ?_; intro mem8
  refine SepWP.weaken_pre (P' := (dst ↦ₛ ser10PolyPrefix re (c + 1)) ∗
      memRegion (dst + BitVec.ofNat 64 (20 * (c + 1))) (320 - 20 * (c + 1)) ∗ F) ?_ ?_
  · have hc := cells20_eq_neonSerialize10Bytes ea c0 c1
    have hp := ser10_prefix_append_chunk dst re c
    dsimp only [m0, m1, c0, c1, ser10Chunk20] at hc hp ⊢
    rw [← hp, ← hc]; sep_frame
  · refine hnext _ (by simp [off6ca0]) (by simp [hrun]) ⟨by simp, by simp [State.spAligned], by simp⟩
      (fun r hr => ?_) ⟨by simp, by simp, by simp, by simp⟩
    cases r with
    | gpr idx =>
      have hne : idx ≠ 11#5 := fun h => hr (h ▸ rfl)
      simp [hne]
    | xzr => simp
    | sp => simp

end Tail16

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps1.Seg6Ser
