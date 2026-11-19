/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8
meta import ProofLib.GenPlacedFetches

/-!
# `B22` → `B04`: `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key` (`Mlkem768.Decaps`)

Partial- and conditional total-correctness contracts for `mlkemBlk22` (`5`-word ABI wrapper)
and `mlkemBlk04` (`13,411`-word NEON core), with tight stack budget `26,960` B
(`1,136 + 25,664 + 160`).

Exports:
- `blk04_decaps_raw_safe_ok`, `blk04_decaps_safe_ok`, `blk04_decaps_raw_ok`, `blk04_decaps_ok`
- `blk22_decaps_raw_safe_ok`, `blk22_decaps_safe_ok`, `blk22_decaps_raw_ok`, `blk22_decaps_ok`
- `blk22_decaps_proj_safe_ok`, `blk22_decaps_proj_ok`, plus `65536`, `extHookStack`, and
  `mlkem768Incremental` specializations.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement mlkemCall_of_blockOk
  mlkemCaller_ok mlkemMpl mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockOk_withNonSyscallPreserved mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Mlkem768DecapsTerminates mlkem768DecapsWith mlkem768Incremental sampleNtt toByteVec)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env toByteVec_toList_of_length withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Base (
  blk22_code_eq blk22_tree_size blkLib22 blkPC04 blkPC22 blkPl04 blkPl22
  blkPlaceable22 blkTree22 mlkemBlk04CoreSpec mlkemBlk04RawSpec
  mlkemBlk04TermCoreSpec mlkemBlk04TermRawSpec mlkemBlockOk_simulates
  mlkemBlockSafeOk_simulates mlkemDecapsCoreSpec mlkemDecapsCore_simulates_proj
  mlkemDecapsProjSpec mlkemDecapsRawSpec mlkemDecapsTermCoreSpec
  mlkemDecapsTermCore_simulates_proj mlkemDecapsTermRawSpec safeSepWP_of_sepWP_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg4 (seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg5 (seg5_ok seg5_safe_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg6 (seg6_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg7 (seg7_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps.Seg8 (seg8_ok)

/-! ## 1. Block 04 (`neon::decapsulate_compressed_key`) Core Contracts -/

/-- `B04` partial-correctness (`SafeSepWP` / `safe_subroutine_ok`) raw contract (`26,960` B stack). -/
theorem blk04_decaps_raw_safe_ok : MlKemBlockSafeOk 4 mlkemBlk04RawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC04 blkPl04 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemBlk04RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hdk, hct1, hct2, hro0⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗
    (memRegion ret 32 ∗ emp), Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine safeSepWP_of_sepWP_env hcl0 hro0
    (seg4_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
      hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hfp4, hx9_4, hx10_4, hx23_4, hx26_4, hx27_4, hx28_4, hP4⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_safe_ok hb hbase s0 s4 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp) hdk
      hpc4 hrun4 hcl4 hro4 hsp4 hspA4 hfp4 hx9_4 hx10_4 hx23_4 hx26_4 hx27_4 hx28_4) ?_) hP4
  rintro s5 P5 ⟨hpc5, hrun5, hcl5, hro5, hsp5, hspA5, hfp5, hx19_5, hx20_5, hP5⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.of_sepWP (SepWP.mono
    (seg6_ok hb hbase s0 s5 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
      hpc5 hrun5 hcl5 hro5 hsp5 hspA5 hfp5 hx19_5 hx20_5) ?_)) hP5
  rintro s6 P6 _ _ ⟨hpc6, hrun6, hcl6, hro6, hsp6, hspA6, hfp6, hx19_6, hx20_6, hP6⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.of_sepWP (SepWP.mono
    (seg7_ok hb hbase s0 s6 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp) hdk
      hpc6 hrun6 hcl6 hro6 hsp6 hspA6 hfp6 hx19_6 hx20_6) ?_)) hP6
  rintro s7 P7 _ _ ⟨hpc7, hrun7, hcl7, hro7, hsp7, hspA7, hfp7, hx19_7, hP7⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.ret_of_sepWP (SepWP.mono
    (seg8_ok hb s0 s7 ret dkA ct1A ct2A dk ct1 ct2 emp hdk hct1 hct2 hsp0
      hpc7 hrun7 hcl7 hro7 hsp7 hspA7 hfp7 hx19_7) ?_)) hP7
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hpost.2 (by sep_frame))) hm,
    hpost.1.1, hpost.1.2⟩

/-- `B04` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk04_decaps_safe_ok : MlKemBlockSafeOk 4 mlkemBlk04CoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk04_decaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 h => by
      dsimp only [mlkemBlk04RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        h.1.2.2.2.2.2.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemBlk04RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B04` conditional total-correctness (`subroutine_ok`) raw contract (`26,960` B stack). -/
theorem blk04_decaps_raw_ok : MlKemBlockOk 4 mlkemBlk04TermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC04 blkPl04 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    mlkemBlk04TermRawSpec, mlkemBlk04RawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hdk, hct1, hct2, hro0⟩, hspat⟩ := hpre
  have hTerm' : Spec.Shake128MatrixTerminates ((dk.drop 2304).take 32) 3 := by
    unfold Mlkem768DecapsTerminates at hTerm
    rwa [toByteVec_toList_of_length hdk] at hTerm
  refine ⟨stackAt s0.sp 26960 ∗ (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗
    (memRegion ret 32 ∗ emp), Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (seg4_ok hb hbase s0 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
      hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 hdk hct1 hct2) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hfp4, hx9_4, hx10_4, hx23_4, hx26_4, hx27_4, hx28_4, hP4⟩
  refine SepWP.weaken_pre hP4 (sepWP_seq_env hcl4 hro4
    (seg5_ok hb hbase s0 s4 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp) hdk hTerm'
      hpc4 hrun4 hcl4 hro4 hsp4 hspA4 hfp4 hx9_4 hx10_4 hx23_4 hx26_4 hx27_4 hx28_4) ?_)
  rintro s5 P5 _ _ _ _ ⟨hpc5, hrun5, hcl5, hro5, hsp5, hspA5, hfp5, hx19_5, hx20_5, hP5⟩
  refine SepWP.weaken_pre hP5 (sepWP_seq_env hcl5 hro5
    (seg6_ok hb hbase s0 s5 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp)
      hpc5 hrun5 hcl5 hro5 hsp5 hspA5 hfp5 hx19_5 hx20_5) ?_)
  rintro s6 P6 _ _ _ _ ⟨hpc6, hrun6, hcl6, hro6, hsp6, hspA6, hfp6, hx19_6, hx20_6, hP6⟩
  refine SepWP.weaken_pre hP6 (sepWP_seq_env hcl6 hro6
    (seg7_ok hb hbase s0 s6 ret dkA ct1A ct2A dk ct1 ct2 (memRegion ret 32 ∗ emp) hdk
      hpc6 hrun6 hcl6 hro6 hsp6 hspA6 hfp6 hx19_6 hx20_6) ?_)
  rintro s7 P7 _ _ _ _ ⟨hpc7, hrun7, hcl7, hro7, hsp7, hspA7, hfp7, hx19_7, hP7⟩
  refine SepWP.weaken_pre hP7 (SepWP.mono
    (seg8_ok hb s0 s7 ret dkA ct1A ct2A dk ct1 ct2 emp hdk hct1 hct2 hsp0
      hpc7 hrun7 hcl7 hro7 hsp7 hspA7 hfp7 hx19_7) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  exact ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hpost.2 (by sep_frame))) hm,
    hpost.1.1, hpost.1.2⟩

attribute [local irreducible] toByteVec Mlkem768DecapsTerminates mlkem768DecapsWith in
/-- `B04` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk04_decaps_ok : MlKemBlockOk 4 mlkemBlk04TermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk04_decaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 h => by
      dsimp only [mlkemBlk04TermRawSpec, mlkemBlk04RawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h2.1.1, h2.1.2.1, h2.1.2.2.1, h2.1.2.2.2.1, h2.1.2.2.2.2.1, h2.1.2.2.2.2.2.1,
        h2.1.2.2.2.2.2.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h2.1.2.2.2.2.2.2.2⟩, h2.2⟩)
    (h_post := fun _mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemBlk04TermRawSpec, mlkemBlk04RawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-! ## 2. Block 22 (`mlkem768::incremental::decapsulate_compressed_key`) ABI Wrapper -/

section Blk22Fetches
gen_placed_fetches blkPC22 blkLib22 blkTree22 blk22_code_eq blk22_tree_size
  via_placement blkPl22 blkPlaceable22 [0x0 → 0x10]
end Blk22Fetches

private theorem blk22_prologue_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl22 b) (hbase : blkPl22.base = b)
    (s0 : State) (ret dkA ct1A ct2A : BitVec 64) (P : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = ret) (hx0 : s0.readReg64 .x0 = dkA)
    (hx1 : s0.readReg64 .x1 = ct1A) (hx2 : s0.readReg64 .x2 = ct2A) :
    SepWP (blkPC22.rebase b (fun _ => none)) (mlkemMpl.base 4) s0 P
      (sepPost (fun s1 =>
        s1.mem = s0.mem ∧ s1.sp = s0.sp ∧ s1.spAligned = s0.spAligned ∧
        s1.readReg64 .lr = s0.readReg64 .lr ∧
        s1.readReg64 .x0 = ret ∧ s1.readReg64 .x1 = dkA ∧
        s1.readReg64 .x2 = ct1A ∧ s1.readReg64 .x3 = ct2A ∧
        CalleeSavedPreserved s0 s1) P) := by
  have _ := hb
  subst hbase
  simp only [Reg.x8, Reg.x0, Reg.x1, Reg.x2] at hx8 hx0 hx1 hx2
  wp_steps 5
  refine SepWP.done
    (by simp [wp_norm, arm64_norm, blkPl22, MultiPlacedLib.blockPlacement])
    (by simp [hrun]) ?_
  rw [sepPost_apply]
  refine ⟨⟨rfl, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm],
    by simp [CalleeSavedPreserved, wp_norm, arm64_norm]⟩, Entails.refl P⟩

private theorem cs_trans {s0 s1 s2 : State}
    (h01 : CalleeSavedPreserved s0 s1) (h12 : CalleeSavedPreserved s1 s2) :
    CalleeSavedPreserved s0 s2 := by
  rcases h01 with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  rcases h12 with ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8, b9.trans a9, b10.trans a10, b11.trans a11, b12.trans a12⟩

/-- `B22` partial-correctness (`safe_subroutine_ok`) raw contract (`26,960` B stack). -/
theorem blk22_decaps_raw_safe_ok : MlKemBlockSafeOk 22 mlkemDecapsRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC22 blkPl22 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemDecapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hx2, hdk, hct1, hct2, hro0⟩, hspat⟩ := hpre
  let P0 := (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960
  refine ⟨P0, hspat, SafeSepWP.of_sepWP (SepWP.mono
    (blk22_prologue_wp hb hbase s0 ret dkA ct1A ct2A P0 hpc hrun hx8 hx0 hx1 hx2) ?_)⟩
  intro s1 P1 hpc1 hrun1 hp1; rw [sepPost_apply] at hp1
  rcases hp1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hcs1⟩, hP1⟩
  refine SafeSepWP.call_subroutine_frame
    (mlkemSafeCall_of_blockSafeOk _ blk04_decaps_raw_safe_ok)
    (x := (ret, dkA, dk, ct1A, ct1, ct2A, ct2)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm1 => by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemBlk04RawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
          satisfies_pure_sepConj]
      refine ⟨hmem1 ▸ hcl0, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, hx1_1, hx2_1, hx3_1, hdk, hct1, hct2, hmem1 ▸ hro0⟩, ?_⟩
      rw [hsp1, emp_sepConj]; exact hm1')
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => SafeSepWP.done fun hmf =>
      Or.inl ⟨⟨hpc_sf, hsp_sf.trans hsp1, hrun_sf⟩, ⟨hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩,
        Satisfies.mono (by dsimp only [mlkemBlk04RawSpec]; sep_frame) hmf⟩)

/-- `B22` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk22_decaps_safe_ok : MlKemBlockSafeOk 22 mlkemDecapsCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk22_decaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 h => by
      dsimp only [mlkemDecapsRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        h.1.2.2.2.2.2.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemDecapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B22` conditional total-correctness (`subroutine_ok`) raw contract (`26,960` B stack). -/
theorem blk22_decaps_raw_ok : MlKemBlockOk 22 mlkemDecapsTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC22 blkPl22 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, dkA, dk, ct1A, ct1, ct2A, ct2⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    mlkemDecapsTermRawSpec, mlkemDecapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hx2, hdk, hct1, hct2, hro0⟩, hspat⟩ := hpre
  let P0 : SepProp :=
    (dkA ↦ₛ dk) ∗ (ct1A ↦ₛ ct1) ∗ (ct2A ↦ₛ ct2) ∗ memRegion ret 32 ∗ stackAt s0.sp 26960
  refine ⟨P0, hspat, SepWP.seq
    (blk22_prologue_wp hb hbase s0 ret dkA ct1A ct2A P0 hpc hrun hx8 hx0 hx1 hx2) ?_⟩
  rintro s1 P1 hpc1 hrun1 hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hx3_1, hcs1⟩, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.weaken_pre (show P0 ⊢ P0 ∗ emp by sep_frame) ?_
  refine SepWP.call_subroutine_frame
    (mlkemCall_of_blockOk (blkPC22.rebase b (fun _ => none)) (j := 4) blk04_decaps_raw_ok)
    (x := (ret, dkA, dk, ct1A, ct1, ct2A, ct2)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded, mlkemBlk04TermRawSpec, mlkemBlk04RawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
        pure_sepConj_of_true (hmem1 ▸ hcl0), sepConj_assoc, pure_sepConj_of_true hTerm,
        sepConj_assoc, pure_sepConj_of_true
          ⟨hx0_1, hx1_1, hx2_1, hx3_1, hdk, hct1, hct2, hmem1 ▸ hro0⟩]
      exact Satisfies.mono (by dsimp only [P0]; rw [hsp1]; sep_frame) hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  refine SepWP.done hpc_sf hrun_sf ⟨fun hmf => ?_, hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩
  refine Satisfies.mono ?_ hmf
  dsimp only [MultiPlacedLib.withCodeLoaded, mlkemBlk04TermRawSpec, mlkemBlk04RawSpec]
  rw [hsp1]
  sep_frame

attribute [local irreducible] toByteVec Mlkem768DecapsTerminates mlkem768DecapsWith in
/-- `B22` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk22_decaps_ok : MlKemBlockOk 22 mlkemDecapsTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk22_decaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 h => by
      dsimp only [mlkemDecapsTermRawSpec, mlkemDecapsRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h2.1.1, h2.1.2.1, h2.1.2.2.1, h2.1.2.2.2.1, h2.1.2.2.2.2.1, h2.1.2.2.2.2.2.1,
        h2.1.2.2.2.2.2.2.1, mlkemRoOk_stripExecOutside (mlkemKeep mpl) h2.1.2.2.2.2.2.2.2⟩, h2.2⟩)
    (h_post := fun _mpl ⟨_ret, _dkA, _dk, _ct1A, _ct1, _ct2A, _ct2⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemDecapsTermRawSpec, mlkemDecapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-! ## 3. Caller-Struct Projections (`26,960 ≤ stk`, `65,536`, & `extHookStack`) -/

/-- `B22` unconditional partial-correctness caller-struct projection (`26960 ≤ stk`). -/
theorem blk22_decaps_proj_safe_ok (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) :
    MlKemBlockSafeOk 22 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec stk K ret dkA dk ct1A ct1 ct2A ct2))) :=
  mlkemBlockSafeOk_simulates
    (mlkemDecapsCore_simulates_proj stk hstk hstk_fit K hK ret dkA dk ct1A ct1 ct2A ct2)
    blk22_decaps_safe_ok

/-- `B22` conditional total-correctness caller-struct projection (`26960 ≤ stk`). -/
theorem blk22_decaps_proj_ok (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128)
    (hTerm : ∀ x, Mlkem768DecapsTerminates (dk x)) :
    MlKemBlockOk 22 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec stk K ret dkA dk ct1A ct1 ct2A ct2))) :=
  mlkemBlockOk_simulates
    (mlkemDecapsTermCore_simulates_proj stk hstk hstk_fit K hK ret dkA dk ct1A ct1 ct2A ct2 hTerm)
    blk22_decaps_ok

/-- `B22` partial-correctness caller-struct projection at `stk = 65536`. -/
theorem blk22_decaps_65536_proj_safe_ok (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) :
    MlKemBlockSafeOk 22 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec 65536 K ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_safe_ok 65536 (by decide) (by decide) K hK ret dkA dk ct1A ct1 ct2A ct2

/-- `B22` conditional total-correctness caller-struct projection at `stk = 65536`. -/
theorem blk22_decaps_65536_proj_ok (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128)
    (hTerm : ∀ x, Mlkem768DecapsTerminates (dk x)) :
    MlKemBlockOk 22 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemDecapsProjSpec 65536 K ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_ok 65536 (by decide) (by decide) K hK ret dkA dk ct1A ct1 ct2A ct2 hTerm

/-- `B22` partial-correctness caller-struct projection at `extHookStack` (`26960 ≤ extHookStack`). -/
theorem blk22_decaps_extHookStack_proj_safe_ok (hstk : 26960 ≤ extHookStack) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) :
    MlKemBlockSafeOk 22 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemDecapsProjSpec extHookStack K ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_safe_ok extHookStack hstk (by decide) K hK ret dkA dk ct1A ct1 ct2A ct2

/-- `B22` conditional total-correctness caller-struct projection at `extHookStack`. -/
theorem blk22_decaps_extHookStack_proj_ok (hstk : 26960 ≤ extHookStack) (K : MlKem)
    (hK : ∀ d c1 c2, K.decaps d c1 c2 =
      toByteVec 32 (mlkem768DecapsWith sampleNtt d.toList c1.toList c2.toList))
    {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128)
    (hTerm : ∀ x, Mlkem768DecapsTerminates (dk x)) :
    MlKemBlockOk 22 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemDecapsProjSpec extHookStack K ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_ok extHookStack hstk (by decide) K hK ret dkA dk ct1A ct1 ct2A ct2 hTerm

/-- `B22` concrete `mlkem768Incremental` partial-correctness projection (`26960 ≤ stk`). -/
theorem blk22_decaps_inc_proj_safe_ok (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128) :
    MlKemBlockSafeOk 22 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemDecapsProjSpec stk mlkem768Incremental ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_safe_ok stk hstk hstk_fit mlkem768Incremental (fun _ _ _ => rfl)
    ret dkA dk ct1A ct1 ct2A ct2

/-- `B22` concrete `mlkem768Incremental` conditional total-correctness projection (`26960 ≤ stk`). -/
theorem blk22_decaps_inc_proj_ok (stk : Nat) (hstk : 26960 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide) {C : Type} (ret : C → BitVec 64)
    (dkA : C → BitVec 64) (dk : C → List.Vector (BitVec 8) 2400)
    (ct1A : C → BitVec 64) (ct1 : C → List.Vector (BitVec 8) 960)
    (ct2A : C → BitVec 64) (ct2 : C → List.Vector (BitVec 8) 128)
    (hTerm : ∀ x, Mlkem768DecapsTerminates (dk x)) :
    MlKemBlockOk 22 (fun mpl => withMlKemRoOk mpl
      (keepsFs (mlkemDecapsProjSpec stk mlkem768Incremental ret dkA dk ct1A ct1 ct2A ct2))) :=
  blk22_decaps_proj_ok stk hstk hstk_fit mlkem768Incremental (fun _ _ _ => rfl)
    ret dkA dk ct1A ct1 ct2A ct2 hTerm

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Decaps
