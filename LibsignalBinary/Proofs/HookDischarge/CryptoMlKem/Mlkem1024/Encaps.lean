/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Specifications.LibsignalTripleRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5
meta import ProofLib.GenPlacedFetches

/-!
# `B24` → `B07`: `libcrux_ml_kem::mlkem1024::kyber::encapsulate` (`Mlkem1024.Encaps`)

Hoare specifications and machine-code proofs for `mlkemBlk24` (4-word ABI wrapper) and
`mlkemBlk07` (10,252-word NEON core) with a `34,240`-byte stack budget (`1,136 + 32,944 + 160`),
preserving `(rA ↦ₛ rand)` in core `post`:

- `blk07_encaps_raw_safe_ok`, `blk07_encaps_safe_ok`, `blk07_encaps_raw_ok`, `blk07_encaps_ok`
- `blk24_kyber_encaps_raw_safe_ok`, `blk24_kyber_encaps_safe_ok`,
  `blk24_kyber_encaps_raw_ok`, `blk24_kyber_encaps_ok`, `blk24_kyber_encaps_atPk_ok`
- Caller projections (`SafeOk` and `Ok` under `∀ x, Kyber1024EncapsTerminates (pk x)`) across
  `keepRand`, `keepRandConcat`, `kemEncaps`, and `kemEncapsVec` at `34240 ≤ stk`, `65536`, and
  `extHookStack`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBase MlKemBlockOk MlKemBlockSafeOk MlKemPlacement mlkemCall_of_blockOk
  mlkemCaller_ok mlkemMpl mlkemSafeCall_of_blockSafeOk mlkemSafeCaller_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift (
  mlkemBlockOk_withNonSyscallPreserved mlkemBlockSafeOk_withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemKeep mlkemRoOk_stripExecOutside stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  Kyber1024EncapsTerminates kyber1024Encaps kyber1024Encaps_ct_len)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  sepWP_seq_env withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Base (
  blk07EncapsRawSpec blk07EncapsTermRawSpec blk24_code_eq blk24_tree_size blkLib24 blkPC07
  blkPC24 blkPl07 blkPl24 blkPlaceable24 blkTree24 keepRand_simulates_concat
  keepRand_simulates_kemEncaps kemEncapsProjSpec kemEncapsVecProjSpec kemEncaps_simulates_vec
  kyber1024EncapsVec kyber1024EncapsVec_fst_toList kyber1024EncapsVec_snd_toList
  kyberEncapsAtPkCoreSpec kyberEncapsCoreSpec kyberEncapsCore_simulates_keepRand
  kyberEncapsKeepRandConcatProjSpec kyberEncapsKeepRandProjSpec kyberEncapsRawSpec
  kyberEncapsTermCoreSpec kyberEncapsTermCore_simulates_atPk kyberEncapsTermCore_simulates_keepRand
  kyberEncapsTermRawSpec safeSepWP_seq_env safe_subroutine_ok_of_simulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a (seg1a_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1b (seg1b_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg2 (
  seg2_safeSepWP seg2_sepWP)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg3 (seg3_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg5 (seg5_ok)

private theorem mlkemBlockOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : MlKemBlockOk j spec₁) :
    MlKemBlockOk j spec₂ :=
  fun [MlKemPlacement] =>
    ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok h

private theorem mlkemBlockSafeOk_simulates {j : Nat} {α β : Type}
    {spec₁ : MultiPlacement → Spec α} {spec₂ : MultiPlacement → Spec β}
    (hsim : ∀ mpl, SpecSimulates (spec₁ mpl) (spec₂ mpl))
    (h : MlKemBlockSafeOk j spec₁) :
    MlKemBlockSafeOk j spec₂ :=
  fun [MlKemPlacement] =>
    safe_subroutine_ok_of_simulates
      ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl) h


/-! ## 1. Block 07 (`neon::kyber_encapsulate`) Core Contracts (`34,240` B Stack) -/

/-- Tight-stack (`34,240` bytes) core contract for `B07` with `NonSyscallPreserved`. -/
@[expose] noncomputable def blk07EncapsCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (blk07EncapsRawSpec mpl)

/-- Tight-stack (`34,240` bytes) total-correctness core contract for `B07` with `NonSyscallPreserved`. -/
@[expose] noncomputable def blk07EncapsTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (blk07EncapsTermRawSpec mpl)

attribute [local irreducible] kyber1024Encaps in
/-- `B07` partial-correctness (`SafeSepWP` / `safe_subroutine_ok`) raw contract (`34,240` B stack). -/
theorem blk07_encaps_raw_safe_ok : MlKemBlockSafeOk 7 blk07EncapsRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC07 blkPl07 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, pkA, pk, rA, rand⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, blk07EncapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hpk, hrnd, hro0⟩, hspat⟩ := hpre
  let Rest0 : SepProp := memRegion ret 1600 ∗ emp
  refine ⟨(pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt s0.sp 34240 ∗ Rest0,
    Satisfies.mono (by dsimp only [Rest0]; sep_frame) hspat, ?_⟩
  refine safeSepWP_seq_env hcl0 hro0
    (seg1a_ok hb hbase s0 ret pkA rA pk rand Rest0 hpk hrnd hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 hpost1
  refine safeSepWP_seq_env hcl1 hro1
    (seg1b_ok hb hbase s0.sp s0 ret pkA rA pk rand Rest0 hpk s1 P1 hpc1 hrun1 hcl1 hro1 hpost1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 hpost2
  refine SafeSepWP.bind
    (seg2_safeSepWP hb hbase s0.sp s0 ret pkA rA pk rand Rest0 hpk s2 P2 hpc2 hrun2 hcl2 hro2 hpost2) ?_
  rintro s3 P3 hpost3
  refine SafeSepWP.of_sepWP (SepWP.mono
    (seg3_ok hb hbase s0.sp s0 ret pkA rA pk rand Rest0 s3 P3 hpost3) ?_)
  rintro s4 P4 _ _ hpost4
  refine SafeSepWP.ret_of_sepWP (SepWP.mono
    (seg5_ok hb hbase s0 ret pkA rA pk rand emp hpk hrnd hsp0 s4 P4 hpost4) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hpost.2 (by sep_frame))) hm,
    hpost.1.1, hpost.1.2⟩

/-- `B07` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk07_encaps_safe_ok : MlKemBlockSafeOk 7 blk07EncapsCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk07_encaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 h => by
      dsimp only [blk07EncapsRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 _sf _ h => by
      dsimp only [blk07EncapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

attribute [local irreducible] kyber1024Encaps in
/-- `B07` conditional total-correctness (`subroutine_ok`) raw contract (`34,240` B stack). -/
theorem blk07_encaps_raw_ok : MlKemBlockOk 7 blk07EncapsTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC07 blkPl07 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, pkA, pk, rA, rand⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    blk07EncapsTermRawSpec, blk07EncapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hpk, hrnd, hTerm, hro0⟩, hspat⟩ := hpre
  let Rest0 : SepProp := memRegion ret 1600 ∗ emp
  refine ⟨(pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ stackAt s0.sp 34240 ∗ Rest0,
    Satisfies.mono (by dsimp only [Rest0]; sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (seg1a_ok hb hbase s0 ret pkA rA pk rand Rest0 hpk hrnd hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 hro1 hpost1
  refine sepWP_seq_env hcl1 hro1
    (seg1b_ok hb hbase s0.sp s0 ret pkA rA pk rand Rest0 hpk s1 P1 hpc1 hrun1 hcl1 hro1 hpost1) ?_
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 hpost2
  refine SepWP.seq
    (seg2_sepWP hb hbase s0.sp s0 ret pkA rA pk rand Rest0 hpk hTerm s2 P2 hpc2 hrun2 hcl2 hro2 hpost2) ?_
  rintro s3 P3 _ _ hpost3
  refine SepWP.seq
    (seg3_ok hb hbase s0.sp s0 ret pkA rA pk rand Rest0 s3 P3 hpost3) ?_
  rintro s4 P4 _ _ hpost4
  refine SepWP.mono
    (seg5_ok hb hbase s0 ret pkA rA pk rand emp hpk hrnd hsp0 s4 P4 hpost4) ?_
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  exact ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.trans hpost.2 (by sep_frame))) hm,
    hpost.1.1, hpost.1.2⟩

attribute [local irreducible] Kyber1024EncapsTerminates kyber1024Encaps in
/-- `B07` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk07_encaps_ok : MlKemBlockOk 7 blk07EncapsTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk07_encaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 h => by
      dsimp only [blk07EncapsTermRawSpec, blk07EncapsRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 _sf _ h => by
      dsimp only [blk07EncapsTermRawSpec, blk07EncapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-! ## 2. Block 24 (`mlkem1024::kyber::encapsulate`) ABI Wrapper -/

section Blk24Fetches
gen_placed_fetches blkPC24 blkLib24 blkTree24 blk24_code_eq blk24_tree_size
  via_placement blkPl24 blkPlaceable24 [0x0 → 0xc]
end Blk24Fetches

private theorem blk24_prologue_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl24 b) (hbase : blkPl24.base = b)
    (s0 : State) (ret pkA rA : BitVec 64) (P : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = ret) (hx0 : s0.readReg64 .x0 = pkA)
    (hx1 : s0.readReg64 .x1 = rA) :
    SepWP (blkPC24.rebase b (fun _ => none)) (mlkemMpl.base 7) s0 P
      (sepPost (fun s1 =>
        s1.mem = s0.mem ∧ s1.sp = s0.sp ∧ s1.spAligned = s0.spAligned ∧
        s1.readReg64 .lr = s0.readReg64 .lr ∧
        s1.readReg64 .x0 = ret ∧ s1.readReg64 .x1 = pkA ∧
        s1.readReg64 .x2 = rA ∧
        CalleeSavedPreserved s0 s1) P) := by
  have _ := hb
  subst hbase
  simp only [Reg.x8, Reg.x0, Reg.x1] at hx8 hx0 hx1
  wp_steps 4
  refine SepWP.done
    (by simp [wp_norm, arm64_norm, blkPl24, MultiPlacedLib.blockPlacement])
    (by simp [hrun]) ?_
  rw [sepPost_apply]
  refine ⟨⟨rfl, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
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

attribute [local irreducible] kyber1024Encaps in
/-- `B24` partial-correctness (`safe_subroutine_ok`) raw contract (`34,240` B stack). -/
theorem blk24_kyber_encaps_raw_safe_ok : MlKemBlockSafeOk 24 kyberEncapsRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC24 blkPl24 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, pkA, pk, rA, rand⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, kyberEncapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hpk, hrnd, hro0⟩, hspat⟩ := hpre
  let P0 := (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  refine ⟨P0, Satisfies.mono (by dsimp only [P0]; sep_frame) hspat, SafeSepWP.of_sepWP (SepWP.mono
    (blk24_prologue_wp hb hbase s0 ret pkA rA P0 hpc hrun hx8 hx0 hx1) ?_)⟩
  intro s1 P1 hpc1 hrun1 hp1; rw [sepPost_apply] at hp1
  rcases hp1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hcs1⟩, hP1⟩
  refine SafeSepWP.call_subroutine_frame
    (mlkemSafeCall_of_blockSafeOk _ blk07_encaps_raw_safe_ok)
    (x := (ret, pkA, pk, rA, rand)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm1 => by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, blk07EncapsRawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
          satisfies_pure_sepConj]
      refine ⟨hmem1 ▸ hcl0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, hx1_1, hx2_1, hpk, hrnd, hmem1 ▸ hro0⟩, ?_⟩
      rw [hsp1, emp_sepConj]
      exact Satisfies.mono (by dsimp only [P0]; sep_frame) hm1')
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => SafeSepWP.done fun hmf =>
      Or.inl ⟨⟨hpc_sf, hsp_sf.trans hsp1, hrun_sf⟩, ⟨hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩,
        Satisfies.mono (by dsimp only [blk07EncapsRawSpec]; sep_frame) hmf⟩)

/-- `B24` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk24_kyber_encaps_safe_ok : MlKemBlockSafeOk 24 kyberEncapsCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk24_kyber_encaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 h => by
      dsimp only [kyberEncapsRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 _sf _ h => by
      dsimp only [kyberEncapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

attribute [local irreducible] kyber1024Encaps in
/-- `B24` conditional total-correctness (`subroutine_ok`) raw contract (`34,240` B stack). -/
theorem blk24_kyber_encaps_raw_ok : MlKemBlockOk 24 kyberEncapsTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC24 blkPl24 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, pkA, pk, rA, rand⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    kyberEncapsTermRawSpec, kyberEncapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hpk, hrnd, hTerm, hro0⟩, hspat⟩ := hpre
  let P0 : SepProp := (pkA ↦ₛ pk) ∗ (rA ↦ₛ rand) ∗ memRegion ret 1600 ∗ stackAt s0.sp 34240
  refine ⟨P0, Satisfies.mono (by dsimp only [P0]; sep_frame) hspat, SepWP.seq
    (blk24_prologue_wp hb hbase s0 ret pkA rA P0 hpc hrun hx8 hx0 hx1) ?_⟩
  rintro s1 P1 hpc1 hrun1 hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hcs1⟩, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.weaken_pre (show P0 ⊢ P0 ∗ emp by sep_frame) ?_
  refine SepWP.call_subroutine_frame
    (mlkemCall_of_blockOk (blkPC24.rebase b (fun _ => none)) (j := 7) blk07_encaps_raw_ok)
    (x := (ret, pkA, pk, rA, rand)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded, blk07EncapsTermRawSpec, blk07EncapsRawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
        pure_sepConj_of_true (hmem1 ▸ hcl0),
        sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        pure_sepConj_of_true ⟨hx0_1, hx1_1, hx2_1, hpk, hrnd, hTerm, hmem1 ▸ hro0⟩]
      exact Satisfies.mono (by dsimp only [P0]; rw [hsp1]; sep_frame) hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  refine SepWP.done hpc_sf hrun_sf ⟨fun hmf => ?_, hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩
  refine Satisfies.mono ?_ hmf
  dsimp only [MultiPlacedLib.withCodeLoaded, blk07EncapsTermRawSpec, blk07EncapsRawSpec]
  rw [hsp1]
  sep_frame

attribute [local irreducible] Kyber1024EncapsTerminates kyber1024Encaps in
/-- `B24` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk24_kyber_encaps_ok : MlKemBlockOk 24 kyberEncapsTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk24_kyber_encaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 h => by
      dsimp only [kyberEncapsTermRawSpec, kyberEncapsRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _pkA, _pk, _rA, _rand⟩ _R _s0 _sf _ h => by
      dsimp only [kyberEncapsTermRawSpec, kyberEncapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B24` total-correctness core contract specialized to a fixed `pk` (`Kyber1024EncapsTerminates pk`). -/
theorem blk24_kyber_encaps_atPk_ok (pk : List (BitVec 8))
    (hTerm : Kyber1024EncapsTerminates pk) :
    MlKemBlockOk 24 (kyberEncapsAtPkCoreSpec pk) :=
  mlkemBlockOk_simulates (kyberEncapsTermCore_simulates_atPk pk hTerm) blk24_kyber_encaps_ok

/-! ## 3. Caller-Struct Projections (`34,240 ≤ stk`, `65,536`, & `extHookStack`) -/

/-- `B24` partial-correctness `keepRand` caller-struct projection (`34240 ≤ stk`). -/
theorem blk24_keepRand_proj_safe_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockSafeOk_simulates
    (kyberEncapsCore_simulates_keepRand (stk := stk) hstk hstk_fit K hK ret pkA pk rA rand)
    blk24_kyber_encaps_safe_ok

/-- `B24` conditional total-correctness `keepRand` caller-struct projection (`34240 ≤ stk`). -/
theorem blk24_keepRand_proj_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockOk_simulates
    (kyberEncapsTermCore_simulates_keepRand (stk := stk) hstk hstk_fit K hK ret pkA pk rA rand hTerm)
    blk24_kyber_encaps_ok

/-- `B24` partial-correctness `keepRand` caller-struct projection at `stk = 65536`. -/
theorem blk24_keepRand_65536_proj_safe_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_keepRand_proj_safe_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `keepRand` caller-struct projection at `stk = 65536`. -/
theorem blk24_keepRand_65536_proj_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_keepRand_proj_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `keepRand` projection at `extHookStack` (`34240 ≤ extHookStack`). -/
theorem blk24_keepRand_extHookStack_proj_safe_ok (hstk : 34240 ≤ extHookStack)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_keepRand_proj_safe_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `keepRand` projection at `extHookStack`. -/
theorem blk24_keepRand_extHookStack_proj_ok (hstk : 34240 ≤ extHookStack)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_keepRand_proj_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `keepRandConcat` (`ret ↦ₛ (ct ++ ss)`) projection (`34240 ≤ stk`). -/
theorem blk24_keepRandConcat_proj_safe_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandConcatProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockSafeOk_simulates
    (keepRand_simulates_concat stk K
      (fun pk' rand' => by rw [hK]; exact kyber1024Encaps_ct_len pk' rand') ret pkA pk rA rand)
    (blk24_keepRand_proj_safe_ok stk hstk hstk_fit K hK ret pkA pk rA rand)

/-- `B24` conditional total-correctness `keepRandConcat` projection (`34240 ≤ stk`). -/
theorem blk24_keepRandConcat_proj_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandConcatProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockOk_simulates
    (keepRand_simulates_concat stk K
      (fun pk' rand' => by rw [hK]; exact kyber1024Encaps_ct_len pk' rand') ret pkA pk rA rand)
    (blk24_keepRand_proj_ok stk hstk hstk_fit K hK ret pkA pk rA rand hTerm)

/-- `B24` partial-correctness `keepRandConcat` projection at `stk = 65536`. -/
theorem blk24_keepRandConcat_65536_proj_safe_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandConcatProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_keepRandConcat_proj_safe_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `keepRandConcat` projection at `stk = 65536`. -/
theorem blk24_keepRandConcat_65536_proj_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberEncapsKeepRandConcatProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_keepRandConcat_proj_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `kemEncaps` (`memRegion (rA x) 32` in `post`) projection (`34240 ≤ stk`). -/
theorem blk24_kemEncaps_proj_safe_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockSafeOk_simulates
    (keepRand_simulates_kemEncaps stk K ret pkA pk rA rand)
    (blk24_keepRand_proj_safe_ok stk hstk hstk_fit K hK ret pkA pk rA rand)

/-- `B24` conditional total-correctness `kemEncaps` projection (`34240 ≤ stk`). -/
theorem blk24_kemEncaps_proj_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockOk_simulates
    (keepRand_simulates_kemEncaps stk K ret pkA pk rA rand)
    (blk24_keepRand_proj_ok stk hstk hstk_fit K hK ret pkA pk rA rand hTerm)

/-- `B24` partial-correctness `kemEncaps` projection at `stk = 65536`. -/
theorem blk24_kemEncaps_65536_proj_safe_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_kemEncaps_proj_safe_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `kemEncaps` projection at `stk = 65536`. -/
theorem blk24_kemEncaps_65536_proj_ok
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_kemEncaps_proj_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `kemEncaps` projection at `extHookStack` (`34240 ≤ extHookStack`). -/
theorem blk24_kemEncaps_extHookStack_proj_safe_ok (hstk : 34240 ≤ extHookStack)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8)) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_kemEncaps_proj_safe_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `kemEncaps` projection at `extHookStack`. -/
theorem blk24_kemEncaps_extHookStack_proj_ok (hstk : 34240 ≤ extHookStack)
    (K : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) × List (BitVec 8))
    (hK : ∀ pk rand, K pk rand = kyber1024Encaps pk rand)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List (BitVec 8))
    (rA : C → BitVec 64) (rand : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x)) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_kemEncaps_proj_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `kemEncapsVec` (`List.Vector`, `kemEncapsName`) projection
    (`34240 ≤ stk`). -/
theorem blk24_kemEncapsVec_proj_safe_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockSafeOk_simulates
    (kemEncaps_simulates_vec stk K kyber1024Encaps hK ret pkA pk rA rand)
    (blk24_kemEncaps_proj_safe_ok stk hstk hstk_fit kyber1024Encaps (fun _ _ => rfl)
      ret pkA (fun x => (pk x).toList) rA (fun x => (rand x).toList))

/-- `B24` conditional total-correctness `kemEncapsVec` (`List.Vector`, `kemEncapsName`)
    projection (`34240 ≤ stk`). -/
theorem blk24_kemEncapsVec_proj_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x).toList) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec stk K ret pkA pk rA rand))) :=
  mlkemBlockOk_simulates
    (kemEncaps_simulates_vec stk K kyber1024Encaps hK ret pkA pk rA rand)
    (blk24_kemEncaps_proj_ok stk hstk hstk_fit kyber1024Encaps (fun _ _ => rfl)
      ret pkA (fun x => (pk x).toList) rA (fun x => (rand x).toList) hTerm)

/-- `B24` partial-correctness `kemEncapsVec` projection at `stk = 65536`. -/
theorem blk24_kemEncapsVec_65536_proj_safe_ok
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_safe_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `kemEncapsVec` projection at `stk = 65536`. -/
theorem blk24_kemEncapsVec_65536_proj_ok
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x).toList) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec 65536 K ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_ok 65536 (by decide) (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` partial-correctness `kemEncapsVec` projection at `extHookStack` (`34240 ≤ extHookStack`). -/
theorem blk24_kemEncapsVec_extHookStack_proj_safe_ok (hstk : 34240 ≤ extHookStack)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) :
    MlKemBlockSafeOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_safe_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand

/-- `B24` conditional total-correctness `kemEncapsVec` projection at `extHookStack`. -/
theorem blk24_kemEncapsVec_extHookStack_proj_ok (hstk : 34240 ≤ extHookStack)
    (K : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (hK : ∀ pk rand,
      (K pk rand).1.toList = (kyber1024Encaps pk.toList rand.toList).1 ∧
      (K pk rand).2.toList = (kyber1024Encaps pk.toList rand.toList).2)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x).toList) :
    MlKemBlockOk 24 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kemEncapsVecProjSpec extHookStack K ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_ok extHookStack hstk (by decide) K hK ret pkA pk rA rand hTerm

/-- `B24` concrete `kyber1024EncapsVec` partial-correctness projection (`34240 ≤ stk`). -/
theorem blk24_kyber1024EncapsVec_proj_safe_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32) :
    MlKemBlockSafeOk 24 (fun mpl => withMlKemRoOk mpl
      (keepsFs (kemEncapsVecProjSpec stk kyber1024EncapsVec ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_safe_ok stk hstk hstk_fit kyber1024EncapsVec
    (fun p r => ⟨kyber1024EncapsVec_fst_toList p r, kyber1024EncapsVec_snd_toList p r⟩)
    ret pkA pk rA rand

/-- `B24` concrete `kyber1024EncapsVec` conditional total-correctness projection (`34240 ≤ stk`). -/
theorem blk24_kyber1024EncapsVec_proj_ok (stk : Nat) (hstk : 34240 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret pkA : C → BitVec 64) (pk : C → List.Vector (BitVec 8) 1568)
    (rA : C → BitVec 64) (rand : C → List.Vector (BitVec 8) 32)
    (hTerm : ∀ x, Kyber1024EncapsTerminates (pk x).toList) :
    MlKemBlockOk 24 (fun mpl => withMlKemRoOk mpl
      (keepsFs (kemEncapsVecProjSpec stk kyber1024EncapsVec ret pkA pk rA rand))) :=
  blk24_kemEncapsVec_proj_ok stk hstk hstk_fit kyber1024EncapsVec
    (fun p r => ⟨kyber1024EncapsVec_fst_toList p r, kyber1024EncapsVec_snd_toList p r⟩)
    ret pkA pk rA rand hTerm

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps
