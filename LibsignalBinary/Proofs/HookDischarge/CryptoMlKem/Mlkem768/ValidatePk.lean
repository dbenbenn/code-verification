/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base
import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
import LibsignalBinary.Specifications.LibsignalTripleRatchet
import LibsignalBinary.Proofs.HookDischarge.Libc.Common
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec.MlKem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Run
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3

/-!
# `B21`: `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`

Machine-code correctness proofs for `mlkemBlk21` (`530` words, `5824 = 4784 + 1040` tight stack
frame, calling `B02` `keccak2::<136, 6>`, `B28` `memcpy`, `B29` `memset`, and `B30` `bcmp`):

- `blk21_validate_pk_raw_ok : MlKemBlockOk 21 mlkemValidatePkValidRawSpec`
- `blk21_validate_pk_validPk_ok : MlKemBlockOk 21 mlkemValidatePkValidCoreSpec`
- `blk21_validate_pk_kproj_ok`: `K : MlKem` caller-struct projection bridge (`rfl`-matching
  `Hooks.mlkemValidatePkSpec K`)
- `blk21_validate_pk_ok`: bridge to `Base.mlkemValidatePkCoreSpec`
- `blk21_validate_pk_proj_ok`: bridge to `Base.mlkemValidatePkProjSpec`
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs (mlkemMultiLib)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables (MlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedCodeBase (
  MlKemBlockOk mlkemCaller_ok mlkemMpl)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase (
  withNonSyscallPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLiftBase (
  mlkemBlockOk_withNonSyscallPreserved mlkemKeep mlkemRoOk_stripExecOutside
  stripS_mem stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (
  mlkem768Incremental mlkem768ValidPk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Keccak.Keccak2_136_6 (
  blk02_keccak2_136_6_RW1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Base (
  blkPC21 blkPl21 mlkemValidatePkCoreSpec mlkemValidatePkCore_simulates_proj
  mlkemValidatePkProjSpec withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg1 (
  seg1_run sepWP_seq_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg2Run (seg2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk.Seg3 (seg3_run)

/-- Raw total-correctness (`subroutine_ok`) contract for `B21` (`validate_pk_bytes`) against
    `mlkem768ValidPk`, prior to `NonSyscallPreserved` lifting. -/
@[expose] def mlkemValidatePkValidRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrA, hdr, ekA, ek) s0 =>
    ⌜s0.readReg64 .x0 = hdrA ∧
      (s0.readReg64 .x1).toNat = hdr.length ∧
      s0.readReg64 .x2 = ekA ∧
      (s0.readReg64 .x3).toNat = ek.length ∧
      MlKemRoOk mpl s0.mem⌝ ∗
      (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824
  post := fun (hdrA, hdr, ekA, ek) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ mlkem768ValidPk hdr ek = true⌝ ∗
      (hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Tight-stack (`5824`-byte) core contract for `B21` (`validate_pk_bytes`) lifted with
    `NonSyscallPreserved` directly against `mlkem768ValidPk`. -/
@[expose] def mlkemValidatePkValidCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (mlkemValidatePkValidRawSpec mpl)

/-- `B21` (`validate_pk_bytes`) unconditional raw total-correctness theorem. -/
theorem blk21_validate_pk_raw_ok : MlKemBlockOk 21 mlkemValidatePkValidRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC21 blkPl21 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨hdrA, hdr, ekA, ek⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, mlkemValidatePkValidRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hx3, hro0⟩, hspat⟩ := hpre
  refine ⟨(hdrA ↦ₛ hdr) ∗ (ekA ↦ₛ ek) ∗ stackAt s0.sp 5824, ?_, ?_⟩
  · exact Satisfies.mono (by sep_frame) hspat
  · refine SepWP.mono
      (SepWP.weaken_pre (by sep_frame)
        (seg1_run blk02_keccak2_136_6_RW1_ok hb hbase s0 hdrA ekA hdr ek emp
          hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hx3 fun sm hpcm hrunm hclm hrom hpre2 => ?_)) ?_
    · refine sepWP_seq_env hclm hrom
        (seg2_ok hb hbase s0 sm hdrA ekA hdr ek emp hpcm hrunm hsp0 hclm hrom hpre2) ?_
      rintro s3 P3 hpc3 hrun3 hcl3 _ ⟨hpre3, hP3⟩
      exact SepWP.weaken_pre hP3
        (seg3_run hb hbase s0 s3 hdrA ekA hdr ek emp hpc3 hrun3 hsp0 hcl3 hpre3)
    · intro sf Pf _ _ hpost
      rcases hpost with ⟨hiff, hsp_sf, hcs_sf, hPf⟩
      refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
      have hm1 := Satisfies.mono (sepConj_mono_left hPf) hm
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hiff, Satisfies.mono (by sep_frame) hm1⟩

/-- `B21` (`validate_pk_bytes`) unconditional tight-stack contract with `NonSyscallPreserved`. -/
theorem blk21_validate_pk_validPk_ok : MlKemBlockOk 21 mlkemValidatePkValidCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk21_validate_pk_raw_ok (by decide)
    (h_pre := fun mpl ⟨_hdrA, _hdr, _ekA, _ek⟩ _R _s0 h => by
      dsimp only [mlkemValidatePkValidRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_hdrA, _hdr, _ekA, _ek⟩ _R _s0 _sf _ h => by
      dsimp only [mlkemValidatePkValidRawSpec] at h ⊢
      simpa only [stripS_readReg64, stripS_sp] using h)

/-- `K.validPkBytes` agrees with `mlkem768ValidPk` whenever `K.validPk` agrees with
    `mlkem768ValidPk` (`mlkem768ValidPk` already enforces `64` / `1152` byte lengths). -/
theorem validPkBytes_eq_mlkem768ValidPk (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    (hdr ek : List (BitVec 8)) :
    K.validPkBytes hdr ek = mlkem768ValidPk hdr ek := by
  unfold MlKem.validPkBytes
  rw [hK hdr ek]
  by_cases hh : hdr.length = 64
  · by_cases he : ek.length = 1152
    · simp [hh, he]
    · unfold mlkem768ValidPk; simp [hh, he]
  · unfold mlkem768ValidPk; simp [hh]

/-- Polymorphic caller-struct projection spec parameterized by `K : MlKem`, matching
    `Hooks.mlkemValidatePkSpec K` by `rfl` when instantiated with `MlkemValidatePkCall`
    projections. -/
@[expose] def mlkemValidatePkKProjSpec (K : MlKem) {C : Type}
    (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) : Spec C where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = hdrA x ∧ (s.readReg64 .x1).toNat = (hdr x).length ∧
      s.readReg64 .x2 = ekA x ∧ (s.readReg64 .x3).toNat = (ek x).length⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (ekA x ↦ₛ ek x) ∗ stackAt s.sp extHookStack
  post := fun x s0 sf =>
    ⌜((sf.readReg64 .x0).setWidth 8 = 0xff#8 ↔ K.validPkBytes (hdr x) (ek x) = true) ∧
      sf.trace = s0.trace⌝ ∗
      (hdrA x ↦ₛ hdr x) ∗ (ekA x ↦ₛ ek x) ∗ stackAt s0.sp extHookStack

/-- Simulation from `mlkemValidatePkValidCoreSpec` to `mlkemValidatePkKProjSpec K`. -/
theorem mlkemValidatePkValidCore_simulates_kproj (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    {C : Type} (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) (mpl : MultiPlacement) :
    SpecSimulates (mlkemValidatePkValidCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (mlkemValidatePkKProjSpec K hdrA hdr ekA ek))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkKProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx2, hx3⟩, hm⟩
  rw [stackAt_shrink s0.sp extHookStack 5824 (by decide)] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 5824)
  refine ⟨(hdrA y, hdr y, ekA y, ek y), slack ∗ R, ?_, ?_⟩
  · dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved, mlkemValidatePkValidRawSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hx3, hro⟩, ?_⟩
    rw [sepConj_comm slack (stackAt s0.sp 5824),
      sepConj_assoc (stackAt s0.sp 5824) slack R] at hm
    exact hm
  · intro sf _ _ hpost
    dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkValidRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, mlkemValidatePkKProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hiff, hpost⟩
    rw [validPkBytes_eq_mlkem768ValidPk K hK (hdr y) (ek y)]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hiff, hnsp.1⟩, ?_⟩
    rw [← sepConj_assoc (stackAt s0.sp 5824) slack R,
      sepConj_comm (stackAt s0.sp 5824) slack,
      ← stackAt_shrink s0.sp extHookStack 5824 (by decide)] at hpost
    exact hpost

/-- `B21` (`validate_pk_bytes`) caller-struct projection contract parameterized by `K : MlKem`
    (instantiates by `rfl` to `Hooks.mlkemValidatePkSpec K`). -/
theorem blk21_validate_pk_kproj_ok (K : MlKem)
    (hK : ∀ hdr ek, K.validPk hdr ek = mlkem768ValidPk hdr ek)
    {C : Type} (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) :
    MlKemBlockOk 21 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemValidatePkKProjSpec K hdrA hdr ekA ek))) := by
  intro _
  exact ((mlkemValidatePkValidCore_simulates_kproj K hK hdrA hdr ekA ek mlkemMpl).withCodeLoaded
    mlkemMultiLib mlkemMpl).subroutine_ok blk21_validate_pk_validPk_ok

/-- `B21` (`validate_pk_bytes`) unconditional bridge to `Base.mlkemValidatePkCoreSpec`. -/
theorem blk21_validate_pk_ok :
    MlKemBlockOk 21 mlkemValidatePkCoreSpec := by
  have hsim : ∀ mpl, SpecSimulates (mlkemValidatePkValidCoreSpec mpl) (mlkemValidatePkCoreSpec mpl) := by
    intro mpl
    refine SpecSimulates.of_map ?_
    rintro ⟨hdrA, hdr, ekA, ek⟩ R s0 hm
    refine ⟨(hdrA, hdr, ekA, ek), R, hm, fun sf _ _ hpost => ?_⟩
    dsimp only [mlkemValidatePkValidCoreSpec, withNonSyscallPreserved,
      mlkemValidatePkValidRawSpec] at hpost
    dsimp only [mlkemValidatePkCoreSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hiff, hpost⟩
    rw [validPkBytes_eq_mlkem768ValidPk mlkem768Incremental (fun _ _ => rfl) hdr ek]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hnsp, hiff⟩, hpost⟩
  intro _
  exact ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl).subroutine_ok
    blk21_validate_pk_validPk_ok

/-- `B21` (`validate_pk_bytes`) unconditional caller-struct projection bridge via
    `Base.mlkemValidatePkCore_simulates_proj` (`mlkem768Incremental`). -/
theorem blk21_validate_pk_proj_ok
    {C : Type} (hdrA : C → BitVec 64) (hdr : C → List (BitVec 8))
    (ekA : C → BitVec 64) (ek : C → List (BitVec 8)) :
    MlKemBlockOk 21 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (mlkemValidatePkProjSpec hdrA hdr ekA ek))) := by
  intro _
  exact ((mlkemValidatePkCore_simulates_proj hdrA hdr ekA ek mlkemMpl).withCodeLoaded
    mlkemMultiLib mlkemMpl).subroutine_ok blk21_validate_pk_ok

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.ValidatePk
