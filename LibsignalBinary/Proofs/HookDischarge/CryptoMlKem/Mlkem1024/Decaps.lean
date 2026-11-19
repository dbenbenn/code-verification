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
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base
import ProofLib.GenPlacedFetches
import ProofLib.SepLogic.SafeSepWP
import LibsignalBinary.Proofs.HookDischarge.RustStd.Common
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.PlacedObjDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.RoTables
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.NoSvcLift
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8VpolyC2
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg9KdfEpilogue
meta import ProofLib.GenPlacedFetches
meta import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `libcrux_ml_kem::mlkem1024::kyber::decapsulate` (`B23` → `B06`)

Machine-code contracts for `mlkemBlk23` (4-word ABI wrapper) and `mlkemBlk06` (13,979-word
NEON core) with a 35,968-byte stack budget (`1,136 + 34,672 + 160`).

Exports partial-correctness (`safe_subroutine_ok`) and conditional total-correctness
(`subroutine_ok`, under `Kyber1024DecapsTerminates`) theorems:
- `B06`: `blk06_decaps_raw_safe_ok`, `blk06_decaps_safe_ok`, `blk06_decaps_raw_ok`,
  `blk06_decaps_ok`
- `B23`: `blk23_kyber_decaps_raw_safe_ok`, `blk23_kyber_decaps_safe_ok`,
  `blk23_kyber_decaps_raw_ok`, `blk23_kyber_decaps_ok`, `blk23_kyber_decaps_atSk_ok`
- Caller projections (`projLen`, `proj`, and `cliProj` / `kyber1024DecapsVec`) for `35968 ≤ stk`,
  `65536`, and `extHookStack`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps

open Arm64 Arm64.Obj ProofLib SepProp BitVec
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
  Kyber1024DecapsTerminates Poly Shake128MatrixTerminates bitsToBytes byteEncode
  compressAndEncode indCpaDecrypt indCpaEncryptWith kyber1024Decaps sampleNtt
  sha3_512List shake256List)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec kyber1024DecapsVec_toList)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Cbd (neonCbd2Poly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.Lane16 (dup4hLow)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Base (
  cell_entails_memRegion8 sepWP_seq_env withMlKemRoOk)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.Seg1a (entails_sub)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem768.Encaps2.VecMem (
  PolyMem Vec128At polyVecNat vecRangeMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1a1 (
  sha3_512List_len shake256List_len)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Encaps.Seg1bPure (
  pkEk0 pkEk1 pkEk2 pkEk3 pkRho rhoW tHatModPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs (SpillSliceMem)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Base (
  SavedFrame06 SpecSimulates.safe_subroutine_ok blk23_code_eq blk23_tree_size blkLib23
  blkPC06 blkPC23 blkPl06 blkPl23 blkPlaceable23 blkTree23 kyberDecapsCliProjSpec
  kyberDecapsCoreSpec kyberDecapsCore_simulates_cliProj kyberDecapsCore_simulates_proj
  kyberDecapsCore_simulates_projLen kyberDecapsCore_simulates_projLen_nsp
  kyberDecapsCore_simulates_proj_nsp kyberDecapsInnerRawSpec kyberDecapsProjLenSpec
  kyberDecapsProjSpec kyberDecapsRawSpec safeSepWP_of_sepWP_env)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1a (
  Seg1aSpatial seg1a_ok stackAt_35968_eq)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1b (
  cst16_3_val seg1b_ok sk_pointsTo_split uHatZetaSpill40)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg1c (
  seg1c_ok sepWP_elim_poly32 sepWP_elim_vec128At spillSliceMem_entails_memRegion)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg2Uhat (seg2_uhat_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg3Decrypt (seg3_decrypt_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4a1 (
  SpilledDecapsWords off39c4 spilledDecapsWords_entails_memRegion128)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg4b2 (off40f0 seg4_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg5SampleMatrix (
  ATransMem06 Seg5MatrixPost06 off76a8 seg5_sample_matrix_ok seg5_sample_matrix_safe_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6CbdPure (
  ATransAt PublicKeyStateAt aTransAt_14432_eq pkStateBytes pkStateBytes_length
  publicKeyStateAt_eq_pointsToBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6E2 (offSeg7Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6RhatNtt (rHatPoly16)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg6PrfRhat (seg6_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg7UvecC1 (
  c1Bytes06 offSeg8Start seg7_uvec_c1_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8Ser5 (offSeg9Start)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg8VpolyC2 (seg8_vpoly_c2_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Seg9KdfEpilogue (
  decaps_select_eq_kyber1024Decaps seg9_ok)

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
    SpecSimulates.safe_subroutine_ok
      ((hsim mlkemMpl).withCodeLoaded mlkemMultiLib mlkemMpl) h

/-! ## 1. Total-Correctness Specifications (`Kyber1024DecapsTerminates`) -/

/-- Tight-stack (`35,968` bytes) core contract for `B06` with `NonSyscallPreserved`. -/
@[expose] noncomputable def kyberDecapsInnerCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberDecapsInnerRawSpec mpl)

/-- Conditional total-correctness tight-stack (`35,968` bytes) raw contract for `B06`. -/
@[expose] noncomputable def kyberDecapsInnerTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜Kyber1024DecapsTerminates sk⌝ ∗ (kyberDecapsInnerRawSpec mpl).pre (ret, skA, sk, ctA, ct) s0
  post := (kyberDecapsInnerRawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Conditional total-correctness tight-stack (`35,968` bytes) core contract for `B06`. -/
@[expose] noncomputable def kyberDecapsInnerTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberDecapsInnerTermRawSpec mpl)

/-- Conditional total-correctness tight-stack (`35,968` bytes) raw contract for `B23`. -/
@[expose] noncomputable def kyberDecapsTermRawSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, skA, sk, ctA, ct) s0 =>
    ⌜Kyber1024DecapsTerminates sk⌝ ∗ (kyberDecapsRawSpec mpl).pre (ret, skA, sk, ctA, ct) s0
  post := (kyberDecapsRawSpec mpl).post
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Conditional total-correctness tight-stack (`35,968` bytes) core contract for `B23` with
    `NonSyscallPreserved`. -/
@[expose] noncomputable def kyberDecapsTermCoreSpec (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) :=
  withNonSyscallPreserved (kyberDecapsTermRawSpec mpl)

/-- Per-key (`sk : List (BitVec 8)`) total-correctness specialization of `kyberDecapsCoreSpec`. -/
@[expose] noncomputable def kyberDecapsAtSkCoreSpec (sk : List (BitVec 8)) (mpl : MultiPlacement) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ret, skA, ctA, ct) s0 =>
    (kyberDecapsCoreSpec mpl).pre (ret, skA, sk, ctA, ct) s0
  post := fun (ret, skA, ctA, ct) s0 sf =>
    (kyberDecapsCoreSpec mpl).post (ret, skA, sk, ctA, ct) s0 sf
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

theorem kyberDecapsTermCore_simulates_atSk {sk : List (BitVec 8)}
    (hTerm : Kyber1024DecapsTerminates sk) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl) (kyberDecapsAtSkCoreSpec sk mpl) := by
  refine SpecSimulates.of_map ?_
  rintro ⟨ret, skA, ctA, ct⟩ R s0 hm
  refine ⟨(ret, skA, sk, ctA, ct), R, ?_, fun _ _ _ hp => hp⟩
  dsimp only [kyberDecapsTermCoreSpec, kyberDecapsAtSkCoreSpec, kyberDecapsCoreSpec,
    withNonSyscallPreserved, kyberDecapsTermRawSpec] at hm ⊢
  rw [sepConj_assoc, pure_sepConj_of_true hTerm]
  exact hm

theorem kyberDecapsTermCore_simulates_projLen_nsp
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (withNonSyscallPreserved
        (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1, hsk, hct⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 35968 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 35968)
  refine (SpecSimulates.of_map ?_) y R s0 ?_
  · intro y' R' s0' hm'
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec] at hm'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
    rcases hm' with ⟨hro', hm'⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm'
    rcases hm' with ⟨⟨hx8', hx0', hx1', hsk', hct'⟩, hm'⟩
    rw [stackAt_shrink s0'.sp stk 35968 hstk hstk_fit] at hm'
    set slack' := memRegion (s0'.sp - BitVec.ofNat 64 stk) (stk - 35968)
    refine ⟨(ret y', skA y', sk y', ctA y', ct y'), slack' ∗ R', ?_, ?_⟩
    · dsimp only [kyberDecapsTermCoreSpec, withNonSyscallPreserved, kyberDecapsTermRawSpec,
        kyberDecapsRawSpec]
      rw [sepConj_assoc, pure_sepConj_of_true (hTerm y'),
        sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx8', hx0', hx1', hsk', hct', hro'⟩, Satisfies.mono (by sep_frame) hm'⟩
    · intro sf _ _ hpost
      dsimp only [kyberDecapsTermCoreSpec, withNonSyscallPreserved, kyberDecapsTermRawSpec,
        kyberDecapsRawSpec] at hpost
      dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hnsp, hpost⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hnsp, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hnsp.1, ?_⟩
      rw [hdec (sk y') (ct y') hsk' hct', stackAt_shrink s0'.sp stk 35968 hstk hstk_fit]
      exact Satisfies.mono (by sep_frame) hpost
  · dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    rw [stackAt_shrink s0.sp stk 35968 hstk hstk_fit]
    exact ⟨⟨hx8, hx0, hx1, hsk, hct⟩, hm⟩

theorem kyberDecapsTermCore_simulates_projLen
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  obtain ⟨x, R₁, hpre₁, hpost₁⟩ :=
    kyberDecapsTermCore_simulates_projLen_nsp decaps hdec stk hstk hstk_fit ret skA sk ctA ct hTerm mpl y R s0 hm
  refine ⟨x, R₁, hpre₁, fun sf hout => ?_⟩
  rcases hpost₁ sf hout with ⟨hret, hcc, hp⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, keepsFs] at hp ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
    exact ⟨hp.1.2.2.2.2.2.2, hp.2⟩
  · exact Or.inr hrest

theorem kyberDecapsTermCore_simulates_proj_nsp
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (withNonSyscallPreserved
        (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  have hm_len : s0.mem ⊨ (withMlKemRoOk mpl (withNonSyscallPreserved
      (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))).pre y s0 ∗ R := by
    dsimp only [withMlKemRoOk, withNonSyscallPreserved, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hsk y, hct y⟩, hm⟩
  exact kyberDecapsTermCore_simulates_projLen_nsp decaps hdec stk hstk hstk_fit
    ret skA sk ctA ct hTerm mpl y R s0 hm_len

theorem kyberDecapsTermCore_simulates_proj
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) := by
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberDecapsProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx8, hx0, hx1⟩, hm⟩
  have hm_len : s0.mem ⊨ (withMlKemRoOk mpl (keepsFs
      (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))).pre y s0 ∗ R := by
    dsimp only [withMlKemRoOk, keepsFs, kyberDecapsProjLenSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hro, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hsk y, hct y⟩, hm⟩
  exact kyberDecapsTermCore_simulates_projLen decaps hdec stk hstk hstk_fit
    ret skA sk ctA ct hTerm mpl y R s0 hm_len

theorem kyberDecapsTermCore_simulates_cliProj
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x).toList) (mpl : MultiPlacement) :
    SpecSimulates (kyberDecapsTermCoreSpec mpl)
      (withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps stk skA sk ctA ct ret))) := by
  refine SpecSimulates.of_map ?_
  intro y R s0 hm
  dsimp only [withMlKemRoOk, keepsFs, kyberDecapsCliProjSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hro, hm⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hx0, hx1, hx8⟩, hm⟩
  rw [stackAt_shrink s0.sp stk 35968 hstk hstk_fit] at hm
  set slack := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 35968)
  refine ⟨(ret y, skA y, (sk y).toList, ctA y, (ct y).toList), slack ∗ R, ?_, ?_⟩
  · dsimp only [kyberDecapsTermCoreSpec, withNonSyscallPreserved, kyberDecapsTermRawSpec,
      kyberDecapsRawSpec]
    rw [sepConj_assoc, pure_sepConj_of_true (hTerm y),
      sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, (sk y).toList_length, (ct y).toList_length, hro⟩,
      Satisfies.mono (by sep_frame) hm⟩
  · intro sf _ _ hpost
    dsimp only [kyberDecapsTermCoreSpec, withNonSyscallPreserved, kyberDecapsTermRawSpec,
      kyberDecapsRawSpec] at hpost
    dsimp only [withMlKemRoOk, keepsFs, kyberDecapsCliProjSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hnsp, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.2.2.2.2.2.2, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hnsp.1, ?_⟩
    rw [hdec (sk y) (ct y), stackAt_shrink s0.sp stk 35968 hstk hstk_fit]
    exact Satisfies.mono (by sep_frame) hpost

/-! ## 2. Spatial Partition Helpers for `B06` (`[sp, sp + 34672)`) -/

private theorem sk_tail_split (skA : BitVec 64) {sk : List (BitVec 8)} (hsk : sk.length = 3168) :
    ((skA + 1536#64) ↦ₛ sk.drop 1536) =
      ((skA + 1536#64) ↦ₛ (sk.drop 1536).take 1568) ∗
      ((skA + 3104#64) ↦ₛ (sk.drop 3104).take 32) ∗
      ((skA + 3136#64) ↦ₛ (sk.drop 3136).take 32) := by
  have h1 : sk.drop 1536 = (sk.drop 1536).take 1568 ++ sk.drop 3104 := by
    conv_lhs => rw [← List.take_append_drop 1568 (sk.drop 1536)]
    rw [List.drop_drop]
  have h2 : sk.drop 3104 = (sk.drop 3104).take 32 ++ (sk.drop 3136).take 32 := by
    have hd3136 : (sk.drop 3104).drop 32 = sk.drop 3136 := by rw [List.drop_drop]
    have hdrop : sk.drop 3136 = (sk.drop 3136).take 32 := by
      symm; apply List.take_of_length_le; simp [hsk]
    conv_lhs => rw [← List.take_append_drop 32 (sk.drop 3104)]
    rw [hd3136, ← hdrop]
  have hl1 : ((sk.drop 1536).take 1568).length = 1568 := by simp [hsk]
  have hl2 : ((sk.drop 3104).take 32).length = 32 := by simp [hsk]
  conv_lhs => rw [h1]
  rw [pointsToBytes_append, hl1]
  conv_lhs => rw [h2]
  rw [pointsToBytes_append, hl2]
  simp only [
    show skA + 1536#64 + BitVec.ofNat 64 1568 = skA + 3104#64 by bv_omega,
    show skA + 3104#64 + BitVec.ofNat 64 32 = skA + 3136#64 by bv_omega]

private theorem pkRho_sk_eq (sk : List (BitVec 8)) :
    pkRho ((sk.drop 1536).take 1568) = (sk.drop 3072).take 32 := by
  have h : ((sk.drop 1536).take 1568).drop 1536 = (sk.drop 3072).take 32 := by
    rw [List.drop_take, List.drop_drop]
  unfold pkRho
  rw [h, List.take_take, Nat.min_self]

private theorem pkRho_sk_len {sk : List (BitVec 8)} (hsk : sk.length = 3168) :
    (pkRho ((sk.drop 1536).take 1568)).length = 32 := by
  rw [pkRho_sk_eq sk]; simp [hsk]

private theorem dup4hLow_3329_trunc64 :
    (dup4hLow 3329#16).truncate 64 = 0x0d010d010d010d01#64 := by decide

private theorem sp_aligned_chk {s : State} {sp : BitVec 64}
    (hsp : s.sp = sp) (hspA : s.spAligned = true) :
    (sp &&& 15#64 == 0#64) = true := by
  unfold State.spAligned at hspA; rwa [hsp] at hspA

private theorem publicKeyStateAt_14432_eq (sp : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt (sp + 14432#64) pk =
      (ATransMem06 sp (pkRho pk) ∗
        PolyMem (sp + 22624#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 23136#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        ((sp + 24672#64) ↦ₛ List.replicate 32 0#8)) := by
  unfold PublicKeyStateAt
  rw [aTransAt_14432_eq]
  simp only [
    show sp + 14432#64 + 8192#64 = sp + 22624#64 by bv_omega,
    show sp + 14432#64 + 8704#64 = sp + 23136#64 by bv_omega,
    show sp + 14432#64 + 9216#64 = sp + 23648#64 by bv_omega,
    show sp + 14432#64 + 9728#64 = sp + 24160#64 by bv_omega,
    show sp + 14432#64 + BitVec.ofNat 64 10240 = sp + 24672#64 by bv_omega]

private theorem publicKeyStateAt_4160_eq (sp : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt (sp + 4160#64) pk =
      (ATransAt (sp + 4160#64) (pkRho pk) ∗
        PolyMem (sp + 12352#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 12864#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 13376#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 13888#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        ((sp + 14400#64) ↦ₛ List.replicate 32 0#8)) := by
  unfold PublicKeyStateAt
  simp only [
    show sp + 4160#64 + 8192#64 = sp + 12352#64 by bv_omega,
    show sp + 4160#64 + 8704#64 = sp + 12864#64 by bv_omega,
    show sp + 4160#64 + 9216#64 = sp + 13376#64 by bv_omega,
    show sp + 4160#64 + 9728#64 = sp + 13888#64 by bv_omega,
    show sp + 4160#64 + BitVec.ofNat 64 10240 = sp + 14400#64 by bv_omega]

private theorem publicKeyStateAt_entails_memRegion (ptr : BitVec 64) (pk : List (BitVec 8)) :
    PublicKeyStateAt ptr pk ⊢ memRegion ptr 10272 := by
  rw [publicKeyStateAt_eq_pointsToBytes]
  simpa only [pkStateBytes_length pk] using pointsToBytes_entails_memRegion ptr (pkStateBytes pk)

private theorem polyMem4_entails_2048 (ptr : BitVec 64) (f0 f1 f2 f3 : Nat → BitVec 128) :
    PolyMem ptr f0 ∗ PolyMem (ptr + 512#64) f1 ∗
      PolyMem (ptr + 1024#64) f2 ∗ PolyMem (ptr + 1536#64) f3 ⊢
      memRegion ptr 2048 := by
  rw [memRegion_split' (b := ptr) (b' := ptr + 512#64) (n := 512) (k := (1536 : Nat)) rfl rfl (by decide),
    memRegion_split' (b := ptr + 512#64) (b' := ptr + 1024#64) (n := 512) (k := (1024 : Nat)) rfl (by bv_omega) (by decide),
    memRegion_split' (b := ptr + 1024#64) (b' := ptr + 1536#64) (n := 512) (k := (512 : Nat)) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (vecRangeMem_entails_memRegion 32 ptr f0)
    (sepConj_mono (vecRangeMem_entails_memRegion 32 (ptr + 512#64) f1)
      (sepConj_mono (vecRangeMem_entails_memRegion 32 (ptr + 1024#64) f2)
        (vecRangeMem_entails_memRegion 32 (ptr + 1536#64) f3)))

private theorem mr_split (sp : BitVec 64) (o1 n k o2 : Nat)
    (ho : sp + BitVec.ofNat 64 o1 + BitVec.ofNat 64 n = sp + BitVec.ofNat 64 o2 := by bv_omega)
    (hk : n + k ≤ 2 ^ 64 := by decide) :
    memRegion (sp + BitVec.ofNat 64 o1) (n + k) =
      memRegion (sp + BitVec.ofNat 64 o1) n ∗ memRegion (sp + BitVec.ofNat 64 o2) k :=
  memRegion_split' rfl ho.symm hk

private theorem vec128At_entails_memRegion16 (ptr : BitVec 64) (v : BitVec 128) :
    Vec128At ptr v ⊢ memRegion ptr 16 := by
  unfold Vec128At
  rw [memRegion_split' (b := ptr) (b' := ptr + 8#64) (n := 8) (k := (8 : Nat)) rfl rfl (by decide)]
  exact sepConj_mono (cell_entails_memRegion8 _ _) (cell_entails_memRegion8 _ _)

private theorem seg1a_split_28952 (sp : BitVec 64) :
    memRegion (sp + 2008#64) 28952 =
      memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗ memRegion (sp + 2024#64) 8 ∗
      memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗ memRegion (sp + 2048#64) 16 ∗
      memRegion (sp + 2064#64) 336 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗ memRegion (sp + 2432#64) 1728 ∗
      memRegion (sp + 4160#64) 2048 ∗ memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 16480#64) 8224 ∗ memRegion (sp + 24704#64) 1616 ∗
      memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 480 ∗
      memRegion (sp + 28880#64) 1568 ∗ memRegion (sp + 30448#64) 512 := by
  rw [mr_split sp 2008 8 28944 2016, mr_split sp 2016 8 28936 2024,
    mr_split sp 2024 8 28928 2032, mr_split sp 2032 8 28920 2040,
    mr_split sp 2040 8 28912 2048, mr_split sp 2048 16 28896 2064,
    mr_split sp 2064 336 28560 2400, mr_split sp 2400 8 28552 2408,
    mr_split sp 2408 8 28544 2416, mr_split sp 2416 8 28536 2424,
    mr_split sp 2424 8 28528 2432, mr_split sp 2432 1728 26800 4160,
    mr_split sp 4160 2048 24752 6208, mr_split sp 6208 8224 16528 14432,
    mr_split sp 14432 512 16016 14944, mr_split sp 14944 1536 14480 16480,
    mr_split sp 16480 8224 6256 24704, mr_split sp 24704 1616 4640 26320,
    mr_split sp 26320 512 4128 26832, mr_split sp 26832 1536 2592 28368,
    mr_split sp 28368 32 2560 28400, mr_split sp 28400 480 2080 28880,
    mr_split sp 28880 1568 512 30448]

private theorem seg1a_split_30960 (sp : BitVec 64) :
    memRegion (sp + 30960#64) 1536 =
      memRegion (sp + 30960#64) 512 ∗ memRegion (sp + 31472#64) 512 ∗ memRegion (sp + 31984#64) 512 := by
  rw [mr_split sp 30960 512 1024 31472, mr_split sp 31472 512 512 31984]

private theorem seg2_to_seg3_2064 (sp : BitVec 64) :
    SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ⊢
      memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 := by
  have h1 : SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ⊢ memRegion (sp + 2064#64) 336 :=
    spillSliceMem_entails_memRegion 21 (sp + 2064#64) uHatZetaSpill40
  have h2 : memRegion (sp + 2064#64) 368 =
      memRegion (sp + 2064#64) 336 ∗ memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
        memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 := by
    rw [mr_split sp 2064 336 32 2400, mr_split sp 2400 8 24 2408,
      mr_split sp 2408 8 16 2416, mr_split sp 2416 8 8 2424]
  rw [← mr_split sp 2064 32 336 2096, h2]
  exact entails_sub h1 (by sep_frame) (by sep_frame)

private theorem seg4_collapse_224 (sp : BitVec 64) (p1 p2 p3 p4 : BitVec 64) (v : BitVec 128) :
    memRegion (sp + 224#64) 1760 ∗ ((sp + 1984#64) ↦₆₄ p1) ∗ memRegion (sp + 1992#64) 8 ∗
      ((sp + 2000#64) ↦₆₄ p2) ∗ memRegion (sp + 2008#64) 8 ∗ ((sp + 2016#64) ↦₆₄ p3) ∗
      memRegion (sp + 2024#64) 8 ∗ ((sp + 2032#64) ↦₆₄ p4) ∗ memRegion (sp + 2040#64) 8 ∗
      Vec128At (sp + 2048#64) v ∗ memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 ⊢
      memRegion (sp + 224#64) 2208 := by
  have heq : memRegion (sp + 224#64) 2208 =
      memRegion (sp + 224#64) 1760 ∗ memRegion (sp + 1984#64) 8 ∗ memRegion (sp + 1992#64) 8 ∗
      memRegion (sp + 2000#64) 8 ∗ memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗
      memRegion (sp + 2024#64) 8 ∗ memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗
      memRegion (sp + 2048#64) 16 ∗ memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 := by
    rw [mr_split sp 224 1760 448 1984, mr_split sp 1984 8 440 1992,
      mr_split sp 1992 8 432 2000, mr_split sp 2000 8 424 2008,
      mr_split sp 2008 8 416 2016, mr_split sp 2016 8 408 2024,
      mr_split sp 2024 8 400 2032, mr_split sp 2032 8 392 2040,
      mr_split sp 2040 8 384 2048, mr_split sp 2048 16 368 2064,
      mr_split sp 2064 32 336 2096]
  rw [heq]
  have hsub := sepConj_mono (cell_entails_memRegion8 (sp + 1984#64) p1)
    (sepConj_mono (cell_entails_memRegion8 (sp + 2000#64) p2)
      (sepConj_mono (cell_entails_memRegion8 (sp + 2016#64) p3)
        (sepConj_mono (cell_entails_memRegion8 (sp + 2032#64) p4)
          (vec128At_entails_memRegion16 (sp + 2048#64) v))))
  exact entails_sub hsub (by sep_frame) (by sep_frame)

private theorem seg4_repartition_upper (sp : BitVec 64) :
    memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
      memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 =
    memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 2176 ∗
      memRegion (sp + 6336#64) 8096 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 26352#64) 2016 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 30448#64) 2016 ∗
      memRegion (sp + 32464#64) 1968 := by
  have hA1 : memRegion (sp + 2560#64) 11872 =
      memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
        memRegion (sp + 6208#64) 8224 := by
    rw [mr_split sp 2560 2112 9760 4672, mr_split sp 4672 1536 8224 6208]
  have hA2 : memRegion (sp + 2560#64) 11872 =
      memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 4160#64) 2176 ∗
        memRegion (sp + 6336#64) 8096 := by
    rw [mr_split sp 2560 1600 10272 4160, mr_split sp 4160 2176 8096 6336]
  have hB1 : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
      memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 := by
    rw [mr_split sp 24704 1616 8112 26320, mr_split sp 26320 512 7600 26832,
      mr_split sp 26832 1536 6064 28368, mr_split sp 28368 32 6032 28400,
      mr_split sp 28400 480 5552 28880, mr_split sp 28880 1568 3984 30448,
      mr_split sp 30448 32 3952 30480, mr_split sp 30480 2016 1936 32496]
  have hB2 : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 26352#64) 2016 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 30448#64) 2016 ∗
      memRegion (sp + 32464#64) 1968 := by
    rw [mr_split sp 24704 1616 8112 26320, mr_split sp 26320 32 8080 26352,
      mr_split sp 26352 2016 6064 28368, mr_split sp 28368 672 5392 29040,
      mr_split sp 29040 1408 3984 30448, mr_split sp 30448 2016 1968 32464]
  calc _ = memRegion (sp + 2560#64) 2112 ∗ memRegion (sp + 4672#64) 1536 ∗
          memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 24704#64) 9728 := by
          rw [hB1]
    _ = memRegion (sp + 2560#64) 11872 ∗ memRegion (sp + 24704#64) 9728 := by
          rw [hA1]; sep_ac_rfl
    _ = _ := by rw [hA2, hB2]; sep_ac_rfl

private theorem seg2_to_seg3_regions (sp : BitVec 64) :
    SpillSliceMem 21 (sp + 2064#64) uHatZetaSpill40 ∗
      memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
      memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗
      memRegion (sp + 14432#64) 2048 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 480 ⊢
      memRegion (sp + 2064#64) 32 ∗ memRegion (sp + 2096#64) 336 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 28368#64) 512 := by
  rw [mr_split sp 14432 512 1536 14944, ← mr_split sp 28368 32 480 28400]
  exact entails_sub (seg2_to_seg3_2064 sp) (by sep_frame) (by sep_frame)

private theorem seg3_to_seg4_regions (sp : BitVec 64) :
    memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 4160#64) 2048 ∗
      memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 14944#64) 1536 ∗
      memRegion (sp + 16480#64) 8224 ∗ memRegion (sp + 30448#64) 2048 ∗
      memRegion (sp + 32496#64) 2176 =
    memRegion (sp + 2432#64) 2240 ∗ memRegion (sp + 4672#64) 1536 ∗
      memRegion (sp + 14432#64) 10272 ∗
      memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 30480#64) 2016 ∗
      memRegion (sp + 32496#64) 1936 ∗ memRegion (sp + 34432#64) 32 ∗
      memRegion (sp + 34464#64) 208 := by
  rw [mr_split sp 4160 512 1536 4672, mr_split sp 2432 1728 512 4160,
    mr_split sp 14432 2048 8224 16480, mr_split sp 14432 512 1536 14944,
    mr_split sp 30448 32 2016 30480,
    mr_split sp 32496 1936 240 34432, mr_split sp 34432 32 208 34464]
  sep_ac_rfl

private theorem compressAndEncode_len (d : Nat) (f : Poly) :
    (compressAndEncode d f).length = (256 * d) / 8 := by
  simp [compressAndEncode, byteEncode, bitsToBytes]

private theorem indCpaDecrypt_length (k dU dV : Nat) (skPke ct : List (BitVec 8)) :
    (indCpaDecrypt k dU dV skPke ct).length = 32 := by
  unfold indCpaDecrypt; exact compressAndEncode_len 1 _

/-! ## 3. Shared Prefix (`Seg1a .. Seg4`, `0x0000 → 0x40f0`) -/

private def Rest5Spatial (s0 : State) (ret skA ctA : BitVec 64)
    (sk ct : List (BitVec 8)) (F : SepProp) : SepProp :=
  let sp := s0.sp - 34832#64
  let m := indCpaDecrypt 4 11 5 (sk.take 1536) ct
  let pk := (sk.drop 1536).take 1568
  let hPk := (sk.drop 3104).take 32
  let z := (sk.drop 3136).take 32
  stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗ SpilledDecapsWords sp m ∗
    ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
    memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ sha3_512List (m ++ hPk)) ∗
    memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 6336#64) 8096 ∗
    PolyMem (sp + 22624#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
    PolyMem (sp + 23136#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
    PolyMem (sp + 23648#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
    PolyMem (sp + 24160#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
    ((sp + 24672#64) ↦ₛ List.replicate 32 0#8) ∗
    memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26352#64) 2016 ∗
    memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 32464#64) 1968 ∗
    ((sp + 34432#64) ↦ₛ shake256List 32 (z ++ ct)) ∗ memRegion (sp + 34464#64) 208 ∗
    (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F

attribute [local irreducible] polyVecNat tHatModPoly16 indCpaDecrypt sha3_512List shake256List in
set_option maxHeartbeats 800000 in
private theorem seg1_to_4_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (sk ct : List (BitVec 8)) (F : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running) (hsp0 : s0.spAligned = true)
    (hcl0 : mlkemMultiLib.CodeLoaded mlkemMpl s0.mem) (hro0 : MlKemRoOk mlkemMpl s0.mem)
    (hx0 : s0.readReg64 .x0 = ret) (hx1 : s0.readReg64 .x1 = skA) (hx2 : s0.readReg64 .x2 = ctA)
    (hsk : sk.length = 3168) (hct : ct.length = 1568) :
    let sp := s0.sp - 34832#64
    let pk := (sk.drop 1536).take 1568
    SepWP (blkPC06.rebase b (fun _ => none)) (b + off40f0) s0
      (stackAt s0.sp 35968 ∗ (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F)
      (fun sf Pf =>
        sf.sp = sp ∧ sf.spAligned = true ∧
        sf.readReg64 .x9 = sp + 30459#64 ∧ sf.readReg64 .x20 = sp + 28379#64 ∧
        sf.readReg64 .x22 = sp + 4160#64 ∧ sf.readReg64 .x23 = sp + 24576#64 ∧
        sf.readReg64 .x25 = sp + 28368#64 ∧ sf.readReg64 .x26 = sp + 28632#64 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readVReg128 0#5 = rhoW (pkRho pk) 1 ++ rhoW (pkRho pk) 0 ∧
        sf.readVReg128 1#5 = rhoW (pkRho pk) 3 ++ rhoW (pkRho pk) 2 ∧
        (Pf ⊢ memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
          memRegion (sp + 224#64) 2208 ∗ memRegion (sp + 4160#64) 2176 ∗
          memRegion (sp + 14432#64) 8192 ∗ memRegion (sp + 26320#64) 32 ∗
          memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 30448#64) 2016 ∗
          Rest5Spatial s0 ret skA ctA sk ct F)) := by
  intro sp pk
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl0 hro0
      (seg1a_ok hb hbase s0 ret skA ctA ((skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ F)
        hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2) ?_)
  rintro s1 P1 hpc1 hrun1 hcl1 hro1
    ⟨hsp1, hspA1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx25_1, hx26_1, hP1⟩
  have hP1' : P1 ⊢ memRegion (sp + 14432#64) 512 ∗ memRegion (sp + 2048#64) 16 ∗
      (memRegion (sp + 2032#64) 8 ∗ memRegion (sp + 30448#64) 512 ∗ memRegion (sp + 30960#64) 512 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
        (memRegion (sp + 136#64) 8 ∗ memRegion (sp + 2016#64) 8 ∗ memRegion (sp + 2064#64) 336 ∗
          memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 31472#64) 512 ∗
          memRegion (sp + 31984#64) 512 ∗ ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
          ((skA + 1536#64) ↦ₛ sk.drop 1536) ∗ stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗
          memRegion sp 128 ∗ ((sp + 128#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 72 ∗
          ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗ memRegion (sp + 224#64) 1760 ∗
          ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ memRegion (sp + 1992#64) 8 ∗
          ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2008#64) 8 ∗
          memRegion (sp + 2024#64) 8 ∗ memRegion (sp + 2040#64) 8 ∗
          memRegion (sp + 2400#64) 8 ∗ memRegion (sp + 2408#64) 8 ∗
          memRegion (sp + 2416#64) 8 ∗ memRegion (sp + 2424#64) 8 ∗
          memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 4160#64) 2048 ∗
          memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 16480#64) 8224 ∗
          memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 512 ∗
          memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 32 ∗
          memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
          memRegion (sp + 32496#64) 2176 ∗ (ctA ↦ₛ ct) ∗ F)) := by
    refine Entails.trans hP1 ?_
    dsimp only [Seg1aSpatial]
    rw [mr_split sp 136 8 72 144, seg1a_split_28952 sp, seg1a_split_30960 sp,
      sk_pointsTo_split skA hsk]
    sep_frame
  refine SepWP.weaken_pre hP1' ?_
  sep_frame_apply (sepWP_elim_poly32 (a := sp + 14432#64)); intro vInit
  sep_frame_apply (sepWP_elim_vec128At (a := sp + 2048#64)); intro v2048
  refine SepWP.weaken_pre (by sep_frame)
    (sepWP_seq_env hcl1 hro1
      (seg1b_ok hb hbase s1 sp skA ctA vInit v2048 sk _
        hpc1 hrun1 hsp1 hspA1 hcl1 hro1 hx19_1 hx20_1 hx21_1 hx22_1 hx25_1 hx26_1 hsk) ?_)
  rintro s2 P2 hpc2 hrun2 hcl2 hro2 ⟨hsp2, hspA2, hfp2, _, hx20_2, hx22_2, hx25_2, hx26_2, hP2⟩
  refine SepWP.weaken_pre (Entails.trans hP2 (by sep_frame))
    (sepWP_seq_env hcl2 hro2
      (seg1c_ok hb hbase s2 sp skA ctA sk _
        hpc2 hrun2 hsp2 hspA2 hcl2 hro2 hx20_2 hx22_2 hx25_2 hx26_2 hsk) ?_)
  rintro s3 P3 hpc3 hrun3 hcl3 hro3
    ⟨hsp3, hspA3, hfp3, hx0_3, hx19_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3,
      hx27_3, hx28_3, hv8_3, _, hP3⟩
  have hv8_3' : (s3.readVReg128 8#5).truncate 64 = 0x0d010d010d010d01#64 := by
    rw [hv8_3, dup4hLow_3329_trunc64]
  refine SepWP.weaken_pre (Entails.trans hP3 (by sep_frame))
    (sepWP_seq_env hcl3 hro3
      (seg2_uhat_ok hb hbase s3 sp ctA ct _
        hpc3 hrun3 hsp3 hspA3 hcl3 hro3 hx0_3 hx19_3 hx22_3 hx23_3 hx24_3 hx27_3 hx28_3 hv8_3' hct) ?_)
  rintro s4 P4 hpc4 hrun4 hcl4 hro4 ⟨hsp4, hspA4, hfp4, hx25_4, hx26_4, _, _, hP4⟩
  let Rest3 : SepProp :=
    SavedFrame06 s0.sp s0 ∗ memRegion sp 128 ∗ ((sp + 128#64) ↦₆₄ ret) ∗
      memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
      memRegion (sp + 224#64) 1760 ∗
      ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ memRegion (sp + 1992#64) 8 ∗
      ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗ memRegion (sp + 2008#64) 8 ∗
      ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ memRegion (sp + 2024#64) 8 ∗
      ((sp + 2032#64) ↦₆₄ skA) ∗ memRegion (sp + 2040#64) 8 ∗
      Vec128At (sp + 2048#64) cst16_3_val ∗ memRegion (sp + 2064#64) 32 ∗
      memRegion (sp + 2432#64) 1728 ∗ memRegion (sp + 6208#64) 8224 ∗
      memRegion (sp + 14944#64) 1536 ∗ memRegion (sp + 16480#64) 8224 ∗
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26832#64) 1536 ∗
      memRegion (sp + 28880#64) 1568 ∗ memRegion (sp + 32496#64) 2176 ∗
      (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      ((skA + 1536#64) ↦ₛ sk.drop 1536) ∗ F
  refine SepWP.weaken_pre ?_
    (sepWP_seq_env hcl4 hro4
      (seg3_decrypt_ok hb hbase s4 sp ctA (sk := sk) hct Rest3
        hpc4 hrun4 hsp4 hspA4 hcl4 hro4) ?_)
  · exact Entails.trans hP4
      (entails_sub (seg2_to_seg3_regions sp)
        (by dsimp only [sp]; sep_frame) (by dsimp only [sp, Rest3]; sep_frame))
  rintro s5 P5 hpc5 hrun5 hcl5 hro5 ⟨hsp5, hspA5, hx23_5, hx25_5, hx26_5, hfp5, hP5⟩
  dsimp only [Rest3] at hP5
  set m := indCpaDecrypt 4 11 5 (sk.take 1536) ct
  set hPk := (sk.drop 3104).take 32
  set z := (sk.drop 3136).take 32
  have hm : m.length = 32 := indCpaDecrypt_length 4 11 5 (sk.take 1536) ct
  have hpk : pk.length = 1568 := by simp [pk, hsk]
  have hhPk : hPk.length = 32 := by simp [hPk, hsk]
  have hz : z.length = 32 := by simp [z, hsk]
  have h4_pre : P5 ⊢ stackAt sp 1136 ∗ memRegion sp 128 ∗
      ((sp + 1984#64) ↦₆₄ (skA + 3104#64)) ∗ ((sp + 2000#64) ↦₆₄ (skA + 3136#64)) ∗
      ((sp + 2016#64) ↦₆₄ (skA + 384#64)) ∗ ((sp + 2032#64) ↦₆₄ skA) ∗
      Vec128At (sp + 2048#64) cst16_3_val ∗
      memRegion (sp + 2432#64) 2240 ∗ memRegion (sp + 14432#64) 10272 ∗
      ((sp + 28368#64) ↦ₛ m) ∗ memRegion (sp + 30448#64) 32 ∗ memRegion (sp + 34432#64) 32 ∗
      ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗
      ((skA + 3136#64) ↦ₛ z) ∗ (ctA ↦ₛ ct) ∗
      (SavedFrame06 s0.sp s0 ∗ ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 144#64) 72 ∗ ((sp + 216#64) ↦₆₄ (sp + 30712#64)) ∗
        memRegion (sp + 224#64) 1760 ∗ memRegion (sp + 1992#64) 8 ∗
        memRegion (sp + 2008#64) 8 ∗ memRegion (sp + 2024#64) 8 ∗
        memRegion (sp + 2040#64) 8 ∗ memRegion (sp + 2064#64) 32 ∗
        memRegion (sp + 2096#64) 336 ∗ memRegion (sp + 4672#64) 1536 ∗
        memRegion (sp + 6208#64) 8224 ∗ memRegion (sp + 24704#64) 1616 ∗
        memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 ∗
        memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1568 ∗
        memRegion (sp + 30480#64) 2016 ∗ memRegion (sp + 32496#64) 1936 ∗
        memRegion (sp + 34464#64) 208 ∗
        (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
        ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
        ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗ F) := by
    refine Entails.trans hP5 ?_
    rw [sk_tail_split skA hsk]
    exact entails_sub (Entails.of_eq (seg3_to_seg4_regions sp))
      (by dsimp only [sp]; sep_frame) (by dsimp only [sp, pk, hPk, z]; sep_frame)
  refine SepWP.weaken_pre h4_pre
    (sepWP_seq_env hcl5 hro5
      (seg4_ok hb hbase s5 sp skA ctA m pk hPk z ct _
        hm hpk hhPk hz hct hpc5 hrun5 hsp5 hspA5 hcl5 hro5 hx23_5) ?_)
  rintro sf Pf hpc_f hrun_f _ _
    ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f, hx25_f, hx26_f, hfp_f, hv0_f, hv1_f, hPf⟩
  refine SepWP.done hpc_f hrun_f
    ⟨hsp_f, hspA_f, hx9_f, hx20_f, hx22_f, hx23_f,
      hx25_f.trans (hx25_5.trans (hx25_4.trans hx25_3)),
      hx26_f.trans (hx26_5.trans (hx26_4.trans hx26_3)),
      hfp_f.trans (hfp5.trans (hfp4.trans (hfp3.trans (hfp2.trans hfp1)))),
      hv0_f, hv1_f, ?_⟩
  refine Entails.trans hPf ?_
  dsimp only [Rest5Spatial]
  have hsk_join : (skA ↦ₛ sk.take 384) ∗ ((skA + 384#64) ↦ₛ (sk.drop 384).take 384) ∗
      ((skA + 768#64) ↦ₛ (sk.drop 768).take 384) ∗
      ((skA + 1152#64) ↦ₛ (sk.drop 1152).take 384) ∗
      ((skA + 1536#64) ↦ₛ pk) ∗ ((skA + 3104#64) ↦ₛ hPk) ∗ ((skA + 3136#64) ↦ₛ z) =
      (skA ↦ₛ sk) := by
    rw [sk_pointsTo_split skA hsk, sk_tail_split skA hsk]
  refine entails_sub (seg4_collapse_224 sp (skA + 3104#64) (skA + 3136#64) (skA + 384#64) skA cst16_3_val)
    (by sep_frame) ?_
  refine entails_sub (Entails.of_eq hsk_join) (by sep_frame) ?_
  exact entails_sub (Entails.of_eq (seg4_repartition_upper sp)) (by sep_frame) (by sep_frame)

/-! ## 4. Shared Suffix (`Seg6 .. Seg9`, `0x76a8 → ret`) -/

private theorem seg5_to_seg6_regions (sp : BitVec 64) :
    memRegion (sp + 144#64) 2288 ∗ memRegion (sp + 4160#64) 2176 ∗
      memRegion (sp + 6336#64) 8096 ∗ memRegion (sp + 24704#64) 1616 ∗
      memRegion (sp + 26320#64) 32 ∗ memRegion (sp + 26352#64) 2016 ∗
      memRegion (sp + 28368#64) 672 ∗ memRegion (sp + 29040#64) 1408 ∗
      memRegion (sp + 30448#64) 2016 ∗ memRegion (sp + 32464#64) 1968 ∗
      memRegion (sp + 34464#64) 208 =
    memRegion (sp + 1488#64) 944 ∗ memRegion (sp + 4160#64) 10272 ∗
      memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
      memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 2048 ∗
      memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 132 ∗
      memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗
      memRegion (sp + 34464#64) 128 ∗
      (memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 26305#64) 15 ∗
        memRegion (sp + 30416#64) 32 ∗ memRegion (sp + 32496#64) 512 ∗
        memRegion (sp + 33140#64) 396 ∗ memRegion (sp + 33664#64) 224 ∗
        memRegion (sp + 34016#64) 416 ∗ memRegion (sp + 34592#64) 80) := by
  have h1 : memRegion (sp + 144#64) 2288 =
      memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 944 := mr_split sp 144 1344 944 1488
  have h2 : memRegion (sp + 4160#64) 10272 =
      memRegion (sp + 4160#64) 2176 ∗ memRegion (sp + 6336#64) 8096 := mr_split sp 4160 2176 8096 6336
  have h3a : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1616 ∗ memRegion (sp + 26320#64) 32 ∗
      memRegion (sp + 26352#64) 2016 ∗ memRegion (sp + 28368#64) 672 ∗
      memRegion (sp + 29040#64) 1408 ∗ memRegion (sp + 30448#64) 2016 ∗
      memRegion (sp + 32464#64) 1968 := by
    rw [mr_split sp 24704 1616 8112 26320, mr_split sp 26320 32 8080 26352,
      mr_split sp 26352 2016 6064 28368, mr_split sp 28368 672 5392 29040,
      mr_split sp 29040 1408 3984 30448, mr_split sp 30448 2016 1968 32464]
  have h3b : memRegion (sp + 24704#64) 9728 =
      memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
      memRegion (sp + 26305#64) 15 ∗ memRegion (sp + 26320#64) 2048 ∗
      memRegion (sp + 28368#64) 2048 ∗ memRegion (sp + 30416#64) 32 ∗
      memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 32496#64) 512 ∗
      memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33140#64) 396 ∗
      memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33664#64) 224 ∗
      memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34016#64) 416 := by
    rw [mr_split sp 24704 1568 8160 26272, mr_split sp 26272 33 8127 26305,
      mr_split sp 26305 15 8112 26320, mr_split sp 26320 2048 6064 28368,
      mr_split sp 28368 2048 4016 30416, mr_split sp 30416 32 3984 30448,
      mr_split sp 30448 2048 1936 32496, mr_split sp 32496 512 1424 33008,
      mr_split sp 33008 132 1292 33140, mr_split sp 33140 396 896 33536,
      mr_split sp 33536 128 768 33664, mr_split sp 33664 224 544 33888,
      mr_split sp 33888 128 416 34016]
  have h4 : memRegion (sp + 34464#64) 208 =
      memRegion (sp + 34464#64) 128 ∗ memRegion (sp + 34592#64) 80 := mr_split sp 34464 128 80 34592
  calc _ = memRegion (sp + 144#64) 2288 ∗ memRegion (sp + 4160#64) 2176 ∗
          memRegion (sp + 6336#64) 8096 ∗ memRegion (sp + 24704#64) 9728 ∗
          memRegion (sp + 34464#64) 208 := by
          rw [h3a]; sep_ac_rfl
    _ = memRegion (sp + 144#64) 2288 ∗ memRegion (sp + 4160#64) 10272 ∗
          memRegion (sp + 24704#64) 9728 ∗ memRegion (sp + 34464#64) 208 := by
          rw [h2]; sep_ac_rfl
    _ = _ := by rw [h1, h3b, h4]; sep_ac_rfl

private theorem seg8_to_seg9_scratch (sp : BitVec 64) (ctA : BitVec 64)
    (pk m hashed ct' : List (BitVec 8))
    (e2 r0 r1 r2 r3 : Nat → BitVec 128)
    (hh : hashed.length = 64) (hct' : ct'.length = 1568) :
    SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      memRegion (sp + 144#64) 1344 ∗ PolyMem (sp + 1488#64) e2 ∗
      memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 208 ∗
      memRegion (sp + 2432#64) 64 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
      memRegion (sp + 2560#64) 1600 ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
      PolyMem (sp + 14432#64) r0 ∗ PolyMem (sp + 14944#64) r1 ∗
      PolyMem (sp + 15456#64) r2 ∗ PolyMem (sp + 15968#64) r3 ∗
      memRegion (sp + 16480#64) 24 ∗ memRegion (sp + 16504#64) 8200 ∗
      ((sp + 24704#64) ↦ₛ ct') ∗ memRegion (sp + 26272#64) 33 ∗
      memRegion (sp + 26305#64) 15 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28368#64) 512 ∗
      memRegion (sp + 28880#64) 1536 ∗ memRegion (sp + 30416#64) 32 ∗
      memRegion (sp + 32016#64) 480 ∗ memRegion (sp + 32496#64) 512 ∗
      memRegion (sp + 33008#64) 512 ∗ memRegion (sp + 33520#64) 8 ∗
      memRegion (sp + 33528#64) 8 ∗ memRegion (sp + 33536#64) 352 ∗
      memRegion (sp + 33888#64) 352 ∗ memRegion (sp + 34240#64) 192 ∗
      memRegion (sp + 34464#64) 128 ∗ memRegion (sp + 34592#64) 80 ⊢
    ((sp + 2496#64) ↦ₛ hashed.take 32) ∗
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 64 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 34368#64) 32 ∗
      memRegion (sp + 34400#64) 32 ∗ memRegion (sp + 34592#64) 32 ∗
      memRegion (sp + 34624#64) 32 ∗
      (memRegion sp 128 ∗ memRegion (sp + 136#64) 2360 ∗
        memRegion (sp + 2528#64) 1632 ∗ memRegion (sp + 4192#64) 10240 ∗
        memRegion (sp + 14496#64) 13872 ∗ memRegion (sp + 28400#64) 2048 ∗
        memRegion (sp + 32016#64) 2352 ∗ memRegion (sp + 34464#64) 128 ∗
        memRegion (sp + 34656#64) 16) := by
  have hhashed : ((sp + 2496#64) ↦ₛ hashed) ⊢
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗ memRegion (sp + 2528#64) 32 := by
    have hsplit : hashed = hashed.take 32 ++ hashed.drop 32 := (List.take_append_drop 32 hashed).symm
    have htk : (hashed.take 32).length = 32 := by simp [hh]
    have hdr : (hashed.drop 32).length = 32 := by simp [hh]
    conv_lhs => rw [hsplit]
    rw [pointsToBytes_append, htk,
      show sp + 2496#64 + BitVec.ofNat 64 32 = sp + 2528#64 by bv_omega]
    exact sepConj_mono_right
      (by simpa only [hdr] using pointsToBytes_entails_memRegion (sp + 2528#64) (hashed.drop 32))
  have he2 : PolyMem (sp + 1488#64) e2 ⊢ memRegion (sp + 1488#64) 512 :=
    vecRangeMem_entails_memRegion 32 (sp + 1488#64) e2
  have hr4 : PolyMem (sp + 14432#64) r0 ∗ PolyMem (sp + 14944#64) r1 ∗
      PolyMem (sp + 15456#64) r2 ∗ PolyMem (sp + 15968#64) r3 ⊢ memRegion (sp + 14432#64) 2048 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using polyMem4_entails_2048 (sp + 14432#64) r0 r1 r2 r3
  have hct_mr : ((sp + 24704#64) ↦ₛ ct') ⊢ memRegion (sp + 24704#64) 1568 := by
    simpa only [hct'] using pointsToBytes_entails_memRegion (sp + 24704#64) ct'
  have hsub := sepConj_mono (spilledDecapsWords_entails_memRegion128 sp m)
    (sepConj_mono (cell_entails_memRegion8 (sp + 136#64) ctA)
      (sepConj_mono he2
        (sepConj_mono hhashed
          (sepConj_mono (publicKeyStateAt_entails_memRegion (sp + 4160#64) pk)
            (sepConj_mono hr4 hct_mr)))))
  refine entails_sub hsub (by sep_frame) ?_
  have m136 : memRegion (sp + 136#64) 2360 =
      memRegion (sp + 136#64) 8 ∗ memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 1488#64) 512 ∗
      memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 208 ∗ memRegion (sp + 2432#64) 64 := by
    rw [mr_split sp 136 8 2352 144, mr_split sp 144 1344 1008 1488,
      mr_split sp 1488 512 496 2000, mr_split sp 2000 224 272 2224,
      mr_split sp 2224 208 64 2432]
  have m2528 : memRegion (sp + 2528#64) 1632 =
      memRegion (sp + 2528#64) 32 ∗ memRegion (sp + 2560#64) 1600 := mr_split sp 2528 32 1600 2560
  have m4160 : memRegion (sp + 4160#64) 10272 =
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 4192#64) 10240 := mr_split sp 4160 32 10240 4192
  have m14432a : memRegion (sp + 14432#64) 13936 =
      memRegion (sp + 14432#64) 2048 ∗ memRegion (sp + 16480#64) 24 ∗
      memRegion (sp + 16504#64) 8200 ∗ memRegion (sp + 24704#64) 1568 ∗
      memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 26305#64) 15 ∗
      memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 := by
    rw [mr_split sp 14432 2048 11888 16480, mr_split sp 16480 24 11864 16504,
      mr_split sp 16504 8200 3664 24704, mr_split sp 24704 1568 2096 26272,
      mr_split sp 26272 33 2063 26305, mr_split sp 26305 15 2048 26320,
      mr_split sp 26320 512 1536 26832]
  have m14432b : memRegion (sp + 14432#64) 13936 =
      memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 14496#64) 13872 := mr_split sp 14432 64 13872 14496
  have m28368 : memRegion (sp + 28368#64) 512 =
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 480 := mr_split sp 28368 32 480 28400
  have m28400 : memRegion (sp + 28400#64) 2048 =
      memRegion (sp + 28400#64) 480 ∗ memRegion (sp + 28880#64) 1536 ∗
      memRegion (sp + 30416#64) 32 := by
    rw [mr_split sp 28400 480 1568 28880, mr_split sp 28880 1536 32 30416]
  have m32016a : memRegion (sp + 32016#64) 2416 =
      memRegion (sp + 32016#64) 480 ∗ memRegion (sp + 32496#64) 512 ∗
      memRegion (sp + 33008#64) 512 ∗ memRegion (sp + 33520#64) 8 ∗
      memRegion (sp + 33528#64) 8 ∗ memRegion (sp + 33536#64) 352 ∗
      memRegion (sp + 33888#64) 352 ∗ memRegion (sp + 34240#64) 192 := by
    rw [mr_split sp 32016 480 1936 32496, mr_split sp 32496 512 1424 33008,
      mr_split sp 33008 512 912 33520, mr_split sp 33520 8 904 33528,
      mr_split sp 33528 8 896 33536, mr_split sp 33536 352 544 33888,
      mr_split sp 33888 352 192 34240]
  have m32016b : memRegion (sp + 32016#64) 2416 =
      memRegion (sp + 32016#64) 2352 ∗ memRegion (sp + 34368#64) 32 ∗
      memRegion (sp + 34400#64) 32 := by
    rw [mr_split sp 32016 2352 64 34368, mr_split sp 34368 32 32 34400]
  have m34592 : memRegion (sp + 34592#64) 80 =
      memRegion (sp + 34592#64) 32 ∗ memRegion (sp + 34624#64) 32 ∗
      memRegion (sp + 34656#64) 16 := by
    rw [mr_split sp 34592 32 48 34624, mr_split sp 34624 32 16 34656]
  rw [m136, m2528, m4160, m28368, m28400, m34592]
  refine entails_sub (Entails.of_eq (m14432a.symm.trans m14432b)) (by sep_frame) ?_
  exact entails_sub (Entails.of_eq (m32016a.symm.trans m32016b)) (by sep_frame) (by sep_frame)

private theorem seg9_merge_stack (sp0 : BitVec 64) :
    let sp := sp0 - 34832#64
    memRegion (sp + 128#64) 8 ∗ memRegion (sp + 2496#64) 32 ∗
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 64 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 30448#64) 1568 ∗
      memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
      memRegion (sp + 34432#64) 32 ∗ memRegion (sp + 34592#64) 32 ∗
      memRegion (sp + 34624#64) 32 ∗ stackAt sp 1136 ∗
      memRegion (sp0 - 160#64) 160 ∗
      (memRegion sp 128 ∗ memRegion (sp + 136#64) 2360 ∗
        memRegion (sp + 2528#64) 1632 ∗ memRegion (sp + 4192#64) 10240 ∗
        memRegion (sp + 14496#64) 13872 ∗ memRegion (sp + 28400#64) 2048 ∗
        memRegion (sp + 32016#64) 2352 ∗ memRegion (sp + 34464#64) 128 ∗
        memRegion (sp + 34656#64) 16) ⊢
    stackAt sp0 35968 := by
  intro sp
  have hm : memRegion sp 34672 =
      memRegion sp 128 ∗ memRegion (sp + 128#64) 8 ∗ memRegion (sp + 136#64) 2360 ∗
      memRegion (sp + 2496#64) 32 ∗ memRegion (sp + 2528#64) 1632 ∗
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 4192#64) 10240 ∗
      memRegion (sp + 14432#64) 64 ∗ memRegion (sp + 14496#64) 13872 ∗
      memRegion (sp + 28368#64) 32 ∗ memRegion (sp + 28400#64) 2048 ∗
      memRegion (sp + 30448#64) 1568 ∗ memRegion (sp + 32016#64) 2352 ∗
      memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
      memRegion (sp + 34432#64) 32 ∗ memRegion (sp + 34464#64) 128 ∗
      memRegion (sp + 34592#64) 32 ∗ memRegion (sp + 34624#64) 32 ∗
      memRegion (sp + 34656#64) 16 := by
    rw [memRegion_split' (b := sp) (b' := sp + 128#64) (n := 128) (k := (34544 : Nat)) rfl rfl (by decide),
      mr_split sp 128 8 34536 136, mr_split sp 136 2360 32176 2496,
      mr_split sp 2496 32 32144 2528, mr_split sp 2528 1632 30512 4160,
      mr_split sp 4160 32 30480 4192, mr_split sp 4192 10240 20240 14432,
      mr_split sp 14432 64 20176 14496, mr_split sp 14496 13872 6304 28368,
      mr_split sp 28368 32 6272 28400, mr_split sp 28400 2048 4224 30448,
      mr_split sp 30448 1568 2656 32016, mr_split sp 32016 2352 304 34368,
      mr_split sp 34368 32 272 34400, mr_split sp 34400 32 240 34432,
      mr_split sp 34432 32 208 34464, mr_split sp 34464 128 80 34592,
      mr_split sp 34592 32 48 34624, mr_split sp 34624 32 16 34656]
  have hstk := stackAt_35968_eq sp0
  dsimp only at hstk
  rw [hstk, hm]
  sep_frame

private theorem indCpaEncryptWith_4_11_5_ct_len
    (sampler : List (BitVec 8) → Poly) (pk m coins : List (BitVec 8)) :
    ((indCpaEncryptWith sampler 4 11 5 pk m coins).1 ++
      (indCpaEncryptWith sampler 4 11 5 pk m coins).2.1).length = 1568 := by
  dsimp only [indCpaEncryptWith]
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_assoc, List.append_nil, List.length_append, compressAndEncode_len]

private theorem seg6_to_seg7_regions (sp : BitVec 64) :
    memRegion (sp + 14432#64) 10272 ∗ memRegion (sp + 24704#64) 1568 ∗
      (memRegion (sp + 33008#64) 132 ∗ memRegion (sp + 33140#64) 396) ∗
      (memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33664#64) 224) ∗
      (memRegion (sp + 33888#64) 128 ∗ memRegion (sp + 34016#64) 416) =
    memRegion (sp + 14432#64) 2072 ∗ memRegion (sp + 16504#64) 8200 ∗
      memRegion (sp + 24704#64) 1408 ∗ memRegion (sp + 26112#64) 160 ∗
      memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33528#64) 8 ∗
      memRegion (sp + 33536#64) 352 ∗
      memRegion (sp + 33888#64) 352 ∗ memRegion (sp + 34240#64) 192 := by
  rw [mr_split sp 14432 2072 8200 16504, mr_split sp 24704 1408 160 26112,
    ← mr_split sp 33008 132 396 33140, mr_split sp 33008 520 8 33528,
    ← mr_split sp 33536 128 224 33664,
    ← mr_split sp 33888 128 416 34016, mr_split sp 33888 352 192 34240]
  sep_ac_rfl

private theorem seg7_to_seg8_regions (sp : BitVec 64) :
    memRegion (sp + 2000#64) 432 ∗ memRegion (sp + 26320#64) 2048 ∗
      memRegion (sp + 28368#64) 2048 ∗ memRegion (sp + 30448#64) 2048 ∗
      memRegion (sp + 33008#64) 520 =
    memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 2224#64) 208 ∗
      memRegion (sp + 26320#64) 512 ∗ memRegion (sp + 26832#64) 1536 ∗
      memRegion (sp + 28368#64) 512 ∗ memRegion (sp + 28880#64) 1536 ∗
      memRegion (sp + 30448#64) 1568 ∗ memRegion (sp + 32016#64) 480 ∗
      memRegion (sp + 33008#64) 512 ∗ memRegion (sp + 33520#64) 8 := by
  rw [mr_split sp 2000 224 208 2224, mr_split sp 26320 512 1536 26832,
    mr_split sp 28368 512 1536 28880, mr_split sp 30448 1568 480 32016,
    mr_split sp 33008 512 8 33520]
  sep_ac_rfl

attribute [local irreducible] polyVecNat tHatModPoly16 indCpaDecrypt indCpaEncryptWith sha3_512List shake256List in
set_option maxHeartbeats 800000 in
private theorem seg6_to_9_ok [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl06 b) (hbase : blkPl06.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (sk ct : List (BitVec 8))
    (hsp0 : s0.spAligned = true) (_hsk : sk.length = 3168) (hct : ct.length = 1568)
    (s5 : State) (P5 : SepProp)
    (hp5 : Seg5MatrixPost06 b (s0.sp - 34832#64) (s0.sp - 96#64)
      (pkRho ((sk.drop 1536).take 1568))
      (Rest5Spatial s0 ret skA ctA sk ct (memRegion ret 32 ∗ emp)) s5 P5) :
    SepWP (blkPC06.rebase b (fun _ => none)) (s0.readReg64 .lr) s5 P5
      (sepPost (fun sf => sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        ((skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ (ret ↦ₛ kyber1024Decaps sk ct) ∗ stackAt s0.sp 35968)) := by
  set sp := s0.sp - 34832#64
  set m := indCpaDecrypt 4 11 5 (sk.take 1536) ct
  set pk := (sk.drop 1536).take 1568
  set hPk := (sk.drop 3104).take 32
  set z := (sk.drop 3136).take 32
  set hashed := sha3_512List (m ++ hPk)
  set kRejPre := shake256List 32 (z ++ ct)
  have hm : m.length = 32 := indCpaDecrypt_length 4 11 5 (sk.take 1536) ct
  have hh : hashed.length = 64 := sha3_512List_len (m ++ hPk)
  have hcoins : (hashed.drop 32).length = 32 := by simp [hh]
  have hkBar : (hashed.take 32).length = 32 := by simp [hh]
  have hkRej : kRejPre.length = 32 := shake256List_len 32 (z ++ ct)
  rcases hp5 with ⟨hpc5, hrun5, hsp5, hspA5, _, hcl5, hro5, _, _, _, hx25_5, _, hfp5, hP5⟩
  have hP5' : P5 ⊢ memRegion (sp + 1488#64) 944 ∗ ((sp + 2496#64) ↦ₛ hashed) ∗
      memRegion (sp + 4160#64) 10272 ∗ PublicKeyStateAt (sp + 14432#64) pk ∗
      memRegion (sp + 24704#64) 1568 ∗ memRegion (sp + 26272#64) 33 ∗
      memRegion (sp + 26320#64) 2048 ∗ memRegion (sp + 28368#64) 2048 ∗
      memRegion (sp + 30448#64) 2048 ∗ memRegion (sp + 33008#64) 132 ∗
      memRegion (sp + 33536#64) 128 ∗ memRegion (sp + 33888#64) 128 ∗
      memRegion (sp + 34464#64) 128 ∗ stackAt sp 1136 ∗
      (SavedFrame06 s0.sp s0 ∗ SpilledDecapsWords sp m ∗
        ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 2432#64) 64 ∗
        memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 26305#64) 15 ∗
        memRegion (sp + 30416#64) 32 ∗ memRegion (sp + 32496#64) 512 ∗
        memRegion (sp + 33140#64) 396 ∗ memRegion (sp + 33664#64) 224 ∗
        memRegion (sp + 34016#64) 416 ∗ ((sp + 34432#64) ↦ₛ kRejPre) ∗
        memRegion (sp + 34592#64) 80 ∗ (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32) := by
    refine Entails.trans hP5 ?_
    dsimp only [Rest5Spatial]
    rw [publicKeyStateAt_14432_eq sp pk]
    exact entails_sub (Entails.of_eq (seg5_to_seg6_regions sp)) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP5'
    (SepWP.seq
      (seg6_ok hb hbase s5 sp pk hashed _ hh hpc5 hrun5 hsp5 hspA5 hx25_5 hcl5 hro5) ?_)
  rintro s6 P6 hpc6 hrun6 ⟨hsp6, hspA6, hx20_6, hfp6, hcl6, hro6, hP6⟩
  have hfp6' : s6.readReg64 .fp = s0.sp - 96#64 := hfp6.trans hfp5
  have hP6' : P6 ⊢ memRegion (sp + 2000#64) 432 ∗ ATransAt (sp + 4160#64) (pkRho pk) ∗
      memRegion (sp + 14432#64) 2072 ∗ memRegion (sp + 24704#64) 1408 ∗
      PolyMem (sp + 26320#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [0#8])))) ∗
      PolyMem (sp + 26832#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [1#8])))) ∗
      PolyMem (sp + 27344#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [2#8])))) ∗
      PolyMem (sp + 27856#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [3#8])))) ∗
      PolyMem (sp + 28368#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [4#8])))) ∗
      PolyMem (sp + 28880#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [5#8])))) ∗
      PolyMem (sp + 29392#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [6#8])))) ∗
      PolyMem (sp + 29904#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [7#8])))) ∗
      PolyMem (sp + 30448#64) (fun _ => 0#128) ∗ PolyMem (sp + 30960#64) (fun _ => 0#128) ∗
      PolyMem (sp + 31472#64) (fun _ => 0#128) ∗ PolyMem (sp + 31984#64) (fun _ => 0#128) ∗
      memRegion (sp + 33008#64) 520 ∗ memRegion (sp + 33536#64) 352 ∗
      memRegion (sp + 33888#64) 352 ∗
      (PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [8#8])))) ∗
        ((sp + 2496#64) ↦ₛ hashed) ∗
        PolyMem (sp + 12352#64) (polyVecNat (tHatModPoly16 (pkEk0 pk))) ∗
        PolyMem (sp + 12864#64) (polyVecNat (tHatModPoly16 (pkEk1 pk))) ∗
        PolyMem (sp + 13376#64) (polyVecNat (tHatModPoly16 (pkEk2 pk))) ∗
        PolyMem (sp + 13888#64) (polyVecNat (tHatModPoly16 (pkEk3 pk))) ∗
        ((sp + 14400#64) ↦ₛ List.replicate 32 0#8) ∗
        memRegion (sp + 16504#64) 8200 ∗ memRegion (sp + 26112#64) 160 ∗
        memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 33528#64) 8 ∗
        memRegion (sp + 34240#64) 192 ∗ memRegion (sp + 34464#64) 128 ∗
        stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗ SpilledDecapsWords sp m ∗
        ((sp + 128#64) ↦₆₄ ret) ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
        memRegion (sp + 144#64) 1344 ∗ memRegion (sp + 2432#64) 64 ∗
        memRegion (sp + 2560#64) 1600 ∗ memRegion (sp + 26305#64) 15 ∗
        memRegion (sp + 30416#64) 32 ∗ memRegion (sp + 32496#64) 512 ∗
        ((sp + 34432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 34592#64) 80 ∗
        (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32) := by
    refine Entails.trans hP6 ?_
    rw [publicKeyStateAt_4160_eq sp pk]
    exact entails_sub (Entails.of_eq (seg6_to_seg7_regions sp)) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP6'
    (SepWP.seq
      (seg7_uvec_c1_ok hb hbase s6 sp (s0.sp - 96#64) (pkRho pk) (hashed.drop 32) _
        hpc6 hrun6 hsp6 hspA6 hx20_6 hfp6' hcl6 hro6) ?_)
  rintro s7 P7 hpc7 hrun7 ⟨hsp7, hspA7, hfp7, hx19_7, hx20_7, hcl7, hro7, hP7⟩
  have hP7' : P7 ⊢ SpilledDecapsWords sp m ∗ ((sp + 136#64) ↦₆₄ ctA) ∗
      PolyMem (sp + 1488#64) (polyVecNat (neonCbd2Poly16 (shake256List 128 (hashed.drop 32 ++ [8#8])))) ∗
      memRegion (sp + 2224#64) 208 ∗ PublicKeyStateAt (sp + 4160#64) pk ∗
      PolyMem (sp + 14432#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [0#8])))) ∗
      PolyMem (sp + 14944#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [1#8])))) ∗
      PolyMem (sp + 15456#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [2#8])))) ∗
      PolyMem (sp + 15968#64) (polyVecNat (rHatPoly16 (shake256List 128 (hashed.drop 32 ++ [3#8])))) ∗
      ((sp + 24704#64) ↦ₛ c1Bytes06 (pkRho pk) (hashed.drop 32)) ∗
      memRegion (sp + 26112#64) 160 ∗ memRegion (sp + 26320#64) 512 ∗
      memRegion (sp + 28368#64) 512 ∗ memRegion (sp + 30448#64) 1568 ∗
      memRegion (sp + 32496#64) 512 ∗ memRegion (sp + 33008#64) 512 ∗
      (memRegion (sp + 2000#64) 224 ∗ memRegion (sp + 16480#64) 24 ∗
        memRegion (sp + 26832#64) 1536 ∗ memRegion (sp + 28880#64) 1536 ∗
        memRegion (sp + 32016#64) 480 ∗ memRegion (sp + 33520#64) 8 ∗
        memRegion (sp + 33536#64) 352 ∗ memRegion (sp + 33888#64) 352 ∗
        ((sp + 2496#64) ↦ₛ hashed) ∗ memRegion (sp + 16504#64) 8200 ∗
        memRegion (sp + 26272#64) 33 ∗ memRegion (sp + 33528#64) 8 ∗
        memRegion (sp + 34240#64) 192 ∗ memRegion (sp + 34464#64) 128 ∗
        stackAt sp 1136 ∗ SavedFrame06 s0.sp s0 ∗
        ((sp + 128#64) ↦₆₄ ret) ∗ memRegion (sp + 144#64) 1344 ∗
        memRegion (sp + 2432#64) 64 ∗ memRegion (sp + 2560#64) 1600 ∗
        memRegion (sp + 26305#64) 15 ∗ memRegion (sp + 30416#64) 32 ∗
        ((sp + 34432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 34592#64) 80 ∗
        (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32) := by
    refine Entails.trans hP7 ?_
    rw [publicKeyStateAt_4160_eq sp pk]
    exact entails_sub (Entails.of_eq (seg7_to_seg8_regions sp)) (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP7'
    (SepWP.seq
      (seg8_vpoly_c2_ok hb hbase s7 sp ctA (s0.sp - 96#64) pk hm hcoins _
        hpc7 hrun7 hsp7 hspA7 hx19_7 hx20_7 hfp7 hcl7 hro7) ?_)
  rintro s8 P8 hpc8 hrun8 ⟨hsp8, hspA8, hx19_8, hx22_8, hfp8, hcl8, hro8, hP8⟩
  set ct' := (indCpaEncryptWith sampleNtt 4 11 5 pk m (hashed.drop 32)).1 ++
    (indCpaEncryptWith sampleNtt 4 11 5 pk m (hashed.drop 32)).2.1
  have hct' : ct'.length = 1568 :=
    indCpaEncryptWith_4_11_5_ct_len sampleNtt pk m (hashed.drop 32)
  have hP8' : P8 ⊢ stackAt sp 1136 ∗ ((sp + 128#64) ↦₆₄ ret) ∗
      ((sp + 2496#64) ↦ₛ hashed.take 32) ∗
      memRegion (sp + 4160#64) 32 ∗ memRegion (sp + 14432#64) 64 ∗
      memRegion (sp + 28368#64) 32 ∗ ((sp + 30448#64) ↦ₛ ct') ∗
      memRegion (sp + 34368#64) 32 ∗ memRegion (sp + 34400#64) 32 ∗
      ((sp + 34432#64) ↦ₛ kRejPre) ∗ memRegion (sp + 34592#64) 32 ∗
      memRegion (sp + 34624#64) 32 ∗ SavedFrame06 s0.sp s0 ∗
      (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗
      ((memRegion sp 128 ∗ memRegion (sp + 136#64) 2360 ∗
        memRegion (sp + 2528#64) 1632 ∗ memRegion (sp + 4192#64) 10240 ∗
        memRegion (sp + 14496#64) 13872 ∗ memRegion (sp + 28400#64) 2048 ∗
        memRegion (sp + 32016#64) 2352 ∗ memRegion (sp + 34464#64) 128 ∗
        memRegion (sp + 34656#64) 16) ∗ (skA ↦ₛ sk)) := by
    refine Entails.trans hP8 ?_
    exact entails_sub
      (seg8_to_seg9_scratch sp ctA pk m hashed ct' _ _ _ _ _ hh hct')
      (by sep_frame) (by sep_frame)
  refine SepWP.weaken_pre hP8'
    (SepWP.mono
      (seg9_ok hb hbase s0 s8 ret ctA (hashed.take 32) kRejPre ct ct' _
        hkBar hkRej hct hct' hsp0 hpc8 hrun8 hsp8 hspA8 hx19_8 hx22_8 hfp8 hcl8 hro8) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost ⊢
  refine ⟨hpost.1, Entails.trans hpost.2 ?_⟩
  have hsel := decaps_select_eq_kyber1024Decaps (sk := sk) hct
  dsimp only at hsel
  rw [hsel]
  exact entails_sub (seg9_merge_stack s0.sp) (by sep_frame) (by sep_frame)

/-! ## 5. Block 06 (`neon::kyber_decapsulate`) Core Contracts (`35,968` B Stack) -/

attribute [local irreducible] kyber1024Decaps in
/-- `B06` partial-correctness (`SafeSepWP` / `safe_subroutine_ok`) raw contract (`35,968` B stack). -/
theorem blk06_decaps_raw_safe_ok : MlKemBlockSafeOk 6 kyberDecapsInnerRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC06 blkPl06 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, skA, sk, ctA, ct⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, kyberDecapsInnerRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hsk, hct, hro0⟩, hspat⟩ := hpre
  refine ⟨stackAt s0.sp 35968 ∗ (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ (memRegion ret 32 ∗ emp),
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine safeSepWP_of_sepWP_env hcl0 hro0
    (seg1_to_4_ok hb hbase s0 ret skA ctA sk ct (memRegion ret 32 ∗ emp)
      hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hsk hct) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx9_4, hx20_4, hx22_4, hx23_4, hx25_4, hx26_4, hfp4, hv0_4, hv1_4, hP4⟩
  refine SafeSepWP.weaken_pre (SafeSepWP.bind
    (seg5_sample_matrix_safe_ok hb hbase (pkRho_sk_len hsk)
      hpc4 hrun4 hsp4 hspA4 (sp_aligned_chk hsp4 hspA4) hcl4 hro4
      hx9_4 hx20_4 hx22_4 hx23_4 hx25_4 hx26_4 hfp4 hv0_4 hv1_4) ?_) hP4
  rintro s5 P5 hp5
  refine SafeSepWP.ret_of_sepWP (SepWP.mono
    (seg6_to_9_ok hb hbase s0 ret skA ctA sk ct hsp0 hsk hct s5 P5 hp5) ?_)
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  refine ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost.2) hm, hpost.1.1, hpost.1.2⟩

/-- `B06` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk06_decaps_safe_ok : MlKemBlockSafeOk 6 kyberDecapsInnerCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk06_decaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 h => by
      dsimp only [kyberDecapsInnerRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 _sf _ h => by
      dsimp only [kyberDecapsInnerRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

attribute [local irreducible] kyber1024Decaps in
/-- `B06` conditional total-correctness (`subroutine_ok`) raw contract (`35,968` B stack). -/
theorem blk06_decaps_raw_ok : MlKemBlockOk 6 kyberDecapsInnerTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC06 blkPl06 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, skA, sk, ctA, ct⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hsk, hct, hro0⟩, hspat⟩ := hpre
  have hTerm' : Shake128MatrixTerminates (pkRho ((sk.drop 1536).take 1568)) 4 := by
    rw [pkRho_sk_eq sk]; exact hTerm
  refine ⟨stackAt s0.sp 35968 ∗ (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ (memRegion ret 32 ∗ emp),
    Satisfies.mono (by sep_frame) hspat, ?_⟩
  refine sepWP_seq_env hcl0 hro0
    (seg1_to_4_ok hb hbase s0 ret skA ctA sk ct (memRegion ret 32 ∗ emp)
      hpc hrun hsp0 hcl0 hro0 hx0 hx1 hx2 hsk hct) ?_
  rintro s4 P4 hpc4 hrun4 hcl4 hro4
    ⟨hsp4, hspA4, hx9_4, hx20_4, hx22_4, hx23_4, hx25_4, hx26_4, hfp4, hv0_4, hv1_4, hP4⟩
  refine SepWP.weaken_pre hP4
    (SepWP.seq
      (seg5_sample_matrix_ok hb hbase (pkRho_sk_len hsk) hTerm'
        hpc4 hrun4 hsp4 hspA4 (sp_aligned_chk hsp4 hspA4) hcl4 hro4
        hx9_4 hx20_4 hx22_4 hx23_4 hx25_4 hx26_4 hfp4 hv0_4 hv1_4) ?_)
  rintro s5 P5 _ _ hp5
  refine SepWP.mono
    (seg6_to_9_ok hb hbase s0 ret skA ctA sk ct hsp0 hsk hct s5 P5 hp5) ?_
  intro sf Pf _ _ hpost; rw [sepPost_apply] at hpost
  exact ⟨fun hm => Satisfies.mono (sepConj_mono_left hpost.2) hm, hpost.1.1, hpost.1.2⟩

attribute [local irreducible] Kyber1024DecapsTerminates kyber1024Decaps in
/-- `B06` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk06_decaps_ok : MlKemBlockOk 6 kyberDecapsInnerTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk06_decaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 h => by
      dsimp only [kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h2.1.1, h2.1.2.1, h2.1.2.2.1, h2.1.2.2.2.1, h2.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h2.1.2.2.2.2.2⟩, h2.2⟩)
    (h_post := fun _mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 _sf _ h => by
      dsimp only [kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-! ## 6. Block 23 (`mlkem1024::kyber::decapsulate`) ABI Wrapper -/

section Blk23Fetches
gen_placed_fetches blkPC23 blkLib23 blkTree23 blk23_code_eq blk23_tree_size
  via_placement blkPl23 blkPlaceable23 [0x0 → 0xc]
end Blk23Fetches

private theorem blk23_prologue_wp [MlKemPlacement] {b : BitVec 64}
    (hb : MlKemBase blkPl23 b) (hbase : blkPl23.base = b)
    (s0 : State) (ret skA ctA : BitVec 64) (P : SepProp)
    (hpc : s0.pc = b) (hrun : s0.status = .Running)
    (hx8 : s0.readReg64 .x8 = ret) (hx0 : s0.readReg64 .x0 = skA)
    (hx1 : s0.readReg64 .x1 = ctA) :
    SepWP (blkPC23.rebase b (fun _ => none)) (mlkemMpl.base 6) s0 P
      (sepPost (fun s1 =>
        s1.mem = s0.mem ∧ s1.sp = s0.sp ∧ s1.spAligned = s0.spAligned ∧
        s1.readReg64 .lr = s0.readReg64 .lr ∧
        s1.readReg64 .x0 = ret ∧ s1.readReg64 .x1 = skA ∧
        s1.readReg64 .x2 = ctA ∧
        CalleeSavedPreserved s0 s1) P) := by
  have _ := hb
  subst hbase
  simp only [Reg.x8, Reg.x0, Reg.x1] at hx8 hx0 hx1
  wp_steps 4
  refine SepWP.done
    (by simp [wp_norm, arm64_norm, blkPl23, MultiPlacedLib.blockPlacement])
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

/-- `B23` partial-correctness (`safe_subroutine_ok`) raw contract (`35,968` B stack). -/
theorem blk23_kyber_decaps_raw_safe_ok : MlKemBlockSafeOk 23 kyberDecapsRawSpec := by
  intro _
  refine mlkemSafeCaller_ok blkPC23 blkPl23 rfl rfl fun b hb hbase => ?_
  apply safe_subroutine_ok_of_safeSepWP
  rintro ⟨ret, skA, sk, ctA, ct⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, kyberDecapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hsk, hct, hro0⟩, hspat⟩ := hpre
  let P0 := (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968
  refine ⟨P0, Satisfies.mono (by dsimp only [P0]; sep_frame) hspat, SafeSepWP.of_sepWP (SepWP.mono
    (blk23_prologue_wp hb hbase s0 ret skA ctA P0 hpc hrun hx8 hx0 hx1) ?_)⟩
  intro s1 P1 hpc1 hrun1 hp1; rw [sepPost_apply] at hp1
  rcases hp1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hcs1⟩, hP1⟩
  refine SafeSepWP.call_subroutine_frame
    (mlkemSafeCall_of_blockSafeOk _ blk06_decaps_raw_safe_ok)
    (x := (ret, skA, sk, ctA, ct)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm1 => by
      have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
      dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec, kyberDecapsInnerRawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
          satisfies_pure_sepConj]
      refine ⟨hmem1 ▸ hcl0, ?_⟩
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_1, hx1_1, hx2_1, hsk, hct, hmem1 ▸ hro0⟩, ?_⟩
      rw [hsp1, emp_sepConj]; exact Satisfies.mono (by dsimp only [P0]; sep_frame) hm1')
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => SafeSepWP.done fun hmf =>
      Or.inl ⟨⟨hpc_sf, hsp_sf.trans hsp1, hrun_sf⟩, ⟨hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩,
        Satisfies.mono (by dsimp only [kyberDecapsInnerRawSpec]; sep_frame) hmf⟩)

/-- `B23` partial-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk23_kyber_decaps_safe_ok : MlKemBlockSafeOk 23 kyberDecapsCoreSpec :=
  mlkemBlockSafeOk_withNonSyscallPreserved blk23_kyber_decaps_raw_safe_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 h => by
      dsimp only [kyberDecapsRawSpec] at h ⊢
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h.1.2.2.2.2.2⟩, h.2⟩)
    (h_post := fun _mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 _sf _ h => by
      dsimp only [kyberDecapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B23` conditional total-correctness (`subroutine_ok`) raw contract (`35,968` B stack). -/
theorem blk23_kyber_decaps_raw_ok : MlKemBlockOk 23 kyberDecapsTermRawSpec := by
  intro _
  refine mlkemCaller_ok blkPC23 blkPl23 rfl rfl fun b hb hbase => ?_
  apply subroutine_ok_of_sepWP_init
  rintro ⟨ret, skA, sk, ctA, ct⟩ R s0 hpc hrun hpre hsp0
  dsimp only [MultiPlacedLib.withCodeLoaded, ToBaseSpec.toSpec,
    kyberDecapsTermRawSpec, kyberDecapsRawSpec] at hpre ⊢
  rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s0.mem⌝, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  obtain ⟨hcl0, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hTerm, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx8, hx0, hx1, hsk, hct, hro0⟩, hspat⟩ := hpre
  let P0 : SepProp := (skA ↦ₛ sk) ∗ (ctA ↦ₛ ct) ∗ memRegion ret 32 ∗ stackAt s0.sp 35968
  refine ⟨P0, Satisfies.mono (by dsimp only [P0]; sep_frame) hspat, SepWP.seq
    (blk23_prologue_wp hb hbase s0 ret skA ctA P0 hpc hrun hx8 hx0 hx1) ?_⟩
  rintro s1 P1 hpc1 hrun1 hpost1
  rw [sepPost_apply] at hpost1
  rcases hpost1 with ⟨⟨hmem1, hsp1, hspA1, hlr1, hx0_1, hx1_1, hx2_1, hcs1⟩, hP1⟩
  refine SepWP.weaken_pre hP1 ?_
  refine SepWP.weaken_pre (show P0 ⊢ P0 ∗ emp by sep_frame) ?_
  refine SepWP.call_subroutine_frame
    (mlkemCall_of_blockOk (blkPC23.rebase b (fun _ => none)) (j := 6) blk06_decaps_raw_ok)
    (x := (ret, skA, sk, ctA, ct)) (F := emp)
    hpc1 hrun1 (hspA1.trans hsp0) hlr1
    (fun R' hm => by
      dsimp only [MultiPlacedLib.withCodeLoaded, kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec]
      rw [sepConj_comm _ ⌜mlkemMultiLib.CodeLoaded mlkemMpl s1.mem⌝, sepConj_assoc,
        pure_sepConj_of_true (hmem1 ▸ hcl0), sepConj_assoc, pure_sepConj_of_true hTerm,
        sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        pure_sepConj_of_true ⟨hx0_1, hx1_1, hx2_1, hsk, hct, hmem1 ▸ hro0⟩]
      exact Satisfies.mono (by dsimp only [P0]; rw [hsp1]; sep_frame) hm)
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf
  refine SepWP.done hpc_sf hrun_sf ⟨fun hmf => ?_, hsp_sf.trans hsp1, cs_trans hcs1 hcs_sf⟩
  refine Satisfies.mono ?_ hmf
  dsimp only [MultiPlacedLib.withCodeLoaded, kyberDecapsInnerTermRawSpec, kyberDecapsInnerRawSpec]
  rw [hsp1]
  sep_frame

attribute [local irreducible] Kyber1024DecapsTerminates kyber1024Decaps in
/-- `B23` conditional total-correctness tight-stack contract lifted with `NonSyscallPreserved`. -/
theorem blk23_kyber_decaps_ok : MlKemBlockOk 23 kyberDecapsTermCoreSpec :=
  mlkemBlockOk_withNonSyscallPreserved blk23_kyber_decaps_raw_ok (by decide)
    (h_pre := fun mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 h => by
      dsimp only [kyberDecapsTermRawSpec, kyberDecapsRawSpec] at h ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
      refine ⟨h.1, ?_⟩
      have h2 := h.2
      rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h2 ⊢
      simp only [stripS_readReg64, stripS_sp, stripS_mem]
      exact ⟨⟨h2.1.1, h2.1.2.1, h2.1.2.2.1, h2.1.2.2.2.1, h2.1.2.2.2.2.1,
        mlkemRoOk_stripExecOutside (mlkemKeep mpl) h2.1.2.2.2.2.2⟩, h2.2⟩)
    (h_post := fun _mpl ⟨_ret, _skA, _sk, _ctA, _ct⟩ _R _s0 _sf _ h => by
      dsimp only [kyberDecapsTermRawSpec, kyberDecapsRawSpec] at h ⊢
      simpa only [stripS_sp] using h)

/-- `B23` per-key (`sk : List (BitVec 8)`) total-correctness specialization under
    `Kyber1024DecapsTerminates sk`. -/
theorem blk23_kyber_decaps_atSk_ok {sk : List (BitVec 8)}
    (hTerm : Kyber1024DecapsTerminates sk) :
    MlKemBlockOk 23 (kyberDecapsAtSkCoreSpec sk) :=
  mlkemBlockOk_simulates (kyberDecapsTermCore_simulates_atSk hTerm) blk23_kyber_decaps_ok

/-! ## 7. Caller-Struct Projections (`35,968 ≤ stk`, `65,536`, & `extHookStack`) -/

/-- `B23` partial-correctness `projLen` caller projection (`35968 ≤ stk`). -/
theorem blk23_projLen_safe_ok
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8)) :
    MlKemBlockSafeOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) :=
  mlkemBlockSafeOk_simulates
    (kyberDecapsCore_simulates_projLen decaps hdec stk hstk hstk_fit ret skA sk ctA ct)
    blk23_kyber_decaps_safe_ok

/-- `B23` conditional total-correctness `projLen` caller projection (`35968 ≤ stk`). -/
theorem blk23_projLen_ok
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) :
    MlKemBlockOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsProjLenSpec decaps stk ret skA sk ctA ct))) :=
  mlkemBlockOk_simulates
    (kyberDecapsTermCore_simulates_projLen decaps hdec stk hstk hstk_fit ret skA sk ctA ct hTerm)
    blk23_kyber_decaps_ok

/-- `B23` partial-correctness `proj` caller projection (`35968 ≤ stk`). -/
theorem blk23_proj_safe_ok
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568) :
    MlKemBlockSafeOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) :=
  mlkemBlockSafeOk_simulates
    (kyberDecapsCore_simulates_proj decaps hdec stk hstk hstk_fit ret skA sk ctA ct hsk hct)
    blk23_kyber_decaps_safe_ok

/-- `B23` conditional total-correctness `proj` caller projection (`35968 ≤ stk`). -/
theorem blk23_proj_ok
    (decaps : List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (hdec : ∀ sk ct, sk.length = 3168 → ct.length = 1568 → decaps sk ct = kyber1024Decaps sk ct)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (ret skA : C → BitVec 64) (sk : C → List (BitVec 8))
    (ctA : C → BitVec 64) (ct : C → List (BitVec 8))
    (hsk : ∀ x, (sk x).length = 3168) (hct : ∀ x, (ct x).length = 1568)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x)) :
    MlKemBlockOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsProjSpec decaps stk ret skA sk ctA ct))) :=
  mlkemBlockOk_simulates
    (kyberDecapsTermCore_simulates_proj decaps hdec stk hstk hstk_fit ret skA sk ctA ct hsk hct hTerm)
    blk23_kyber_decaps_ok

/-- `B23` partial-correctness `cliProj` (`List.Vector`, `kemDecapsName`) projection
    (`35968 ≤ stk`). -/
theorem blk23_cliProj_safe_ok
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) :
    MlKemBlockSafeOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps stk skA sk ctA ct ret))) :=
  mlkemBlockSafeOk_simulates
    (kyberDecapsCore_simulates_cliProj decaps hdec stk hstk hstk_fit skA sk ctA ct ret)
    blk23_kyber_decaps_safe_ok

/-- `B23` conditional total-correctness `cliProj` (`List.Vector`, `kemDecapsName`)
    projection (`35968 ≤ stk`). -/
theorem blk23_cliProj_ok
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    (stk : Nat) (hstk : 35968 ≤ stk) (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x).toList) :
    MlKemBlockOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps stk skA sk ctA ct ret))) :=
  mlkemBlockOk_simulates
    (kyberDecapsTermCore_simulates_cliProj decaps hdec stk hstk hstk_fit skA sk ctA ct ret hTerm)
    blk23_kyber_decaps_ok

/-- `B23` partial-correctness `cliProj` projection at `stk = 65536`. -/
theorem blk23_cliProj_65536_safe_ok
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) :
    MlKemBlockSafeOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps 65536 skA sk ctA ct ret))) :=
  blk23_cliProj_safe_ok decaps hdec 65536 (by decide) (by decide) skA sk ctA ct ret

/-- `B23` conditional total-correctness `cliProj` projection at `stk = 65536`. -/
theorem blk23_cliProj_65536_ok
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x).toList) :
    MlKemBlockOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps 65536 skA sk ctA ct ret))) :=
  blk23_cliProj_ok decaps hdec 65536 (by decide) (by decide) skA sk ctA ct ret hTerm

/-- `B23` partial-correctness `cliProj` projection at `extHookStack` (`35968 ≤ extHookStack`). -/
theorem blk23_cliProj_extHookStack_safe_ok (hstk : 35968 ≤ extHookStack)
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) :
    MlKemBlockSafeOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps extHookStack skA sk ctA ct ret))) :=
  blk23_cliProj_safe_ok decaps hdec extHookStack hstk (by decide) skA sk ctA ct ret

/-- `B23` conditional total-correctness `cliProj` projection at `extHookStack`. -/
theorem blk23_cliProj_extHookStack_ok (hstk : 35968 ≤ extHookStack)
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (hdec : ∀ sk ct, (decaps sk ct).toList = kyber1024Decaps sk.toList ct.toList)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x).toList) :
    MlKemBlockOk 23 (fun mpl =>
      withMlKemRoOk mpl (keepsFs (kyberDecapsCliProjSpec decaps extHookStack skA sk ctA ct ret))) :=
  blk23_cliProj_ok decaps hdec extHookStack hstk (by decide) skA sk ctA ct ret hTerm

/-- `B23` concrete `kyber1024DecapsVec` partial-correctness projection (`35968 ≤ stk`). -/
theorem blk23_kyber1024DecapsVec_safe_ok (stk : Nat) (hstk : 35968 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64) :
    MlKemBlockSafeOk 23 (fun mpl => withMlKemRoOk mpl
      (keepsFs (kyberDecapsCliProjSpec kyber1024DecapsVec stk skA sk ctA ct ret))) :=
  blk23_cliProj_safe_ok kyber1024DecapsVec kyber1024DecapsVec_toList
    stk hstk hstk_fit skA sk ctA ct ret

/-- `B23` concrete `kyber1024DecapsVec` conditional total-correctness projection (`35968 ≤ stk`). -/
theorem blk23_kyber1024DecapsVec_ok (stk : Nat) (hstk : 35968 ≤ stk)
    (hstk_fit : stk ≤ 2 ^ 64 := by decide)
    {C : Type} (skA : C → BitVec 64) (sk : C → List.Vector (BitVec 8) 3168)
    (ctA : C → BitVec 64) (ct : C → List.Vector (BitVec 8) 1568)
    (ret : C → BitVec 64)
    (hTerm : ∀ x, Kyber1024DecapsTerminates (sk x).toList) :
    MlKemBlockOk 23 (fun mpl => withMlKemRoOk mpl
      (keepsFs (kyberDecapsCliProjSpec kyber1024DecapsVec stk skA sk ctA ct ret))) :=
  blk23_cliProj_ok kyber1024DecapsVec kyber1024DecapsVec_toList
    stk hstk hstk_fit skA sk ctA ct ret hTerm

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps
