/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignature
import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlacedB
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-! # Blocks `204` and `203` (`verify_signature*`) Against Extended-Edwards Hooks -/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped CryptoVerification.E2E.Pqxdh.Shared

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (IsLsBlockProg LibsignalCodeLoaded LibsignalFullPlacement LibsignalHooks
  LibsignalPlacement blkPC_203 blkPC_204 blkPC_204_pairStep_0x104 blkPC_213 blkPl_203 blkPl_204
  blkPl_213 libsignalSessionLib lsBlackBoxU8Sym lsMemcpySym ls_blockPlacement_base lscall_blk
  lsjump_blk lsmpl ls_hook_ok_any lsρ sepWP_seq_lscl withMemEq)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded extract_withLsCodeRoLoaded
  keys_ls_subroutine_ok_of_block_cro sessionMemcpyRegionSpec sessionMemsetSpec
  subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsFrozen)
open CryptoVerification.SignalSession.CliExt (inputAfter pureByteFunctionSpec withStack)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives blockLevelPrims fitVec modelPrims
  ofU8 toU8 u8Vec vecU8)
open CryptoVerification.E2E.Pqxdh.Shared (structuralPrims_modelPrims)
open CryptoVerification.E2E.Pqxdh.Shared (CurveVerifyAndCanonPlacedOk DalekMontToEdGhost
  SepWP.done_ro SepWP.step_ldpSimd128_ro VerifySignatureMultipartPlacedGhost
  VerifySignaturePlacedGhost VerifySignaturePrims and64_mask255_ite_1_0 blockBuf_tail32_pack
  blockBuf_tail32_unpack bv_add_neg64 bv_sub_sub_lit bytesToBv8 bytesToBv8_append
  bytesToBv8_getD_eq cell_split7 cells_10_merge cells_16_merge compressInPlaceStubSpec
  compressInPlaceStubSpecPlaced cryptoLeafStubSpec csinc_eq_zero32_ite_1_0
  ecPubKeyIsCanonicalCallSpec exists_pad97_cells exists_sig_capS_cells exists_unpack64_of_length_64
  exists_unpack64_revWords64_of_length_64 first7 first7_pack fitBv8 fitBv8_64_sha512CompressOutBytes
  fitBv8_of_length_eq lsDalekCompressSym lsDalekDoubleMulSym lsDalekEdNegSym lsDalekMontToEdSym
  lsDalekScalarModSym lsDalekScalarWideSym lsDalekTorsionFreeSym lsSha512CompressSym
  lsVerifyMemsetSym lsVerifyMontToEdSym lsVerifySha512IVRoSym pointsToBytes_32_merge_128
  pointsToBytes_entails_memRegion_n pqxdhHookStack pqxdhHookStackExt readReg_setMem_setPC_pre
  readReg_setPC_pre readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre
  readReg64_setPC_pre revWords64 revWords64_length roStop sClamped_buf_pre sha512CompressOutBytes
  sha512CompressOutBytes_length sha512IVBytesLE sha512IVBytesLE_eq_unpack64 sha512IV_placed_holdsBytes
  sha512IV_placed_quad0 sha512IV_placed_quad1 sha512Ref_of_length_1633 sha512Ref_of_length_97
  sig_split_32 signBit_shr7_and_one sp_setMem_setPC_pre sp_setPC_pre stackAt_split_cells
  truncate8_zeroExtend32_and7f u64le verifySig_end_seg verifySig_epilogue_false_placed
  verifySig_epilogue_placed verifySig_memRegion_1152_seg1a_merge verifySig_memRegion_1152_seg1a_split
  verifySig_memRegion_752_seg1b_merge verifySig_memRegion_752_seg1b_split
  verifySig_seg1b_to_seg1c_split verifySig_seg1c_invalid_placed verifySig_seq_seg
  verifySig_seq_seg_lscl verifySig_seq_seg_lscro verifySig_stackAt_1248_split
  verifySig_xeddsaVerifyRef_of_60_false verifySignatureCallSpec verifySignatureMultipartCallSpec
  verifySignature_epilogue_placed verifySignature_prologue_placed x0_cteq_simplify)
open SignalPqxdh (Bytes encodeBitLen128BE encodeBitLen64BE isCanonicalRef sha512InitState)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat (blackBoxSpecSat
  ctEqSliceMemSpec16 ct_eq_mem_placed_ok_16_sat hookSat_blackBox_of_eq)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (hookSat_withLsRet
  satisfies_withLsRet_of_blockPlacement_base_add specSimulates_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open VerifiedLibraries.Common (EdPoint edBasepoint edExtOfAffine edExtToAffine edOnCurve edOrderL
  edSmul edSub encodeEd fpInv leBytesToNat natToLeBytes recoverXEven)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.PointCodec (leBytesToNat_natToLeBytes_of_lt)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (edDoubleScalarMulBasepoint
  edExtOfBytes fe51LimbsBoundedAt fe51Point4Bounded montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (dalekEdNegBytes
  dalekEdNegBytes_bounded dalekEdNegBytes_length dalekEdNegVec dalekScalarModVec
  dalekScalarWideVec pipeline2_xeddsa_verify_compress_eq)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (edExtToAffine_edExtOfAffine)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (montToEdwards_some_onCurve)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (DalekPrims DalekPrimsSound
  PqxdhHookPrims dalekPrimsRef dalekPrimsRef_sound natToLeBytes_len pqxdhPrimsOfHooks
  u8Vec_toList_of_length xeddsaVerifyRef_congr_of_sound xeddsaVerifyRef_dalekPrimsRef_capRCheck_eq
  xeddsaVerifyRef_dalekPrimsRef_eq xeddsaVerifyRef_eq_closed_of_sound)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202 (IsCanonicalCurveSound
  bytesToBv8_eq_ofU8 dalekHookStack dalekMontToEdExtOutAt dalekMontToEdExtOutAt_and_one_eq_toNat
  dalekMontToEdExtOutAt_congr_mod2 dalekMontToEdExtOutAt_none dalekMontToEdExtOutAt_some
  dalekMontToEdExtSpec dalekTorsionFreeExtSpec hookSat_dalekMontToEdExtSpec_mono
  hookSat_withLsRet_of_withVmPreserved isCanonicalCurveSound_modelPrims_dalekPrimsRef
  isCanonicalCurveSound_modelPrims_of_sound isCanonical_ext_placed_ok_at_cl
  isCanonical_ext_pqxdh_placed_ok_cl modelPrims_isCanonicalEC_eq_isCanonicalRef)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  VmPreserved fpInv recoverXEven edSmul fe51Point4Bounded edExtOfBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64

private theorem calleeSavedVRegs_setPC_pre_placed (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := calleeSavedVRegs_setPC s pc
private theorem calleeSavedVRegs_setMem_setPC_pre_placed (s : State) (m : Memory) (pc : BitVec 64) :
    calleeSavedVRegs ((s.setMem m).setPC pc) = calleeSavedVRegs s := by
  rw [calleeSavedVRegs_setPC, calleeSavedVRegs_setMem]

attribute [local arm64_norm ↓, local wp_norm ↓] sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre calleeSavedVRegs_setPC_pre_placed
  calleeSavedVRegs_setMem_setPC_pre_placed
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  and64_mask255_ite_1_0 csinc_eq_zero32_ite_1_0

/-! ## 1. Placement-Free Extended-Edwards Consumer Hook Specifications -/

private theorem fe51Point4Bounded_mono_local {bs : List (BitVec 8)} {b₁ b₂ : Nat}
    (hb : b₁ ≤ b₂) (h : fe51Point4Bounded bs b₁) : fe51Point4Bounded bs b₂ := by
  unfold fe51Point4Bounded fe51LimbsBoundedAt at h ⊢; omega

/-- Ghost parameters for `<EdwardsPoint>::compress` (`x0 = inPtr`, `x8 = outPtr`). -/
structure DalekCompressExtGhost where
  inPtr : BitVec 64
  edBytes : List (BitVec 8)
  outPtr : BitVec 64

/-- Placement-free consumer specification for `<EdwardsPoint>::compress` (`B14`). -/
@[expose] def dalekCompressExtSpec (hookStack : Nat) : Spec DalekCompressExtGhost where
  pre g s := ⌜s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x8 = g.outPtr ∧
      g.edBytes.length = 160 ∧ fe51Point4Bounded g.edBytes (2 ^ 52)⌝ ∗
    (g.inPtr ↦ₛ g.edBytes) ∗ memRegion g.outPtr 32 ∗ stackAt s.sp hookStack
  post g s0 sf := ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗
    (g.outPtr ↦ₛ encodeEd (edExtToAffine (edExtOfBytes g.edBytes))) ∗ stackAt s0.sp hookStack

/-- Ghost parameters for `<&EdwardsPoint as Neg>::neg` (`x0 = inPtr`, `x8 = outPtr`). -/
structure DalekEdNegExtGhost where
  inPtr : BitVec 64
  edBytes : List (BitVec 8)
  outPtr : BitVec 64

/-- Placement-free consumer specification for `<&EdwardsPoint as Neg>::neg`. -/
@[expose] def dalekEdNegExtSpec (hookStack : Nat) : Spec DalekEdNegExtGhost where
  pre g s := ⌜s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.edBytes.length = 160⌝ ∗
    (g.inPtr ↦ₛ g.edBytes) ∗ memRegion g.outPtr 160 ∗ stackAt s.sp hookStack
  post g s0 sf := ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗
    (g.outPtr ↦ₛ dalekEdNegBytes g.edBytes) ∗ stackAt s0.sp hookStack

/-- Unstacked `Vector`-typed specification for `<&EdwardsPoint as Neg>::neg` (`EdNegCode`). -/
@[expose] def edwardsPointNegUnstackedSpec (byVal : Bool := false) :
    Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64) where
  pre := fun (inA, v, ret) s =>
    ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret 160
  post := fun (inA, v, ret) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ inputAfter byVal inA v ∗ (ret ↦ₛ (dalekEdNegVec v).toList)

/-- Ghost parameters for `<Scalar>::from_bytes_mod_order_wide` (`x0 = inPtr`, `x8 = outPtr`). -/
structure DalekScalarWideExtGhost where
  inPtr : BitVec 64
  inBytes : List (BitVec 8)
  outPtr : BitVec 64

/-- Placement-free consumer specification for `<Scalar>::from_bytes_mod_order_wide` (`B02`). -/
@[expose] def dalekScalarWideExtSpec (hookStack : Nat) : Spec DalekScalarWideExtGhost where
  pre g s := ⌜s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 64⌝ ∗
    (g.inPtr ↦ₛ g.inBytes) ∗ memRegion g.outPtr 32 ∗ stackAt s.sp hookStack
  post g s0 sf := ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.inBytes) ∗
    (g.outPtr ↦ₛ natToLeBytes 32 (leBytesToNat g.inBytes % edOrderL)) ∗ stackAt s0.sp hookStack

/-- Ghost parameters for `<Scalar>::from_bytes_mod_order` (`x0 = inPtr`, `x8 = outPtr`). -/
structure DalekScalarModExtGhost where
  inPtr : BitVec 64
  inBytes : List (BitVec 8)
  outPtr : BitVec 64

/-- Placement-free consumer specification for `<Scalar>::from_bytes_mod_order` (`B01`). -/
@[expose] def dalekScalarModExtSpec (hookStack : Nat) : Spec DalekScalarModExtGhost where
  pre g s := ⌜s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 32⌝ ∗
    (g.inPtr ↦ₛ g.inBytes) ∗ memRegion g.outPtr 32 ∗ stackAt s.sp hookStack
  post g s0 sf := ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.inBytes) ∗
    (g.outPtr ↦ₛ natToLeBytes 32 (leBytesToNat g.inBytes % edOrderL)) ∗ stackAt s0.sp hookStack

/-- Ghost parameters for `<EdwardsPoint>::vartime_double_scalar_mul_basepoint` (`B17`). -/
structure DalekDsmbExtGhost where
  aPtr : BitVec 64
  aBytes : List (BitVec 8)
  pPtr : BitVec 64
  pBytes : List (BitVec 8)
  bPtr : BitVec 64
  bBytes : List (BitVec 8)
  outPtr : BitVec 64

/-- Placement-free consumer specification for `vartime_double_scalar_mul_basepoint` (`B17`). -/
@[expose] def dalekDsmbExtSpec (hookStack : Nat) : Spec DalekDsmbExtGhost where
  pre g s := ⌜s.readReg64 .x0 = g.aPtr ∧ s.readReg64 .x1 = g.pPtr ∧ s.readReg64 .x2 = g.bPtr ∧
      s.readReg64 .x8 = g.outPtr ∧ g.aBytes.length = 32 ∧ g.pBytes.length = 160 ∧
      fe51Point4Bounded g.pBytes (2 ^ 52) ∧ g.bBytes.length = 32⌝ ∗
    (g.aPtr ↦ₛ g.aBytes) ∗ (g.pPtr ↦ₛ g.pBytes) ∗ (g.bPtr ↦ₛ g.bBytes) ∗
    memRegion g.outPtr 160 ∗ stackAt s.sp hookStack
  post g s0 sf := ⌜sf.trace = s0.trace⌝ ∗ (g.aPtr ↦ₛ g.aBytes) ∗ (g.pPtr ↦ₛ g.pBytes) ∗
    (g.bPtr ↦ₛ g.bBytes) ∗ (∃∗ res_bs : List (BitVec 8),
      ⌜res_bs.length = 160 ∧ fe51Point4Bounded res_bs (2 ^ 52) ∧
        edExtOfBytes res_bs = edDoubleScalarMulBasepoint g.aBytes g.pBytes g.bBytes⌝ ∗
      (g.outPtr ↦ₛ res_bs)) ∗ stackAt s0.sp hookStack

theorem stackAt_split_low (sp : BitVec 64) {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    stackAt sp s₂ = memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ stackAt sp s₁ :=
  @ProofLib.memRegion_split' (sp - BitVec.ofNat 64 s₂) (sp - BitVec.ofNat 64 s₁)
    (s₂ - s₁) s₁ s₂ (by omega) (by bv_omega) (by omega)

private theorem hookSat_of_specSimulates {α β : Type} {H : String → Option (State → State)}
    {sym : String} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (hh : HookSat H sym spec₁) : HookSat H sym spec₂ := by
  obtain ⟨f, hf, hok⟩ := hh; refine ⟨f, hf, fun y R s0 hrun hpre hsp => ?_⟩
  obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hok x R₁ s0 hrun hpre₁ hsp; exact ⟨hkf, hsym, hmap (f s0) hout⟩

theorem specSimulates_sessionMemsetSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (sessionMemsetSpec s₁) (sessionMemsetSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem hookSat_sessionMemsetSpec_mono {H : LibsignalHooks} {sym : String} {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) (hh : HookSat H sym (sessionMemsetSpec s₁)) :
    HookSat H sym (sessionMemsetSpec s₂) :=
  hookSat_of_specSimulates (specSimulates_sessionMemsetSpec_mono hle hbound) hh

theorem specSimulates_dalekCompressExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekCompressExtSpec s₁) (dalekCompressExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekCompressExtSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [dalekCompressExtSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem specSimulates_dalekEdNegExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekEdNegExtSpec s₁) (dalekEdNegExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekEdNegExtSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [dalekEdNegExtSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem specSimulates_dalekScalarWideExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekScalarWideExtSpec s₁) (dalekScalarWideExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekScalarWideExtSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [dalekScalarWideExtSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem specSimulates_dalekScalarModExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekScalarModExtSpec s₁) (dalekScalarModExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekScalarModExtSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [dalekScalarModExtSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem specSimulates_dalekDsmbExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekDsmbExtSpec s₁) (dalekDsmbExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre =>
    ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
  · dsimp only [dalekDsmbExtSpec] at hpre ⊢; rw [stackAt_split_low s0.sp hle hbound] at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  · dsimp only [dalekDsmbExtSpec] at hpost ⊢; rw [stackAt_split_low s0.sp hle hbound]
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost

theorem hookSat_withLsRet_map [LibsignalPlacement] {α β : Type} {H : LibsignalHooks} {sym : String}
    {spec₁ : Spec α} {spec₂ : Spec β} (hsim : SpecSimulates spec₁ spec₂)
    (hh : HookSat H sym (withLsRet spec₁)) : HookSat H sym (withLsRet spec₂) :=
  hookSat_of_specSimulates (specSimulates_withLsRet hsim) hh

theorem specSimulates_dalekEdNegExtSpec_of_unstacked (hookStack : Nat) :
    SpecSimulates (edwardsPointNegUnstackedSpec false) (dalekEdNegExtSpec hookStack) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [dalekEdNegExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hrest⟩
  refine ⟨(g.inPtr, ⟨g.edBytes, hlen⟩, g.outPtr), stackAt s0.sp hookStack ∗ R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [edwardsPointNegUnstackedSpec]; rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hrest⟩
  · dsimp only [edwardsPointNegUnstackedSpec, inputAfter] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
    change sf.mem ⊨ (⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗
      (g.outPtr ↦ₛ dalekEdNegBytes g.edBytes)) ∗ (stackAt s0.sp hookStack ∗ R) at hp
    dsimp only [dalekEdNegExtSpec]; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

theorem hookSat_dalekEdNegExtSpec_of_unstacked [LibsignalPlacement] {H : LibsignalHooks}
    (hookStack : Nat) (hh : HookSat H lsDalekEdNegSym (withLsRet (edwardsPointNegUnstackedSpec false))) :
    HookSat H lsDalekEdNegSym (withLsRet (dalekEdNegExtSpec hookStack)) :=
  hookSat_withLsRet_map (specSimulates_dalekEdNegExtSpec_of_unstacked hookStack) hh

theorem hookSat_dalekEdNegExtSpec_of_unstacked_plain [LibsignalPlacement] {H : LibsignalHooks}
    (hookStack : Nat) (hh : HookSat H lsDalekEdNegSym (edwardsPointNegUnstackedSpec false)) :
    HookSat H lsDalekEdNegSym (withLsRet (dalekEdNegExtSpec hookStack)) :=
  hookSat_dalekEdNegExtSpec_of_unstacked hookStack (hookSat_withLsRet hh)

private theorem toList_u8Vec_toU8 {n : Nat} {bs : List (BitVec 8)} (hlen : bs.length = n) :
    (u8Vec n (toU8 bs)).toList = bs := by
  have hlen_u8 : (toU8 bs).length = n := by unfold toU8; simp [hlen]
  rw [u8Vec_toList_of_length hlen_u8, ← bytesToBv8_eq_ofU8]; unfold bytesToBv8 toU8
  rw [List.map_map]; simp [Function.comp_def]

private theorem bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    bytesToBv8 (vecU8 v) = v.toList := by
  unfold vecU8 bytesToBv8 toU8; rw [List.map_map]; simp [Function.comp_def]

theorem hookSat_dalekEdNegExtSpec_of_cryptoLeafStub [LibsignalPlacement] {H : LibsignalHooks}
    {hookStack : Nat} (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack ≤ 2 ^ 64)
    (hh : HookSat H lsDalekEdNegSym
      (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :
    HookSat H lsDalekEdNegSym (withLsRet (dalekEdNegExtSpec hookStack)) := by
  refine hookSat_withLsRet_map
    (specSimulates_dalekEdNegExtSpec_mono (s₁ := pqxdhHookStack) hle hbound)
    (hookSat_withLsRet_map (SpecSimulates.of_map fun g R s0 hpre => ?_) (hookSat_withLsRet hh))
  dsimp only [dalekEdNegExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hrest⟩
  have hu8_len : (toU8 g.edBytes).length = 160 := by unfold toU8; simp [hlen]
  have hbs : bytesToBv8 (toU8 g.edBytes) = g.edBytes := by
    rw [bytesToBv8_eq_ofU8, ← u8Vec_toList_of_length hu8_len, toList_u8Vec_toU8 hlen]
  refine ⟨{ inPtr := g.inPtr, inBytes := toU8 g.edBytes, outPtr := g.outPtr }, R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [cryptoLeafStubSpec]; rw [hbs, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, hu8_len⟩, hrest⟩
  · dsimp only [cryptoLeafStubSpec] at hp; dsimp only [dalekEdNegExtSpec]
    have hout_len : (vecU8 (dalekEdNegVec (u8Vec 160 (toU8 g.edBytes)))).length = 160 := by
      unfold vecU8 toU8; simp
    rw [hbs, fitBv8_of_length_eq hout_len, bytesToBv8_vecU8] at hp
    have hv_ed : (dalekEdNegVec (u8Vec 160 (toU8 g.edBytes))).toList =
        dalekEdNegBytes (u8Vec 160 (toU8 g.edBytes)).toList := rfl
    rw [hv_ed, toList_u8Vec_toU8 hlen] at hp
    exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

theorem specSimulates_dalekEdNegExtSpec_of_withStack (hookStack : Nat) :
    SpecSimulates (withStack (edwardsPointNegUnstackedSpec false) hookStack)
      (dalekEdNegExtSpec hookStack) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [dalekEdNegExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hrest⟩
  refine ⟨(g.inPtr, ⟨g.edBytes, hlen⟩, g.outPtr), R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [edwardsPointNegUnstackedSpec, withStack]; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hrest⟩
  · dsimp only [edwardsPointNegUnstackedSpec, withStack, inputAfter] at hp
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    change sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗
      (g.outPtr ↦ₛ dalekEdNegBytes g.edBytes)) ∗ stackAt s0.sp hookStack) ∗ R at hp
    dsimp only [dalekEdNegExtSpec]; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

theorem specSimulates_dalekScalarWideExtSpec_of_withStack (hookStack : Nat) :
    SpecSimulates (withStack
      ({ pre := fun (inA, (v : List.Vector (BitVec 8) 64), ret) s =>
           ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret 32
         post := fun (inA, v, ret) s0 sf =>
           ⌜sf.trace = s0.trace⌝ ∗ inputAfter false inA v ∗ (ret ↦ₛ (dalekScalarWideVec v).toList) } :
        Spec (BitVec 64 × List.Vector (BitVec 8) 64 × BitVec 64)) hookStack)
      (dalekScalarWideExtSpec hookStack) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [dalekScalarWideExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hrest⟩
  refine ⟨(g.inPtr, ⟨g.inBytes, hlen⟩, g.outPtr), R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [withStack]; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hrest⟩
  · dsimp only [withStack, inputAfter] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
    change sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.inBytes) ∗
      (g.outPtr ↦ₛ natToLeBytes 32 (leBytesToNat g.inBytes % edOrderL))) ∗ stackAt s0.sp hookStack) ∗ R at hp
    dsimp only [dalekScalarWideExtSpec]; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

theorem specSimulates_dalekScalarModExtSpec_of_withStack (hookStack : Nat) :
    SpecSimulates (withStack
      ({ pre := fun (inA, (v : List.Vector (BitVec 8) 32), ret) s =>
           ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret⌝ ∗ (inA ↦ₛ v.toList) ∗ memRegion ret 32
         post := fun (inA, v, ret) s0 sf =>
           ⌜sf.trace = s0.trace⌝ ∗ inputAfter false inA v ∗ (ret ↦ₛ (dalekScalarModVec v).toList) } :
        Spec (BitVec 64 × List.Vector (BitVec 8) 32 × BitVec 64)) hookStack)
      (dalekScalarModExtSpec hookStack) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [dalekScalarModExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen⟩, hrest⟩
  refine ⟨(g.inPtr, ⟨g.inBytes, hlen⟩, g.outPtr), R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [withStack]; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hrest⟩
  · dsimp only [withStack, inputAfter] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
    change sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.inBytes) ∗
      (g.outPtr ↦ₛ natToLeBytes 32 (leBytesToNat g.inBytes % edOrderL))) ∗ stackAt s0.sp hookStack) ∗ R at hp
    dsimp only [dalekScalarModExtSpec]; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

theorem specSimulates_dalekCompressExtSpec_of_vecSpec (hookStack bound : Nat) (hbnd : 2 ^ 52 ≤ bound) :
    SpecSimulates (withStack
      ({ pre := fun (inA, (v : List.Vector (BitVec 8) 160), ret) s =>
           ⌜s.readReg64 .x0 = inA ∧ s.readReg64 .x8 = ret ∧ fe51Point4Bounded v.toList bound⌝ ∗
             (inA ↦ₛ v.toList) ∗ memRegion ret 32
         post := fun (inA, v, ret) s0 sf =>
           ⌜sf.trace = s0.trace⌝ ∗ inputAfter false inA v ∗
             (ret ↦ₛ encodeEd (edExtToAffine (edExtOfBytes v.toList))) } :
        Spec (BitVec 64 × List.Vector (BitVec 8) 160 × BitVec 64)) hookStack)
      (dalekCompressExtSpec hookStack) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  dsimp only [dalekCompressExtSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; rcases hpre with ⟨⟨hx0, hx8, hlen, hfe⟩, hrest⟩
  refine ⟨(g.inPtr, ⟨g.edBytes, hlen⟩, g.outPtr), R, ?_, fun sf _ _ hp => ?_⟩
  · dsimp only [withStack]; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, fe51Point4Bounded_mono_local hbnd hfe⟩,
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hrest⟩
  · dsimp only [withStack, inputAfter] at hp; simp only [Bool.false_eq_true, ↓reduceIte] at hp
    change sf.mem ⊨ ((⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗
      (g.outPtr ↦ₛ encodeEd (edExtToAffine (edExtOfBytes g.edBytes)))) ∗ stackAt s0.sp hookStack) ∗ R at hp
    dsimp only [dalekCompressExtSpec]; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hp

/-- Placement-free extended-Edwards hook bundle for Blocks `204` and `203`. -/
structure VerifySignatureExtHooks (hookStack : Nat := dalekHookStack)
    (P : SignalPqxdh.Primitives) (H : LibsignalHooks) [LibsignalPlacement] : Prop where
  memcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  memset : HookSat H lsVerifyMemsetSym (sessionMemsetSpec hookStack)
  blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat
  sha512Compress : HookSat H lsSha512CompressSym
    (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128))
  montToEd : HookSat H lsVerifyMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack))
  compress : HookSat H lsDalekCompressSym (withLsRet (dalekCompressExtSpec hookStack))
  edNeg : HookSat H lsDalekEdNegSym (withLsRet (dalekEdNegExtSpec hookStack))
  scalarWide : HookSat H lsDalekScalarWideSym (withLsRet (dalekScalarWideExtSpec hookStack))
  scalarMod : HookSat H lsDalekScalarModSym (withLsRet (dalekScalarModExtSpec hookStack))
  doubleMul : HookSat H lsDalekDoubleMulSym (withLsRet (dalekDsmbExtSpec hookStack))

theorem hookSat_blackBox_of_exact {H : LibsignalHooks} (hb : H lsBlackBoxU8Sym = some blackBoxHook) :
    HookSat H lsBlackBoxU8Sym blackBoxSpecSat := hookSat_blackBox_of_eq hb

theorem hookSat_sha512Compress_of_stub {H : LibsignalHooks} (P : SignalPqxdh.Primitives)
    (hh : HookSat H lsSha512CompressSym (compressInPlaceStubSpec (sha512CompressOutBytes P) 64 128)) :
    HookSat H lsSha512CompressSym (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128) := hh

theorem VerifySignatureExtHooks.mono [LibsignalPlacement] {s₁ s₂ : Nat}
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64)
    (hH : VerifySignatureExtHooks s₁ P H) : VerifySignatureExtHooks s₂ P H where
  memcpy := hH.memcpy; memset := hookSat_sessionMemsetSpec_mono hle hbound hH.memset
  blackBox := hH.blackBox; sha512Compress := hH.sha512Compress
  montToEd := hookSat_dalekMontToEdExtSpec_mono hle hbound hH.montToEd
  compress := hookSat_withLsRet_map (specSimulates_dalekCompressExtSpec_mono hle hbound) hH.compress
  edNeg := hookSat_withLsRet_map (specSimulates_dalekEdNegExtSpec_mono hle hbound) hH.edNeg
  scalarWide := hookSat_withLsRet_map (specSimulates_dalekScalarWideExtSpec_mono hle hbound) hH.scalarWide
  scalarMod := hookSat_withLsRet_map (specSimulates_dalekScalarModExtSpec_mono hle hbound) hH.scalarMod
  doubleMul := hookSat_withLsRet_map (specSimulates_dalekDsmbExtSpec_mono hle hbound) hH.doubleMul

theorem VerifySignatureExtHooks.of_vmPreserved [LibsignalPlacement] {hookStack : Nat}
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (h_memcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (h_memset : HookSat H lsVerifyMemsetSym (sessionMemsetSpec hookStack))
    (h_blackBox : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (h_sha512Compress : HookSat H lsSha512CompressSym
      (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128)))
    (h_montToEd : HookSat H lsVerifyMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (h_compress : HookSat H lsDalekCompressSym (withLsRet (withVmPreserved (dalekCompressExtSpec hookStack))))
    (h_edNeg : HookSat H lsDalekEdNegSym (withLsRet (withVmPreserved (dalekEdNegExtSpec hookStack))))
    (h_scalarWide : HookSat H lsDalekScalarWideSym (withLsRet (withVmPreserved (dalekScalarWideExtSpec hookStack))))
    (h_scalarMod : HookSat H lsDalekScalarModSym (withLsRet (withVmPreserved (dalekScalarModExtSpec hookStack))))
    (h_doubleMul : HookSat H lsDalekDoubleMulSym (withLsRet (withVmPreserved (dalekDsmbExtSpec hookStack)))) :
    VerifySignatureExtHooks hookStack P H where
  memcpy := h_memcpy; memset := h_memset; blackBox := h_blackBox; sha512Compress := h_sha512Compress
  montToEd := hookSat_withLsRet_of_withVmPreserved h_montToEd
  compress := hookSat_withLsRet_of_withVmPreserved h_compress
  edNeg := hookSat_withLsRet_of_withVmPreserved h_edNeg
  scalarWide := hookSat_withLsRet_of_withVmPreserved h_scalarWide
  scalarMod := hookSat_withLsRet_of_withVmPreserved h_scalarMod
  doubleMul := hookSat_withLsRet_of_withVmPreserved h_doubleMul

theorem subroutine_ok_strip_withLsRet_204 [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (off : BitVec 64)
    (hok : subroutine_ok prog entry (withLsRet spec)) (ho : off.toNat < lsLen 204 := by decide) :
    subroutine_ok prog entry
      { spec with pre := fun x s => ⌜s.readReg64 .lr = (blkPl_204).base + off⌝ ∗ spec.pre x s } :=
  subroutine_ok_mono hok (fun _ _ _ hpre => by
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    exact satisfies_withLsRet_of_blockPlacement_base_add 204 off hpre.1 hpre.2 (by decide) ho)
    (fun _ _ _ _ hq => hq)

/-! ## 2. Call Specifications & `XeddsaCurveSound` (`Phase4RefBridge` Bridge) -/

/-- Relocatable call specification for Block `204` (`hookStack + 1248` stack bytes). -/
@[expose] def verifySignatureMultipartCallSpecAt (hookStack : Nat)
    (P : SignalPqxdh.Primitives) : Spec VerifySignatureMultipartPlacedGhost where
  pre g s := ⌜s.readReg64 .x0 = g.pkPtr ∧ s.readReg64 .x1 = g.slicesPtr ∧ s.readReg64 .x2 = 1#64 ∧
      s.readReg64 .x3 = g.sigPtr ∧ s.readReg64 .x4 = 64#64 ∧ g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧ g.sig.length = 64⌝ ∗
    (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.slicesPtr ↦₆₄ g.msgPtr) ∗
    ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
    (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt s.sp (hookStack + 1248)
  post g s0 sf := ⌜sf.readReg64 .x0 =
      (if SignalPqxdh.xeddsaVerifyRef P g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗ (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.slicesPtr ↦₆₄ g.msgPtr) ∗
    ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
    (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt s0.sp (hookStack + 1248)

theorem verifySignatureMultipartCallSpecAt_pqxdhHookStack (P : SignalPqxdh.Primitives) :
    verifySignatureMultipartCallSpecAt pqxdhHookStack P = verifySignatureMultipartCallSpec P := rfl

/-- Relocatable call specification for Block `203` (`hookStack + 1280` stack bytes). -/
@[expose] def verifySignatureCallSpecAt (hookStack : Nat)
    (P : SignalPqxdh.Primitives) : Spec VerifySignaturePlacedGhost where
  pre g s := ⌜s.readReg64 .x0 = g.pkPtr ∧ s.readReg64 .x1 = g.msgPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧ s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧ g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧ g.sig.length = 64⌝ ∗
    (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
    (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt s.sp (hookStack + 1280)
  post g s0 sf := ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗ (g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
    (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt s0.sp (hookStack + 1280)

theorem verifySignatureCallSpecAt_pqxdhHookStack (P : SignalPqxdh.Primitives) :
    verifySignatureCallSpecAt pqxdhHookStack P = verifySignatureCallSpec P := rfl

/-- Curve-soundness predicate on `P : SignalPqxdh.Primitives` for XEdDSA verification. -/
structure XeddsaCurveSound (P : SignalPqxdh.Primitives) : Prop where
  sha512Compress_len : ∀ st blk, (P.sha512Compress st blk).length = 64
  sha512_eq : ∀ m, P.sha512 m = SignalPqxdh.sha512Ref P m
  sigVerify_eq : ∀ pk m sig, P.sigVerify pk m sig = SignalPqxdh.xeddsaVerifyRef P pk m sig
  xeddsaVerifyRef_eq : ∀ pk m sig,
    pk.length = 32 → sig.length = 64 → ((sig.getD 63 0 &&& 0x60) == 0) = true →
    SignalPqxdh.xeddsaVerifyRef P pk m sig =
      match montToEdwards (ofU8 pk) ((sig.getD 63 0 &&& 0x80) >>> 7).toNat with
      | none => false
      | some Apt =>
        let capA := toU8 (encodeEd Apt); let capR := sig.take 32
        let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
        let hNat := leBytesToNat (u8Vec 64 (P.sha512 (capR ++ capA ++ m))).toList % edOrderL
        let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
        toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt))) == capR

theorem xeddsaVerifyRef_blockLevelPrims_eq_of_sound {D : DalekPrims} (hD : DalekPrimsSound D)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (sha512 : List UInt8 → List UInt8) (pk m sig : List UInt8) :
    SignalPqxdh.xeddsaVerifyRef
      ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩ with sha512 }) pk m sig =
      if pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0) then
        match montToEdwards (ofU8 pk) ((sig.getD 63 0 &&& 0x80) >>> 7).toNat with
        | none => false
        | some Apt =>
          let capA := toU8 (encodeEd Apt); let capR := sig.take 32
          let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
          let hNat := leBytesToNat (u8Vec 64 (sha512 (capR ++ capA ++ m))).toList % edOrderL
          let sNat := leBytesToNat (u8Vec 32 sClamped).toList % edOrderL
          toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt))) == capR
      else false := by
  rw [xeddsaVerifyRef_congr_of_sound hD dalekPrimsRef_sound X C Qh sha512 pk m sig,
    xeddsaVerifyRef_dalekPrimsRef_eq X C Qh sha512 pk m sig]; rfl

theorem xeddsaCurveSound_blockLevelPrims_of_sound {D : DalekPrims} (hD : DalekPrimsSound D)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    let B := blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩
    let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
    XeddsaCurveSound { B1 with sigVerify := SignalPqxdh.xeddsaVerifyRef B1 } := by
  dsimp only; refine ⟨fun st blk => (VerifySignaturePrims.of_structuralPrims
      (structuralPrims_modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩)).sha512Compress_len st blk,
    fun _ => rfl, fun _ _ _ => rfl, fun pk m sig hpk hsig h60 => ?_⟩
  change SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩ with
    sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) }) pk m sig = _
  rw [xeddsaVerifyRef_blockLevelPrims_eq_of_sound hD X C Qh _ pk m sig]
  have hcond : (pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0)) = true := by
    rw [beq_iff_eq.mpr hpk, beq_iff_eq.mpr hsig, h60]; rfl
  rw [hcond, show ∀ x y : Bool, (if true = true then x else y) = x from fun _ _ => rfl]

theorem xeddsaCurveSound_modelPrims_of_sound {D : DalekPrims} (hD : DalekPrimsSound D)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    XeddsaCurveSound (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) := by
  refine ⟨fun st blk => (VerifySignaturePrims.of_structuralPrims
      (structuralPrims_modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩)).sha512Compress_len st blk,
    fun _ => rfl, fun _ _ _ => rfl, fun pk m sig hpk hsig h60 => ?_⟩
  change SignalPqxdh.xeddsaVerifyRef ({ blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩ with
    sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) }) pk m sig = _
  rw [xeddsaVerifyRef_blockLevelPrims_eq_of_sound hD X C Qh _ pk m sig]
  have hcond : (pk.length == 32 && sig.length == 64 && ((sig.getD 63 0 &&& 0x60) == 0)) = true := by
    rw [beq_iff_eq.mpr hpk, beq_iff_eq.mpr hsig, h60]; rfl
  rw [hcond, show ∀ x y : Bool, (if true = true then x else y) = x from fun _ _ => rfl]; rfl

theorem xeddsaCurveSound_blockLevelPrims_dalekPrimsRef
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    let B := blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩
    let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
    XeddsaCurveSound { B1 with sigVerify := SignalPqxdh.xeddsaVerifyRef B1 } :=
  xeddsaCurveSound_blockLevelPrims_of_sound dalekPrimsRef_sound X C Qh

theorem xeddsaCurveSound_modelPrims_dalekPrimsRef
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    XeddsaCurveSound (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) :=
  xeddsaCurveSound_modelPrims_of_sound dalekPrimsRef_sound X C Qh

/-! ## 3. Block `204` Segment Proofs Against Extended-Edwards Hooks -/

private abbrev savedRegs12 (fsp x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 ret : BitVec 64) : SepProp :=
  ((fsp + 1152#64) ↦₆₄ x29) ∗ ((fsp + 1160#64) ↦₆₄ ret) ∗ ((fsp + 1168#64) ↦₆₄ x28) ∗
  ((fsp + 1176#64) ↦₆₄ x27) ∗ ((fsp + 1184#64) ↦₆₄ x26) ∗ ((fsp + 1192#64) ↦₆₄ x25) ∗
  ((fsp + 1200#64) ↦₆₄ x24) ∗ ((fsp + 1208#64) ↦₆₄ x23) ∗ ((fsp + 1216#64) ↦₆₄ x22) ∗
  ((fsp + 1224#64) ↦₆₄ x21) ∗ ((fsp + 1232#64) ↦₆₄ x20) ∗ ((fsp + 1240#64) ↦₆₄ x19)

private theorem bytesToBv8_toU8 (bs : List (BitVec 8)) : bytesToBv8 (toU8 bs) = bs := by
  unfold bytesToBv8 toU8; rw [List.map_map]; simp [Function.comp_def]

private theorem list_sig_split_63 {sig : Bytes} (hsig : sig.length = 64) :
    bytesToBv8 sig = bytesToBv8 (sig.take 63) ++ [(bytesToBv8 sig).getD 63 0#8] := by
  rcases sig with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31,
    _ | ⟨b32, _ | ⟨b33, _ | ⟨b34, _ | ⟨b35, _ | ⟨b36, _ | ⟨b37, _ | ⟨b38, _ | ⟨b39,
    _ | ⟨b40, _ | ⟨b41, _ | ⟨b42, _ | ⟨b43, _ | ⟨b44, _ | ⟨b45, _ | ⟨b46, _ | ⟨b47,
    _ | ⟨b48, _ | ⟨b49, _ | ⟨b50, _ | ⟨b51, _ | ⟨b52, _ | ⟨b53, _ | ⟨b54, _ | ⟨b55,
    _ | ⟨b56, _ | ⟨b57, _ | ⟨b58, _ | ⟨b59, _ | ⟨b60, _ | ⟨b61, _ | ⟨b62, _ | ⟨b63, _ |
      _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (simp at hsig)
  rfl

private theorem sig_focus_63 {sig : Bytes} (sigPtr : BitVec 64) (h : sig.length = 64) :
    (sigPtr ↦ₛ bytesToBv8 sig) =
      ((sigPtr ↦ₛ bytesToBv8 (sig.take 63)) ∗ ((sigPtr + 63#64) ↦₈ (bytesToBv8 sig).getD 63 0#8)) := by
  have hl63 : (bytesToBv8 (sig.take 63)).length = 63 := by simp [bytesToBv8, h]
  conv => lhs; rw [list_sig_split_63 h]
  rw [pointsToBytes_append, hl63]; simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

@[local simp, local wp_norm, local arm64_norm]
private theorem sig_getD63_ushiftRight7_eq_signBit (sig : Bytes) :
    (bytesToBv8 sig).getD 63 0#8 >>> 7 = BitVec.ofNat 8 (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) := by
  rw [bytesToBv8_getD_eq]; rcases sig.getD 63 0 with ⟨bv⟩; revert bv; decide

private theorem memRegion168_of_cell_and_memRegion160_v (a v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ⊢ memRegion a 168 := by
  refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion a v)) ?_
  rw [← @ProofLib.memRegion_split' a (a + 8#64) 8 160 168 rfl (by bv_omega) (by decide)]; exact Entails.refl _

private theorem memRegion168_of_cell_and_bytes160 (a v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ⊢ memRegion a 168 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion a v)
    (pointsToBytes_entails_memRegion_n (a + 8#64) bs hlen)) ?_
  rw [← @ProofLib.memRegion_split' a (a + 8#64) 8 160 168 rfl (by bv_omega) (by decide)]; exact Entails.refl _

private theorem exists_unpack64_of_length_160_eq {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64,
      ∀ a : BitVec 64, (a ↦ₛ bs) =
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
         ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
         ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
         ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) ∗
         ((a + 128#64) ↦₆₄ w16) ∗ ((a + 136#64) ↦₆₄ w17) ∗ ((a + 144#64) ↦₆₄ w18) ∗ ((a + 152#64) ↦₆₄ w19)) := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  have h4 : (bs.drop 128).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 h4
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, fun a => ?_⟩
  have hsplit : bs = bs.take 32 ++ ((bs.drop 32).take 32 ++ ((bs.drop 64).take 32 ++
    ((bs.drop 96).take 32 ++ bs.drop 128))) := by
    have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
    have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
    have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
    have s1 : bs = bs.take 32 ++ bs.drop 32 := (List.take_append_drop 32 bs).symm
    rw [s4] at s3; rw [s3] at s2; rw [s2] at s1; exact s1
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, pointsToBytes_append, h1, hp1, pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem uint8_and7f_ule32_of_and60_eq_true (b : UInt8) (h : (b &&& 0x60 == 0) = true) :
    (32#64).ule (BitVec.zeroExtend 64 b.toBitVec &&& 545460846719#64) = false := by
  rcases b with ⟨bv⟩; revert bv h; decide

private theorem truncate32_and7f_eq (sig : Bytes) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec &&& 545460846719#64) =
      BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32 := by
  rw [bytesToBv8_getD_eq]; generalize sig.getD 63 0 = b; rcases b with ⟨bv⟩; revert bv; decide

private theorem of_sepWP_sha512IV_placed {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop} {pl : Obj.MultiPlacement}
    (hro : Obj.HoldsBytes s.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (h : SepWP prog (roStop mid) s P (fun sm Pm =>
      Obj.HoldsBytes sm.mem (pl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro) →
        SepWP prog target_pc sm Pm post)) : SepWP prog target_pc s P post := by
  unfold roStop at h; exact SepWP.seq_frozen (fun _ _ h0 hkf => holdsBytes_ro_of_keepsFrozen h0 hkf) hro h

private theorem sha512IV_cells_eq (a : BitVec 64) :
    ((a ↦₆₄ 0x6a09e667f3bcc908#64) ∗ ((a + 8#64) ↦₆₄ 0xbb67ae8584caa73b#64) ∗
     ((a + 16#64) ↦₆₄ 0x3c6ef372fe94f82b#64) ∗ ((a + 24#64) ↦₆₄ 0xa54ff53a5f1d36f1#64) ∗
     ((a + 32#64) ↦₆₄ 0x510e527fade682d1#64) ∗ ((a + 40#64) ↦₆₄ 0x9b05688c2b3e6c1f#64) ∗
     ((a + 48#64) ↦₆₄ 0x1f83d9abfb41bd6b#64) ∗ ((a + 56#64) ↦₆₄ 0x5be0cd19137e2179#64)) =
      (a ↦ₛ sha512IVBytesLE) := by
  rw [sha512IVBytesLE_eq_unpack64]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd]

set_option maxHeartbeats 1600000 in
private theorem verifySig_seg1a_ext_placed_at [LibsignalPlacement] (hookStack : Nat) (H : LibsignalHooks)
    (hmontHook : HookSat H lsVerifyMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (s : State) (fsp pkPtr slicesPtr sigPtr retAddr : BitVec 64) (pk sig : Bytes) (Frame : SepProp)
    (hpk : pk.length = 32) (hsig : sig.length = 64) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running) (hpc : s.pc = (blkPl_204).base) (hsp : s.sp = fsp + 1248#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr) (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = 1#64) (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64) (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 84#64) s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ cells fsp 1 ∗ cells (fsp + 16#64) 4 ∗
       memRegion (fsp + 800#64) 168 ∗ cells (fsp + 1152#64) 12 ∗ stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
          memRegion (fsp + 16#64) 32 ∗
          dalekMontToEdExtOutAt (fsp + 800#64) (bytesToBv8 pk) (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) ∗
          savedRegs12 fsp (s.readReg64 (.gpr 19#5)) (s.readReg64 (.gpr 20#5)) (s.readReg64 (.gpr 21#5))
            (s.readReg64 (.gpr 22#5)) (s.readReg64 (.gpr 23#5)) (s.readReg64 (.gpr 24#5))
            (s.readReg64 (.gpr 25#5)) (s.readReg64 (.gpr 26#5)) (s.readReg64 (.gpr 27#5))
            (s.readReg64 (.gpr 28#5)) (s.readReg64 (.gpr 29#5)) retAddr ∗ stackAt fsp hookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 84#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = sigPtr ∧ sm.readReg64 (.gpr 20#5) = slicesPtr ∧
        sm.readReg64 (.gpr 21#5) = 1#64 ∧
        sm.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 ((bytesToBv8 sig).getD 63 0#8) ∧
        sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmont := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    84#64 (ls_hook_ok_any hmontHook (by set_option maxRecDepth 20000 in decide))
  dsimp only [dalekMontToEdExtSpec] at hmont; clear hmontHook
  have hpk_bv : (bytesToBv8 pk).length = 32 := by simp [bytesToBv8, hpk]
  obtain ⟨p0, p1, p2, p3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hpk_bv
  cells_pre_unfold_fast; wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_focus_63 sigPtr hsig)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_focus_63 sigPtr hsig).symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hpk_cells pkPtr).symm) (by sep_frame)
  have hpk_sp16 := (hpk_cells (fsp + 16#64)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk_sp16
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hpk_sp16) (by sep_frame)
  wp_call hmont ⟨pk, (sig.getD 63 0 &&& 0x80) >>> 7, fsp + 16#64, fsp + 800#64⟩
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq
    (dalekMontToEdExtOutAt_and_one_eq_toNat (fsp + 800#64) (bytesToBv8 pk) ((sig.getD 63 0 &&& 0x80) >>> 7)))
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := pointsToBytes_entails_memRegion_n (fsp + 16#64) _ hpk_bv) (by sep_frame)
  wp_simp_pre_fast [hsp_sf]; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

private theorem verifySig_seg1a_none_ext_placed [LibsignalPlacement] (H : LibsignalHooks) (s : State)
    (fsp : BitVec 64) (pk_bs : List (BitVec 8)) (sign : Nat) (Frame : SepProp)
    (hmont : montToEdwards pk_bs sign = none) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running) (hpc : s.pc = (blkPl_204).base + 84#64) (hsp : s.sp = fsp) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 1096#64) s
      (dalekMontToEdExtOutAt (fsp + 800#64) pk_bs sign ∗ Frame)
      (fun sm Pm => (Pm ⊢ memRegion (fsp + 800#64) 168 ∗ Frame) ∧ sm.status = ExecStatus.Running ∧
        sm.pc = (blkPl_204).base + 1096#64 ∧ sm.sp = fsp ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (dalekMontToEdExtOutAt_none (fsp + 800#64) pk_bs sign hmont))
    (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := memRegion168_of_cell_and_memRegion160_v (fsp + 800#64) 0#64) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
private theorem verifySig_seg1b_ext_placed_at [LibsignalPlacement] (hookStack : Nat) (H : LibsignalHooks)
    (hcompHook : HookSat H lsDalekCompressSym (withLsRet (dalekCompressExtSpec hookStack)))
    (s : State) (fsp : BitVec 64) (ed_bs : List (BitVec 8)) (Apt : EdPoint) (Frame : SepProp)
    (hed_len : ed_bs.length = 160) (hed_bnd : fe51Point4Bounded ed_bs (2 ^ 52))
    (hed_eq : edExtOfBytes ed_bs = edExtOfAffine Apt) (hApt_on : edOnCurve Apt = true)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 84#64) (hsp : s.sp = fsp) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 232#64) s
      (cells (fsp + 48#64) 20 ∗ cells (fsp + 208#64) 20 ∗ memRegion (fsp + 368#64) 32 ∗
       ((fsp + 800#64) ↦₆₄ 1#64) ∗ ((fsp + 800#64 + 8#64) ↦ₛ ed_bs) ∗ stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ ed_bs) ∗
          ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗ memRegion (fsp + 800#64) 168 ∗
          stackAt fsp hookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 232#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧ sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧ sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hcomp := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    232#64 (ls_hook_ok_any hcompHook (by set_option maxRecDepth 20000 in decide))
  dsimp only [dalekCompressExtSpec] at hcomp; clear hcompHook
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
    hed_cells⟩ := exists_unpack64_of_length_160_eq hed_len
  cells_pre_unfold_fast; wp_extract_exists
  have hed_808 := hed_cells (fsp + 800#64 + 8#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_808
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_808.symm) (by sep_frame)
  have hm168 := memRegion168_of_cell_and_bytes160 (fsp + 800#64) 1#64 hed_len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm168
  apply ProofLib.SepWP.replace_pre (hPQ := hm168) (by sep_frame)
  have hed_48 := (hed_cells (fsp + 48#64)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_48
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_48) (by sep_frame)
  have hed_208 := (hed_cells (fsp + 208#64)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hed_208
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hed_208) (by sep_frame)
  wp_call hcomp ⟨fsp + 48#64, ed_bs, fsp + 368#64⟩
  have hcomp_eq : encodeEd (edExtToAffine (edExtOfBytes ed_bs)) = bytesToBv8 (toU8 (encodeEd Apt)) := by
    rw [hed_eq, edExtToAffine_edExtOfAffine hApt_on, bytesToBv8_toU8]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (congrArg ((fsp + 368#64) ↦ₛ ·) hcomp_eq)) (by sep_frame)
  wp_simp_pre_fast [hsp, hsp_sf]
  apply ProofLib.SepWP.replace_pre (hPQ := pointsToBytes_entails_memRegion_n (fsp + 48#64) _ hed_len) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
private theorem verifySig_seg1c_ext_placed_at [LibsignalPlacement] (hookStack : Nat) (H : LibsignalHooks)
    (hednegHook : HookSat H lsDalekEdNegSym (withLsRet (dalekEdNegExtSpec hookStack)))
    (s : State) (fsp sigPtr : BitVec 64) (ed_bs : List (BitVec 8)) (capA sig : Bytes) (Frame : SepProp)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hed_len : ed_bs.length = 160) (hcapA : capA.length = 32) (hsig : sig.length = 64)
    (hvalid : (sig.getD 63 0 &&& 0x60 == 0) = true) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running) (hpc : s.pc = (blkPl_204).base + 232#64) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 (.gpr 19#5) = sigPtr)
    (hx22 : s.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 320#64) s
      (memRegion fsp 4 ∗ memRegion (fsp + 4#64) 4 ∗ cells (fsp + 8#64) 1 ∗
       ((fsp + 208#64) ↦ₛ ed_bs) ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗ memRegion (fsp + 400#64) 160 ∗
       cells (fsp + 560#64) 8 ∗ memRegion (fsp + 687#64) 1 ∗ cells (fsp + 688#64) 10 ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion fsp 4 ∗ ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 capA) ∗
          ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗ ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ capA)) ∗
          ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ sha512IVBytesLE) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
          ((fsp + 760#64) ↦₆₄ 0#64) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp hookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 320#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧ sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧ sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hedneg := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    260#64 (ls_hook_ok_any hednegHook (by set_option maxRecDepth 20000 in decide))
  dsimp only [dalekEdNegExtSpec] at hedneg; clear hednegHook
  have hsig32_bv : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  obtain ⟨r0, r1, r2, r3, _, hsig32_cells⟩ := exists_unpack64_of_length_32 hsig32_bv
  have hcapA_bv : (bytesToBv8 capA).length = 32 := by simp [bytesToBv8, hcapA]
  obtain ⟨a0, a1, a2, a3, _, hcapA_cells⟩ := exists_unpack64_of_length_32 hcapA_bv
  rw [ProofLib.memRegion_four (fsp + 4#64), ProofLib.memRegion_one (fsp + 687#64)]
  cells_pre_unfold_fast; wp_extract_exists
  apply of_sepWP_sha512IV_placed hro (mid := (blkPl_204).base + 272#64)
  wp_step; wp_step; wp_step
  rw [uint8_and7f_ule32_of_and60_eq_true (sig.getD 63 0) hvalid]; simp only [Bool.false_eq_true, ↓reduceIte]
  wp_steps
  wp_call hedneg ⟨fsp + 208#64, ed_bs, fsp + 400#64⟩
  wp_simp_pre_fast [truncate32_and7f_eq, hsp, hsp_sf]
  apply blkPC_204_pairStep_0x104 (blkPl_204).base H rfl (by wp_norm_goal) (by wp_norm_goal)
  wp_steps; apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs); intro hro1
  apply of_sepWP_sha512IV_placed hro1 (mid := (blkPl_204).base + 288#64)
  wp_step_ldp_ro (sha512IV_placed_quad0 hro1)
  wp_steps; apply SepWP.done_ro (by wp_norm_lhs) (by wp_norm_lhs); intro hro2
  wp_step_ldp_ro (sha512IV_placed_quad1 hro2)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr)) (by sep_frame)
  have hcapA_368 := hcapA_cells (fsp + 368#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_368
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368) (by sep_frame)
  wp_steps
  have hsha_688 := sha512IV_cells_eq (fsp + 688#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsha_688
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsha_688) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig32_cells sigPtr).symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig).symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_368.symm) (by sep_frame)
  have hsig_560 := (hsig32_cells (fsp + 560#64)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsig_560
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsig_560) (by sep_frame)
  have hcapA_592 := (hcapA_cells (fsp + 592#64)).symm; simp only [BitVec.add_assoc, BitVec.reduceAdd] at hcapA_592
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hcapA_592) (by sep_frame)
  have hmerge_560 : ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32)) ∗ ((fsp + 592#64) ↦ₛ bytesToBv8 capA) =
      ((fsp + 560#64) ↦ₛ bytesToBv8 (sig.take 32 ++ capA)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hsig32_bv, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge_560) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := pointsToBytes_entails_memRegion_n (fsp + 208#64) _ hed_len) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

private theorem stackAt_1248_split_low (fsp : BitVec 64) {hookStack : Nat}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64) :
    stackAt (fsp + 1248#64) (hookStack + 1248) =
      memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗
        stackAt (fsp + 1248#64) (pqxdhHookStack + 1248) := by
  have hb : fsp + 1248#64 - BitVec.ofNat 64 (hookStack + 1248) =
      fsp - BitVec.ofNat 64 hookStack := by bv_omega
  have hn : hookStack + 1248 - (pqxdhHookStack + 1248) = hookStack - pqxdhHookStack := by omega
  rw [stackAt_split_low (fsp + 1248#64) (by omega : pqxdhHookStack + 1248 ≤ hookStack + 1248)
    hbound, hb, hn]

private theorem stackAt_1280_split_low (fsp : BitVec 64) {hookStack : Nat}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64) :
    stackAt (fsp + 1280#64) (hookStack + 1280) =
      memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗
        stackAt (fsp + 1280#64) (pqxdhHookStack + 1280) := by
  have hb : fsp + 1280#64 - BitVec.ofNat 64 (hookStack + 1280) =
      fsp - BitVec.ofNat 64 hookStack := by bv_omega
  have hn : hookStack + 1280 - (pqxdhHookStack + 1280) = hookStack - pqxdhHookStack := by omega
  rw [stackAt_split_low (fsp + 1280#64) (by omega : pqxdhHookStack + 1280 ≤ hookStack + 1280)
    hbound, hb, hn]

private theorem memRegion_800_seg3a_split (fsp : BitVec 64) :
    memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 =
      cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
      memRegion (fsp + 1136#64) 16 := by
  rw [← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 968#64) 168 184 352 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 928#64) 128 224 352 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 928#64) (fsp + 1008#64) 80 144 224 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1136#64) 128 16 144 rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 16 (by decide), memRegion_cells (fsp + 928#64) 10 (by decide),
    memRegion_cells (fsp + 1008#64) 16 (by decide)]

private theorem seg3a_to_seg3b_split (fsp : BitVec 64) :
    cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 =
      cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 960#64) 48 ∗
      memRegion (fsp + 1008#64) 32 ∗ memRegion (fsp + 1040#64) 96 := by
  rw [← memRegion_cells (fsp + 800#64) 16 (by decide), ← memRegion_cells (fsp + 928#64) 10 (by decide),
    ← memRegion_cells (fsp + 1008#64) 16 (by decide),
    ← @ProofLib.memRegion_split' (fsp + 928#64) (fsp + 1008#64) 80 128 208 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 928#64) 128 208 336 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 832#64) 32 304 336 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 832#64) (fsp + 960#64) 128 176 304 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 960#64) (fsp + 1008#64) 48 128 176 rfl (by bv_omega) (by decide),
    @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1040#64) 32 96 128 rfl (by bv_omega) (by decide),
    memRegion_cells (fsp + 800#64) 4 (by decide)]

private theorem seg3b_to_epilogue_merge_bv (fsp : BitVec 64) (v4 : BitVec 32) (v8 : BitVec 64)
    {capA_bs minusCapA_bs h_bs : List (BitVec 8)}
    (hcapA : capA_bs.length = 32) (hnegA : minusCapA_bs.length = 160) (hh : h_bs.length = 32) :
    memRegion fsp 4 ∗ ((fsp + 4#64) ↦₃₂ v4) ∗ ((fsp + 8#64) ↦₆₄ v8) ∗
      memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
      ((fsp + 368#64) ↦ₛ capA_bs) ∗ ((fsp + 400#64) ↦ₛ minusCapA_bs) ∗
      cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗ ((fsp + 768#64) ↦ₛ h_bs) ∗
      memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 960#64) 48 ∗ memRegion (fsp + 1008#64) 32 ∗
      memRegion (fsp + 1040#64) 96 ∗ memRegion (fsp + 1136#64) 16 ⊢ memRegion fsp 1152 := by
  have hw4 := pointsTo32_entails_memRegion (fsp + 4#64) v4
  have hw8 := pointsTo64_entails_memRegion (fsp + 8#64) v8
  have hw368 := pointsToBytes_entails_memRegion_n (fsp + 368#64) capA_bs hcapA
  have hw400 := pointsToBytes_entails_memRegion_n (fsp + 400#64) minusCapA_bs hnegA
  have hw768 := pointsToBytes_entails_memRegion_n (fsp + 768#64) h_bs hh
  rw [← memRegion_cells (fsp + 560#64) 16 (by decide), ← memRegion_cells (fsp + 688#64) 10 (by decide)]
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono hw4 (sepConj_mono hw8
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hw368 (sepConj_mono hw400
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw768)))))))))))
    (Entails.of_eq ?_)
  rw [← @ProofLib.memRegion_split' (fsp + 1040#64) (fsp + 1136#64) 96 16 112 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 1008#64) (fsp + 1040#64) 32 112 144 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 960#64) (fsp + 1008#64) 48 144 192 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 800#64) (fsp + 960#64) 160 192 352 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 768#64) (fsp + 800#64) 32 352 384 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 688#64) (fsp + 768#64) 80 384 464 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 560#64) (fsp + 688#64) 128 464 592 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 400#64) (fsp + 560#64) 160 592 752 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 368#64) (fsp + 400#64) 32 752 784 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 208#64) (fsp + 368#64) 160 784 944 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 48#64) (fsp + 208#64) 160 944 1104 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 16#64) (fsp + 48#64) 32 1104 1136 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 8#64) (fsp + 16#64) 8 1136 1144 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' (fsp + 4#64) (fsp + 8#64) 4 1144 1148 rfl (by bv_omega) (by decide),
    ← @ProofLib.memRegion_split' fsp (fsp + 4#64) 4 1148 1152 rfl (by bv_omega) (by decide)]

private def pqxdhCtEqMemSpec16 (m : Memory) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s0 =>
    ⌜s0.readReg64 .x0 = p1 ∧ s0.readReg64 .x1 = p2 ∧ s0.sp = sp ∧
      k1.length = 32 ∧ k2.length = 32 ∧ s0.mem = m⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ₛ k2) ∗ memRegion (sp - 64#64) 64
  post := ctEqSliceMemSpec16.post

private theorem pqxdhCtEq_call_ok_sat [LibsignalPlacement] {callerProg : Program}
    {i : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hbb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    {m : Memory} (hcl : LibsignalCodeLoaded lsmpl m) (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 213) (pqxdhCtEqMemSpec16 m) := by
  have hblk : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsmpl.base 213)
      ctEqSliceMemSpec16 := by
    simpa only [ls_blockPlacement_base] using ct_eq_mem_placed_ok_16_sat hbb
  exact subroutine_ok_mono (lscall_blk (callerProg := callerProg) hblk hcl hi (by decide) (by decide))
    (fun ⟨p1, k1, p2, k2, sp⟩ R s0 hp => by
      dsimp only [pqxdhCtEqMemSpec16] at hp
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp
      rcases hp with ⟨⟨hx0, hx1, hsp0, hk1, hk2, hm⟩, hspat⟩
      dsimp only [withMemEq, ctEqSliceMemSpec16]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hm, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hx0, hx1, hsp0, hk1, hk2⟩, hspat⟩)
    (fun _ _ _ _ hq => hq)

set_option maxHeartbeats 1600000 in
private theorem verifySig_seg2_1569_ext_placed [LibsignalPlacement]
    (P : SignalPqxdh.Primitives) (H : LibsignalHooks)
    (hmemcpyHook : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hshaHook : HookSat H lsSha512CompressSym
      (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128)))
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 1569) (_hst0 : st0.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 320#64) (hsp : s.sp = fsp)
    (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr) (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (m.drop 1472)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗
          ((fsp + 688#64) ↦ₛ bytesToBv8 (sha512CompressOutBytes P
            (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)) ((m.drop 64).take 1408))) ∗
          ((fsp + 752#64) ↦₆₄ 12#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗
          stackAt fsp pqxdhHookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hmemcpyHook
  have hshaRaw := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hshaHook
  have hsha1 := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    456#64 hshaRaw
  have hsha2 := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    512#64 hshaRaw
  dsimp only [compressInPlaceStubSpecPlaced, compressInPlaceStubSpec] at hsha1 hsha2
  clear hmemcpyHook hshaHook hshaRaw
  have hlen_m64_bv : (bytesToBv8 (m.take 64)).length = 64 := by simp [bytesToBv8, hm]
  have hlen_m1408 : ((m.drop 64).take 1408).length = 128 * 11 := by simp [hm]
  have hlen_m1408_bv : (bytesToBv8 ((m.drop 64).take 1408)).length = 1408 := by simp [bytesToBv8, hm]
  have hlen_m97_bv : (bytesToBv8 (m.drop 1472)).length = 97 := by simp [bytesToBv8, hm]
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_blk0 : (pre64 ++ m.take 64).length = 128 * 1 := by simp [hpre64, hm]
  have hlen_blk0_bv : (bytesToBv8 (pre64 ++ m.take 64)).length = 128 := by simp [bytesToBv8, hpre64, hm]
  have hst1_len : (sha512CompressOutBytes P st0 (pre64 ++ m.take 64)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  have hm_split : msgPtr ↦ₛ bytesToBv8 m =
      ((msgPtr ↦ₛ bytesToBv8 (m.take 64)) ∗ ((msgPtr + 64#64) ↦ₛ bytesToBv8 ((m.drop 64).take 1408)) ∗
       ((msgPtr + 1472#64) ↦ₛ bytesToBv8 (m.drop 1472))) := by
    have h1 : m = m.take 64 ++ ((m.drop 64).take 1408 ++ m.drop 1472) := by
      have ha : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
        rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
      rw [ha, List.take_append_drop]
    conv => lhs; rw [h1, bytesToBv8_append, bytesToBv8_append]
    rw [pointsToBytes_append, pointsToBytes_append, hlen_m64_bv, hlen_m1408_bv]
    rw [show BitVec.ofNat 64 64 = 64#64 from rfl, BitVec.add_assoc,
      show 64#64 + BitVec.ofNat 64 1408 = 1472#64 from rfl]
  have hbuf64_in : memRegion (fsp + 624#64) 63 ∗ ((fsp + 687#64) ↦₈ 64#8) ⊢
      memRegion (fsp + 624#64) (bytesToBv8 (m.take 64)).length := by
    rw [hlen_m64_bv, @ProofLib.memRegion_split' (fsp + 624#64) (fsp + 687#64) 63 1 64
      rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
    exact sepConj_mono_right (Entails.sepExists_intro 64#8)
  have hbuf128_weaken : ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) ⊢
      memRegion (fsp + 560#64) (bytesToBv8 (m.drop 1472)).length ∗ memRegion (fsp + 657#64) 30 ∗
      (∃∗ b687 : BitVec 8, (fsp + 687#64) ↦₈ b687) := by
    refine Entails.trans (Q := memRegion (fsp + 560#64) 128) ?_ (Entails.of_eq ?_)
    · rw [← hlen_blk0_bv]; exact pointsToBytes_entails_memRegion _ _
    · rw [hlen_m97_bv, @ProofLib.memRegion_split' (fsp + 560#64) (fsp + 657#64) 97 31 128
        rfl (by bv_omega) (by decide),
        @ProofLib.memRegion_split' (fsp + 657#64) (fsp + 687#64) 30 1 31
        rfl (by bv_omega) (by decide), ProofLib.memRegion_one]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf64_in) (by sep_frame)
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 (m.take 64)⟩
  have hmerge128 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 (m.take 64)) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m.take 64)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge128) (by sep_frame)
  wp_steps
  wp_call hsha1 ⟨fsp + 688#64, st0, fsp + 560#64, pre64 ++ m.take 64, 1⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf128_weaken) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hsha2 ⟨fsp + 688#64, sha512CompressOutBytes P st0 (pre64 ++ m.take 64), msgPtr + 64#64,
    (m.drop 64).take 1408, 11⟩
  rw [fitBv8_64_sha512CompressOutBytes]
  wp_steps
  wp_call hmemcpy ⟨fsp + 560#64, msgPtr + 1472#64, bytesToBv8 (m.drop 1472)⟩
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hm_split.symm) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by rw [hsp_sf_1, hsp_sf, hsp]; sep_ac_rfl), by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal⟩

set_option maxHeartbeats 1600000 in
private theorem verifySig_seg2_33_ext_placed [LibsignalPlacement]
    (H : LibsignalHooks) (hmemcpyHook : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (s : State) (fsp slicesPtr msgPtr : BitVec 64) (pre64 m st0 : Bytes) (Frame : SepProp)
    (hpre64 : pre64.length = 64) (hm : m.length = 33) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running) (hpc : s.pc = (blkPl_204).base + 320#64)
    (hsp : s.sp = fsp) (hx20 : s.readReg64 (.gpr 20#5) = slicesPtr)
    (hx21 : s.readReg64 (.gpr 21#5) = 1#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 548#64) s
      ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ memRegion (fsp + 624#64) 63 ∗
       ((fsp + 687#64) ↦₈ 64#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗ ((fsp + 752#64) ↦₆₄ 0#64) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) ∗ memRegion (fsp + 657#64) 30 ∗
          ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st0) ∗
          ((fsp + 752#64) ↦₆₄ 0#64) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗ stackAt fsp pqxdhHookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 548#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemcpy := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hmemcpyHook
  clear hmemcpyHook
  have hlen_pre_bv : (bytesToBv8 pre64).length = 64 := by simp [bytesToBv8, hpre64]
  have hlen_m_bv : (bytesToBv8 m).length = 33 := by simp [bytesToBv8, hm]
  have hbuf63_split : memRegion (fsp + 624#64) 63 =
      memRegion (fsp + 624#64) (bytesToBv8 m).length ∗ memRegion (fsp + 657#64) 30 := by
    rw [hlen_m_bv]; exact @ProofLib.memRegion_split' (fsp + 624#64) (fsp + 657#64) 33 30 63
      rfl (by bv_omega) (by decide)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf63_split) (by sep_frame)
  wp_steps
  wp_call hmemcpy ⟨fsp + 624#64, msgPtr, bytesToBv8 m⟩
  have hmerge97 :
      ((fsp + 560#64) ↦ₛ bytesToBv8 pre64) ∗ ((fsp + 624#64) ↦ₛ bytesToBv8 m) =
        ((fsp + 560#64) ↦ₛ bytesToBv8 (pre64 ++ m)) := by
    rw [bytesToBv8_append, pointsToBytes_append, hlen_pre_bv, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hmerge97) (by sep_frame)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
private theorem verifySig_seg3a_ext_placed_at [LibsignalPlacement]
    (hookStack : Nat) (P : SignalPqxdh.Primitives) (H : LibsignalHooks)
    (hmemsetHook : HookSat H lsVerifyMemsetSym (sessionMemsetSpec hookStack))
    (hshaHook : HookSat H lsSha512CompressSym
      (withLsRet (compressInPlaceStubSpecPlaced (sha512CompressOutBytes P) 64 128)))
    (hwideHook : HookSat H lsDalekScalarWideSym (withLsRet (dalekScalarWideExtSpec hookStack)))
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack ≤ 2 ^ 64)
    (s : State) (fsp : BitVec 64) (tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat)
    (Frame : SepProp) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 548#64) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64) (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 992#64) s
      (((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗ ((fsp + 752#64) ↦₆₄ blkCnt) ∗
       ((fsp + 760#64) ↦₆₄ 0#64) ∗ memRegion (fsp + 768#64) 32 ∗ cells (fsp + 800#64) 16 ∗
       cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗ stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗
          ((fsp + 768#64) ↦ₛ natToLeBytes 32 (leBytesToNat (bytesToBv8 (revWords64
            (sha512CompressOutBytes P st
              (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)))) % edOrderL)) ∗
          cells (fsp + 800#64) 16 ∗ cells (fsp + 928#64) 10 ∗ cells (fsp + 1008#64) 16 ∗
          stackAt fsp hookStack ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 992#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 23#5) = fsp + 800#64 ∧ sm.readReg64 (.gpr 29#5) = fsp + 1152#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmemset := ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hmemsetHook
  have hsha := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    808#64 (ls_hook_ok_any (prog := (blkPC_204).rebase (blkPl_204).base H) hshaHook)
  dsimp only [compressInPlaceStubSpecPlaced, compressInPlaceStubSpec] at hsha
  have hwide := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    992#64 (ls_hook_ok_any hwideHook (by set_option maxRecDepth 20000 in decide))
  dsimp only [dalekScalarWideExtSpec] at hwide; clear hmemsetHook hshaHook hwideHook
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, _p12, _p13, hp1, hp2, hp3⟩ :=
    exists_pad97_cells htail97
  have hst_bv : (bytesToBv8 st).length = 64 := by simp [bytesToBv8, hst]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, hw_st⟩ := exists_unpack64_of_length_64 hst_bv
  cells_pre_unfold_fast; wp_extract_exists
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hp1 (fsp + 560#64))) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hw_st (fsp + 688#64))) (by sep_frame)
  wp_simp_pre_fast [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  apply ProofLib.SepWP.replace_pre
    (hPQ := blockBuf_tail32_pack (fsp + 656#64) ((bytesToBv8 tail97).getD 96 0#8) 97#8) (by sep_frame)
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_left; intro b12; apply SepWP.exists_left; intro b13
  apply SepWP.exists_left; intro b14; apply SepWP.exists_left; intro b15
  apply SepWP.pure_elim; rintro ⟨hb12, hb15⟩
  wp_steps
  have hsp7 : ((fsp + 920#64) ↦₆₄ b15) =
      (((fsp + 920#64) ↦ₛ first7 b15) ∗ ((fsp + 927#64) ↦₈ 97#8)) := by
    rw [cell_split7 (fsp + 920#64) b15, hb15, BitVec.add_assoc]; rfl
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7) (by sep_frame)
  wp_steps
  have hunpack32 := blockBuf_tail32_unpack (fsp + 896#64) b12 b13 b14 b15
    ((bytesToBv8 tail97).getD 96 0#8) 97#8 hb12
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hunpack32
  apply ProofLib.SepWP.replace_pre (hPQ := hunpack32) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  wp_steps
  wp_call hmemset (fsp + 898#64, 0#8, 30)
  have hp2_896 := hp2 (fsp + 896#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp2_896
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp2_896) (by sep_frame)
  wp_steps
  have hbithi : rev64 (BitVec.truncate 64 ((0#64 ++ blkCnt) >>> 54)) = 0#64 := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hbitlo : rev64 (blkCnt <<< 10 ||| 776#64) = rev64 (BitVec.ofNat 64 (8 * L)) := by
    rcases hblkL with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hp3_1008 := hp3 (fsp + 1008#64) (hblkL.imp And.right And.right)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hp3_1008
  have hw_st_928 := (hw_st (fsp + 928#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hw_st_928
  wp_simp_pre_fast [hbithi, hbitlo, hsp_sf, hsp]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hw_st_928) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound))
    (by sep_frame)
  have hpad_len :
      (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L)).length = 128 := by
    simp [encodeBitLen128BE, encodeBitLen64BE, htail97]
  wp_call hsha ⟨fsp + 928#64, st, fsp + 1008#64, tail97 ++ [0x80] ++ List.replicate 14 0 ++
    encodeBitLen128BE L, 1⟩
  have hpad_norm :
      tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L) =
        tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L := by
    simp [List.append_assoc]
  wp_simp_pre_fast [fitBv8_64_sha512CompressOutBytes, hpad_norm, hsp_sf_1, hsp_sf, hsp]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound).symm)
    (by sep_frame)
  have hst_out_len :
      (sha512CompressOutBytes P st
        (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)).length = 64 :=
    sha512CompressOutBytes_length P _ _
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, hu_st, hu_rev⟩ :=
    exists_unpack64_revWords64_of_length_64 hst_out_len
  have hu_st_928 := hu_st (fsp + 928#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_st_928
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_st_928) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hp3_1008.symm) (by sep_frame)
  have hsp7_920 := cell_split7 (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L)))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsp7_920
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hsp7_920) (by sep_frame)
  wp_steps
  have hpk7_920 := first7_pack (fsp + 920#64) (rev64 (BitVec.ofNat 64 (8 * L))) 0#8
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hpk7_920
  apply ProofLib.SepWP.replace_pre (hPQ := hpk7_920) (by sep_frame)
  simp only [sepExists_sepConj_left]; apply SepWP.exists_left; intro _
  wp_steps
  have hu_rev_1008 := (hu_rev (fsp + 1008#64)).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hu_rev_1008
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008) (by sep_frame)
  have hrev_bv_len :
      (bytesToBv8 (revWords64 (sha512CompressOutBytes P st
        (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)))).length = 64 := by
    simp [bytesToBv8, revWords64_length (sha512CompressOutBytes_length P _ _)]
  have hrev_bv_len' :
      (bytesToBv8 (revWords64 (sha512CompressOutBytes P st
        (tail97 ++ 128 :: (List.replicate 14 0 ++ encodeBitLen128BE L))))).length = 64 := by
    simp [bytesToBv8, revWords64_length (sha512CompressOutBytes_length P _ _)]
  wp_call hwide ⟨fsp + 1008#64, bytesToBv8 (revWords64 (sha512CompressOutBytes P st
    (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L))), fsp + 768#64⟩
  wp_simp_pre_fast [hpad_norm, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hu_rev_1008.symm) (by sep_frame)
  have hm560 := cells_16_merge (fsp + 560#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm560
  apply ProofLib.SepWP.replace_pre (hPQ := hm560) (by sep_frame)
  have hm688 := cells_10_merge (fsp + 688#64) w0 w1 w2 w3 w4 w5 w6 w7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm688
  apply ProofLib.SepWP.replace_pre (hPQ := hm688) (by sep_frame)
  have hm800 := cells_16_merge (fsp + 800#64)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm800
  apply ProofLib.SepWP.replace_pre (hPQ := hm800) (by sep_frame)
  have hm928 := cells_10_merge (fsp + 928#64) u0 u1 u2 u3 u4 u5 u6 u7 blkCnt 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm928
  apply ProofLib.SepWP.replace_pre (hPQ := hm928) (by sep_frame)
  have hm1008 := cells_16_merge (fsp + 1008#64)
    (rev64 u0) (rev64 u1) (rev64 u2) (rev64 u3) (rev64 u4) (rev64 u5) (rev64 u6) (rev64 u7)
    0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm1008
  apply ProofLib.SepWP.replace_pre (hPQ := hm1008) (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
    by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩

set_option maxHeartbeats 2400000 in
private theorem verifySig_seg3b_ext_placed_at [LibsignalPlacement]
    (hookStack : Nat) (H : LibsignalHooks)
    (hmodHook : HookSat H lsDalekScalarModSym (withLsRet (dalekScalarModExtSpec hookStack)))
    (hdmulHook : HookSat H lsDalekDoubleMulSym (withLsRet (dalekDsmbExtSpec hookStack)))
    (hcompHook : HookSat H lsDalekCompressSym (withLsRet (dalekCompressExtSpec hookStack)))
    (hbb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat)
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack ≤ 2 ^ 64)
    (s : State) (fsp sigPtr : BitVec 64) (pk_bs ed_bs : List (BitVec 8)) (sign : Nat)
    (Apt : EdPoint) (sig shaOut : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmont : montToEdwards pk_bs sign = some Apt)
    (hed_bnd : fe51Point4Bounded ed_bs (2 ^ 52)) (hed_eq : edExtOfBytes ed_bs = edExtOfAffine Apt)
    (hsig : sig.length = 64) (hfsp_align : fsp &&& 15#64 == 0#64)
    (hrun : s.status = ExecStatus.Running) (hpc : s.pc = (blkPl_204).base + 992#64)
    (hsp : s.sp = fsp) (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64)
    (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) ((blkPl_204).base + 1100#64) s
      (((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗
       ((fsp + 768#64) ↦ₛ natToLeBytes 32 (leBytesToNat (bytesToBv8 shaOut) % edOrderL)) ∗
       cells (fsp + 800#64) 4 ∗ memRegion (fsp + 832#64) 128 ∗ memRegion (fsp + 1008#64) 32 ∗
       stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
          ((fsp + 8#64) ↦₆₄ sigPtr) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗
          ((fsp + 768#64) ↦ₛ natToLeBytes 32 (leBytesToNat (bytesToBv8 shaOut) % edOrderL)) ∗
          memRegion (fsp + 800#64) 160 ∗ memRegion (fsp + 1008#64) 32 ∗ stackAt fsp hookStack ∗
          Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = (blkPl_204).base + 1100#64 ∧ sm.sp = fsp ∧
        sm.readReg64 (.gpr 0#5) =
          (let sClamped := (sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]
           let hNat := leBytesToNat (bytesToBv8 shaOut) % edOrderL
           let sNat := leBytesToNat (bytesToBv8 sClamped) % edOrderL
           let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
           if (capRCheck == sig.take 32) = true then 1#64 else 0#64) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hmod := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    1032#64 (ls_hook_ok_any hmodHook (by set_option maxRecDepth 20000 in decide))
  have hdmul := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    1052#64 (ls_hook_ok_any hdmulHook (by set_option maxRecDepth 20000 in decide))
  have hcomp := subroutine_ok_strip_withLsRet_204 (prog := (blkPC_204).rebase (blkPl_204).base H)
    1064#64 (ls_hook_ok_any hcompHook (by set_option maxRecDepth 20000 in decide))
  dsimp only [dalekScalarModExtSpec] at hmod
  dsimp only [dalekDsmbExtSpec] at hdmul
  dsimp only [dalekCompressExtSpec] at hcomp
  clear hmodHook hdmulHook hcompHook
  apply sepWP_seq_lscl hcl (mid := (blkPl_204).base + 1072#64)
  obtain ⟨q0_lo, q0_hi, q1_lo, q1_hi, hsig_q0, hsig_q1, hbuf_q0, hbuf_q1⟩ :=
    exists_sig_capS_cells hsig
  cells_pre_unfold_fast; wp_extract_exists; rename_i v0 v1 v2 v3
  have hsbuf := sClamped_buf_pre (fsp + 800#64) v0 v1 v2 v3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hsbuf
  apply ProofLib.SepWP.replace_pre (hPQ := hsbuf) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q0 sigPtr)) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq ((hsig_q0 sigPtr).symm.trans (hsig_q1 sigPtr))) (by sep_frame)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (hsig_q1 sigPtr).symm) (by sep_frame)
  have hbuf0 := hbuf_q0 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf0
  apply ProofLib.SepWP.replace_pre (hPQ := hbuf0) (by sep_frame)
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_left; intro _; apply SepWP.exists_left; intro _
  wp_steps
  wp_simp_pre_fast [truncate8_zeroExtend32_and7f]
  have hbuf1 := hbuf_q1 (fsp + 800#64)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hbuf1
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hbuf1) (by sep_frame)
  have hsClamped_bv_len :
      (bytesToBv8 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F])).length = 32 := by
    simp [bytesToBv8, hsig]
  have hsClamped_bv_len' :
      (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
        [(List.drop 32 sig).getD 31 0 &&& 127])).length = 32 := by
    simp [bytesToBv8, hsig]
  wp_call hmod ⟨fsp + 800#64,
    bytesToBv8 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]), fsp + 1008#64⟩
  wp_simp_pre_fast [hsp_sf, hsp]
  wp_steps
  have hm160 := pointsToBytes_32_merge_128 (fsp + 800#64) _ hsClamped_bv_len'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm160
  apply ProofLib.SepWP.replace_pre (hPQ := hm160) (by sep_frame)
  have hh_len : (natToLeBytes 32 (leBytesToNat (bytesToBv8 shaOut) % edOrderL)).length = 32 :=
    natToLeBytes_len 32 _
  have hneg_len : (dalekEdNegBytes ed_bs).length = 160 := dalekEdNegBytes_length ed_bs
  have hneg_bnd : fe51Point4Bounded (dalekEdNegBytes ed_bs) (2 ^ 52) := dalekEdNegBytes_bounded hed_bnd
  have hs_len : (natToLeBytes 32 (leBytesToNat (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
      [(List.drop 32 sig).getD 31 0 &&& 127])) % edOrderL)).length = 32 := natToLeBytes_len 32 _
  wp_call hdmul ⟨fsp + 768#64, natToLeBytes 32 (leBytesToNat (bytesToBv8 shaOut) % edOrderL),
    fsp + 400#64, dalekEdNegBytes ed_bs,
    fsp + 1008#64, natToLeBytes 32 (leBytesToNat (bytesToBv8 (List.take 31 (List.drop 32 sig) ++
      [(List.drop 32 sig).getD 31 0 &&& 127])) % edOrderL),
    fsp + 800#64⟩
  have hres_len : w.length = 160 := by assumption
  have hres_bnd : fe51Point4Bounded w (2 ^ 52) := by assumption
  wp_simp_pre_fast [hsp_sf_1, hsp_sf, hsp]
  wp_steps
  apply ProofLib.SepWP.replace_pre
    (hPQ := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hs_len) (by sep_frame)
  wp_call hcomp ⟨fsp + 800#64, w, fsp + 1008#64⟩
  have hedL_pos : 0 < edOrderL := by unfold edOrderL; decide
  have hedL_lt : edOrderL < 256 ^ 32 := by unfold edOrderL; decide
  have hh_nat : leBytesToNat (natToLeBytes 32 (leBytesToNat (bytesToBv8 shaOut) % edOrderL)) =
      leBytesToNat (bytesToBv8 shaOut) % edOrderL :=
    leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans (Nat.mod_lt _ hedL_pos) hedL_lt)
  have hs_nat : leBytesToNat (natToLeBytes 32 (leBytesToNat (bytesToBv8
      (List.take 31 (List.drop 32 sig) ++ [(List.drop 32 sig).getD 31 0 &&& 127])) % edOrderL)) =
      leBytesToNat (bytesToBv8
        ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F])) % edOrderL :=
    leBytesToNat_natToLeBytes_of_lt (Nat.lt_trans (Nat.mod_lt _ hedL_pos) hedL_lt)
  have hcapR_eq : encodeEd (edExtToAffine (edExtOfBytes w)) =
      bytesToBv8 (toU8 (encodeEd (edSub
        (edSmul (leBytesToNat (bytesToBv8
          ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F])) % edOrderL) edBasepoint)
        (edSmul (leBytesToNat (bytesToBv8 shaOut) % edOrderL) Apt)))) := by
    rw [bytesToBv8_toU8, hpost_1, pipeline2_xeddsa_verify_compress_eq hmont hed_bnd hed_eq hh_len
      (by rw [hh_nat]; exact Nat.mod_lt _ hedL_pos) hs_len
      (by rw [hs_nat]; exact Nat.mod_lt _ hedL_pos), hh_nat, hs_nat]
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (congrArg ((fsp + 1008#64) ↦ₛ ·) hcapR_eq)) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl_call
  have hcteq := pqxdhCtEq_call_ok_sat (callerProg := (blkPC_204).rebase (blkPl_204).base H)
    hbb hcl_call
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig)) (by sep_frame)
  have hstk64 : stackAt fsp hookStack =
      memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - 64) ∗ memRegion (fsp - 64#64) 64 :=
    stackAt_split_low fsp (Nat.le_trans (by decide : 64 ≤ pqxdhHookStack) hle) hbound
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hstk64) (by sep_frame)
  let capRCheck : Bytes := toU8 (encodeEd (edSub
    (edSmul (leBytesToNat (bytesToBv8
      ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F])) % edOrderL) edBasepoint)
    (edSmul (leBytesToNat (bytesToBv8 shaOut) % edOrderL) Apt)))
  have hcapR_bv_len : (bytesToBv8 capRCheck).length = 32 := by simp [capRCheck, bytesToBv8, toU8]
  have hsig32_bv_len : (bytesToBv8 (sig.take 32)).length = 32 := by simp [bytesToBv8, hsig]
  wp_call hcteq (fsp + 1008#64, bytesToBv8 capRCheck, sigPtr, bytesToBv8 (sig.take 32), fsp)
  wp_steps
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (sig_split_32 sigPtr hsig).symm)
    (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq hstk64.symm) (by sep_frame)
  apply ProofLib.SepWP.replace_pre
    (hPQ := pointsToBytes_entails_memRegion_n (fsp + 800#64) _ hres_len) (by sep_frame)
  apply ProofLib.SepWP.replace_pre
    (hPQ := pointsToBytes_entails_memRegion_n (fsp + 1008#64) _ hcapR_bv_len) (by sep_frame)
  wp_simp_pre_fast [hsp_sf_3, hsp_sf_2, hsp_sf_1, hsp_sf, hsp]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine ⟨Entails.of_eq (by sep_ac_rfl), by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, ?_,
    by wp_norm_goal, by wp_norm_goal⟩
  wp_norm_goal
  exact x0_cteq_simplify capRCheck (sig.take 32)

set_option maxHeartbeats 1600000 in
private theorem verifySig_tail_from_548_ext_placed_at [LibsignalPlacement]
    (hookStack : Nat) (P : SignalPqxdh.Primitives) (H : LibsignalHooks)
    (hH : VerifySignatureExtHooks hookStack P H)
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (s : State) (fsp sigPtr retAddr : BitVec 64)
    (x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 : BitVec 64)
    (pk_bs ed_bs : List (BitVec 8)) (sign : Nat) (Apt : EdPoint)
    (m sig tail97 st : Bytes) (blkCnt : BitVec 64) (L : Nat) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hmont : montToEdwards pk_bs sign = some Apt)
    (hed_bnd : fe51Point4Bounded ed_bs (2 ^ 52)) (hed_eq : edExtOfBytes ed_bs = edExtOfAffine Apt)
    (hsig : sig.length = 64) (htail97 : tail97.length = 97) (hst : st.length = 64)
    (hblkL : (blkCnt = 0#64 ∧ L = 97) ∨ (blkCnt = 12#64 ∧ L = 1633))
    (hsha_eq : revWords64 (sha512CompressOutBytes P st
      (tail97 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE L)) =
        P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m))
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base + 548#64) (hsp : s.sp = fsp)
    (hx23 : s.readReg64 (.gpr 23#5) = fsp + 800#64) (hx29 : s.readReg64 (.gpr 29#5) = fsp + 1152#64) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
      (memRegion fsp 4 ∗
       ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
       ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
       memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
       ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗
       ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗
       ((fsp + 560#64) ↦ₛ bytesToBv8 tail97) ∗ memRegion (fsp + 657#64) 30 ∗
       ((fsp + 687#64) ↦₈ 97#8) ∗ ((fsp + 688#64) ↦ₛ bytesToBv8 st) ∗
       ((fsp + 752#64) ↦₆₄ blkCnt) ∗ ((fsp + 760#64) ↦₆₄ 0#64) ∗
       memRegion (fsp + 768#64) 32 ∗ memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ∗
       ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
       ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
       ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
       ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
       ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
       ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt fsp hookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) =
          (let capA := toU8 (encodeEd Apt)
           let capR := sig.take 32
           let sRaw := sig.drop 32
           let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
           let hNat := leBytesToNat (bytesToBv8 (P.sha512 (capR ++ capA ++ m))) % edOrderL
           let sNat := leBytesToNat (bytesToBv8 sClamped) % edOrderL
           let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
           if (capRCheck == capR) = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = x19_0 ∧ sm.readReg64 (.gpr 20#5) = x20_0 ∧
        sm.readReg64 (.gpr 21#5) = x21_0 ∧ sm.readReg64 (.gpr 22#5) = x22_0 ∧
        sm.readReg64 (.gpr 23#5) = x23_0 ∧ sm.readReg64 (.gpr 24#5) = x24_0 ∧
        sm.readReg64 (.gpr 25#5) = x25_0 ∧ sm.readReg64 (.gpr 26#5) = x26_0 ∧
        sm.readReg64 (.gpr 27#5) = x27_0 ∧ sm.readReg64 (.gpr 28#5) = x28_0 ∧
        sm.readReg64 (.gpr 29#5) = x29_0 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hbound0 : hookStack ≤ 2 ^ 64 := by omega
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (memRegion_800_seg3a_split fsp))
    (by sep_frame)
  apply verifySig_seq_seg_lscl hcl (verifySig_seg3a_ext_placed_at hookStack P H
    hH.memset hH.sha512Compress hH.scalarWide hle hbound0 s fsp tail97 st blkCnt L
    (memRegion fsp 4 ∗
     ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
     ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗
     memRegion (fsp + 48#64) 160 ∗ memRegion (fsp + 208#64) 160 ∗
     ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗
     ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗ memRegion (fsp + 1136#64) 16 ∗
     ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
     ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
     ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
     ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
     ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
     ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗
     (sigPtr ↦ₛ bytesToBv8 sig) ∗ Frame)
    htail97 hst hblkL hfsp_align hrun hpc hsp hx23 hx29)
    (Entails.of_eq (by sep_ac_rfl))
  intro s1 hpc1 hrun1 hcl1 ⟨_, _, hsp1, hx23_1, hx29_1, hv1, htr1⟩
  rw [hsha_eq]
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (seg3a_to_seg3b_split fsp)) (by sep_frame)
  apply verifySig_seq_seg (verifySig_seg3b_ext_placed_at hookStack H
    hH.scalarMod hH.doubleMul hH.compress hH.blackBox hle hbound0 s1 fsp sigPtr
    pk_bs ed_bs sign Apt sig (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m))
    (memRegion fsp 4 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
     memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗
     cells (fsp + 560#64) 16 ∗ cells (fsp + 688#64) 10 ∗ memRegion (fsp + 960#64) 48 ∗
     memRegion (fsp + 1040#64) 96 ∗ memRegion (fsp + 1136#64) 16 ∗
     ((fsp + 1152#64) ↦₆₄ x29_0) ∗ ((fsp + 1160#64) ↦₆₄ retAddr) ∗
     ((fsp + 1168#64) ↦₆₄ x28_0) ∗ ((fsp + 1176#64) ↦₆₄ x27_0) ∗
     ((fsp + 1184#64) ↦₆₄ x26_0) ∗ ((fsp + 1192#64) ↦₆₄ x25_0) ∗
     ((fsp + 1200#64) ↦₆₄ x24_0) ∗ ((fsp + 1208#64) ↦₆₄ x23_0) ∗
     ((fsp + 1216#64) ↦₆₄ x22_0) ∗ ((fsp + 1224#64) ↦₆₄ x21_0) ∗
     ((fsp + 1232#64) ↦₆₄ x20_0) ∗ ((fsp + 1240#64) ↦₆₄ x19_0) ∗ Frame)
    hcl1 hmont hed_bnd hed_eq hsig hfsp_align hrun1 hpc1 hsp1 hx23_1 hx29_1)
    (Entails.of_eq (by sep_ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, hv2, htr2⟩
  have hcapA_bv : (bytesToBv8 (toU8 (encodeEd Apt))).length = 32 := by simp [bytesToBv8, toU8]
  apply ProofLib.SepWP.replace_pre
    (hPQ := seg3b_to_epilogue_merge_bv fsp
      (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32) sigPtr
      hcapA_bv (dalekEdNegBytes_length ed_bs) (natToLeBytes_len 32 _)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0)) (by sep_frame)
  apply verifySig_end_seg (verifySig_epilogue_placed H s2 fsp retAddr (s2.readReg64 (.gpr 0#5))
    x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
    ((sigPtr ↦ₛ bytesToBv8 sig) ∗
      memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
    hfsp_align hrun2 hpc2 hsp2 rfl)
    (Entails.of_eq (by sep_ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3, htr3⟩
  have hP3' : P3 ⊢ (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame := by
    rw [stackAt_1248_split_low fsp hle hbound]
    exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))
  exact ⟨hP3', hrun3, hpc3, hsp3, hx0_3.trans hx0_2,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
    hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩

/-! ## 4. Public Block `204` & `203` Theorems & Corollaries -/

private theorem verifySig_stackAt_1248_ext_split (fsp : BitVec 64) {hookStack : Nat}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64) :
    stackAt (fsp + 1248#64) (hookStack + 1248) =
      stackAt fsp hookStack ∗ memRegion fsp 1152 ∗ cells (fsp + 1152#64) 12 := by
  rw [stackAt_1248_split_low fsp hle hbound, verifySig_stackAt_1248_split fsp,
    stackAt_split_low fsp hle (by omega)]; sep_ac_rfl

private theorem verifySig_stackAt_1280_ext_split (fsp : BitVec 64) {hookStack : Nat}
    (hbound : hookStack + 1280 ≤ 2 ^ 64) :
    stackAt (fsp + 1280#64) (hookStack + 1280) =
      stackAt (fsp + 1248#64) (hookStack + 1248) ∗ cells (fsp + 1248#64) 4 := by
  have h1 : fsp + 1280#64 - BitVec.ofNat 64 (8 * 4) = fsp + 1248#64 := by
    change fsp + 1280#64 - 32#64 = fsp + 1248#64; bv_omega
  have h2 : hookStack + 1280 = (hookStack + 1248) + 8 * 4 := by omega
  rw [h2, ProofLib.stackAt_split_cells (fsp + 1280#64) (hookStack + 1248) 4 hbound, h1]

private theorem xeddsaVerifyRef_of_montToEd_none_ext (P : SignalPqxdh.Primitives)
    (hcurve : XeddsaCurveSound P) {pk : Bytes} (m : Bytes) {sig : Bytes}
    (hpk : pk.length = 32) (hsig : sig.length = 64)
    (hmont : montToEdwards (bytesToBv8 pk) (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) = none) :
    SignalPqxdh.xeddsaVerifyRef P pk m sig = false := by
  cases h60 : (sig.getD 63 0 &&& 0x60 == 0) with
  | false => exact verifySig_xeddsaVerifyRef_of_60_false P h60
  | true => rw [hcurve.xeddsaVerifyRef_eq pk m sig hpk hsig h60, ← bytesToBv8_eq_ofU8 pk, hmont]

private theorem xeddsaVerifyRef_eq_capRCheck_of_some (P : SignalPqxdh.Primitives)
    (hcurve : XeddsaCurveSound P) {pk m sig : Bytes} {Apt : EdPoint}
    (hpk : pk.length = 32) (hsig : sig.length = 64)
    (h60 : (sig.getD 63 0 &&& 0x60 == 0) = true)
    (hmont : montToEdwards (bytesToBv8 pk) (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) = some Apt)
    (hsha64 : (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m)).length = 64) :
    (let capA := toU8 (encodeEd Apt)
     let capR := sig.take 32
     let sRaw := sig.drop 32
     let sClamped := sRaw.take 31 ++ [sRaw.getD 31 0 &&& 0x7F]
     let hNat := leBytesToNat (bytesToBv8 (P.sha512 (capR ++ capA ++ m))) % edOrderL
     let sNat := leBytesToNat (bytesToBv8 sClamped) % edOrderL
     let capRCheck := toU8 (encodeEd (edSub (edSmul sNat edBasepoint) (edSmul hNat Apt)))
     if (capRCheck == capR) = true then (1#64 : BitVec 64) else 0#64) =
      (if SignalPqxdh.xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) := by
  have hs32 : ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]).length = 32 := by
    simp [hsig]
  have hh_vec : (u8Vec 64 (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m))).toList =
      bytesToBv8 (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m)) := by
    rw [u8Vec_toList_of_length hsha64, bytesToBv8_eq_ofU8]
  have hs_vec : (u8Vec 32 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F])).toList =
      bytesToBv8 ((sig.drop 32).take 31 ++ [(sig.drop 32).getD 31 0 &&& 0x7F]) := by
    rw [u8Vec_toList_of_length hs32, bytesToBv8_eq_ofU8]
  rw [hcurve.xeddsaVerifyRef_eq pk m sig hpk hsig h60, ← bytesToBv8_eq_ofU8 pk, hmont]
  change _ = (if (toU8 (encodeEd (edSub
    (edSmul (leBytesToNat (u8Vec 32 ((sig.drop 32).take 31 ++
      [(sig.drop 32).getD 31 0 &&& 0x7F])).toList % edOrderL) edBasepoint)
    (edSmul (leBytesToNat (u8Vec 64 (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m))).toList %
      edOrderL) Apt))) == sig.take 32) = true then (1#64 : BitVec 64) else 0#64)
  rw [hh_vec, hs_vec]

set_option maxHeartbeats 2400000 in
/-- End-to-end `SepWP` theorem for Block `204` (`verify_signature_for_multipart_message`)
against extended-Edwards hooks `VerifySignatureExtHooks hookStack P H`. -/
theorem verifySignatureMultipart_ext_sepWP_placed_at [LibsignalPlacement]
    (hookStack : Nat) (P : SignalPqxdh.Primitives) (H : LibsignalHooks)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (s : State) (fsp pkPtr slicesPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32) (hm : m.length = 33 ∨ m.length = 1569) (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_204).base) (hsp : s.sp = fsp + 1248#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr) (hx1 : s.readReg64 (.gpr 1#5) = slicesPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = 1#64) (hx3 : s.readReg64 (.gpr 3#5) = sigPtr)
    (hx4 : s.readReg64 (.gpr 4#5) = 64#64) (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_204).rebase (blkPl_204).base H) retAddr s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
          ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1248#64 ∧
        sm.readReg64 (.gpr 0#5) =
          (if SignalPqxdh.xeddsaVerifyRef P pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hbound0 : hookStack ≤ 2 ^ 64 := by omega
  let x19_0 := s.readReg64 (.gpr 19#5); let x20_0 := s.readReg64 (.gpr 20#5)
  let x21_0 := s.readReg64 (.gpr 21#5); let x22_0 := s.readReg64 (.gpr 22#5)
  let x23_0 := s.readReg64 (.gpr 23#5); let x24_0 := s.readReg64 (.gpr 24#5)
  let x25_0 := s.readReg64 (.gpr 25#5); let x26_0 := s.readReg64 (.gpr 26#5)
  let x27_0 := s.readReg64 (.gpr 27#5); let x28_0 := s.readReg64 (.gpr 28#5)
  let x29_0 := s.readReg64 (.gpr 29#5)
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (verifySig_stackAt_1248_ext_split fsp hle hbound)) (by sep_frame)
  apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_memRegion_1152_seg1a_split fsp))
    (by sep_frame)
  apply verifySig_seq_seg_lscro ⟨hcl, hro⟩ (verifySig_seg1a_ext_placed_at hookStack H hH.montToEd
    s fsp pkPtr slicesPtr sigPtr retAddr pk sig
    ((slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
     (msgPtr ↦ₛ bytesToBv8 m) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 48#64) 752 ∗
     memRegion (fsp + 968#64) 184 ∗ Frame)
    hpk hsig hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by sep_ac_rfl))
  intro s1 hpc1 hrun1 ⟨hcl1, hro1⟩ ⟨_, _, hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx29_1, hv1, htr1⟩
  cases hmont : montToEdwards (bytesToBv8 pk) (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) with
  | none =>
    have hxed := xeddsaVerifyRef_of_montToEd_none_ext P hcurve m hpk hsig hmont
    apply verifySig_seq_seg (verifySig_seg1a_none_ext_placed H s1 fsp (bytesToBv8 pk)
      (((sig.getD 63 0 &&& 0x80) >>> 7).toNat)
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 752 ∗
       memRegion (fsp + 968#64) 184 ∗
       savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
       stackAt fsp hookStack ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hmont hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by sep_ac_rfl))
    intro s2 hpc2 hrun2 ⟨_, _, hsp2, hv2, htr2⟩
    apply ProofLib.SepWP.replace_pre (hPQ := verifySig_memRegion_1152_seg1a_merge fsp) (by sep_frame)
    apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0))
      (by sep_frame)
    apply verifySig_end_seg (verifySig_epilogue_false_placed H s2 fsp retAddr
      x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
       ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
       (sigPtr ↦ₛ bytesToBv8 sig) ∗
       memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
      hfsp_align hrun2 hpc2 hsp2)
      (Entails.of_eq (by sep_ac_rfl))
    intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
      h29, hv3, htr3⟩
    rw [hxed]
    have hP3' : P3 ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
        ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
        (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame := by
      rw [stackAt_1248_split_low fsp hle hbound]
      exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))
    exact ⟨hP3', hrun3, hpc3, hsp3, hx0_3, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
      hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩
  | some Apt =>
    have hApt_on : edOnCurve Apt = true := montToEdwards_some_onCurve hmont
    have hcapA_len : (toU8 (encodeEd Apt)).length = 32 := by unfold toU8; simp
    apply ProofLib.SepWP.replace_pre
      (hPQ := Entails.of_eq (dalekMontToEdExtOutAt_some (fsp + 800#64) (bytesToBv8 pk)
        (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) Apt hmont)) (by sep_frame)
    simp only [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_left; intro ed_bs
    apply SepWP.pure_elim; rintro ⟨hed_len, hed_bnd, hed_eq⟩
    apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (verifySig_memRegion_752_seg1b_split fsp))
      (by sep_frame)
    apply verifySig_seq_seg_lscro ⟨hcl1, hro1⟩ (verifySig_seg1b_ext_placed_at hookStack H hH.compress
      s1 fsp ed_bs Apt
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗ (fsp ↦₆₄ 0#64) ∗
       memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 400#64) 400 ∗
       memRegion (fsp + 968#64) 184 ∗
       savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
       (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
       (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
      hed_len hed_bnd hed_eq hApt_on hfsp_align hrun1 hpc1 hsp1)
      (Entails.of_eq (by sep_ac_rfl))
    intro s2 hpc2 hrun2 ⟨hcl2, hro2⟩ ⟨_, _, hsp2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx29_2,
      hv2, htr2⟩
    have hx19_s2 : s2.readReg64 (.gpr 19#5) = sigPtr := hx19_2.trans hx19_1
    have hx20_s2 : s2.readReg64 (.gpr 20#5) = slicesPtr := hx20_2.trans hx20_1
    have hx21_s2 : s2.readReg64 (.gpr 21#5) = 1#64 := hx21_2.trans hx21_1
    have hx22_s2 : s2.readReg64 (.gpr 22#5) = BitVec.zeroExtend 64 (sig.getD 63 0).toBitVec := by
      rw [hx22_2, hx22_1, bytesToBv8_getD_eq sig 63]
      generalize sig.getD 63 0 = b; rcases b with ⟨bv⟩; revert bv; decide
    have hx29_s2 : s2.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_2.trans hx29_1
    cases h60 : (sig.getD 63 0 &&& 0x60 == 0) with
    | false =>
      have hxed : SignalPqxdh.xeddsaVerifyRef P pk m sig = false :=
        verifySig_xeddsaVerifyRef_of_60_false P h60
      apply verifySig_seq_seg (verifySig_seg1c_invalid_placed H s2 sig
        (memRegion (fsp + 48#64) 160 ∗ ((fsp + 208#64) ↦ₛ ed_bs) ∗
         ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗ memRegion (fsp + 800#64) 168 ∗
         stackAt fsp hookStack ∗ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
         (fsp ↦₆₄ 0#64) ∗ memRegion (fsp + 8#64) 8 ∗ memRegion (fsp + 16#64) 32 ∗
         memRegion (fsp + 400#64) 400 ∗ memRegion (fsp + 968#64) 184 ∗
         savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
         (slicesPtr ↦₆₄ msgPtr) ∗ ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗
         (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        h60 hrun2 hpc2 hx22_s2)
        (Entails.of_eq (by sep_ac_rfl))
      intro s3 hpc3 hrun3 ⟨_, _, hsp3, hv3, htr3⟩
      have hsp3_eq : s3.sp = fsp := hsp3.trans hsp2
      have hed_u8_len : (toU8 ed_bs).length = 160 := by unfold toU8; simp [hed_len]
      apply ProofLib.SepWP.replace_pre
        (hPQ := Entails.of_eq (congrArg ((fsp + 208#64) ↦ₛ ·) (bytesToBv8_toU8 ed_bs).symm))
        (by sep_frame)
      apply ProofLib.SepWP.replace_pre
        (hPQ := verifySig_memRegion_752_seg1b_merge fsp hed_u8_len hcapA_len) (by sep_frame)
      apply ProofLib.SepWP.replace_pre (hPQ := verifySig_memRegion_1152_seg1a_merge fsp)
        (by sep_frame)
      apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0))
        (by sep_frame)
      apply verifySig_end_seg (verifySig_epilogue_false_placed H s3 fsp retAddr
        x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
        ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
         (sigPtr ↦ₛ bytesToBv8 sig) ∗
         memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
        hfsp_align hrun3 hpc3 hsp3_eq)
        (Entails.of_eq (by sep_ac_rfl))
      intro s4 P4 hP4 ⟨hrun4, hpc4, hsp4, hx0_4, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
        h29, hv4, htr4⟩
      rw [hxed]
      have hP4' : P4 ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
          ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
          (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame := by
        rw [stackAt_1248_split_low fsp hle hbound]
        exact Entails.trans hP4 (Entails.of_eq (by sep_ac_rfl))
      exact ⟨hP4', hrun4, hpc4, hsp4, hx0_4, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
        hv4.trans (hv3.trans (hv2.trans hv1)), htr4.trans (htr3.trans (htr2.trans htr1))⟩
    | true =>
      apply ProofLib.SepWP.replace_pre (hPQ := verifySig_seg1b_to_seg1c_split fsp) (by sep_frame)
      apply verifySig_seq_seg_lscl hcl2 (verifySig_seg1c_ext_placed_at hookStack H hH.edNeg
        s2 fsp sigPtr ed_bs (toU8 (encodeEd Apt)) sig
        (memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
         memRegion (fsp + 624#64) 63 ∗ memRegion (fsp + 768#64) 32 ∗
         memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ∗
         savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
         (pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
         ((slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 m.length) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
        hro2 hed_len hcapA_len hsig h60 hfsp_align hrun2 hpc2 hsp2 hx19_s2 hx22_s2)
        (Entails.of_eq (by sep_ac_rfl))
      intro s3 hpc3 hrun3 hcl3 ⟨_, _, hsp3, hx20_3, hx21_3, hx23_3, hx29_3, hv3, htr3⟩
      have hx20_s3 : s3.readReg64 (.gpr 20#5) = slicesPtr := hx20_3.trans hx20_s2
      have hx21_s3 : s3.readReg64 (.gpr 21#5) = 1#64 := hx21_3.trans hx21_s2
      have hx23_s3 : s3.readReg64 (.gpr 23#5) = fsp + 800#64 := hx23_3.trans hx23_2
      have hx29_s3 : s3.readReg64 (.gpr 29#5) = fsp + 1152#64 := hx29_3.trans hx29_s2
      have hpre64 : (sig.take 32 ++ toU8 (encodeEd Apt)).length = 64 := by simp [hsig, hcapA_len]
      have hshaIV : sha512IVBytesLE = bytesToBv8 (revWords64 sha512InitState) := rfl
      have hst0 : (revWords64 sha512InitState).length = 64 := revWords64_length (by decide)
      rw [hshaIV]
      apply ProofLib.SepWP.replace_pre (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0))
        (by sep_frame)
      rcases hm with hm33 | hm1569
      · rw [hm33, show BitVec.ofNat 64 33 = 33#64 from rfl]
        apply verifySig_seq_seg_lscl hcl3 (verifySig_seg2_33_ext_placed H hH.memcpy
          s3 fsp slicesPtr msgPtr (sig.take 32 ++ toU8 (encodeEd Apt)) m (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
           memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗
           ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗ memRegion (fsp + 768#64) 32 ∗
           memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ∗
           savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
           memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
          hpre64 hm33 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by sep_ac_rfl))
        intro s4 hpc4 hrun4 hcl4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        apply ProofLib.SepWP.replace_pre
          (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0).symm) (by sep_frame)
        have htail97 : ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m).length = 97 := by
          simp [hsig, hcapA_len, hm33]
        have hsha_eq : revWords64 (sha512CompressOutBytes P (revWords64 sha512InitState)
            (((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m) ++ [0x80] ++ List.replicate 14 0 ++
            encodeBitLen128BE 97)) =
            P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m) := by
          rw [hcurve.sha512_eq, sha512Ref_of_length_97 P htail97]
        have hsha64 : (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m)).length = 64 := by
          rw [← hsha_eq]; exact revWords64_length (sha512CompressOutBytes_length P _ _)
        have hxed_eq := xeddsaVerifyRef_eq_capRCheck_of_some P hcurve hpk hsig h60 hmont hsha64
        apply verifySig_end_seg (verifySig_tail_from_548_ext_placed_at hookStack P H hH hle hbound
          s4 fsp sigPtr retAddr x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
          (bytesToBv8 pk) ed_bs (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) Apt m sig
          ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m) (revWords64 sha512InitState) 0#64 97
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 33#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hcl4 hmont hed_bnd hed_eq hsig htail97 hst0 (Or.inl ⟨rfl, rfl⟩)
          hsha_eq hfsp_align hrun4 hpc4 hsp4 (hx23_4.trans hx23_s3) (hx29_4.trans hx29_s3))
          (Entails.of_eq (by sep_ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by sep_ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩
      · rw [hm1569, show BitVec.ofNat 64 1569 = 1569#64 from rfl]
        apply verifySig_seq_seg_lscl hcl3 (verifySig_seg2_1569_ext_placed P H hH.memcpy
          hH.sha512Compress s3 fsp slicesPtr msgPtr (sig.take 32 ++ toU8 (encodeEd Apt)) m
          (revWords64 sha512InitState)
          (memRegion fsp 4 ∗
           ((fsp + 4#64) ↦₃₂ (BitVec.zeroExtend 32 ((bytesToBv8 sig).getD 63 0#8) &&& 0x7f#32)) ∗
           ((fsp + 8#64) ↦₆₄ sigPtr) ∗ memRegion (fsp + 16#64) 32 ∗ memRegion (fsp + 48#64) 160 ∗
           memRegion (fsp + 208#64) 160 ∗ ((fsp + 368#64) ↦ₛ bytesToBv8 (toU8 (encodeEd Apt))) ∗
           ((fsp + 400#64) ↦ₛ dalekEdNegBytes ed_bs) ∗ memRegion (fsp + 768#64) 32 ∗
           memRegion (fsp + 800#64) 168 ∗ memRegion (fsp + 968#64) 184 ∗
           savedRegs12 fsp x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0 retAddr ∗
           (pkPtr ↦ₛ bytesToBv8 pk) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
           memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
          hpre64 hm1569 hst0 hfsp_align hrun3 hpc3 hsp3 hx20_s3 hx21_s3)
          (Entails.of_eq (by sep_ac_rfl))
        intro s4 hpc4 hrun4 hcl4 ⟨_, _, hsp4, hx23_4, hx29_4, hv4, htr4⟩
        apply ProofLib.SepWP.replace_pre
          (hPQ := Entails.of_eq (stackAt_split_low fsp hle hbound0).symm) (by sep_frame)
        have hblk0 : ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m.take 64).length = 128 := by
          simp [hsig, hcapA_len, hm1569]
        have hblks11 : ((m.drop 64).take 1408).length = 1408 := by simp [hm1569]
        have htail97 : (m.drop 1472).length = 97 := by simp [hm1569]
        have hm_split : ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m.take 64) ++
            (m.drop 64).take 1408 ++ m.drop 1472 = sig.take 32 ++ toU8 (encodeEd Apt) ++ m := by
          have h1 : (m.drop 64).take 1408 ++ m.drop 1472 = m.drop 64 := by
            rw [show (1472 : Nat) = 64 + 1408 from rfl, ← List.drop_drop, List.take_append_drop]
          rw [List.append_assoc, List.append_assoc (sig.take 32 ++ toU8 (encodeEd Apt)), h1,
            List.take_append_drop]
        have hst12 : (sha512CompressOutBytes P (sha512CompressOutBytes P
            (revWords64 sha512InitState) ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m.take 64))
            ((m.drop 64).take 1408)).length = 64 := sha512CompressOutBytes_length P _ _
        have hsha_eq : revWords64 (sha512CompressOutBytes P
            (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
              ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m.take 64)) ((m.drop 64).take 1408))
            (m.drop 1472 ++ [0x80] ++ List.replicate 14 0 ++ encodeBitLen128BE 1633)) =
            P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m) := by
          rw [hcurve.sha512_eq, ← hm_split, sha512Ref_of_length_1633 P hblk0 hblks11 htail97]
        have hsha64 : (P.sha512 (sig.take 32 ++ toU8 (encodeEd Apt) ++ m)).length = 64 := by
          rw [← hsha_eq]; exact revWords64_length (sha512CompressOutBytes_length P _ _)
        have hxed_eq := xeddsaVerifyRef_eq_capRCheck_of_some P hcurve hpk hsig h60 hmont hsha64
        apply verifySig_end_seg (verifySig_tail_from_548_ext_placed_at hookStack P H hH hle hbound
          s4 fsp sigPtr retAddr x19_0 x20_0 x21_0 x22_0 x23_0 x24_0 x25_0 x26_0 x27_0 x28_0 x29_0
          (bytesToBv8 pk) ed_bs (((sig.getD 63 0 &&& 0x80) >>> 7).toNat) Apt m sig (m.drop 1472)
          (sha512CompressOutBytes P (sha512CompressOutBytes P (revWords64 sha512InitState)
            ((sig.take 32 ++ toU8 (encodeEd Apt)) ++ m.take 64)) ((m.drop 64).take 1408))
          12#64 1633
          ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (slicesPtr ↦₆₄ msgPtr) ∗
           ((slicesPtr + 8#64) ↦₆₄ 1569#64) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ Frame)
          hcl4 hmont hed_bnd hed_eq hsig htail97 hst12 (Or.inr ⟨rfl, rfl⟩)
          hsha_eq hfsp_align hrun4 hpc4 hsp4 (hx23_4.trans hx23_s3) (hx29_4.trans hx29_s3))
          (Entails.of_eq (by sep_ac_rfl))
        intro s5 P5 hP5 ⟨hrun5, hpc5, hsp5, hx0_5, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28,
          h29, hv5, htr5⟩
        exact ⟨Entails.trans hP5 (Entails.of_eq (by sep_ac_rfl)), hrun5, hpc5, hsp5,
          hx0_5.trans hxed_eq, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29,
          hv5.trans (hv4.trans (hv3.trans (hv2.trans hv1))),
          htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1)))⟩

theorem verifySignatureMultipart_ext_placed_ok_at [LibsignalPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H) :
    subroutine_ok ((blkPC_204).rebase (blkPl_204).base H) (blkPl_204).base
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpecAt hookStack P)) := by
  refine subroutine_ok_of_sepWP fun g R s0 hpc hrun hpre hsp => ?_
  obtain ⟨⟨hcl, hro_all⟩, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hro := sha512IV_placed_holdsBytes hro_all
  dsimp only [verifySignatureMultipartCallSpecAt] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hfsp_align : ((s0.sp - 1248#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1248#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1248#64) + 1248#64 = s0.sp := by bv_omega
  refine ⟨((g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.slicesPtr ↦₆₄ g.msgPtr) ∗
      ((g.slicesPtr + 8#64) ↦₆₄ BitVec.ofNat 64 g.m.length) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt ((s0.sp - 1248#64) + 1248#64) (hookStack + 1248) ∗
      emp), R, ?_, ?_⟩
  · rw [hfsp_add, sepConj_emp]; exact Arm64.Satisfies.of_eq hmem (by sep_ac_rfl)
  · refine SepWP.mono
      (verifySignatureMultipart_ext_sepWP_placed_at hookStack P H hcurve hH hle hbound
        s0 (s0.sp - 1248#64) g.pkPtr g.slicesPtr g.msgPtr g.sigPtr (s0.readReg64 Reg.lr)
        g.pk g.m g.sig emp hcl hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm
        hx0 hx1 hx2 hx3 hx4 rfl) ?_
    intro sf Pf _ _ ⟨hPf, _, _, hsp_f, hx0_f,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩
    refine ⟨fun hsat => ?_, hsp_f.trans hfsp_add,
      ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩
    rw [hfsp_add, sepConj_emp] at hPf
    dsimp only [verifySignatureMultipartCallSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, htr⟩,
      Arm64.Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))))
        hsat⟩

theorem verifySignatureMultipart_ext_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpecAt hookStack P)) := by
  simpa only [ls_blockPlacement_base] using
    keys_ls_subroutine_ok_of_block_cro (j := 204)
      (verifySignatureMultipart_ext_placed_ok_at hle hbound hcurve hH) hi

theorem verifySignatureMultipart_ext_placed_frozen_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsFrozen lsmpl (verifySignatureMultipartCallSpecAt hookStack P)) :=
  subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
    (verifySignatureMultipart_ext_placed_ok_of_block_at hle hbound hcurve hH hi)

/-- End-to-end `SepWP` theorem for Block `203` (`verify_signature`) against extended-Edwards hooks
`VerifySignatureExtHooks hookStack P H`. -/
theorem verifySignature_ext_sepWP_placed_at [LibsignalPlacement]
    (hookStack : Nat) (P : SignalPqxdh.Primitives) (H : LibsignalHooks)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (s : State) (fsp pkPtr msgPtr sigPtr retAddr : BitVec 64)
    (pk m sig : Bytes) (Frame : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hro : Obj.HoldsBytes s.mem (lsmpl.ρ lsVerifySha512IVRoSym) sha512IVBytesLE (fun _ => Perm.ro))
    (hpk : pk.length = 32) (hm : m.length = 33 ∨ m.length = 1569) (hsig : sig.length = 64)
    (hfsp_align : fsp &&& 15#64 == 0#64) (hrun : s.status = ExecStatus.Running)
    (hpc : s.pc = (blkPl_203).base) (hsp : s.sp = fsp + 1280#64)
    (hx0 : s.readReg64 (.gpr 0#5) = pkPtr) (hx1 : s.readReg64 (.gpr 1#5) = msgPtr)
    (hx2 : s.readReg64 (.gpr 2#5) = BitVec.ofNat 64 m.length)
    (hx3 : s.readReg64 (.gpr 3#5) = sigPtr) (hx4 : s.readReg64 (.gpr 4#5) = 64#64)
    (hx30 : s.readReg64 (.gpr 30#5) = retAddr) :
    SepWP ((blkPC_203).rebase (blkPl_203).base H) retAddr s
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1280#64) (hookStack + 1280) ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
          stackAt (fsp + 1280#64) (hookStack + 1280) ∗ Frame) ∧
        sm.status = ExecStatus.Running ∧ sm.pc = retAddr ∧ sm.sp = fsp + 1280#64 ∧
        sm.readReg64 (.gpr 0#5) = (if P.sigVerify pk m sig = true then 1#64 else 0#64) ∧
        sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5) ∧
        sm.readReg64 (.gpr 20#5) = s.readReg64 (.gpr 20#5) ∧
        sm.readReg64 (.gpr 21#5) = s.readReg64 (.gpr 21#5) ∧
        sm.readReg64 (.gpr 22#5) = s.readReg64 (.gpr 22#5) ∧
        sm.readReg64 (.gpr 23#5) = s.readReg64 (.gpr 23#5) ∧
        sm.readReg64 (.gpr 24#5) = s.readReg64 (.gpr 24#5) ∧
        sm.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5) ∧
        sm.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5) ∧
        sm.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5) ∧
        sm.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5) ∧
        sm.readReg64 (.gpr 29#5) = s.readReg64 (.gpr 29#5) ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ sm.trace = s.trace) := by
  have hbound1248 : hookStack + 1248 ≤ 2 ^ 64 := by omega
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (verifySig_stackAt_1280_ext_split fsp hbound)) (by sep_frame)
  apply verifySig_seq_seg_lscro ⟨hcl, hro⟩
    (verifySignature_prologue_placed H s fsp pkPtr msgPtr (BitVec.ofNat 64 m.length) sigPtr retAddr
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       stackAt (fsp + 1248#64) (hookStack + 1248) ∗ Frame)
      hfsp_align hrun hpc hsp hx0 hx1 hx2 hx3 hx4 hx30)
    (Entails.of_eq (by sep_ac_rfl))
  intro s1 hpc1 hrun1 ⟨hcl1, hro1⟩ ⟨_, _, hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx30_1,
    h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hv1, htr1⟩
  have hmp_on_203 := lsjump_blk (callerProg := (blkPC_203).rebase (blkPl_203).base H)
    hcl1 (by decide) (by decide) (by decide)
    (verifySignatureMultipart_ext_sepWP_placed_at hookStack P H hcurve hH hle hbound1248
      s1 fsp pkPtr (fsp + 1248#64) msgPtr sigPtr ((blkPl_203).base + 28#64) pk m sig
      (((fsp + 1264#64) ↦₆₄ s.readReg64 (.gpr 29#5)) ∗ ((fsp + 1272#64) ↦₆₄ retAddr) ∗ Frame)
      hcl1 hro1 hpk hm hsig hfsp_align hrun1 hpc1 hsp1 hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx30_1)
  apply verifySig_seq_seg hmp_on_203
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))
  intro s2 hpc2 hrun2 ⟨_, _, hsp2, hx0_2, h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2,
    h27_2, h28_2, _, hv2, htr2⟩
  apply ProofLib.SepWP.replace_pre
    (hPQ := Entails.of_eq (stackAt_1248_split_low fsp hle hbound1248)) (by sep_frame)
  apply verifySig_end_seg
    (verifySignature_epilogue_placed H s2 fsp msgPtr (BitVec.ofNat 64 m.length)
      (s.readReg64 (.gpr 29#5)) retAddr
      ((pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗ (sigPtr ↦ₛ bytesToBv8 sig) ∗
       memRegion (fsp - BitVec.ofNat 64 hookStack) (hookStack - pqxdhHookStack) ∗ Frame)
      hfsp_align hrun2 hpc2 hsp2)
    (Entails.of_eq (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_ac_rfl))
  intro s3 P3 hP3 ⟨hrun3, hpc3, hsp3, hx0_3, h19_3, h20_3, h21_3, h22_3, h23_3, h24_3, h25_3, h26_3,
    h27_3, h28_3, h29_3, hv3, htr3⟩
  rw [hcurve.sigVerify_eq pk m sig]
  have hP3' : P3 ⊢ (pkPtr ↦ₛ bytesToBv8 pk) ∗ (msgPtr ↦ₛ bytesToBv8 m) ∗
      (sigPtr ↦ₛ bytesToBv8 sig) ∗ stackAt (fsp + 1280#64) (hookStack + 1280) ∗ Frame := by
    rw [stackAt_1280_split_low fsp hle hbound]
    exact Entails.trans hP3 (Entails.of_eq (by sep_ac_rfl))
  exact ⟨hP3', hrun3, hpc3, hsp3, hx0_3.trans hx0_2,
    h19_3.trans (h19_2.trans h19_1), h20_3.trans (h20_2.trans h20_1),
    h21_3.trans (h21_2.trans h21_1), h22_3.trans (h22_2.trans h22_1),
    h23_3.trans (h23_2.trans h23_1), h24_3.trans (h24_2.trans h24_1),
    h25_3.trans (h25_2.trans h25_1), h26_3.trans (h26_2.trans h26_1),
    h27_3.trans (h27_2.trans h27_1), h28_3.trans (h28_2.trans h28_1),
    h29_3, hv3.trans (hv2.trans hv1), htr3.trans (htr2.trans htr1)⟩

theorem verifySignature_ext_placed_ok_at [LibsignalPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H) (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpecAt hookStack P)) := by
  refine subroutine_ok_of_sepWP fun g R s0 hpc hrun hpre hsp => ?_
  obtain ⟨⟨hcl, hro_all⟩, hpre0⟩ := extract_withLsCodeRoLoaded hpre
  have hro := sha512IV_placed_holdsBytes hro_all
  dsimp only [verifySignatureCallSpecAt] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hx4, hpk, hm, hsig⟩, hmem⟩
  have hfsp_align : ((s0.sp - 1280#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 1280#64 hsp (by decide)
  have hfsp_add : (s0.sp - 1280#64) + 1280#64 = s0.sp := by bv_omega
  refine ⟨((g.pkPtr ↦ₛ bytesToBv8 g.pk) ∗ (g.msgPtr ↦ₛ bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ bytesToBv8 g.sig) ∗ stackAt ((s0.sp - 1280#64) + 1280#64) (hookStack + 1280) ∗
      emp), R, ?_, ?_⟩
  · rw [hfsp_add, sepConj_emp]; exact Arm64.Satisfies.of_eq hmem (by sep_ac_rfl)
  · refine SepWP.mono
      (verifySignature_ext_sepWP_placed_at hookStack P H hcurve hH hle hbound
        s0 (s0.sp - 1280#64) g.pkPtr g.msgPtr g.sigPtr (s0.readReg64 Reg.lr)
        g.pk g.m g.sig emp hcl hro hpk hm hsig hfsp_align hrun hpc hfsp_add.symm
        hx0 hx1 hx2 hx3 hx4 rfl) ?_
    intro sf Pf _ _ ⟨hPf, _, _, hsp_f, hx0_f,
      h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs, htr⟩
    refine ⟨fun hsat => ?_, hsp_f.trans hfsp_add,
      ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, hvregs⟩⟩
    rw [hfsp_add, sepConj_emp] at hPf
    dsimp only [verifySignatureCallSpecAt]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, htr⟩,
      Arm64.Satisfies.mono (sepConj_mono_left (Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))))
        hsat⟩

theorem verifySignature_ext_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpecAt hookStack P)) := by
  simpa only [ls_blockPlacement_base] using
    keys_ls_subroutine_ok_of_block_cro (j := 203)
      (verifySignature_ext_placed_ok_at hle hbound hcurve hH) hi

theorem verifySignature_ext_placed_frozen_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks hookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsFrozen lsmpl (verifySignatureCallSpecAt hookStack P)) :=
  subroutine_ok_withLsFrozen_of_withLsCodeRoLoaded
    (verifySignature_ext_placed_ok_of_block_at hle hbound hcurve hH hi)

/-! ### Stack Specializations, `DalekPrimsSound` / `dalekPrimsRef` Corollaries, and Bundles -/

theorem verifySignatureMultipart_ext_pqxdh_placed_ok [LibsignalPlacement]
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H) :
    subroutine_ok ((blkPC_204).rebase (blkPl_204).base H) (blkPl_204).base
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_ext_placed_ok_at (Nat.le_refl _) (by decide) hcurve hH

theorem verifySignatureMultipart_ext_pqxdh_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpec P)) :=
  verifySignatureMultipart_ext_placed_ok_of_block_at (Nat.le_refl _) (by decide) hcurve hH hi

theorem verifySignature_ext_pqxdh_placed_ok [LibsignalPlacement]
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H) (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_ext_placed_ok_at (Nat.le_refl _) (by decide) hcurve hH

theorem verifySignature_ext_pqxdh_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_ext_placed_ok_of_block_at (Nat.le_refl _) (by decide) hcurve hH hi

theorem verifySignature_ext_pqxdh_placed_frozen_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsFrozen lsmpl (verifySignatureCallSpec P)) :=
  verifySignature_ext_placed_frozen_ok_of_block_at (Nat.le_refl _) (by decide) hcurve hH hi

theorem verifySignatureMultipart_ext_dalek_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks dalekHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204)
      (withLsCodeRoLoaded lsmpl (verifySignatureMultipartCallSpecAt dalekHookStack P)) :=
  verifySignatureMultipart_ext_placed_ok_of_block_at (by decide) (by decide) hcurve hH hi

theorem verifySignature_ext_dalek_placed_ok [LibsignalPlacement]
    {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks dalekHookStack P H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H) (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpecAt dalekHookStack P)) :=
  verifySignature_ext_placed_ok_at (by decide) (by decide) hcurve hH

theorem verifySignature_ext_dalek_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks dalekHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpecAt dalekHookStack P)) :=
  verifySignature_ext_placed_ok_of_block_at (by decide) (by decide) hcurve hH hi

theorem verifySignature_ext_pqxdhExt_of_dalek_placed_ok_of_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks dalekHookStack P H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureCallSpecAt pqxdhHookStackExt P)) :=
  verifySignature_ext_placed_ok_of_block_at (by decide) (by decide) hcurve
    (hH.mono (by decide) (by decide)) hi

theorem verifySignatureMultipart_ext_modelPrims_of_sound_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204) (withLsCodeRoLoaded lsmpl
      (verifySignatureMultipartCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))) :=
  verifySignatureMultipart_ext_placed_ok_of_block_at hle hbound
    (xeddsaCurveSound_modelPrims_of_sound hD X C Qh) hH hi

theorem verifySignature_ext_modelPrims_of_sound_placed_ok_at [LibsignalPlacement]
    {hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H) (blkPl_203).base
      (withLsCodeRoLoaded lsmpl
        (verifySignatureCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))) :=
  verifySignature_ext_placed_ok_at hle hbound
    (xeddsaCurveSound_modelPrims_of_sound hD X C Qh) hH

theorem verifySignature_ext_modelPrims_of_sound_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203) (withLsCodeRoLoaded lsmpl
      (verifySignatureCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))) :=
  verifySignature_ext_placed_ok_of_block_at hle hbound
    (xeddsaCurveSound_modelPrims_of_sound hD X C Qh) hH hi

theorem verifySignature_ext_modelPrims_of_sound_placed_frozen_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203) (withLsFrozen lsmpl
      (verifySignatureCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))) :=
  verifySignature_ext_placed_frozen_ok_of_block_at hle hbound
    (xeddsaCurveSound_modelPrims_of_sound hD X C Qh) hH hi

theorem verifySignatureMultipart_ext_dalekPrimsRef_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1248 ≤ 2 ^ 64)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 204) (withLsCodeRoLoaded lsmpl
      (verifySignatureMultipartCallSpecAt hookStack
        (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))) :=
  verifySignatureMultipart_ext_modelPrims_of_sound_placed_ok_of_block_at hle hbound
    dalekPrimsRef_sound X C Qh hH hi

theorem verifySignature_ext_dalekPrimsRef_placed_ok_at [LibsignalPlacement]
    {hookStack : Nat} {H : LibsignalHooks}
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) H) :
    subroutine_ok ((blkPC_203).rebase (blkPl_203).base H) (blkPl_203).base
      (withLsCodeRoLoaded lsmpl
        (verifySignatureCallSpecAt hookStack
          (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))) :=
  verifySignature_ext_modelPrims_of_sound_placed_ok_at hle hbound
    dalekPrimsRef_sound X C Qh hH

theorem verifySignature_ext_dalekPrimsRef_placed_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203) (withLsCodeRoLoaded lsmpl
      (verifySignatureCallSpecAt hookStack
        (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))) :=
  verifySignature_ext_modelPrims_of_sound_placed_ok_of_block_at hle hbound
    dalekPrimsRef_sound X C Qh hH hi

theorem verifySignature_ext_dalekPrimsRef_placed_frozen_ok_of_block_at [LibsignalPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hle : pqxdhHookStack ≤ hookStack) (hbound : hookStack + 1280 ≤ 2 ^ 64)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hH : VerifySignatureExtHooks hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) H)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 203) (withLsFrozen lsmpl
      (verifySignatureCallSpecAt hookStack
        (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))) :=
  verifySignature_ext_modelPrims_of_sound_placed_frozen_ok_of_block_at hle hbound
    dalekPrimsRef_sound X C Qh hH hi

theorem curveVerifyAndCanon_ext_placed_ok_of_canon [LibsignalPlacement] {α : Type}
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] {canonSpec : Spec α}
    (h_canon : subroutine_ok callerProg (lsmpl.base 202) canonSpec)
    (hcurve : XeddsaCurveSound P) (hH : VerifySignatureExtHooks pqxdhHookStack P H)
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg canonSpec where
  isCanonical := h_canon
  verifySignature := verifySignature_ext_pqxdh_placed_ok_of_block hcurve hH hi
  verifySignatureMultipart := verifySignatureMultipart_ext_pqxdh_placed_ok_of_block hcurve hH hi

theorem curveVerifyAndCanon_ext_full_placed_ok [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k)
    (hcanonCurve : IsCanonicalCurveSound P) (hxedCurve : XeddsaCurveSound P)
    (hH : VerifySignatureExtHooks pqxdhHookStack P H)
    (htorsHook : HookSat H lsDalekTorsionFreeSym
      (withLsRet (dalekTorsionFreeExtSpec pqxdhHookStack)))
    (hi : i < 619 := by decide) :
    CurveVerifyAndCanonPlacedOk P callerProg
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpec P)) :=
  curveVerifyAndCanon_ext_placed_ok_of_canon
    (isCanonical_ext_pqxdh_placed_ok_cl hisCanon hcanonCurve hH.montToEd htorsHook)
    hxedCurve hH hi

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
