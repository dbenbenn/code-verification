/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonicalPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Block `202` (`<PublicKey>::is_canonical`) Against Extended-Edwards Hook Contracts

Relocatable `<libsignal_core::curve::PublicKey>::is_canonical` (Block `202`) proof under
`[LibsignalFullPlacement]` against placement-free `5×51`-bit `EdExtPoint` consumer hook contracts
(`dalekMontToEdExtSpec`, `dalekTorsionFreeExtSpec`) wrapped in `withLsRet`, parameterized by
`hookStack : Nat` (`hookStack + 400 ≤ 2 ^ 64`), bridged to `P.isCanonicalEC` (`= isCanonicalRef P`)
for curve-sound `P`, `DalekPrimsSound D`, and `dalekPrimsRef` via `Phase4RefBridge`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202

open Arm64 ProofLib ProofLib.ProgramReflection SepProp BitVec
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (IsLsBlockProg LibsignalFullPlacement LibsignalHooks LibsignalPlacement
  blkPC_202 blkPl_202 full_ls_subroutine_ok_of_plain libsignalSessionLib lsmpl lsρ ls_hook_ok_any)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives blockLevelPrims modelPrims ofU8)
open CryptoVerification.E2E.Pqxdh.Shared (DalekMontToEdGhost KeyCanonicalGhost bv_add_neg64
  bv_sub_sub_lit bytesToBv8 lsDalekMontToEdSym lsDalekTorsionFreeSym pqxdhHookStack
  pqxdhHookStackExt readReg_setMem_setPC_pre readReg_setPC_pre readReg32_setMem_setPC_pre
  readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre sp_setMem_setPC_pre
  sp_setPC_pre u64le)
open CryptoVerification.E2E.Pqxdh.ResponderCore (ofSignalPqxdhPrimitives toSignalPqxdhPrimitives)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs subroutine_ok_drop_keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  satisfies_withLsRet_of_blockPlacement_base_add specSimulates_withLsRet withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open VerifiedLibraries.Common (EdPoint edExtOfAffine edExtToAffine edOrderL edSmul edZero fpInv
  recoverXEven)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs (edExtOfBytes fe51Point4Bounded
  montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Edwards (EdExtValid
  edExtToAffine_edExtOfAffine edExtValid_edExtOfAffine)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Math.Birational (montToEdwards_some_onCurve)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4RefBridge (DalekPrims DalekPrimsSound
  PqxdhHookPrims dalekPrimsRef dalekPrimsRef_sound isCanonicalRef_congr_of_sound
  isCanonicalRef_dalekPrimsRef_eq pqxdhPrimsOfHooks)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
  VmPreserved fpInv recoverXEven edSmul fe51Point4Bounded edExtOfBytes
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓] sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Placement-Free Extended-Edwards Consumer Hook Specifications -/

/-- Default stack budget (`5120` bytes) for the in-image `curve25519-dalek` hooks. -/
abbrev dalekHookStack : Nat := 5120

/-- Output `Option<EdwardsPoint>` at `outPtr` (8-byte `u64` tag + 160-byte `EdExtPoint` payload). -/
@[expose] def dalekMontToEdExtOutAt (outPtr : BitVec 64) (u_bs : List (BitVec 8)) (sign : Nat) :
    SepProp :=
  match montToEdwards u_bs sign with
  | some Apt => ∃∗ ed_bs : List (BitVec 8),
      ⌜ed_bs.length = 160 ∧ fe51Point4Bounded ed_bs (2 ^ 52) ∧
        edExtOfBytes ed_bs = edExtOfAffine Apt⌝ ∗ (outPtr ↦ₛ (u64le 1#64 ++ ed_bs))
  | none => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160

theorem dalekMontToEdExtOutAt_none (outPtr : BitVec 64) (u_bs : List (BitVec 8)) (sign : Nat)
    (hmont : montToEdwards u_bs sign = none) :
    dalekMontToEdExtOutAt outPtr u_bs sign = ((outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160) := by
  unfold dalekMontToEdExtOutAt; rw [hmont]
theorem dalekMontToEdExtOutAt_some (outPtr : BitVec 64) (u_bs : List (BitVec 8)) (sign : Nat)
    (Apt : EdPoint) (hmont : montToEdwards u_bs sign = some Apt) :
    dalekMontToEdExtOutAt outPtr u_bs sign = (∃∗ ed_bs : List (BitVec 8),
      ⌜ed_bs.length = 160 ∧ fe51Point4Bounded ed_bs (2 ^ 52) ∧
        edExtOfBytes ed_bs = edExtOfAffine Apt⌝ ∗ ((outPtr ↦₆₄ 1#64) ∗ ((outPtr + 8#64) ↦ₛ ed_bs))) := by
  unfold dalekMontToEdExtOutAt; rw [hmont]; apply congrArg sepExists; funext ed_bs
  have hu1 : u64le 1#64 = unpack64 1#64 := rfl
  rw [hu1, pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes]
theorem montToEdwards_congr_mod2 (u_bs : List (BitVec 8)) {s₁ s₂ : Nat} (h : s₁ % 2 = s₂ % 2) :
    montToEdwards u_bs s₁ = montToEdwards u_bs s₂ := by unfold montToEdwards; rw [h]
theorem dalekMontToEdExtOutAt_congr_mod2 (outPtr : BitVec 64) (u_bs : List (BitVec 8))
    {s₁ s₂ : Nat} (h : s₁ % 2 = s₂ % 2) :
    dalekMontToEdExtOutAt outPtr u_bs s₁ = dalekMontToEdExtOutAt outPtr u_bs s₂ := by
  unfold dalekMontToEdExtOutAt; rw [montToEdwards_congr_mod2 u_bs h]
theorem uint8_and_one_toNat_eq_mod2 (b : UInt8) : (b &&& 1).toNat = b.toNat % 2 := by
  rcases b with ⟨bv⟩; revert bv; decide
theorem dalekMontToEdExtOutAt_and_one_eq_mod2 (outPtr : BitVec 64) (u_bs : List (BitVec 8))
    (b : UInt8) : dalekMontToEdExtOutAt outPtr u_bs (b &&& 1).toNat =
      dalekMontToEdExtOutAt outPtr u_bs (b.toNat % 2) := by rw [uint8_and_one_toNat_eq_mod2]
theorem dalekMontToEdExtOutAt_and_one_eq_toNat (outPtr : BitVec 64) (u_bs : List (BitVec 8))
    (b : UInt8) : dalekMontToEdExtOutAt outPtr u_bs (b &&& 1).toNat =
      dalekMontToEdExtOutAt outPtr u_bs b.toNat :=
  dalekMontToEdExtOutAt_congr_mod2 outPtr u_bs (by rw [uint8_and_one_toNat_eq_mod2, Nat.mod_mod])

/-- Placement-free consumer hook spec for `MontgomeryPoint::to_edwards` (`lsDalekMontToEdSym`). -/
@[expose] def dalekMontToEdExtSpec (hookStack : Nat) : Spec DalekMontToEdGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ (s.readReg64 .x1).setWidth 8 = BitVec.ofNat 8 g.signBit.toNat ∧
      s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗ stackAt s.sp hookStack
  post := fun g s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdExtOutAt g.outPtr (bytesToBv8 g.inBytes) (g.signBit &&& 1).toNat ∗
      stackAt s0.sp hookStack

/-- Ghost parameters for `EdwardsPoint::is_torsion_free` over a 160-byte `EdExtPoint` at `inPtr`. -/
structure DalekTorsionFreeExtGhost where
  inPtr : BitVec 64
  edBytes : List (BitVec 8)

/-- Placement-free consumer hook spec for `EdwardsPoint::is_torsion_free` (`lsDalekTorsionFreeSym`). -/
@[expose] def dalekTorsionFreeExtSpec (hookStack : Nat) : Spec DalekTorsionFreeExtGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ g.edBytes.length = 160 ∧
      fe51Point4Bounded g.edBytes (2 ^ 52) ∧ EdExtValid (edExtOfBytes g.edBytes)⌝ ∗
      (g.inPtr ↦ₛ g.edBytes) ∗ stackAt s.sp hookStack
  post := fun g s0 sf =>
    ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 32 =
      (if edSmul edOrderL (edExtToAffine (edExtOfBytes g.edBytes)) == edZero
       then 1#32 else 0#32)⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗ stackAt s0.sp hookStack

/-! ### `withVmPreserved` & `hookStack` Monotonicity Helpers for Extended-Edwards Hooks -/

theorem hookSat_withLsRet_of_withVmPreserved [LibsignalPlacement] {α : Type}
    {H : String → Option (State → State)} {sym : String} {spec : Spec α}
    (h : HookSat H sym (withLsRet (withVmPreserved spec))) : HookSat H sym (withLsRet spec) := by
  obtain ⟨f, hf, hok⟩ := h; refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcs, hq⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcs, ?_⟩⟩; dsimp only [withLsRet, withVmPreserved] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2
  · exact ⟨hkf, hsym, Or.inr hrest⟩
private theorem stackAt_split_ext (sp : BitVec 64) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    stackAt sp s₂ = stackAt sp s₁ ∗ memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) := by
  have h := ProofLib.stackAt_split_bottom sp s₁ (s₂ - s₁) (by omega)
  rw [Nat.add_sub_of_le hle, sepConj_comm] at h; exact h
private theorem hookSat_of_specSimulates {α β : Type} {H : String → Option (State → State)}
    {sym : String} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂) (hh : HookSat H sym spec₁) : HookSat H sym spec₂ := by
  obtain ⟨f, hf, hok⟩ := hh; refine ⟨f, hf, fun y R s0 hrun hpre hsp => ?_⟩
  obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
  obtain ⟨hkf, hsym, hout⟩ := hok x R₁ s0 hrun hpre₁ hsp; exact ⟨hkf, hsym, hmap (f s0) hout⟩
private theorem specSimulates_withVmPreserved_pure {α β : Type} {spec₁ : Spec α} {spec₂ : Spec β}
    (hsim : SpecSimulates spec₁ spec₂)
    (hpan₁ : spec₁.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₁ : spec₁.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₁ : spec₁.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (hpan₂ : spec₂.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex₂ : spec₂.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom₂ : spec₂.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withVmPreserved spec₁) (withVmPreserved spec₂) := by
  refine SpecSimulates.of_map (fun y R s0 hpre => ?_)
    (by simp [withVmPreserved, hpan₁]) (by simp [withVmPreserved, hex₁])
    (by simp [withVmPreserved, hoom₁])
  obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
  refine ⟨x, R₁, hpre₁, fun sf hret hcc hq => ?_⟩
  dsimp only [withVmPreserved] at hq ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  refine ⟨hq.1, ?_⟩
  rcases hmap sf (Or.inl ⟨hret, hcc, hq.2⟩) with ⟨_, _, hq₂⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · exact hq₂
  · rw [hpan₂] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [hex₂] at he; exact False.elim (not_satisfies_false_sepConj he)
  · rw [hoom₂] at ho; exact False.elim (not_satisfies_false_sepConj ho)
private theorem specSimulates_dalekMontToEdExtSpec {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekMontToEdExtSpec s₁) (dalekMontToEdExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  have hre : ∀ (A B C D E : SepProp), (A ∗ B ∗ C ∗ (D ∗ E)) ∗ R = (A ∗ B ∗ C ∗ D) ∗ (E ∗ R) :=
    fun _ _ _ _ _ => by sep_ac_rfl
  dsimp only [dalekMontToEdExtSpec] at hpre ⊢; rw [stackAt_split_ext s0.sp hle hbound, hre] at hpre
  refine ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, hpre, fun sf _ _ hq => ?_⟩
  rw [stackAt_split_ext s0.sp hle hbound, hre]; exact hq
private theorem specSimulates_dalekTorsionFreeExtSpec {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekTorsionFreeExtSpec s₁) (dalekTorsionFreeExtSpec s₂) := by
  refine SpecSimulates.of_map fun g R s0 hpre => ?_
  have hre : ∀ (A B D E : SepProp), (A ∗ B ∗ (D ∗ E)) ∗ R = (A ∗ B ∗ D) ∗ (E ∗ R) :=
    fun _ _ _ _ => by sep_ac_rfl
  dsimp only [dalekTorsionFreeExtSpec] at hpre ⊢; rw [stackAt_split_ext s0.sp hle hbound, hre] at hpre
  refine ⟨g, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, hpre, fun sf _ _ hq => ?_⟩
  rw [stackAt_split_ext s0.sp hle hbound, hre]; exact hq

theorem hookSat_dalekMontToEdExtSpec_mono [LibsignalPlacement]
    {H : String → Option (State → State)} {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64)
    (hh : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec s₁))) :
    HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec s₂)) :=
  hookSat_of_specSimulates (specSimulates_withLsRet (specSimulates_dalekMontToEdExtSpec hle hbound)) hh
theorem hookSat_dalekMontToEdExtVmSpec_mono [LibsignalPlacement]
    {H : String → Option (State → State)} {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64)
    (hh : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec s₁)))) :
    HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec s₂))) :=
  hookSat_of_specSimulates (specSimulates_withLsRet
    (specSimulates_withVmPreserved_pure (specSimulates_dalekMontToEdExtSpec hle hbound))) hh
theorem hookSat_dalekTorsionFreeExtSpec_mono [LibsignalPlacement]
    {H : String → Option (State → State)} {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64)
    (hh : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec s₁))) :
    HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec s₂)) :=
  hookSat_of_specSimulates
    (specSimulates_withLsRet (specSimulates_dalekTorsionFreeExtSpec hle hbound)) hh
theorem hookSat_dalekTorsionFreeExtVmSpec_mono [LibsignalPlacement]
    {H : String → Option (State → State)} {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64)
    (hh : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec s₁)))) :
    HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec s₂))) :=
  hookSat_of_specSimulates (specSimulates_withLsRet
    (specSimulates_withVmPreserved_pure (specSimulates_dalekTorsionFreeExtSpec hle hbound))) hh

/-! ## 2. Call Specifications & Curve-Soundness Bridges (`Phase4RefBridge`) -/

/-- `<libsignal_core::curve::PublicKey>::is_canonical` call spec parameterized by `hookStack : Nat`. -/
@[expose] def ecPubKeyIsCanonicalCallSpecAt (hookStack : Nat) (P : SignalPqxdh.Primitives) :
    Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s.sp (hookStack + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s0.sp (hookStack + 400)

theorem ecPubKeyIsCanonicalCallSpecAt_pqxdhHookStack (P : SignalPqxdh.Primitives) :
    ecPubKeyIsCanonicalCallSpecAt pqxdhHookStack P =
      CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpec P := rfl
theorem ecPubKeyIsCanonicalCallSpecAt_pqxdhHookStackExt (P : SignalPqxdh.Primitives) :
    ecPubKeyIsCanonicalCallSpecAt pqxdhHookStackExt P =
      CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpecExt P := rfl

/-- `Initiator.Primitives`-typed call spec parameterized by `hookStack : Nat`. -/
@[expose] def ecPubKeyIsCanonicalResponderCallSpecAt (hookStack : Nat)
    (P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives) :
    Spec CryptoVerification.E2E.Pqxdh.Initiator.KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
      (g.keyPtr ↦ₛ CryptoVerification.E2E.Pqxdh.Initiator.bytesToBv8 g.keyBytes) ∗
      stackAt s.sp (hookStack + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
      (g.keyPtr ↦ₛ CryptoVerification.E2E.Pqxdh.Initiator.bytesToBv8 g.keyBytes) ∗
      stackAt s0.sp (hookStack + 400)

theorem ecPubKeyIsCanonicalResponderCallSpecAt_pqxdhHookStack
    (P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives) :
    ecPubKeyIsCanonicalResponderCallSpecAt pqxdhHookStack P =
      CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec P := rfl
theorem ecPubKeyIsCanonicalResponderCallSpecAt_pqxdhHookStackExt
    (P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives) :
    ecPubKeyIsCanonicalResponderCallSpecAt pqxdhHookStackExt P =
      CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpecExt P := rfl

/-- Curve-soundness predicate connecting `SignalPqxdh.isCanonicalRef P` to `montToEdwards`/`edSmul`. -/
@[expose] def IsCanonicalCurveSound (P : SignalPqxdh.Primitives) : Prop :=
  ∀ keyBytes : List UInt8, keyBytes.length = 32 →
    ((keyBytes.getD 31 0 &&& 0x80) == 0) = true → SignalPqxdh.scalarIsInRange keyBytes = true →
    SignalPqxdh.isCanonicalRef P keyBytes =
      match montToEdwards (bytesToBv8 keyBytes) 0 with
      | none => false | some Apt => edSmul edOrderL Apt == edZero

theorem bytesToBv8_eq_ofU8 (bs : List UInt8) : bytesToBv8 bs = ofU8 bs := by
  unfold bytesToBv8 ofU8; congr 1; funext b; rcases b with ⟨bv⟩; simp [BitVec.ofNat_toNat]
theorem isCanonicalRef_eq_of_curveSound {P : SignalPqxdh.Primitives}
    (hcurve : IsCanonicalCurveSound P) {keyBytes : List UInt8} (hlen : keyBytes.length = 32) :
    SignalPqxdh.isCanonicalRef P keyBytes =
      if ((keyBytes.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange keyBytes then
        match montToEdwards (bytesToBv8 keyBytes) 0 with
        | none => false | some Apt => edSmul edOrderL Apt == edZero
      else false := by
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr hlen
  cases hb31 : ((keyBytes.getD 31 0 &&& 0x80) == 0)
  · unfold SignalPqxdh.isCanonicalRef; rw [hlen_beq, hb31]
    simp only [Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · cases hsc : SignalPqxdh.scalarIsInRange keyBytes
    · unfold SignalPqxdh.isCanonicalRef; rw [hlen_beq, hb31, hsc]
      simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    · have hit (x y : Bool) : (if (true && true) = true then x else y) = x := rfl
      rw [hit]; exact hcurve keyBytes hlen hb31 hsc
private theorem modelPrims_eq_def (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    modelPrims X W =
      let B := blockLevelPrims X W
      let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
      { B1 with
        sigVerify := SignalPqxdh.xeddsaVerifyRef B1
        isCanonical := SignalPqxdh.isCanonicalRef B1
        hkdfDerive96 := SignalPqxdh.hkdfDerive96Ref B1
        rootCreateChain := SignalPqxdh.rootCreateChainRef B1
        chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1
        chainKdfNext := SignalPqxdh.chainKdfNextRef B1
        deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1
        aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1
        aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 } := modelPrims.eq_1 X W
private theorem upd_outer_isCanonical (B1 : SignalPqxdh.Primitives)
    (sv f h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    ({ B1 with
       sigVerify := sv, isCanonical := f, hkdfDerive96 := h96, rootCreateChain := rcc,
       chainKdfSeed := cks, chainKdfNext := ckn, deriveMsgKeys := dmk,
       aeadEnc := ae, aeadDec := ad } : SignalPqxdh.Primitives).isCanonical pk = f pk := rfl
private theorem upd_outer_isCanonicalRef (B1 : SignalPqxdh.Primitives)
    (sv ic h96 rcc cks ckn dmk ae ad) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef
      { B1 with
        sigVerify := sv, isCanonical := ic, hkdfDerive96 := h96, rootCreateChain := rcc,
        chainKdfSeed := cks, chainKdfNext := ckn, deriveMsgKeys := dmk,
        aeadEnc := ae, aeadDec := ad } pk =
      SignalPqxdh.isCanonicalRef B1 pk := rfl
private theorem upd_sha512_isCanonicalRef (B : SignalPqxdh.Primitives)
    (s : List UInt8 → List UInt8) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef { B with sha512 := s } pk =
      SignalPqxdh.isCanonicalRef B pk := rfl
private theorem match_edPoint_swap (m : Option EdPoint) (f : EdPoint → Bool) :
    (match m with | some P => f P | none => false) =
      (match m with | none => false | some Apt => f Apt) := by
  cases m <;> rfl
theorem modelPrims_isCanonicalEC_eq (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    (modelPrims X W).isCanonicalEC pk = SignalPqxdh.isCanonicalRef (blockLevelPrims X W) pk :=
  (congrArg (fun M : SignalPqxdh.Primitives => M.isCanonical pk) (modelPrims_eq_def X W)).trans
    ((upd_outer_isCanonical _ _ _ _ _ _ _ _ _ _ pk).trans
      (upd_sha512_isCanonicalRef _ _ pk))
theorem isCanonicalRef_modelPrims_eq (X : UnreachedPqxdhPrimitives) (W : PEParams) (pk : List UInt8) :
    SignalPqxdh.isCanonicalRef (modelPrims X W) pk =
      SignalPqxdh.isCanonicalRef (blockLevelPrims X W) pk :=
  (congrArg (fun M : SignalPqxdh.Primitives => SignalPqxdh.isCanonicalRef M pk)
    (modelPrims_eq_def X W)).trans
    ((upd_outer_isCanonicalRef _ _ _ _ _ _ _ _ _ _ pk).trans
      (upd_sha512_isCanonicalRef _ _ pk))
theorem modelPrims_isCanonicalEC_eq_isCanonicalRef (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (pk : List UInt8) :
    (modelPrims X W).isCanonicalEC pk = SignalPqxdh.isCanonicalRef (modelPrims X W) pk :=
  (modelPrims_isCanonicalEC_eq X W pk).trans (isCanonicalRef_modelPrims_eq X W pk).symm
theorem isCanonicalCurveSound_blockLevelPrims_of_sound {D : DalekPrims} (hD : DalekPrimsSound D)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    IsCanonicalCurveSound (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) := by
  intro keyBytes hlen hb31 hsc
  rw [isCanonicalRef_congr_of_sound hD dalekPrimsRef_sound X C Qh keyBytes,
    isCanonicalRef_dalekPrimsRef_eq X C Qh keyBytes]
  have hlen_beq : (keyBytes.length == 32) = true := beq_iff_eq.mpr hlen
  have hcond : (keyBytes.length == 32 && ((keyBytes.getD 31 0 &&& 0x80) == 0) &&
      SignalPqxdh.scalarIsInRange keyBytes) = true := by rw [hlen_beq, hb31, hsc]; rfl
  have hit (x y : Bool) : (if true = true then x else y) = x := rfl
  rw [hcond, hit, ← bytesToBv8_eq_ofU8]
  exact match_edPoint_swap (montToEdwards (bytesToBv8 keyBytes) 0) (fun P => edSmul edOrderL P == edZero)
theorem isCanonicalCurveSound_modelPrims_of_sound {D : DalekPrims} (hD : DalekPrimsSound D)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    IsCanonicalCurveSound (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩) := by
  intro keyBytes hlen hb31 hsc; rw [isCanonicalRef_modelPrims_eq]
  exact isCanonicalCurveSound_blockLevelPrims_of_sound hD X C Qh keyBytes hlen hb31 hsc
theorem isCanonicalCurveSound_blockLevelPrims_dalekPrimsRef
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    IsCanonicalCurveSound (blockLevelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) :=
  isCanonicalCurveSound_blockLevelPrims_of_sound dalekPrimsRef_sound X C Qh
theorem isCanonicalCurveSound_modelPrims_dalekPrimsRef
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims) :
    IsCanonicalCurveSound (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩) :=
  isCanonicalCurveSound_modelPrims_of_sound dalekPrimsRef_sound X C Qh

/-! ## 3. Stack, Memory, Scalar-Range, and `SepWP` Helpers for Block `202` -/

theorem stackAt_ecPubKeyIsCanonical_call_at (sp : BitVec 64) {hookStack : Nat}
    (hstack : hookStack + 400 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 400) =
      stackAt (sp - 400#64) hookStack ∗ cells (sp - 400#64) 4 ∗ memRegion (sp - 368#64) 8 ∗
      memRegion (sp - 360#64) 168 ∗ memRegion (sp - 192#64) 160 ∗ cells (sp - 32#64) 4 := by
  rw [show (hookStack + 400 : Nat) = hookStack + 8 * 50 by omega,
    stackAt_split_cells sp hookStack 50 (by omega), ← memRegion_cells (sp - 400#64) 50 (by decide)]
  change stackAt (sp - 400#64) hookStack ∗ memRegion (sp - 400#64) 400 = _
  rw [memRegion_split (sp - 400#64) 32 368 (by decide), memRegion_cells (sp - 400#64) 4 (by decide),
    memRegion_split (sp - 400#64 + 32#64) 8 360 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64) 168 192 (by decide),
    memRegion_split (sp - 400#64 + 32#64 + 8#64 + 168#64) 160 32 (by decide),
    memRegion_cells (sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64) 4 (by decide),
    show sp - 400#64 + 32#64 + 8#64 + 168#64 + 160#64 = sp - 32#64 by bv_arith,
    show sp - 400#64 + 32#64 + 8#64 + 168#64 = sp - 192#64 by bv_arith,
    show sp - 400#64 + 32#64 + 8#64 = sp - 360#64 by bv_arith,
    show sp - 400#64 + 32#64 = sp - 368#64 by bv_arith]
private theorem memRegion168_of_cell_and_memRegion160 (a : BitVec 64) (v : BitVec 64)
    (R_tail : SepProp) : (a ↦₆₄ v) ∗ memRegion (a + 8#64) 160 ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  refine Entails.trans (sepConj_mono_left h1) ?_
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]; exact Entails.refl _
private theorem memRegion168_of_cell_and_bytes160 (a : BitVec 64) (v : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦₆₄ v) ∗ ((a + 8#64) ↦ₛ bs) ∗ R_tail ⊢ memRegion a 168 ∗ R_tail := by
  have h1 : (a ↦₆₄ v) ⊢ memRegion a 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right v (Entails.refl _)
  have h2 : ((a + 8#64) ↦ₛ bs) ⊢ memRegion (a + 8#64) 160 := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion (a + 8#64) bs
  refine Entails.trans (sepConj_mono_left h1)
    (Entails.trans (sepConj_mono_right (sepConj_mono_left h2)) ?_)
  rw [← sepConj_assoc, ← memRegion_split a 8 160 (by decide)]; exact Entails.refl _
private theorem memRegion160_of_bytes160 (a : BitVec 64)
    {bs : List (BitVec 8)} (hlen : bs.length = 160) (R_tail : SepProp) :
    (a ↦ₛ bs) ∗ R_tail ⊢ memRegion a 160 ∗ R_tail :=
  sepConj_mono_left (by rw [← hlen]; exact pointsToBytes_entails_memRegion a bs)

private theorem exists_unpack64_of_length_160 {bs : List (BitVec 8)} (h : bs.length = 160) :
    ∃ w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 : BitVec 64, ∀ a R_tail,
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1 ∗ ((a + 16#64) ↦₆₄ w2 ∗ ((a + 24#64) ↦₆₄ w3 ∗
      ((a + 32#64) ↦₆₄ w4 ∗ ((a + 40#64) ↦₆₄ w5 ∗ ((a + 48#64) ↦₆₄ w6 ∗ ((a + 56#64) ↦₆₄ w7 ∗
      ((a + 64#64) ↦₆₄ w8 ∗ ((a + 72#64) ↦₆₄ w9 ∗ ((a + 80#64) ↦₆₄ w10 ∗ ((a + 88#64) ↦₆₄ w11 ∗
      ((a + 96#64) ↦₆₄ w12 ∗ ((a + 104#64) ↦₆₄ w13 ∗ ((a + 112#64) ↦₆₄ w14 ∗ ((a + 120#64) ↦₆₄ w15 ∗
      ((a + 128#64) ↦₆₄ w16 ∗ ((a + 136#64) ↦₆₄ w17 ∗ ((a + 144#64) ↦₆₄ w18 ∗
      ((a + 152#64) ↦₆₄ w19 ∗ R_tail))))))))))))))))))) = (a ↦ₛ bs) ∗ R_tail := by
  have h0 : (bs.take 32).length = 32 := by simp [h]
  have h1 : ((bs.drop 32).take 32).length = 32 := by simp [h]
  have h2 : ((bs.drop 64).take 32).length = 32 := by simp [h]
  have h3 : ((bs.drop 96).take 32).length = 32 := by simp [h]
  obtain ⟨w0, w1, w2, w3, _, hp0⟩ := exists_unpack64_of_length_32 h0
  obtain ⟨w4, w5, w6, w7, _, hp1⟩ := exists_unpack64_of_length_32 h1
  obtain ⟨w8, w9, w10, w11, _, hp2⟩ := exists_unpack64_of_length_32 h2
  obtain ⟨w12, w13, w14, w15, _, hp3⟩ := exists_unpack64_of_length_32 h3
  obtain ⟨w16, w17, w18, w19, _, hp4⟩ := exists_unpack64_of_length_32 (bs := bs.drop 128) (by simp [h])
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, fun a R_tail => ?_⟩
  have s4 : bs.drop 96 = (bs.drop 96).take 32 ++ bs.drop 128 := by
    simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 96)).symm
  have s3 : bs.drop 64 = (bs.drop 64).take 32 ++ bs.drop 96 := by
    simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 64)).symm
  have s2 : bs.drop 32 = (bs.drop 32).take 32 ++ bs.drop 64 := by
    simpa [List.drop_drop] using (List.take_append_drop 32 (bs.drop 32)).symm
  have hsplit := (List.take_append_drop 32 bs).symm; rw [s4] at s3; rw [s3] at s2; rw [s2] at hsplit
  symm; conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, h0, hp0, pointsToBytes_append, h1, hp1, pointsToBytes_append, h2, hp2,
    pointsToBytes_append, h3, hp3, hp4]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
private theorem sepWP_memRegion160_head {prog : Program} {ret : BitVec 64} {s : State}
    (a : BitVec 64) {P_pre F_rest : SepProp} (heq : P_pre = memRegion a 160 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 : BitVec 64,
      SepWP prog ret s ((a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1 ∗ ((a + 16#64) ↦₆₄ u2 ∗
        ((a + 24#64) ↦₆₄ u3 ∗ ((a + 32#64) ↦₆₄ u4 ∗ ((a + 40#64) ↦₆₄ u5 ∗ ((a + 48#64) ↦₆₄ u6 ∗
        ((a + 56#64) ↦₆₄ u7 ∗ ((a + 64#64) ↦₆₄ u8 ∗ ((a + 72#64) ↦₆₄ u9 ∗ ((a + 80#64) ↦₆₄ u10 ∗
        ((a + 88#64) ↦₆₄ u11 ∗ ((a + 96#64) ↦₆₄ u12 ∗ ((a + 104#64) ↦₆₄ u13 ∗ ((a + 112#64) ↦₆₄ u14 ∗
        ((a + 120#64) ↦₆₄ u15 ∗ ((a + 128#64) ↦₆₄ u16 ∗ ((a + 136#64) ↦₆₄ u17 ∗ ((a + 144#64) ↦₆₄ u18 ∗
        ((a + 152#64) ↦₆₄ u19 ∗ F_rest)))))))))))))))))))) Q) : SepWP prog ret s P_pre Q := by
  rw [heq, memRegion_eq_exists_bytes a 160 (by decide), sepExists_sepConj_left]
  refine SepWP.exists_elim fun bs => ?_; rw [sepConj_assoc]; refine SepWP.pure_elim fun hlen => ?_
  obtain ⟨u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13, u14, u15,
    u16, u17, u18, u19, hbs⟩ := exists_unpack64_of_length_160 hlen
  rw [← hbs a F_rest]; exact h u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19
private theorem sepWP_dalekMontToEdExtOutAt_some_elim {prog : Program} {ret : BitVec 64}
    {s : State} (outPtr : BitVec 64) {u_bs : List (BitVec 8)} {Apt : EdPoint}
    (hmont : montToEdwards u_bs 0 = some Apt) {P_pre F_rest : SepProp}
    (heq : P_pre = dalekMontToEdExtOutAt outPtr u_bs 0 ∗ F_rest) {Q : State → SepProp → Prop}
    (h : ∀ ed_bs : List (BitVec 8), ed_bs.length = 160 → fe51Point4Bounded ed_bs (2 ^ 52) →
      edExtOfBytes ed_bs = edExtOfAffine Apt →
      SepWP prog ret s ((outPtr ↦₆₄ 1#64) ∗ (((outPtr + 8#64) ↦ₛ ed_bs) ∗ F_rest)) Q) :
    SepWP prog ret s P_pre Q := by
  rw [heq, dalekMontToEdExtOutAt_some outPtr u_bs 0 Apt hmont, sepExists_sepConj_left]
  refine SepWP.exists_elim fun ed_bs => ?_; rw [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hlen, hbnd, hext⟩ => ?_; rw [sepConj_assoc]; exact h ed_bs hlen hbnd hext
private theorem bytesToBv8_getD (bs : List UInt8) (i : Nat) :
    (bytesToBv8 bs).getD i 0#8 = (bs.getD i 0).toBitVec := by
  induction bs generalizing i with
  | nil => simp [bytesToBv8]
  | cons b rest ih => cases i with
    | zero => rcases b with ⟨⟨val, isLt⟩⟩; simp [bytesToBv8]
    | succ j => exact ih j
private theorem uint8_getLsbD7_eq_true_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = true ↔ ((b &&& 0x80) == 0) = false := by rcases b with ⟨bv⟩; revert bv; decide
private theorem uint8_getLsbD7_eq_false_iff (b : UInt8) :
    b.toBitVec.getLsbD 7 = false ↔ ((b &&& 0x80) == 0) = true := by rcases b with ⟨bv⟩; revert bv; decide
private theorem uint8_ult237_eq_true_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = true ↔ decide (b ≥ 0xED) = false := by
  rcases b with ⟨bv⟩; revert bv; decide
private theorem uint8_ult237_eq_false_iff (b : UInt8) :
    (BitVec.zeroExtend 64 b.toBitVec).ult 237#64 = false ↔ decide (b ≥ 0xED) = true := by
  rcases b with ⟨bv⟩; revert bv; decide
private theorem uint8_b31_7f_eq (b : UInt8) (h7 : ((b &&& 0x80) == 0) = true) :
    (BitVec.truncate 32 (BitVec.signExtend 64 b.toBitVec) == 127#32) = ((b &&& 0x7F) == 0x7F) := by
  rcases b with ⟨bv⟩; revert bv h7; decide
private theorem uint8_toBitVec_eq_ff_iff (b : UInt8) : (b.toBitVec = 0xff#8) ↔ (b = 0xFF) := by
  rcases b with ⟨bv⟩; exact ⟨fun h => by subst h; rfl, congrArg UInt8.toBitVec⟩
private theorem bv64_add1_eq_zero_iff (x : BitVec 64) :
    (x + 1#64 == 0#64) = (x == 0xffffffffffffffff#64) := by bv_bits
private theorem bv64_allOnes_getElem (i : Nat) (hi : i < 64) :
    (0xffffffffffffffff#64 : BitVec 64)[i] = true := by revert i hi; decide
private theorem bv64_and_eq_allOnes_iff (a b : BitVec 64) :
    (a &&& b = 0xffffffffffffffff#64) ↔ (a = 0xffffffffffffffff#64 ∧ b = 0xffffffffffffffff#64) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => by subst h1 h2; rfl⟩ <;> ext i hi <;>
    have hi' := congrArg (fun v : BitVec 64 => v[i]) h <;>
    rw [BitVec.getElem_and, bv64_allOnes_getElem i hi, Bool.and_eq_true] at hi' <;>
    rw [bv64_allOnes_getElem i hi]
  · exact hi'.1
  · exact hi'.2
private theorem pack64_eq_allOnes_iff (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (pack64 b0 b1 b2 b3 b4 b5 b6 b7 = 0xffffffffffffffff#64) ↔
      (b0 = 0xff#8 ∧ b1 = 0xff#8 ∧ b2 = 0xff#8 ∧ b3 = 0xff#8 ∧
       b4 = 0xff#8 ∧ b5 = 0xff#8 ∧ b6 = 0xff#8 ∧ b7 = 0xff#8) := by unfold pack64; bv_bits
private theorem list_take_drop_succ (xs : List UInt8) (i n : Nat) (hi : i < xs.length) :
    (xs.drop i).take (n + 1) = xs.getD i 0 :: (xs.drop (i + 1)).take n := by
  have hget : xs.getD i 0 = xs[i] := by simp [List.getD, hi]
  rw [List.drop_eq_getElem_cons hi, ← hget]; rfl
private theorem list32_drop1_take30_eq (xs : List UInt8) (h : xs.length = 32) :
    (xs.drop 1).take 30 = [xs.getD 1 0, xs.getD 2 0, xs.getD 3 0, xs.getD 4 0, xs.getD 5 0,
      xs.getD 6 0, xs.getD 7 0, xs.getD 8 0, xs.getD 9 0, xs.getD 10 0, xs.getD 11 0, xs.getD 12 0,
      xs.getD 13 0, xs.getD 14 0, xs.getD 15 0, xs.getD 16 0, xs.getD 17 0, xs.getD 18 0,
      xs.getD 19 0, xs.getD 20 0, xs.getD 21 0, xs.getD 22 0, xs.getD 23 0, xs.getD 24 0,
      xs.getD 25 0, xs.getD 26 0, xs.getD 27 0, xs.getD 28 0, xs.getD 29 0, xs.getD 30 0] := by
  repeat (rw [list_take_drop_succ _ _ _ (by omega)])
  rfl
private theorem list32_drop1_take30_eq_replicate_iff (xs : List UInt8) (h : xs.length = 32) :
    ((xs.drop 1).take 30 == List.replicate 30 0xFF) = true ↔
      (xs.getD 1 0 = 0xFF ∧ xs.getD 2 0 = 0xFF ∧ xs.getD 3 0 = 0xFF ∧ xs.getD 4 0 = 0xFF ∧
       xs.getD 5 0 = 0xFF ∧ xs.getD 6 0 = 0xFF ∧ xs.getD 7 0 = 0xFF ∧ xs.getD 8 0 = 0xFF ∧
       xs.getD 9 0 = 0xFF ∧ xs.getD 10 0 = 0xFF ∧ xs.getD 11 0 = 0xFF ∧ xs.getD 12 0 = 0xFF ∧
       xs.getD 13 0 = 0xFF ∧ xs.getD 14 0 = 0xFF ∧ xs.getD 15 0 = 0xFF ∧ xs.getD 16 0 = 0xFF ∧
       xs.getD 17 0 = 0xFF ∧ xs.getD 18 0 = 0xFF ∧ xs.getD 19 0 = 0xFF ∧ xs.getD 20 0 = 0xFF ∧
       xs.getD 21 0 = 0xFF ∧ xs.getD 22 0 = 0xFF ∧ xs.getD 23 0 = 0xFF ∧ xs.getD 24 0 = 0xFF ∧
       xs.getD 25 0 = 0xFF ∧ xs.getD 26 0 = 0xFF ∧ xs.getD 27 0 = 0xFF ∧ xs.getD 28 0 = 0xFF ∧
       xs.getD 29 0 = 0xFF ∧ xs.getD 30 0 = 0xFF) := by
  rw [beq_iff_eq, list32_drop1_take30_eq xs h]
  have hrep : List.replicate 30 (0xFF : UInt8) = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF] := rfl
  rw [hrep]; simp only [List.cons.injEq, and_true]
private abbrev pack64Mid30 (bs : List (BitVec 8)) : BitVec 64 :=
  pack64 (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8) (bs.getD 4 0#8)
      (bs.getD 5 0#8) (bs.getD 6 0#8) (bs.getD 7 0#8) (bs.getD 8 0#8) &&&
    pack64 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8)
      (bs.getD 13 0#8) (bs.getD 14 0#8) (bs.getD 15 0#8) (bs.getD 16 0#8) &&&
    (pack64 (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8) (bs.getD 20 0#8)
        (bs.getD 21 0#8) (bs.getD 22 0#8) (bs.getD 23 0#8) (bs.getD 24 0#8) &&&
      pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
        (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8))
private theorem pack64_4_allOnes_eq_drop1_take30 (keyBytes : List UInt8) (h : keyBytes.length = 32) :
    (pack64Mid30 (bytesToBv8 keyBytes) + 1#64 == 0#64) =
      ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) := by
  rw [bv64_add1_eq_zero_iff]; apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff, bv64_and_eq_allOnes_iff,
    pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff, pack64_eq_allOnes_iff,
    list32_drop1_take30_eq_replicate_iff keyBytes h]
  simp only [bytesToBv8_getD, uint8_toBitVec_eq_ff_iff]; constructor
  · rintro ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
            ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨_, _, h25, h26, h27, h28, h29, h30⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
           h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
            h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩
    exact ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13, h14, h15, h16⟩⟩,
           ⟨h17, h18, h19, h20, h21, h22, h23, h24⟩, ⟨h23, h24, h25, h26, h27, h28, h29, h30⟩⟩
private theorem scalarIsInRange_tail_eq (keyBytes : List UInt8) (h : keyBytes.length = 32)
    (hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true) :
    (if SignalPqxdh.scalarIsInRange keyBytes = true then (1#8 : BitVec 8) else 0#8) =
      BitVec.setWidth 8 (if (if (BitVec.truncate 32
          (BitVec.signExtend 64 ((bytesToBv8 keyBytes).getD 31 0#8)) == 127#32) = true then
        pack64Mid30 (bytesToBv8 keyBytes) + 1#64 == 0#64 else false) = true
        then (0#64 : BitVec 64) else 1#64) := by
  rw [pack64_4_allOnes_eq_drop1_take30 keyBytes h, bytesToBv8_getD keyBytes 31,
    uint8_b31_7f_eq (keyBytes.getD 31 0) hb31_u8]
  simp only [SignalPqxdh.scalarIsInRange, hb31_u8, hb0_u8]
  cases ((keyBytes.drop 1).take 30 == List.replicate 30 0xFF) <;>
    cases ((keyBytes.getD 31 0 &&& 0x7F) == 0x7F) <;> rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem State_ite_setPState_setPC (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) :
    @ite State c inst ((s.setPState ps1).setPC pc) ((s.setPState ps2).setPC pc) =
      (s.setPState (@ite PState c inst ps1 ps2)).setPC pc := by by_cases hc : c <;> simp [hc]
@[local simp, local wp_norm, local arm64_norm]
private theorem State_ite_setPState_setPC_setMem (c : Prop) [inst : Decidable c] (s : State)
    (ps1 ps2 : PState) (pc : BitVec 64) (m : Memory) :
    @ite State c inst (((s.setPState ps1).setPC pc).setMem m)
      (((s.setPState ps2).setPC pc).setMem m) =
      ((s.setPState (@ite PState c inst ps1 ps2)).setPC pc).setMem m := by by_cases hc : c <;> simp [hc]
@[local simp, local wp_norm, local arm64_norm]
private theorem ConditionHolds_ite (cond : CondCode) (c : Prop) [inst : Decidable c]
    (ps1 ps2 : PState) : ConditionHolds cond (@ite PState c inst ps1 ps2) =
      @ite Bool c inst (ConditionHolds cond ps1) (ConditionHolds cond ps2) := by
  by_cases hc : c <;> simp [hc]

@[local simp, local wp_norm, local arm64_norm]
private theorem fs_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).fs = s.fs := rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := rfl
@[local simp, local wp_norm, local arm64_norm]
private theorem fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fs = s.fs := rfl

/-! ## 4. Unified `OptVm` + `keepsFs` Machine-Code Proof for Block `202` -/

private def OptVm (useVm : Bool) (s0 sf : State) : Prop := if useVm then VmPreserved s0 sf else True
private theorem optVm_refl (useVm : Bool) (s : State) : OptVm useVm s s := by
  cases useVm; exact trivial; exact VmPreserved.refl s
private theorem optVm_trans {useVm : Bool} {s0 s1 s2 : State}
    (h1 : OptVm useVm s0 s1) (h2 : OptVm useVm s1 s2) : OptVm useVm s0 s2 := by
  cases useVm; exact trivial; exact h1.trans h2
private theorem optVm_of_vm (useVm : Bool) {s0 s1 : State} (h : VmPreserved s0 s1) :
    OptVm useVm s0 s1 := by cases useVm; exact trivial; exact h

private def dalekMontToEdExtOptSpec (useVm : Bool) (hookStack : Nat) : Spec DalekMontToEdGhost where
  pre := (dalekMontToEdExtSpec hookStack).pre
  post := fun g s0 sf =>
    ⌜OptVm useVm s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdExtOutAt g.outPtr (bytesToBv8 g.inBytes) (g.signBit &&& 1).toNat ∗
      stackAt s0.sp hookStack
private def dalekTorsionFreeExtOptSpec (useVm : Bool) (hookStack : Nat) :
    Spec DalekTorsionFreeExtGhost where
  pre := (dalekTorsionFreeExtSpec hookStack).pre
  post := fun g s0 sf =>
    ⌜OptVm useVm s0 sf ∧ sf.fs = s0.fs ∧ sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 32 =
        (if edSmul edOrderL (edExtToAffine (edExtOfBytes g.edBytes)) == edZero
         then 1#32 else 0#32)⌝ ∗ (g.inPtr ↦ₛ g.edBytes) ∗ stackAt s0.sp hookStack
private def withOptVm {α : Type} (useVm : Bool) (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜OptVm useVm s0 sf⌝ ∗ spec.post x s0 sf }

private theorem subroutine_ok_withOptVm_intro {α : Type} {useVm : Bool}
    {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => OptVm useVm s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withOptVm useVm spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ ⟨hopt, hq, hsp, hcs⟩ =>
    ⟨fun hm => by
      dsimp only [withOptVm]; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hopt, hq hm⟩,
     hsp, hcs⟩
private theorem sepWP_optVm_of_vm {prog : Program} {target : BitVec 64} {useVm : Bool}
    {s0 s : State} {Pre : SepProp} {post : State → SepProp → Prop} (h0 : OptVm useVm s0 s)
    (h : SepWP prog target s Pre (fun sf P_f => VmPreserved s sf ∧ post sf P_f)) :
    SepWP prog target s Pre (fun sf P_f => OptVm useVm s0 sf ∧ post sf P_f) :=
  SepWP.mono h fun _ _ _ _ ⟨hvm, hp⟩ => ⟨optVm_trans h0 (optVm_of_vm useVm hvm), hp⟩
private theorem sepWP_cut_vm {P : Program} {b mid ret : BitVec 64}
    {Hk : String → Option (State → State)} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) ret sm Pm post oom))) :
    SepWP (P.rebase b Hk) ret s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  obtain ⟨sm, hsteps1, ⟨_, _, Pm, hPm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ := SepWP.to_reaches_pc h hm hL
  · obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc (hcont hvm) hPm (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)
private theorem subroutine_ok_strip_withLsRet_202 [LibsignalFullPlacement] {α : Type}
    {prog : Program} {entry : BitVec 64} {spec : Spec α} (off : BitVec 64)
    (hok : subroutine_ok prog entry (withLsRet spec)) (ho : off.toNat < lsLen 202 := by decide) :
    subroutine_ok prog entry
      { spec with pre := fun x s => ⌜s.readReg64 .lr = (blkPl_202).base + off⌝ ∗ spec.pre x s } :=
  subroutine_ok_mono hok
    (fun _ _ _ hpre => by
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      exact satisfies_withLsRet_of_blockPlacement_base_add 202 off hpre.1 hpre.2 (by decide) ho)
    (fun _ _ _ _ hq => hq)
private theorem hookSat_withLsRet_post_mono [LibsignalPlacement] {α : Type}
    {H : LibsignalHooks} {sym : String} {spec₁ spec₂ : Spec α}
    (hh : HookSat H sym (withLsRet spec₁))
    (hpost : ∀ g R s0 sf, (sf.mem ⊨ spec₁.post g s0 sf ∗ R) → (sf.mem ⊨ spec₂.post g s0 sf ∗ R))
    (hpre : spec₁.pre = spec₂.pre := by rfl) (hpan : spec₁.onPanic = spec₂.onPanic := by rfl)
    (hex : spec₁.onExit = spec₂.onExit := by rfl) (hoom : spec₁.onOom = spec₂.onOom := by rfl) :
    HookSat H sym (withLsRet spec₂) := by
  obtain ⟨f, hf, hok⟩ := hh; refine ⟨f, hf, fun g R s0 hrun hp hsp => ?_⟩
  have hp' : s0.mem ⊨ (withLsRet spec₁).pre g s0 ∗ R := by dsimp only [withLsRet] at hp ⊢; rwa [hpre]
  rcases hok g R s0 hrun hp' hsp with ⟨hkf, hsym, ⟨hret, hcs, hq⟩ | ⟨hp1, hqp⟩ | ⟨c, he1, hqe⟩ | ⟨ho1, hqo⟩⟩
  · exact ⟨hkf, hsym, Or.inl ⟨hret, hcs, hpost g R s0 (f s0) hq⟩⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inl ⟨hp1, by dsimp only [withLsRet] at hqp ⊢; rwa [← hpan]⟩)⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inr (Or.inl ⟨c, he1, by dsimp only [withLsRet] at hqe ⊢; rwa [← hex]⟩))⟩
  · exact ⟨hkf, hsym, Or.inr (Or.inr (Or.inr ⟨ho1, by dsimp only [withLsRet] at hqo ⊢; rwa [← hoom]⟩))⟩
private theorem hookSat_dalekMontToEdExtOpt_false [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hh : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack))) :
    HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtOptSpec false hookStack)) :=
  hookSat_withLsRet_post_mono hh fun _ _ _ _ hq => by
    dsimp only [dalekMontToEdExtSpec, dalekMontToEdExtOptSpec] at hq ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; exact ⟨⟨trivial, hq.1⟩, hq.2⟩
private theorem hookSat_dalekMontToEdExtOpt_true [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hh : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack)))) :
    HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtOptSpec true hookStack)) :=
  hookSat_withLsRet_post_mono hh fun _ _ _ _ hq => by
    dsimp only [withVmPreserved, dalekMontToEdExtSpec, dalekMontToEdExtOptSpec, OptVm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; rcases hq with ⟨hvm, hq'⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢; exact ⟨⟨hvm, hq'.1⟩, hq'.2⟩
private theorem hookSat_dalekTorsionFreeExtOpt_false [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hh : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtOptSpec false hookStack)) :=
  hookSat_withLsRet_post_mono hh fun _ _ _ _ hq => by
    dsimp only [dalekTorsionFreeExtSpec, dalekTorsionFreeExtOptSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; exact ⟨⟨trivial, hq.1⟩, hq.2⟩
private theorem hookSat_dalekTorsionFreeExtOpt_true [LibsignalPlacement] {H : LibsignalHooks} {hookStack : Nat}
    (hh : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtOptSpec true hookStack)) :=
  hookSat_withLsRet_post_mono hh fun _ _ _ _ hq => by
    dsimp only [withVmPreserved, dalekTorsionFreeExtSpec, dalekTorsionFreeExtOptSpec, OptVm] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq; rcases hq with ⟨hvm, hq'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢; exact ⟨⟨hvm, hq'.1⟩, hq'.2⟩

private def eqEdZero (Q : EdPoint) : Bool := Q == edZero
private theorem eqEdZero_eq (Q : EdPoint) : eqEdZero Q = (Q == edZero) := rfl
private theorem match_edPoint_congr (m : Option EdPoint) {f1 f2 : EdPoint → Bool}
    (hf : ∀ P, f1 P = f2 P) :
    (match m with | none => false | some Apt => f1 Apt) =
      (match m with | none => false | some Apt => f2 Apt) := by
  cases m with
  | none => rfl
  | some Apt => exact hf Apt

private def canonRhs (keyBytes : List UInt8) (m : Option EdPoint) : Bool :=
  if ((keyBytes.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange keyBytes then
    match m with | none => false | some Apt => eqEdZero (edSmul edOrderL Apt)
  else false

private theorem isCanonicalRef_eq_canonRhs_of_curveSound {P : SignalPqxdh.Primitives}
    (hcurve : IsCanonicalCurveSound P) {keyBytes : List UInt8} (hlen : keyBytes.length = 32) :
    SignalPqxdh.isCanonicalRef P keyBytes =
      canonRhs keyBytes (montToEdwards (bytesToBv8 keyBytes) 0) :=
  (isCanonicalRef_eq_of_curveSound hcurve hlen).trans
    (congrArg
      (fun t => if ((keyBytes.getD 31 0 &&& 0x80) == 0) && SignalPqxdh.scalarIsInRange keyBytes
        then t else false)
      (match_edPoint_congr (montToEdwards (bytesToBv8 keyBytes) 0)
        (fun Apt => (eqEdZero_eq (edSmul edOrderL Apt)).symm)))

private theorem canonRhs_none (keyBytes : List UInt8) : canonRhs keyBytes none = false := by
  unfold canonRhs; split <;> rfl
private theorem canonRhs_some_false (keyBytes : List UInt8) {Apt : EdPoint}
    (htors : (edSmul edOrderL Apt == edZero) = false) :
    canonRhs keyBytes (some Apt) = false := by
  dsimp only [canonRhs]; rw [eqEdZero_eq, htors]; split <;> rfl
private theorem canonRhs_some_b31_false (keyBytes : List UInt8) (Apt : EdPoint)
    (hb31 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false) :
    canonRhs keyBytes (some Apt) = false := by
  simp only [canonRhs, hb31, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
private theorem canonRhs_some_true (keyBytes : List UInt8) {Apt : EdPoint}
    (hb31 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (hsc : SignalPqxdh.scalarIsInRange keyBytes = true)
    (htors : (edSmul edOrderL Apt == edZero) = true) :
    canonRhs keyBytes (some Apt) = true := by
  dsimp only [canonRhs]; rw [hb31, hsc, eqEdZero_eq, htors]; rfl
private theorem canonRhs_some_eq_scalarIsInRange (keyBytes : List UInt8) {Apt : EdPoint}
    (hb31 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true)
    (htors : (edSmul edOrderL Apt == edZero) = true) :
    canonRhs keyBytes (some Apt) = SignalPqxdh.scalarIsInRange keyBytes := by
  dsimp only [canonRhs]; rw [hb31, eqEdZero_eq, htors]
  cases SignalPqxdh.scalarIsInRange keyBytes <;> rfl

set_option maxHeartbeats 1600000 in
private theorem isCanonical_ext_optVm_placed_ok_at [LibsignalFullPlacement]
    {useVm : Bool} {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    (hstack : hookStack + 400 ≤ 2 ^ 64) (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k)
    (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtOptSpec useVm hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtOptSpec useVm hookStack))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (withOptVm useVm (keepsFs (ecPubKeyIsCanonicalCallSpecAt hookStack P))) := by
  apply subroutine_ok_withOptVm_intro
  have hmont_call := subroutine_ok_strip_withLsRet_202
    (prog := (blkPC_202).rebase (blkPl_202).base H) 44#64 (ls_hook_ok_any hmontHook)
  have htors_call := subroutine_ok_strip_withLsRet_202
    (prog := (blkPC_202).rebase (blkPl_202).base H) 116#64 (ls_hook_ok_any htorsHook)
  clear hmontHook htorsHook
  dsimp only [dalekMontToEdExtOptSpec, dalekMontToEdExtSpec] at hmont_call
  dsimp only [dalekTorsionFreeExtOptSpec, dalekTorsionFreeExtSpec] at htors_call
  intro ⟨keyPtr, keyBytes⟩ R s0 hpc hrun hpre hsp_align
  have hsp_al : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  dsimp only [keepsFs, ecPubKeyIsCanonicalCallSpecAt] at *
  refine SepWP.pure_elim ?_; rintro ⟨h_1, h⟩; subst h_1
  simp only [stackAt_ecPubKeyIsCanonical_call_at _ hstack]; cells_unfold; wp_pull_exists
  rw [hisCanon keyBytes, isCanonicalRef_eq_canonRhs_of_curveSound hcurve h]
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  have hpk_sp_tail (R_tail : SepProp) : (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗
      ((s0.sp - 384#64) ↦₆₄ w2 ∗ ((s0.sp - 376#64) ↦₆₄ w3 ∗ R_tail))) =
      (s0.sp - 400#64) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    have hpk_sp := hpk_cells (s0.sp - 400#64)
    rw [show s0.sp - 400#64 + 8#64 = s0.sp - 392#64 by bv_arith,
      show s0.sp - 400#64 + 16#64 = s0.sp - 384#64 by bv_arith,
      show s0.sp - 400#64 + 24#64 = s0.sp - 376#64 by bv_arith] at hpk_sp
    rw [hpk_sp, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  have hpk_reg0_tail (R_tail : SepProp) :
      s0.readReg64 (Reg.gpr 0#5) ↦₆₄ w0 ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ w1 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ w2 ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ w3 ∗ R_tail))) =
      s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail := by
    rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5)), sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply sepWP_cut_vm (mid := lsρ lsDalekMontToEdSym)
  by_vm_steps (
    wp_conv_pre => rw [← hpk_reg0_tail]
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all)
      ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    wp_conv_pre => rw [hpk_reg0_tail, hpk_sp_tail]
    wp_call hmont_call ⟨keyBytes, 0, s0.sp - 400#64, s0.sp - 360#64⟩
    wp_conv_pre => rw [show ((0 : UInt8) &&& 1).toNat = 0 from rfl, ← hpk_sp_tail]
    have hopt12 : OptVm useVm s0 sf := optVm_trans (optVm_of_vm useVm hvm1) ‹OptVm useVm _ sf›
    have hfs1 : sf.fs = s0.fs := by simp_all
    have htr1 : sf.trace = s0.trace := by simp_all
    cases hmont : montToEdwards (bytesToBv8 keyBytes) 0 with
    | none =>
      rw [canonRhs_none]; apply sepWP_optVm_of_vm hopt12
      by_vm_steps (
        wp_conv_pre =>
          rw [dalekMontToEdExtOutAt_none (s0.sp - 360#64) (bytesToBv8 keyBytes) 0 hmont, sepConj_assoc]
        wp_steps
        refine SepWP.weaken_pre (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (memRegion168_of_cell_and_memRegion160 (s0.sp - 360#64) 0#64 _))))) ?_
        wp_done)
    | some Apt =>
      refine sepWP_dalekMontToEdExtOutAt_some_elim (s0.sp - 360#64) hmont
        (F_rest := (s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗ ((s0.sp - 384#64) ↦₆₄ w2 ∗
          ((s0.sp - 376#64) ↦₆₄ w3 ∗ (stackAt (s0.sp - 400#64) hookStack ∗
          (s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ (memRegion (s0.sp - 368#64) 8 ∗
          (memRegion (s0.sp - 192#64) 160 ∗ ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗ ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))))))))))
        (by sep_ac_rfl) fun ed_bs hed_len hpt_bnd hpt_eq => ?_
      have hApt_on := montToEdwards_some_onCurve hmont
      have hpt_valid_aff : EdExtValid (edExtOfAffine Apt) := edExtValid_edExtOfAffine hApt_on
      have hpt_valid : EdExtValid (edExtOfBytes ed_bs) := by rw [hpt_eq]; exact hpt_valid_aff
      have hpt_bnd' : fe51Point4Bounded ed_bs 4503599627370496 := hpt_bnd
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
        e16, e17, e18, e19, hed_cells⟩ := exists_unpack64_of_length_160 hed_len
      refine sepWP_memRegion160_head (s0.sp - 192#64)
        (F_rest := (s0.sp - 360#64) ↦₆₄ 1#64 ∗ (((s0.sp - 360#64 + 8#64) ↦ₛ ed_bs) ∗
          ((s0.sp - 400#64) ↦₆₄ w0 ∗ ((s0.sp - 392#64) ↦₆₄ w1 ∗ ((s0.sp - 384#64) ↦₆₄ w2 ∗
          ((s0.sp - 376#64) ↦₆₄ w3 ∗ (stackAt (s0.sp - 400#64) hookStack ∗
          (s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ (memRegion (s0.sp - 368#64) 8 ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 28#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)))))))))))))
        (by sep_ac_rfl) fun u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 => ?_
      apply sepWP_cut_vm (mid := lsρ lsDalekTorsionFreeSym)
      by_vm_steps (
        wp_conv_pre => rw [← hed_cells (s0.sp - 360#64 + 8#64)]
        wp_steps
        refine SepWP.done (by simp only [wp_norm, arm64_norm]) (by simp_all)
          ⟨by simp only [wp_norm, arm64_norm], fun hvm2 => ?_⟩
        wp_conv_pre => rw [hed_cells (s0.sp - 192#64), hed_cells (s0.sp - 360#64 + 8#64)]
        refine SepWP.weaken_pre
          (sepConj_mono_right (memRegion168_of_cell_and_bytes160 (s0.sp - 360#64) 1#64 hed_len _)) ?_
        wp_call htors_call ⟨s0.sp - 192#64, ed_bs⟩
        have hopt23 : OptVm useVm s0 sf_1 :=
          optVm_trans hopt12 (optVm_trans (optVm_of_vm useVm hvm2) ‹OptVm useVm _ sf_1›)
        have hfs2 : sf_1.fs = s0.fs := by simp_all
        have htr2 : sf_1.trace = s0.trace := by simp_all
        rw [hpt_eq, edExtToAffine_edExtOfAffine hApt_on] at hpost_1
        refine SepWP.weaken_pre (memRegion160_of_bytes160 (s0.sp - 192#64) hed_len _) ?_
        apply sepWP_optVm_of_vm hopt23
        by_vm_steps (
          cases htors : (edSmul edOrderL Apt == edZero) with
          | false =>
            rw [canonRhs_some_false keyBytes htors]
            simp only [htors, Bool.false_eq_true, ite_false] at hpost_1
            have hx0_8 : BitVec.setWidth 8 (sf_1.readReg64 (Reg.gpr 0#5)) = 0#8 := by revert hpost_1; bv_bits
            wp_steps; wp_done
          | true =>
            simp only [htors, ite_true] at hpost_1
            have hfocus8 (off : Nat) (hoff : off < 32) (R_tail : SepProp) :
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
                  ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₈ (bytesToBv8 keyBytes).getD off 0#8) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
                   ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 1)) ↦ₛ
                    (bytesToBv8 keyBytes).drop (off + 1) ∗ R_tail)) := by
              rw [pointsToBytes_focus8 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
                  (by rw [hlen_bv]; exact hoff), sepConj_assoc, sepConj_assoc]
            have hfocus64 (off : Nat) (hoff : off + 8 ≤ 32) (R_tail : SepProp) :
                s0.readReg64 (Reg.gpr 0#5) ↦ₛ bytesToBv8 keyBytes ∗ R_tail =
                  ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 off) ↦₆₄
                    pack64 ((bytesToBv8 keyBytes).getD off 0#8) ((bytesToBv8 keyBytes).getD (off + 1) 0#8)
                      ((bytesToBv8 keyBytes).getD (off + 2) 0#8) ((bytesToBv8 keyBytes).getD (off + 3) 0#8)
                      ((bytesToBv8 keyBytes).getD (off + 4) 0#8) ((bytesToBv8 keyBytes).getD (off + 5) 0#8)
                      ((bytesToBv8 keyBytes).getD (off + 6) 0#8) ((bytesToBv8 keyBytes).getD (off + 7) 0#8)) ∗
                  ((s0.readReg64 (Reg.gpr 0#5) ↦ₛ (bytesToBv8 keyBytes).take off) ∗
                   ((s0.readReg64 (Reg.gpr 0#5) + BitVec.ofNat 64 (off + 8)) ↦ₛ
                    (bytesToBv8 keyBytes).drop (off + 8) ∗ R_tail)) := by
              rw [pointsToBytes_focus64 (s0.readReg64 (Reg.gpr 0#5)) (bytesToBv8 keyBytes) off
                  (by rw [hlen_bv]; exact hoff), sepConj_assoc, sepConj_assoc]
            wp_conv_pre => rw [hfocus8 31 (by decide)]
            wp_steps; wp_conv_pre => rw [← hfocus8 31 (by decide)]
            cases hb31 : ((bytesToBv8 keyBytes).getD 31 0#8).getLsbD 7 with
            | true =>
              have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = false := by
                rw [bytesToBv8_getD] at hb31; exact (uint8_getLsbD7_eq_true_iff _).mp hb31
              rw [canonRhs_some_b31_false keyBytes Apt hb31_u8]
              simp only [beq_self_eq_true, ite_true]; wp_steps; wp_done
            | false =>
              have hb31_u8 : ((keyBytes.getD 31 0 &&& 0x80) == 0) = true := by
                rw [bytesToBv8_getD] at hb31; exact (uint8_getLsbD7_eq_false_iff _).mp hb31
              simp only [beq_iff_eq, Bool.false_eq_true, ite_false]
              wp_conv_pre => rw [hfocus8 0 (by decide)]
              wp_steps; wp_conv_pre => rw [← hfocus8 0 (by decide)]
              cases hb0 : (BitVec.zeroExtend 64 ((bytesToBv8 keyBytes).getD 0 0#8)).ult 237#64 with
              | true =>
                have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = false := by
                  rw [bytesToBv8_getD] at hb0; exact (uint8_ult237_eq_true_iff _).mp hb0
                have hsc_true : SignalPqxdh.scalarIsInRange keyBytes = true := by
                  simp only [SignalPqxdh.scalarIsInRange, hb31_u8, hb0_u8]; rfl
                rw [canonRhs_some_true keyBytes hb31_u8 hsc_true htors]
                simp only [ite_true]; wp_steps; wp_done
              | false =>
                have hb0_u8 : decide (keyBytes.getD 0 0 ≥ 0xED) = true := by
                  rw [bytesToBv8_getD] at hb0; exact (uint8_ult237_eq_false_iff _).mp hb0
                simp only [Bool.false_eq_true, ite_false]
                wp_conv_pre => rw [hfocus64 1 (by decide)]
                wp_step; wp_conv_pre => rw [← hfocus64 1 (by decide), hfocus64 9 (by decide)]
                wp_steps; wp_conv_pre => rw [← hfocus64 9 (by decide), hfocus64 17 (by decide)]
                wp_step; wp_conv_pre => rw [← hfocus64 17 (by decide), hfocus64 23 (by decide)]
                wp_steps; wp_conv_pre => rw [← hfocus64 23 (by decide)]
                rw [canonRhs_some_eq_scalarIsInRange keyBytes hb31_u8 htors,
                  scalarIsInRange_tail_eq keyBytes h hb31_u8 hb0_u8]; wp_done)))

/-! ## 5. Public Block `202` Theorems & Corollaries -/

private theorem subroutine_ok_drop_withOptVm_false {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry (withOptVm false spec)) : subroutine_ok prog entry spec :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) fun _ _ _ _ hq => by
    dsimp only [withOptVm] at hq; rw [sepConj_assoc, satisfies_pure_sepConj] at hq; exact hq.2
private theorem subroutine_ok_keepsFs_withVmPreserved_of_withOptVm_true {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (h : subroutine_ok prog entry (withOptVm true (keepsFs spec))) :
    subroutine_ok prog entry (keepsFs (withVmPreserved spec)) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) fun _ _ _ _ hq => by
    dsimp only [withOptVm, OptVm, keepsFs, withVmPreserved] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢; rcases hq with ⟨hvm, hq'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq' ⊢; exact ⟨hq'.1, hvm, hq'.2⟩

/-- Block `202` preserves `.fs` and meets `ecPubKeyIsCanonicalCallSpecAt hookStack P`. -/
theorem isCanonical_ext_keepsFs_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (keepsFs (ecPubKeyIsCanonicalCallSpecAt hookStack P)) :=
  subroutine_ok_drop_withOptVm_false (isCanonical_ext_optVm_placed_ok_at hstack hisCanon hcurve
    (hookSat_dalekMontToEdExtOpt_false hmontHook) (hookSat_dalekTorsionFreeExtOpt_false htorsHook))
/-- Block `202` meets `ecPubKeyIsCanonicalCallSpecAt hookStack P`. -/
theorem isCanonical_ext_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpecAt hookStack P) :=
  subroutine_ok_drop_keepsFs (isCanonical_ext_keepsFs_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)
/-- `keepsFs ∘ withVmPreserved` Block `202` contract from `withVmPreserved` extended-Edwards hooks. -/
theorem isCanonical_ext_keepsFs_vm_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (keepsFs (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack P))) :=
  subroutine_ok_keepsFs_withVmPreserved_of_withOptVm_true (isCanonical_ext_optVm_placed_ok_at hstack hisCanon
    hcurve (hookSat_dalekMontToEdExtOpt_true hmontHook) (hookSat_dalekTorsionFreeExtOpt_true htorsHook))
/-- `withVmPreserved` Block `202` contract from `withVmPreserved` extended-Edwards hooks. -/
theorem isCanonical_ext_vm_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack P)) :=
  subroutine_ok_drop_keepsFs (isCanonical_ext_keepsFs_vm_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)

/-! ### `withCodeLoaded` (`_cl`) Liftings -/

theorem isCanonical_ext_keepsFs_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (keepsFs (ecPubKeyIsCanonicalCallSpecAt hookStack P))) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_ext_keepsFs_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)
theorem isCanonical_ext_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpecAt hookStack P)) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_ext_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)
theorem isCanonical_ext_keepsFs_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (keepsFs (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack P)))) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_ext_keepsFs_vm_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)
theorem isCanonical_ext_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack P))) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_ext_vm_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook)

/-! ### Specializations at `dalekHookStack` (`5120`), `pqxdhHookStack` (`4096`), and `pqxdhHookStackExt` (`16384`) -/

theorem isCanonical_ext_dalek_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec dalekHookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec dalekHookStack))) :
    subroutine_ok callerProg (lsmpl.base 202)
      (libsignalSessionLib.withCodeLoaded lsmpl (ecPubKeyIsCanonicalCallSpecAt dalekHookStack P)) :=
  isCanonical_ext_placed_ok_at_cl (by decide) hisCanon hcurve hmontHook htorsHook
theorem isCanonical_ext_dalek_vm_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec dalekHookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym
      (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec dalekHookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt dalekHookStack P))) :=
  isCanonical_ext_vm_placed_ok_at_cl (by decide) hisCanon hcurve hmontHook htorsHook
theorem isCanonical_ext_pqxdh_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec pqxdhHookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec pqxdhHookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpec P)) :=
  isCanonical_ext_placed_ok_at_cl (hookStack := pqxdhHookStack) (by decide) hisCanon hcurve hmontHook htorsHook
theorem isCanonical_ext_pqxdhExt_of_dalek_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec dalekHookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec dalekHookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (CryptoVerification.E2E.Pqxdh.Shared.ecPubKeyIsCanonicalCallSpecExt P)) :=
  isCanonical_ext_placed_ok_at_cl (hookStack := pqxdhHookStackExt) (by decide) hisCanon hcurve
    (hookSat_dalekMontToEdExtSpec_mono (by decide) (by decide) hmontHook)
    (hookSat_dalekTorsionFreeExtSpec_mono (by decide) (by decide) htorsHook)

/-! ### Closed `DalekPrimsSound` & `dalekPrimsRef` Corollaries (`modelPrims`) -/

theorem isCanonical_ext_modelPrims_of_sound_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩)) :=
  isCanonical_ext_placed_ok_at hstack
    (modelPrims_isCanonicalEC_eq_isCanonicalRef X ⟨C, pqxdhPrimsOfHooks Qh D⟩)
    (isCanonicalCurveSound_modelPrims_of_sound hD X C Qh) hmontHook htorsHook
theorem isCanonical_ext_modelPrims_of_sound_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (ecPubKeyIsCanonicalCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))) :=
  full_ls_subroutine_ok_of_plain (j := 202)
    (isCanonical_ext_modelPrims_of_sound_placed_ok_at hstack hD X C Qh hmontHook htorsHook)
theorem isCanonical_ext_modelPrims_of_sound_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩)))) :=
  isCanonical_ext_vm_placed_ok_at_cl hstack
    (modelPrims_isCanonicalEC_eq_isCanonicalRef X ⟨C, pqxdhPrimsOfHooks Qh D⟩)
    (isCanonicalCurveSound_modelPrims_of_sound hD X C Qh) hmontHook htorsHook
theorem isCanonical_ext_dalekPrimsRef_placed_ok_at [LibsignalFullPlacement]
    {hookStack : Nat} {H : LibsignalHooks} (hstack : hookStack + 400 ≤ 2 ^ 64)
    (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok ((blkPC_202).rebase (blkPl_202).base H) (blkPl_202).base
      (ecPubKeyIsCanonicalCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩)) :=
  isCanonical_ext_modelPrims_of_sound_placed_ok_at hstack dalekPrimsRef_sound X C Qh hmontHook htorsHook
theorem isCanonical_ext_dalekPrimsRef_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hstack : hookStack + 400 ≤ 2 ^ 64) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (ecPubKeyIsCanonicalCallSpecAt hookStack (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))) :=
  isCanonical_ext_modelPrims_of_sound_placed_ok_at_cl hstack dalekPrimsRef_sound X C Qh hmontHook htorsHook
theorem isCanonical_ext_dalekPrimsRef_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hstack : hookStack + 400 ≤ 2 ^ 64) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalCallSpecAt hookStack
        (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩)))) :=
  isCanonical_ext_modelPrims_of_sound_vm_placed_ok_at_cl hstack dalekPrimsRef_sound X C Qh hmontHook htorsHook

/-! ### `Initiator.Primitives` (`ResponderCore` / `AcceptBudget`) & `withAlloc` Corollaries -/

theorem ecPubKeyIsCanonical_ext_responder_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec hookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec hookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (ecPubKeyIsCanonicalResponderCallSpecAt hookStack P)) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  exact (isCanonical_ext_placed_ok_at_cl (P := toSignalPqxdhPrimitives P)
    hstack hisCanon hcurve hmontHook htorsHook).mono_outcome ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp
    fun _ hout => hout
theorem ecPubKeyIsCanonical_ext_responder_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalResponderCallSpecAt hookStack P))) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  exact (isCanonical_ext_vm_placed_ok_at_cl (P := toSignalPqxdhPrimitives P)
    hstack hisCanon hcurve hmontHook htorsHook).mono_outcome ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp
    fun _ hout => hout
theorem ecPubKeyIsCanonical_ext_responder_keepsFs_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (keepsFs (withVmPreserved (ecPubKeyIsCanonicalResponderCallSpecAt hookStack P)))) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  exact (isCanonical_ext_keepsFs_vm_placed_ok_at_cl (P := toSignalPqxdhPrimitives P)
    hstack hisCanon hcurve hmontHook htorsHook).mono_outcome ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp
    fun _ hout => hout

/-- Variant of `FullPlacementCorollaries.ecPubKeyIsCanonical_placed_ok_cl` discharged from extended-Edwards hooks. -/
theorem ecPubKeyIsCanonical_ext_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (dalekMontToEdExtSpec pqxdhHookStack)))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (dalekTorsionFreeExtSpec pqxdhHookStack))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (CryptoVerification.E2E.Pqxdh.ResponderCore.ecPubKeyIsCanonicalCallSpec P)) :=
  ecPubKeyIsCanonical_ext_responder_placed_ok_at_cl (hookStack := pqxdhHookStack) (by decide)
    hisCanon hcurve hmontHook htorsHook
/-- Variant of `FullPlacementCorollariesBudget.ecPubKeyIsCanonical_placed_ok_cl` discharged from extended-Edwards hooks. -/
theorem ecPubKeyIsCanonical_ext_budget_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec pqxdhHookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym
      (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec pqxdhHookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget.ecPubKeyIsCanonicalCallSpec P)) :=
  ecPubKeyIsCanonical_ext_responder_vm_placed_ok_at_cl (hookStack := pqxdhHookStack) (by decide)
    hisCanon hcurve hmontHook htorsHook
/-- `AcceptBudget.ecPubKeyIsCanonicalCallSpecExt P` discharged from `dalekHookStack` hooks. -/
theorem ecPubKeyIsCanonical_ext_budget_ext_of_dalek_placed_ok_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {P : CryptoVerification.E2E.Pqxdh.Initiator.Primitives}
    {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) k)
    (hcurve : IsCanonicalCurveSound (toSignalPqxdhPrimitives P))
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec dalekHookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym
      (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec dalekHookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptBudget.ecPubKeyIsCanonicalCallSpecExt P)) :=
  ecPubKeyIsCanonical_ext_responder_vm_placed_ok_at_cl (hookStack := pqxdhHookStackExt) (by decide)
    hisCanon hcurve (hookSat_dalekMontToEdExtVmSpec_mono (by decide) (by decide) hmontHook)
    (hookSat_dalekTorsionFreeExtVmSpec_mono (by decide) (by decide) htorsHook)
/-- Closed `DalekPrimsSound D` specialization on `ofSignalPqxdhPrimitives (modelPrims ...)`. -/
theorem ecPubKeyIsCanonical_ext_responder_of_sound_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {D : DalekPrims} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hD : DalekPrimsSound D) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalResponderCallSpecAt hookStack
        (ofSignalPqxdhPrimitives (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh D⟩))))) := by
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre hsp => ?_
  exact (isCanonical_ext_modelPrims_of_sound_vm_placed_ok_at_cl hstack hD X C Qh hmontHook htorsHook).mono_outcome
    ⟨g.keyPtr, g.keyBytes⟩ R s0 hpc hrun hpre hsp fun _ hout => hout
/-- Closed `dalekPrimsRef` specialization on `ofSignalPqxdhPrimitives (modelPrims ...)`. -/
theorem ecPubKeyIsCanonical_ext_responder_dalekPrimsRef_vm_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i hookStack : Nat} {H : LibsignalHooks} [IsLsBlockProg callerProg i H]
    (hstack : hookStack + 400 ≤ 2 ^ 64) (X : UnreachedPqxdhPrimitives) (C : Crypto) (Qh : PqxdhHookPrims)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withVmPreserved (ecPubKeyIsCanonicalResponderCallSpecAt hookStack
        (ofSignalPqxdhPrimitives (modelPrims X ⟨C, pqxdhPrimsOfHooks Qh dalekPrimsRef⟩))))) :=
  ecPubKeyIsCanonical_ext_responder_of_sound_vm_placed_ok_at_cl
    hstack dalekPrimsRef_sound X C Qh hmontHook htorsHook

/-- Lift any `subroutine_ok prog entry (withVmPreserved spec)` to `withAlloc A lim spec`. -/
theorem subroutine_ok_withAlloc_of_withVmPreserved {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry (withVmPreserved spec)) :
    subroutine_ok prog entry (withAlloc (M := M) A lim spec) := by
  refine SpecSimulates.subroutine_ok (fun ⟨x, st⟩ R s0 hpre => ?_) h
  dsimp only [withAlloc, withVmPreserved] at hpre; rw [sepConj_assoc] at hpre
  refine ⟨x, A.pool lim st s0 ∗ R, hpre, fun sf hout => ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩; dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; rcases hpost with ⟨hvm, hrest⟩
    dsimp only [withAlloc]; rw [A.pool_transport lim st s0 sf hvm, sepConj_assoc]; exact hrest
  · exact Or.inr (Or.inl ⟨hpan, Satisfies.drop_mid hp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, Satisfies.drop_mid he⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, Satisfies.drop_mid ho⟩))

/-- Lift `isCanonical_ext_vm_placed_ok_at_cl` directly to `withAlloc A lim` inside `withCodeLoaded`. -/
theorem isCanonical_ext_withAlloc_placed_ok_at_cl [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {hookStack : Nat} {P : SignalPqxdh.Primitives} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hstack : hookStack + 400 ≤ 2 ^ 64)
    (hisCanon : ∀ k, P.isCanonicalEC k = SignalPqxdh.isCanonicalRef P k) (hcurve : IsCanonicalCurveSound P)
    (hmontHook : HookSat H lsDalekMontToEdSym (withLsRet (withVmPreserved (dalekMontToEdExtSpec hookStack))))
    (htorsHook : HookSat H lsDalekTorsionFreeSym (withLsRet (withVmPreserved (dalekTorsionFreeExtSpec hookStack)))) :
    subroutine_ok callerProg (lsmpl.base 202) (libsignalSessionLib.withCodeLoaded lsmpl
      (withAlloc (M := M) A lim (ecPubKeyIsCanonicalCallSpecAt hookStack P))) :=
  full_ls_subroutine_ok_of_plain (j := 202) (subroutine_ok_withAlloc_of_withVmPreserved A lim
    (isCanonical_ext_vm_placed_ok_at hstack hisCanon hcurve hmontHook htorsHook))

end LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202

