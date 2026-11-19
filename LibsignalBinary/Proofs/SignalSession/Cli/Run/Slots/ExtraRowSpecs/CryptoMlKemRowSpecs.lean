/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTracedPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon

/-!
# `libcrux_ml_kem` Consumer `HookOk` Row Arms & Pure Fallbacks (`ExtraRowSpecs.CryptoMlKemRowSpecs`)

Consumer-contract leaf module for the 7 linked `libcrux_ml_kem` symbols:
- Hook #1 (`kemEncapsName`, block 24, tight stack `34,240` B): `KemEncapsRowSpecAt` / `KemEncapsRowSpec`
- Hook #2 (`kemDecapsName`, block 23, tight stack `35,968` B): `KemDecapsRowSpecAt` / `KemDecapsRowSpec`
- Hook #3 (`mlkemFromSeedName`, block 10, tight stack `33,664` B): `MlkemFromSeedRowSpecAt` / `MlkemFromSeedRowSpec`
- Hook #4 (`mlkemEncaps1Name`, block 19, tight stack `18,304` B): `MlkemEncaps1RowSpecAt` / `MlkemEncaps1RowSpec`
- Hook #5 (`mlkemEncaps2Name`, block 20, tight stack `6,128` B): `MlkemEncaps2RowSpecAt` / `MlkemEncaps2RowSpec`
- Hook #6 (`mlkemDecapsName`, block 22, tight stack `26,960` B): `MlkemDecapsRowSpecAt` / `MlkemDecapsRowSpec`
- Hook #7 (`mlkemValidatePkName`, block 21, tight stack `5,824` B): `MlkemValidatePkRowSpecAt` / `MlkemValidatePkRowSpec`

Provides:
1. Stack-monotonicity (`s₁ ≤ s₂ ≤ 2 ^ 64`), randomness-weakening (`kemEncapsPreservedAtSpec` →
   `kemEncapsAtSpec`), and `PqxdhPrims` / `MlKem` equation-transport `SpecSimulates` bridges.
2. `DalekLsRowTuple`-packaged row predicates at arbitrary `stk` and at `mlkemHookStack = 65536`,
   together with `extHookStack = 16384` specializations for Hooks #5 and #7 (`6128, 5824 ≤ 16384`).
3. Pure fallback hooks (`*Fallback`) instantiating the `PqxdhHooksCommon` definitions on
   `kyber1024EncapsVec`, `kyber1024DecapsVec`, and `mlkem768Incremental`, with `PureFallbackPreserved`,
   `HookFsTraced IsFsC`, `HookOk *Fallback (keepsFs (*AtSpec stk …))` for arbitrary `stk`, and
   `DalekLsRowTuple` instances.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (
  PqxdhPrims Sha512State kemDecapsHook kemEncapsHook mlkemDecapsHook mlkemEncaps1Hook
  mlkemEncaps2Hook mlkemFromSeedHook mlkemValidatePkHook readVecN
)
open CryptoVerification.E2E.Pqxdh (readVecN_eq_of_pointsToBytes)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalSession.NonVacuityWitness (readReg64_setPC_writeReg64_x0)
open CryptoVerification.LibsignalSpqrV1 (
  MlKem MlkemDecapsCall MlkemEncaps1Call MlkemEncaps2Call MlkemFromSeedCall MlkemValidatePkCall
  mlkemDecapsSpec mlkemEncaps1Spec mlkemEncaps2Spec mlkemFromSeedSpec mlkemValidatePkSpec
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open CryptoVerification.SignalSession.CliExt (kemDecapsSpec kemEncapsSpec)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.Fine (
  hookOk_withVmPreserved mlkemDecapsHook_vmPreserved mlkemEncaps1Hook_vmPreserved
  mlkemEncaps2Hook_vmPreserved mlkemFromSeedHook_vmPreserved mlkemValidatePkHook_vmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.ConsumerBridgesBase (
  kemDecapsAtSpec kemDecapsAtSpec_extHookStack kemEncapsAtSpec kemEncapsAtSpec_extHookStack
  kemEncapsPreservedAtSpec mlkemDecapsAtSpec mlkemDecapsAtSpec_extHookStack mlkemEncaps1AtSpec
  mlkemEncaps1AtSpec_extHookStack mlkemEncaps2AtSpec mlkemEncaps2AtSpec_extHookStack
  mlkemFromSeedAtSpec mlkemFromSeedAtSpec_extHookStack mlkemValidatePkAtSpec
  mlkemValidatePkAtSpec_extHookStack
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec kyber1024EncapsVec
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges (
  specSimulates_keepsFs specSimulates_withVmPreserved
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (PureFallbackPreserved)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204 (stackAt_split_low)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs withStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc (withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet (
  hookOk_withLsRet specSimulates_withLsRet withLsRet
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs (
  DalekLsRowTuple hookOk_of_simulates hookOk_withLsRet_of_simulates rowTuple_of_keepsFs_vm
)

attribute [local irreducible] kyber1024EncapsVec kyber1024DecapsVec mlkem768Incremental

/-! ## 1. Stack Constants & Concrete `PqxdhPrims` Instantiations -/

/-- Default CLI hook stack budget (`65,536` B), dominating all 7 ML-KEM tight
    frame bounds (`max = 35,968` B). -/
@[expose] def mlkemHookStack : Nat := 65536

@[expose] def kemEncapsTightStack : Nat := 34240
@[expose] def kemDecapsTightStack : Nat := 35968
@[expose] def mlkemFromSeedTightStack : Nat := 33664
@[expose] def mlkemEncaps1TightStack : Nat := 18304
@[expose] def mlkemEncaps2TightStack : Nat := 6128
@[expose] def mlkemDecapsTightStack : Nat := 26960
@[expose] def mlkemValidatePkTightStack : Nat := 5824

/-- Concrete `PqxdhPrims` bundle pairing an arbitrary `F512` compression function with the real
    `libcrux_ml_kem` specifications `kyber1024EncapsVec`, `kyber1024DecapsVec`, and
    `mlkem768Incremental`. -/
@[expose] noncomputable def kyber1024Prims
    (F512 : Sha512State → List (BitVec 8) → Sha512State) : PqxdhPrims where
  F512 := F512
  encaps := kyber1024EncapsVec
  decaps := kyber1024DecapsVec
  K := mlkem768Incremental

/-- Canonical `PqxdhPrims` witness for `F512`-independent Kyber-1024 row specs. -/
@[expose] noncomputable def kyber1024Prims₀ : PqxdhPrims :=
  kyber1024Prims (fun st _ => st)

theorem kyber1024Prims₀_encaps : kyber1024Prims₀.encaps = kyber1024EncapsVec := by
  unfold kyber1024Prims₀ kyber1024Prims; rfl

theorem kyber1024Prims₀_decaps : kyber1024Prims₀.decaps = kyber1024DecapsVec := by
  unfold kyber1024Prims₀ kyber1024Prims; rfl

/-! ## 2. `SpecSimulates` Bridges (Stack Monotonicity, `rA` Weakening, & Equation Transport) -/

private theorem satisfies_stack_split_tail {m : Memory} {P R : SepProp} {sp : BitVec 64}
    {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    (m ⊨ (P ∗ stackAt sp s₂) ∗ R) ↔
      (m ⊨ (P ∗ stackAt sp s₁) ∗ (memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R)) := by
  rw [stackAt_split_low sp hle hb]
  exact (congrArg (m ⊨ ·) (by sep_ac_rfl)).to_iff

private theorem specSimulates_withStack_mono {α : Type} (core : Spec α) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64)
    (hpan : core.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : core.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : core.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withStack core s₁) (withStack core s₂) :=
  SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun x R s0 hpre =>
    ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R,
      (satisfies_stack_split_tail hle hb).mp hpre,
      fun _ _ _ hq => (satisfies_stack_split_tail hle hb).mpr hq⟩

theorem specSimulates_kemEncapsAtSpec_mono (Q : PqxdhPrims) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (kemEncapsAtSpec s₁ Q) (kemEncapsAtSpec s₂ Q) :=
  specSimulates_withStack_mono _ hle hb

theorem specSimulates_kemEncapsPreservedAtSpec_mono (Q : PqxdhPrims) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (kemEncapsPreservedAtSpec s₁ Q) (kemEncapsPreservedAtSpec s₂ Q) :=
  specSimulates_withStack_mono _ hle hb

theorem specSimulates_kemDecapsAtSpec_mono (Q : PqxdhPrims) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (kemDecapsAtSpec s₁ Q) (kemDecapsAtSpec s₂ Q) :=
  specSimulates_withStack_mono _ hle hb

theorem specSimulates_mlkemFromSeedAtSpec_mono (K : MlKem) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (mlkemFromSeedAtSpec s₁ K) (mlkemFromSeedAtSpec s₂ K) :=
  SpecSimulates.of_map fun x R s0 hpre => by
    refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
    · dsimp only [mlkemFromSeedAtSpec] at hpre ⊢
      rw [stackAt_split_low s0.sp hle hb] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [mlkemFromSeedAtSpec] at hpost ⊢
      rw [stackAt_split_low s0.sp hle hb]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem specSimulates_mlkemEncaps1AtSpec_mono (K : MlKem) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (mlkemEncaps1AtSpec s₁ K) (mlkemEncaps1AtSpec s₂ K) :=
  SpecSimulates.of_map fun x R s0 hpre => by
    refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
    · dsimp only [mlkemEncaps1AtSpec] at hpre ⊢
      rw [stackAt_split_low s0.sp hle hb] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [mlkemEncaps1AtSpec] at hpost ⊢
      rw [stackAt_split_low s0.sp hle hb]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem specSimulates_mlkemEncaps2AtSpec_mono (K : MlKem) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (mlkemEncaps2AtSpec s₁ K) (mlkemEncaps2AtSpec s₂ K) :=
  SpecSimulates.of_map fun x R s0 hpre => by
    refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
    · dsimp only [mlkemEncaps2AtSpec] at hpre ⊢
      rw [stackAt_split_low s0.sp hle hb] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [mlkemEncaps2AtSpec] at hpost ⊢
      rw [stackAt_split_low s0.sp hle hb]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem specSimulates_mlkemDecapsAtSpec_mono (K : MlKem) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (mlkemDecapsAtSpec s₁ K) (mlkemDecapsAtSpec s₂ K) :=
  SpecSimulates.of_map fun x R s0 hpre => by
    refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
    · dsimp only [mlkemDecapsAtSpec] at hpre ⊢
      rw [stackAt_split_low s0.sp hle hb] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [mlkemDecapsAtSpec] at hpost ⊢
      rw [stackAt_split_low s0.sp hle hb]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

theorem specSimulates_mlkemValidatePkAtSpec_mono (K : MlKem) {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) :
    SpecSimulates (mlkemValidatePkAtSpec s₁ K) (mlkemValidatePkAtSpec s₂ K) :=
  SpecSimulates.of_map fun x R s0 hpre => by
    refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R, ?_, fun sf _ _ hpost => ?_⟩
    · dsimp only [mlkemValidatePkAtSpec] at hpre ⊢
      rw [stackAt_split_low s0.sp hle hb] at hpre
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
    · dsimp only [mlkemValidatePkAtSpec] at hpost ⊢
      rw [stackAt_split_low s0.sp hle hb]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost

/-- Weakens `kemEncapsPreservedAtSpec` (which preserves `rA ↦ₛ rnd.toList`) to `kemEncapsAtSpec`
    (which weakens `rA` to `memRegion rA 32`). -/
theorem specSimulates_kemEncapsAtSpec_of_preserved (stk : Nat) (Q : PqxdhPrims) :
    SpecSimulates (kemEncapsPreservedAtSpec stk Q) (kemEncapsAtSpec stk Q) :=
  SpecSimulates.of_map fun ⟨pkA, pk, rA, rnd, ret⟩ R s0 hpre => by
    refine ⟨(pkA, pk, rA, rnd, ret), R, hpre, fun sf _ _ hpost => ?_⟩
    dsimp only [kemEncapsPreservedAtSpec, kemEncapsAtSpec, withStack] at hpost ⊢
    have hweak : rA ↦ₛ rnd.toList ⊢ memRegion rA 32 := by
      simpa only [rnd.toList_length] using pointsToBytes_entails_memRegion rA rnd.toList
    have hm1 : sf.mem ⊨ (rA ↦ₛ rnd.toList) ∗
        ((⌜sf.trace = s0.trace⌝ ∗ (pkA ↦ₛ pk.toList) ∗
          (ret ↦ₛ (Q.encaps pk rnd).1.toList) ∗
          ((ret + 1568#64) ↦ₛ (Q.encaps pk rnd).2.toList) ∗ stackAt s0.sp stk) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
    have hm2 := Satisfies.mono (sepConj_mono_left hweak) hm1
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2

theorem kemEncapsPreservedAtSpec_eq_of_encaps_eq (stk : Nat) {Q₁ Q₂ : PqxdhPrims}
    (h : Q₁.encaps = Q₂.encaps) :
    kemEncapsPreservedAtSpec stk Q₁ = kemEncapsPreservedAtSpec stk Q₂ := by
  unfold kemEncapsPreservedAtSpec; rw [h]

theorem kemEncapsAtSpec_eq_of_encaps_eq (stk : Nat) {Q₁ Q₂ : PqxdhPrims}
    (h : Q₁.encaps = Q₂.encaps) :
    kemEncapsAtSpec stk Q₁ = kemEncapsAtSpec stk Q₂ := by
  unfold kemEncapsAtSpec; rw [h]

theorem kemDecapsAtSpec_eq_of_decaps_eq (stk : Nat) {Q₁ Q₂ : PqxdhPrims}
    (h : Q₁.decaps = Q₂.decaps) :
    kemDecapsAtSpec stk Q₁ = kemDecapsAtSpec stk Q₂ := by
  unfold kemDecapsAtSpec; rw [h]

/-! ## 3. Pure Fallbacks (`*Fallback`), `PureFallbackPreserved`, & `HookOk` at Arbitrary `stk` -/

@[expose] noncomputable def kemEncapsFallback : State → State :=
  kemEncapsHook kyber1024EncapsVec

@[expose] noncomputable def kemDecapsFallback : State → State :=
  kemDecapsHook kyber1024DecapsVec

@[expose] noncomputable def mlkemFromSeedFallback : State → State :=
  mlkemFromSeedHook mlkem768Incremental

@[expose] noncomputable def mlkemEncaps1Fallback : State → State :=
  mlkemEncaps1Hook mlkem768Incremental

@[expose] noncomputable def mlkemEncaps2Fallback : State → State :=
  mlkemEncaps2Hook mlkem768Incremental

@[expose] noncomputable def mlkemDecapsFallback : State → State :=
  mlkemDecapsHook mlkem768Incremental

@[expose] noncomputable def mlkemValidatePkFallback : State → State :=
  mlkemValidatePkHook mlkem768Incremental

private theorem writeBytes_perm (m : Memory) :
    ∀ (a : BitVec 64) (bs : List (BitVec 8)) (p : BitVec 64),
      (m.writeBytes a bs).perm p = m.perm p
  | _, [], _ => rfl
  | a, b :: bs, p => by
    simp only [Memory.writeBytes]
    rw [writeBytes_perm (m.write8 a b) (a + 1#64) bs p, Memory.perm_write8]

theorem kemEncapsHook_vmPreserved
    (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
      List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32)
    (s : State) : VmPreserved s (kemEncapsHook encaps s) := by
  unfold kemEncapsHook returnToLinkRegister
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => ?_, fun _ _ _ => rfl⟩
  dsimp only [State.setPC, State.setMem]
  rw [writeBytes_perm, writeBytes_perm]

theorem kemDecapsHook_vmPreserved
    (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32)
    (s : State) : VmPreserved s (kemDecapsHook decaps s) := by
  unfold kemDecapsHook returnToLinkRegister
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun a => ?_, fun _ _ _ => rfl⟩
  dsimp only [State.setPC, State.setMem]
  rw [writeBytes_perm]

theorem kemEncapsFallback_preserved : PureFallbackPreserved kemEncapsFallback := by
  intro s; unfold kemEncapsFallback
  exact ⟨kemEncapsHook_vmPreserved kyber1024EncapsVec s, rfl, rfl, rfl, rfl⟩

theorem kemDecapsFallback_preserved : PureFallbackPreserved kemDecapsFallback := by
  intro s; unfold kemDecapsFallback
  exact ⟨kemDecapsHook_vmPreserved kyber1024DecapsVec s, rfl, rfl, rfl, rfl⟩

theorem mlkemFromSeedFallback_preserved : PureFallbackPreserved mlkemFromSeedFallback := by
  intro s; unfold mlkemFromSeedFallback
  exact ⟨mlkemFromSeedHook_vmPreserved mlkem768Incremental s, rfl, rfl, rfl, rfl⟩

theorem mlkemEncaps1Fallback_preserved : PureFallbackPreserved mlkemEncaps1Fallback := by
  intro s
  refine ⟨mlkemEncaps1Hook_vmPreserved mlkem768Incremental s, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold mlkemEncaps1Fallback mlkemEncaps1Hook retHook
    dsimp only
    split <;> (try split) <;> rfl

theorem mlkemEncaps2Fallback_preserved : PureFallbackPreserved mlkemEncaps2Fallback := by
  intro s; unfold mlkemEncaps2Fallback
  exact ⟨mlkemEncaps2Hook_vmPreserved mlkem768Incremental s, rfl, rfl, rfl, rfl⟩

theorem mlkemDecapsFallback_preserved : PureFallbackPreserved mlkemDecapsFallback := by
  intro s; unfold mlkemDecapsFallback
  exact ⟨mlkemDecapsHook_vmPreserved mlkem768Incremental s, rfl, rfl, rfl, rfl⟩

theorem mlkemValidatePkFallback_preserved : PureFallbackPreserved mlkemValidatePkFallback := by
  intro s
  refine ⟨mlkemValidatePkHook_vmPreserved mlkem768Incremental s, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold mlkemValidatePkFallback mlkemValidatePkHook retHook
    cases s; rfl

theorem kemEncapsFallback_fsT : HookFsTraced IsFsC kemEncapsFallback :=
  fun s => FsTraced.of_eq (kemEncapsFallback_preserved s).2.2.1
    (congrArg (·.files) (kemEncapsFallback_preserved s).2.1)

theorem kemDecapsFallback_fsT : HookFsTraced IsFsC kemDecapsFallback :=
  fun s => FsTraced.of_eq (kemDecapsFallback_preserved s).2.2.1
    (congrArg (·.files) (kemDecapsFallback_preserved s).2.1)

theorem mlkemFromSeedFallback_fsT : HookFsTraced IsFsC mlkemFromSeedFallback :=
  fun s => FsTraced.of_eq (mlkemFromSeedFallback_preserved s).2.2.1
    (congrArg (·.files) (mlkemFromSeedFallback_preserved s).2.1)

theorem mlkemEncaps1Fallback_fsT : HookFsTraced IsFsC mlkemEncaps1Fallback :=
  fun s => FsTraced.of_eq (mlkemEncaps1Fallback_preserved s).2.2.1
    (congrArg (·.files) (mlkemEncaps1Fallback_preserved s).2.1)

theorem mlkemEncaps2Fallback_fsT : HookFsTraced IsFsC mlkemEncaps2Fallback :=
  fun s => FsTraced.of_eq (mlkemEncaps2Fallback_preserved s).2.2.1
    (congrArg (·.files) (mlkemEncaps2Fallback_preserved s).2.1)

theorem mlkemDecapsFallback_fsT : HookFsTraced IsFsC mlkemDecapsFallback :=
  fun s => FsTraced.of_eq (mlkemDecapsFallback_preserved s).2.2.1
    (congrArg (·.files) (mlkemDecapsFallback_preserved s).2.1)

theorem mlkemValidatePkFallback_fsT : HookFsTraced IsFsC mlkemValidatePkFallback :=
  fun s => FsTraced.of_eq (mlkemValidatePkFallback_preserved s).2.2.1
    (congrArg (·.files) (mlkemValidatePkFallback_preserved s).2.1)

/-- `kemEncapsHook Q.encaps` satisfies `keepsFs (kemEncapsPreservedAtSpec stk Q)` at any stack `stk`. -/
theorem kemEncapsHook_preservedAt_keepsFs_ok (Q : PqxdhPrims) (stk : Nat) :
    HookOk (kemEncapsHook Q.encaps) (keepsFs (kemEncapsPreservedAtSpec stk Q)) := by
  rintro ⟨pkA, pk, rA, rnd, ret⟩ R s0 hrun hpre _hsp
  dsimp only [keepsFs, kemEncapsPreservedAtSpec, withStack] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hmem_pk : s0.mem ⊨ (pkA ↦ₛ pk.toList) ∗
      ((rA ↦ₛ rnd.toList) ∗ memRegion ret 1600 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hpk : readVecN s0.mem pkA 1568 = pk := readVecN_eq_of_pointsToBytes hmem_pk
  have hmem_rnd : s0.mem ⊨ (rA ↦ₛ rnd.toList) ∗
      ((pkA ↦ₛ pk.toList) ∗ memRegion ret 1600 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hrnd : readVecN s0.mem rA 32 = rnd := readVecN_eq_of_pointsToBytes hmem_rnd
  let ct := (Q.encaps pk rnd).1.toList
  let ss := (Q.encaps pk rnd).2.toList
  have hct_len : ct.length = 1568 := List.Vector.toList_length _
  have hss_len : ss.length = 32 := List.Vector.toList_length _
  have hsplit : memRegion ret 1600 = memRegion ret 1568 ∗ memRegion (ret + 0x620#64) 32 :=
    memRegion_split' (b := ret) (n := 1568) (k := 32) (b' := ret + 0x620#64)
      rfl (by bv_omega) (by decide)
  have hmem1 : s0.mem ⊨ memRegion ret ct.length ∗
      (memRegion (ret + 0x620#64) 32 ∗ (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗
        stackAt s0.sp stk ∗ R) := by
    rw [hct_len]
    rw [hsplit] at hmem
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf1 := keepsFrozen_writeBytes_of_memRegion ct (by omega) hmem1
  have hw1 := satisfies_writeBytes ct (by omega) hmem1
  have hmem2 : s0.mem.writeBytes ret ct ⊨ memRegion (ret + 0x620#64) ss.length ∗
      ((ret ↦ₛ ct) ∗ (pkA ↦ₛ pk.toList) ∗ (rA ↦ₛ rnd.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [hss_len]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw1
  have hkf2 := keepsFrozen_writeBytes_of_memRegion ss (by omega) hmem2
  have hw2 := satisfies_writeBytes ss (by omega) hmem2
  unfold kemEncapsHook returnToLinkRegister
  rw [hx0, hx1, hx8, hpk, hrnd]
  refine ⟨hkf1.trans hkf2, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [keepsFs, kemEncapsPreservedAtSpec, withStack, State.setPC, State.setMem]
  have hoff : ret + 1568#64 = ret + 0x620#64 := rfl
  rw [hoff]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw2⟩

/-- `kemDecapsHook Q.decaps` satisfies `keepsFs (kemDecapsAtSpec stk Q)` at any stack `stk`. -/
theorem kemDecapsHook_at_keepsFs_ok (Q : PqxdhPrims) (stk : Nat) :
    HookOk (kemDecapsHook Q.decaps) (keepsFs (kemDecapsAtSpec stk Q)) := by
  rintro ⟨skA, sk, ctA, ct, ret⟩ R s0 hrun hpre _hsp
  dsimp only [keepsFs, kemDecapsAtSpec, withStack] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8⟩, hmem⟩
  have hmem_sk : s0.mem ⊨ (skA ↦ₛ sk.toList) ∗
      ((ctA ↦ₛ ct.toList) ∗ memRegion ret 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hsk : readVecN s0.mem skA 3168 = sk := readVecN_eq_of_pointsToBytes hmem_sk
  have hmem_ct : s0.mem ⊨ (ctA ↦ₛ ct.toList) ∗
      ((skA ↦ₛ sk.toList) ∗ memRegion ret 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hct : readVecN s0.mem ctA 1568 = ct := readVecN_eq_of_pointsToBytes hmem_ct
  let ss := (Q.decaps sk ct).toList
  have hss_len : ss.length = 32 := List.Vector.toList_length _
  have hmem_ret : s0.mem ⊨ memRegion ret ss.length ∗
      ((skA ↦ₛ sk.toList) ∗ (ctA ↦ₛ ct.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [hss_len]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf := keepsFrozen_writeBytes_of_memRegion ss (by omega) hmem_ret
  have hw := satisfies_writeBytes ss (by omega) hmem_ret
  unfold kemDecapsHook returnToLinkRegister
  rw [hx0, hx1, hx8, hsk, hct]
  refine ⟨hkf, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
  dsimp only [keepsFs, kemDecapsAtSpec, withStack, State.setPC, State.setMem]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw⟩

/-- `mlkemFromSeedHook K` satisfies `keepsFs (mlkemFromSeedAtSpec stk K)` at any stack `stk`. -/
theorem mlkemFromSeedHook_at_keepsFs_ok (K : MlKem) (stk : Nat) :
    HookOk (mlkemFromSeedHook K) (keepsFs (mlkemFromSeedAtSpec stk K)) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  dsimp only [keepsFs, mlkemFromSeedAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8⟩, hmem⟩
  have hseed : readVecN s0.mem x.seedA 64 = x.seed := readVecN_eq_of_pointsToBytes hmem
  let dk := (K.fromSeed x.seed).2.2.toList
  have hdk_len : dk.length = 2400 := List.Vector.toList_length _
  have hmem_kp : s0.mem ⊨ memRegion x.kpA dk.length ∗
      ((x.seedA ↦ₛ x.seed.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [hdk_len]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf := keepsFrozen_writeBytes_of_memRegion dk (by omega) hmem_kp
  have hw := satisfies_writeBytes dk (by omega) hmem_kp
  dsimp only [mlkemFromSeedHook, retHook]
  rw [hx0, hx8, hseed]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [keepsFs, mlkemFromSeedAtSpec, State.setMem, State.setPC]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw⟩

/-- `mlkemEncaps1Hook K` satisfies `keepsFs (mlkemEncaps1AtSpec stk K)` at any stack `stk`. -/
theorem mlkemEncaps1Hook_at_keepsFs_ok (K : MlKem) (stk : Nat) :
    HookOk (mlkemEncaps1Hook K) (keepsFs (mlkemEncaps1AtSpec stk K)) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  dsimp only [keepsFs, mlkemEncaps1AtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, hmem⟩
  obtain ⟨_, hread_hdr⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
  have hmem_rand : s0.mem ⊨ (x.randA ↦ₛ x.rand.toList) ∗
      ((x.hdrA ↦ₛ x.hdr) ∗ memRegion x.ret 961 ∗ memRegion x.esA 2080 ∗
        memRegion x.ssA 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hrand : readVecN s0.mem x.randA 32 = x.rand := readVecN_eq_of_pointsToBytes hmem_rand
  have hlen_ok : (decide ((s0.readReg64 .x4).toNat < 2080) ||
      decide ((s0.readReg64 .x6).toNat < 32)) = false := by
    rw [hx4, hx6]; decide
  dsimp only [mlkemEncaps1Hook, retHook]
  simp only [hlen_ok, Bool.false_eq_true, ↓reduceIte]
  rw [hx8, hx0, hx1, hread_hdr, hx2, hrand, hx3, hx5]
  rcases henc : K.encaps1 x.hdr x.rand with _ | ⟨ct1, es, ss⟩
  · dsimp only
    have hsplit : memRegion x.ret 961 =
        memRegion x.ret 1 ∗
          ((∃∗ err : BitVec 8, (x.ret + 1#64) ↦₈ err) ∗ memRegion (x.ret + 2#64) 959) := by
      rw [memRegion_split' (n := 1) (k := 960) rfl rfl (by decide),
        memRegion_split' (b := x.ret + 1#64) (n := 1) (k := 959) (b' := x.ret + 2#64)
          rfl (by bv_omega) (by decide),
        memRegion_one (x.ret + 1#64)]
    have hmem_ret : s0.mem ⊨ memRegion x.ret ([1#8] : List (BitVec 8)).length ∗
        (((∃∗ err : BitVec 8, (x.ret + 1#64) ↦₈ err) ∗ memRegion (x.ret + 2#64) 959) ∗
          (x.hdrA ↦ₛ x.hdr) ∗ (x.randA ↦ₛ x.rand.toList) ∗
          memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗ stackAt s0.sp stk ∗ R) := by
      change s0.mem ⊨ memRegion x.ret 1 ∗ _
      rw [hsplit] at hmem
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hkf := keepsFrozen_writeBytes_of_memRegion [1#8] (by decide) hmem_ret
    have hw := satisfies_writeBytes [1#8] (by decide) hmem_ret
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp] at hw
    refine ⟨hkf, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [keepsFs, mlkemEncaps1AtSpec, State.setMem, State.setPC]
    rw [henc]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw⟩
  · dsimp only
    let retBs : List (BitVec 8) := 0#8 :: ct1.toList
    have hret_len : retBs.length = 961 := by simp [retBs, List.Vector.toList_length]
    have hes_len : es.toList.length = 2080 := List.Vector.toList_length _
    have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
    have hmem1 : s0.mem ⊨ memRegion x.ret retBs.length ∗
        (memRegion x.esA 2080 ∗ memRegion x.ssA 32 ∗ (x.hdrA ↦ₛ x.hdr) ∗
          (x.randA ↦ₛ x.rand.toList) ∗ stackAt s0.sp stk ∗ R) := by
      rw [hret_len]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
    have hkf1 := keepsFrozen_writeBytes_of_memRegion retBs (by omega) hmem1
    have hw1 := satisfies_writeBytes retBs (by omega) hmem1
    have hmem2 : s0.mem.writeBytes x.ret retBs ⊨ memRegion x.esA es.toList.length ∗
        ((x.ret ↦ₛ retBs) ∗ memRegion x.ssA 32 ∗ (x.hdrA ↦ₛ x.hdr) ∗
          (x.randA ↦ₛ x.rand.toList) ∗ stackAt s0.sp stk ∗ R) := by
      rw [hes_len]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw1
    have hkf2 := keepsFrozen_writeBytes_of_memRegion es.toList (by omega) hmem2
    have hw2 := satisfies_writeBytes es.toList (by omega) hmem2
    have hmem3 : (s0.mem.writeBytes x.ret retBs).writeBytes x.esA es.toList ⊨
        memRegion x.ssA ss.toList.length ∗
          ((x.ret ↦ₛ retBs) ∗ (x.esA ↦ₛ es.toList) ∗ (x.hdrA ↦ₛ x.hdr) ∗
            (x.randA ↦ₛ x.rand.toList) ∗ stackAt s0.sp stk ∗ R) := by
      rw [hss_len]
      exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw2
    have hkf3 := keepsFrozen_writeBytes_of_memRegion ss.toList (by omega) hmem3
    have hw3 := satisfies_writeBytes ss.toList (by omega) hmem3
    have hret_cons : (x.ret ↦ₛ retBs) = (x.ret ↦₈ 0#8) ∗ ((x.ret + 1#64) ↦ₛ ct1.toList) := by
      dsimp only [retBs]
      rw [pointsToBytes_cons]
    rw [hret_cons] at hw3
    refine ⟨(hkf1.trans hkf2).trans hkf3, rfl, hrun,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    dsimp only [keepsFs, mlkemEncaps1AtSpec, State.setMem, State.setPC]
    rw [henc]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw3⟩

/-- `mlkemEncaps2Hook K` satisfies `keepsFs (mlkemEncaps2AtSpec stk K)` at any stack `stk`. -/
theorem mlkemEncaps2Hook_at_keepsFs_ok (K : MlKem) (stk : Nat) :
    HookOk (mlkemEncaps2Hook K) (keepsFs (mlkemEncaps2AtSpec stk K)) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  dsimp only [keepsFs, mlkemEncaps2AtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1⟩, hmem⟩
  have hmem_es : s0.mem ⊨ (x.esA ↦ₛ x.es.toList) ∗
      ((x.ekA ↦ₛ x.ek.toList) ∗ memRegion x.ret 128 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hes : readVecN s0.mem x.esA 2080 = x.es := readVecN_eq_of_pointsToBytes hmem_es
  have hmem_ek : s0.mem ⊨ (x.ekA ↦ₛ x.ek.toList) ∗
      ((x.esA ↦ₛ x.es.toList) ∗ memRegion x.ret 128 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hek : readVecN s0.mem x.ekA 1152 = x.ek := readVecN_eq_of_pointsToBytes hmem_ek
  let ct2 := (K.encaps2 x.es x.ek).toList
  have hct2_len : ct2.length = 128 := List.Vector.toList_length _
  have hmem_ret : s0.mem ⊨ memRegion x.ret ct2.length ∗
      ((x.esA ↦ₛ x.es.toList) ∗ (x.ekA ↦ₛ x.ek.toList) ∗ stackAt s0.sp stk ∗ R) := by
    rw [hct2_len]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf := keepsFrozen_writeBytes_of_memRegion ct2 (by omega) hmem_ret
  have hw := satisfies_writeBytes ct2 (by omega) hmem_ret
  dsimp only [mlkemEncaps2Hook, retHook]
  rw [hx8, hx0, hx1, hes, hek]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [keepsFs, mlkemEncaps2AtSpec, State.setMem, State.setPC]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw⟩

/-- `mlkemDecapsHook K` satisfies `keepsFs (mlkemDecapsAtSpec stk K)` at any stack `stk`. -/
theorem mlkemDecapsHook_at_keepsFs_ok (K : MlKem) (stk : Nat) :
    HookOk (mlkemDecapsHook K) (keepsFs (mlkemDecapsAtSpec stk K)) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  dsimp only [keepsFs, mlkemDecapsAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2⟩, hmem⟩
  have hmem_dk : s0.mem ⊨ (x.dkA ↦ₛ x.dk.toList) ∗
      ((x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
        memRegion x.ret 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hdk : readVecN s0.mem x.dkA 2400 = x.dk := readVecN_eq_of_pointsToBytes hmem_dk
  have hmem_ct1 : s0.mem ⊨ (x.ct1A ↦ₛ x.ct1.toList) ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
        memRegion x.ret 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hct1 : readVecN s0.mem x.ct1A 960 = x.ct1 := readVecN_eq_of_pointsToBytes hmem_ct1
  have hmem_ct2 : s0.mem ⊨ (x.ct2A ↦ₛ x.ct2.toList) ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗
        memRegion x.ret 32 ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hct2 : readVecN s0.mem x.ct2A 128 = x.ct2 := readVecN_eq_of_pointsToBytes hmem_ct2
  let ss := (K.decaps x.dk x.ct1 x.ct2).toList
  have hss_len : ss.length = 32 := List.Vector.toList_length _
  have hmem_ret : s0.mem ⊨ memRegion x.ret ss.length ∗
      ((x.dkA ↦ₛ x.dk.toList) ∗ (x.ct1A ↦ₛ x.ct1.toList) ∗ (x.ct2A ↦ₛ x.ct2.toList) ∗
        stackAt s0.sp stk ∗ R) := by
    rw [hss_len]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  have hkf := keepsFrozen_writeBytes_of_memRegion ss (by omega) hmem_ret
  have hw := satisfies_writeBytes ss (by omega) hmem_ret
  dsimp only [mlkemDecapsHook, retHook]
  rw [hx8, hx0, hx1, hx2, hdk, hct1, hct2]
  refine ⟨hkf, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [keepsFs, mlkemDecapsAtSpec, State.setMem, State.setPC]
  simp only [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨trivial, trivial, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hw⟩

/-- `mlkemValidatePkHook K` satisfies `keepsFs (mlkemValidatePkAtSpec stk K)` at any stack `stk`. -/
theorem mlkemValidatePkHook_at_keepsFs_ok (K : MlKem) (stk : Nat) :
    HookOk (mlkemValidatePkHook K) (keepsFs (mlkemValidatePkAtSpec stk K)) := by
  refine retHook_ok fun x R s0 hrun hpre _hsp => ?_
  dsimp only [keepsFs, mlkemValidatePkAtSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3⟩, hmem⟩
  obtain ⟨_, hread_hdr⟩ := (IsBlock.pointsToBytes x.hdrA x.hdr).read hmem
  have hmem_ek : s0.mem ⊨ (x.ekA ↦ₛ x.ek) ∗ ((x.hdrA ↦ₛ x.hdr) ∗ stackAt s0.sp stk ∗ R) :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem
  obtain ⟨_, hread_ek⟩ := (IsBlock.pointsToBytes x.ekA x.ek).read hmem_ek
  refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, hrun,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  dsimp only [keepsFs, mlkemValidatePkAtSpec, mlkemValidatePkHook, retHook]
  rw [hx0, hx1, hread_hdr, hx2, hx3, hread_ek, readReg64_setPC_writeReg64_x0]
  have hfs_eq : (s0.writeReg64 .x0 (if K.validPkBytes x.hdr x.ek then 0xff#64 else 0#64) |>.setPC
      (s0.readReg64 .lr)).fs = s0.fs := by cases s0; rfl
  have htr_eq : (s0.writeReg64 .x0 (if K.validPkBytes x.hdr x.ek then 0xff#64 else 0#64) |>.setPC
      (s0.readReg64 .lr)).trace = s0.trace := by cases s0; rfl
  have hmem_eq : (s0.writeReg64 .x0 (if K.validPkBytes x.hdr x.ek then 0xff#64 else 0#64)).mem =
      s0.mem := by cases s0; rfl
  rw [hmem_eq, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hfs_eq, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨?_, htr_eq⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  cases hval : K.validPkBytes x.hdr x.ek <;> decide

/-! ## 4. `DalekLsRowTuple` Row-Spec Definitions, Projections, & Pure Fallback Instances -/

section WithPlacement

variable [LibsignalPlacement]

/-- Generic `DalekLsRowTuple` builder for any pure fallback hook `f` with `PureFallbackPreserved f`
    and `HookOk f (keepsFs spec)`. -/
theorem rowTuple_of_fallback {α : Type} {f : State → State} {spec : Spec α}
    (hfb : PureFallbackPreserved f) (hok : HookOk f (keepsFs spec)) :
    DalekLsRowTuple f spec :=
  rowTuple_of_keepsFs_vm
    (hookOk_withLsRet (hookOk_withVmPreserved hok (fun s0 => (hfb s0).1)))

/-- Transport a `DalekLsRowTuple` along `SpecSimulates` + `SpecSimulates (keepsFs s₁) (keepsFs s₂)`. -/
theorem rowTuple_of_simulates {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (hsim : SpecSimulates s₁ s₂) (h : DalekLsRowTuple f s₁) :
    DalekLsRowTuple f s₂ :=
  rowTuple_of_keepsFs_vm
    (hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved (specSimulates_keepsFs hsim))
      h.keepsFsVm)

/-- Hook #1 (`kemEncapsName`, `B24`) row contract at stack `stk` (preserving `rA ↦ₛ rnd.toList`). -/
abbrev KemEncapsRowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (kemEncapsPreservedAtSpec stk kyber1024Prims₀)

/-- Hook #1 (`kemEncapsName`, `B24`) default `65,536`-B row contract. -/
abbrev KemEncapsRowSpec (f : State → State) : Prop :=
  KemEncapsRowSpecAt mlkemHookStack f

/-- Hook #2 (`kemDecapsName`, `B23`) row contract at stack `stk`. -/
abbrev KemDecapsRowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (kemDecapsAtSpec stk kyber1024Prims₀)

/-- Hook #2 (`kemDecapsName`, `B23`) default `65,536`-B row contract. -/
abbrev KemDecapsRowSpec (f : State → State) : Prop :=
  KemDecapsRowSpecAt mlkemHookStack f

/-- Hook #3 (`mlkemFromSeedName`, `B10`) row contract at stack `stk`. -/
abbrev MlkemFromSeedRowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (mlkemFromSeedAtSpec stk mlkem768Incremental)

/-- Hook #3 (`mlkemFromSeedName`, `B10`) default `65,536`-B row contract. -/
abbrev MlkemFromSeedRowSpec (f : State → State) : Prop :=
  MlkemFromSeedRowSpecAt mlkemHookStack f

/-- Hook #4 (`mlkemEncaps1Name`, `B19`) row contract at stack `stk`. -/
abbrev MlkemEncaps1RowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (mlkemEncaps1AtSpec stk mlkem768Incremental)

/-- Hook #4 (`mlkemEncaps1Name`, `B19`) default `65,536`-B row contract. -/
abbrev MlkemEncaps1RowSpec (f : State → State) : Prop :=
  MlkemEncaps1RowSpecAt mlkemHookStack f

/-- Hook #5 (`mlkemEncaps2Name`, `B20`) row contract at stack `stk`. -/
abbrev MlkemEncaps2RowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (mlkemEncaps2AtSpec stk mlkem768Incremental)

/-- Hook #5 (`mlkemEncaps2Name`, `B20`) default `65,536`-B row contract. -/
abbrev MlkemEncaps2RowSpec (f : State → State) : Prop :=
  MlkemEncaps2RowSpecAt mlkemHookStack f

/-- Hook #6 (`mlkemDecapsName`, `B22`) row contract at stack `stk`. -/
abbrev MlkemDecapsRowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (mlkemDecapsAtSpec stk mlkem768Incremental)

/-- Hook #6 (`mlkemDecapsName`, `B22`) default `65,536`-B row contract. -/
abbrev MlkemDecapsRowSpec (f : State → State) : Prop :=
  MlkemDecapsRowSpecAt mlkemHookStack f

/-- Hook #7 (`mlkemValidatePkName`, `B21`) row contract at stack `stk`. -/
abbrev MlkemValidatePkRowSpecAt (stk : Nat) (f : State → State) : Prop :=
  DalekLsRowTuple f (mlkemValidatePkAtSpec stk mlkem768Incremental)

/-- Hook #7 (`mlkemValidatePkName`, `B21`) default `65,536`-B row contract. -/
abbrev MlkemValidatePkRowSpec (f : State → State) : Prop :=
  MlkemValidatePkRowSpecAt mlkemHookStack f

/-! ### Row-Spec Stack-Lift, Weakening, & Equation-Transport Projections -/

theorem KemEncapsRowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : KemEncapsRowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    KemEncapsRowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_kemEncapsPreservedAtSpec_mono kyber1024Prims₀ hle hb) h

theorem KemEncapsRowSpecAt.for_Q_preserved {stk : Nat} {f : State → State}
    (h : KemEncapsRowSpecAt stk f) {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    DalekLsRowTuple f (kemEncapsPreservedAtSpec stk Q) := by
  have heq : kemEncapsPreservedAtSpec stk kyber1024Prims₀ = kemEncapsPreservedAtSpec stk Q :=
    kemEncapsPreservedAtSpec_eq_of_encaps_eq stk (kyber1024Prims₀_encaps.trans hQ.symm)
  rwa [← heq]

theorem KemEncapsRowSpecAt.for_Q {stk : Nat} {f : State → State}
    (h : KemEncapsRowSpecAt stk f) {Q : PqxdhPrims} (hQ : Q.encaps = kyber1024EncapsVec) :
    DalekLsRowTuple f (kemEncapsAtSpec stk Q) :=
  rowTuple_of_simulates (specSimulates_kemEncapsAtSpec_of_preserved stk Q) (h.for_Q_preserved hQ)

theorem KemDecapsRowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : KemDecapsRowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    KemDecapsRowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_kemDecapsAtSpec_mono kyber1024Prims₀ hle hb) h

theorem KemDecapsRowSpecAt.for_Q {stk : Nat} {f : State → State}
    (h : KemDecapsRowSpecAt stk f) {Q : PqxdhPrims} (hQ : Q.decaps = kyber1024DecapsVec) :
    DalekLsRowTuple f (kemDecapsAtSpec stk Q) := by
  have heq : kemDecapsAtSpec stk kyber1024Prims₀ = kemDecapsAtSpec stk Q :=
    kemDecapsAtSpec_eq_of_decaps_eq stk (kyber1024Prims₀_decaps.trans hQ.symm)
  rwa [← heq]

theorem MlkemFromSeedRowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : MlkemFromSeedRowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    MlkemFromSeedRowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_mlkemFromSeedAtSpec_mono mlkem768Incremental hle hb) h

theorem MlkemFromSeedRowSpecAt.for_K {stk : Nat} {f : State → State}
    (h : MlkemFromSeedRowSpecAt stk f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemFromSeedAtSpec stk K) := by
  subst hK; exact h

theorem MlkemEncaps1RowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : MlkemEncaps1RowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    MlkemEncaps1RowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_mlkemEncaps1AtSpec_mono mlkem768Incremental hle hb) h

theorem MlkemEncaps1RowSpecAt.for_K {stk : Nat} {f : State → State}
    (h : MlkemEncaps1RowSpecAt stk f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps1AtSpec stk K) := by
  subst hK; exact h

theorem MlkemEncaps2RowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : MlkemEncaps2RowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    MlkemEncaps2RowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_mlkemEncaps2AtSpec_mono mlkem768Incremental hle hb) h

theorem MlkemEncaps2RowSpecAt.for_K {stk : Nat} {f : State → State}
    (h : MlkemEncaps2RowSpecAt stk f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps2AtSpec stk K) := by
  subst hK; exact h

/-- Direct specialization of Hook #5 (`6,128` B tight stack) to `extHookStack = 16,384` B. -/
theorem MlkemEncaps2RowSpecAt.at_extHookStack {f : State → State}
    (h : MlkemEncaps2RowSpecAt mlkemEncaps2TightStack f) {K : MlKem}
    (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemEncaps2Spec K) := by
  rw [← mlkemEncaps2AtSpec_extHookStack K]
  exact (h.mono (s₂ := extHookStack) (by decide) (by decide)).for_K hK

theorem MlkemDecapsRowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : MlkemDecapsRowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    MlkemDecapsRowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_mlkemDecapsAtSpec_mono mlkem768Incremental hle hb) h

theorem MlkemDecapsRowSpecAt.for_K {stk : Nat} {f : State → State}
    (h : MlkemDecapsRowSpecAt stk f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemDecapsAtSpec stk K) := by
  subst hK; exact h

theorem MlkemValidatePkRowSpecAt.mono {s₁ s₂ : Nat} {f : State → State}
    (h : MlkemValidatePkRowSpecAt s₁ f) (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64 := by decide) :
    MlkemValidatePkRowSpecAt s₂ f :=
  rowTuple_of_simulates (specSimulates_mlkemValidatePkAtSpec_mono mlkem768Incremental hle hb) h

theorem MlkemValidatePkRowSpecAt.for_K {stk : Nat} {f : State → State}
    (h : MlkemValidatePkRowSpecAt stk f) {K : MlKem} (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemValidatePkAtSpec stk K) := by
  subst hK; exact h

/-- Direct specialization of Hook #7 (`5,824` B tight stack) to `extHookStack = 16,384` B. -/
theorem MlkemValidatePkRowSpecAt.at_extHookStack {f : State → State}
    (h : MlkemValidatePkRowSpecAt mlkemValidatePkTightStack f) {K : MlKem}
    (hK : K = mlkem768Incremental) :
    DalekLsRowTuple f (mlkemValidatePkSpec K) := by
  rw [← mlkemValidatePkAtSpec_extHookStack K]
  exact (h.mono (s₂ := extHookStack) (by decide) (by decide)).for_K hK

/-! ### Pure Fallback `RowSpecAt` & `RowSpec` Witnesses -/

theorem kemEncapsFallback_rowSpecAt (stk : Nat) : KemEncapsRowSpecAt stk kemEncapsFallback := by
  refine rowTuple_of_fallback kemEncapsFallback_preserved ?_
  unfold kemEncapsFallback
  rw [← kyber1024Prims₀_encaps]
  exact kemEncapsHook_preservedAt_keepsFs_ok kyber1024Prims₀ stk

theorem kemEncapsFallback_rowSpec : KemEncapsRowSpec kemEncapsFallback :=
  kemEncapsFallback_rowSpecAt mlkemHookStack

theorem kemDecapsFallback_rowSpecAt (stk : Nat) : KemDecapsRowSpecAt stk kemDecapsFallback := by
  refine rowTuple_of_fallback kemDecapsFallback_preserved ?_
  unfold kemDecapsFallback
  rw [← kyber1024Prims₀_decaps]
  exact kemDecapsHook_at_keepsFs_ok kyber1024Prims₀ stk

theorem kemDecapsFallback_rowSpec : KemDecapsRowSpec kemDecapsFallback :=
  kemDecapsFallback_rowSpecAt mlkemHookStack

theorem mlkemFromSeedFallback_rowSpecAt (stk : Nat) :
    MlkemFromSeedRowSpecAt stk mlkemFromSeedFallback :=
  rowTuple_of_fallback mlkemFromSeedFallback_preserved
    (mlkemFromSeedHook_at_keepsFs_ok mlkem768Incremental stk)

theorem mlkemFromSeedFallback_rowSpec : MlkemFromSeedRowSpec mlkemFromSeedFallback :=
  mlkemFromSeedFallback_rowSpecAt mlkemHookStack

theorem mlkemEncaps1Fallback_rowSpecAt (stk : Nat) :
    MlkemEncaps1RowSpecAt stk mlkemEncaps1Fallback :=
  rowTuple_of_fallback mlkemEncaps1Fallback_preserved
    (mlkemEncaps1Hook_at_keepsFs_ok mlkem768Incremental stk)

theorem mlkemEncaps1Fallback_rowSpec : MlkemEncaps1RowSpec mlkemEncaps1Fallback :=
  mlkemEncaps1Fallback_rowSpecAt mlkemHookStack

theorem mlkemEncaps2Fallback_rowSpecAt (stk : Nat) :
    MlkemEncaps2RowSpecAt stk mlkemEncaps2Fallback :=
  rowTuple_of_fallback mlkemEncaps2Fallback_preserved
    (mlkemEncaps2Hook_at_keepsFs_ok mlkem768Incremental stk)

theorem mlkemEncaps2Fallback_rowSpec : MlkemEncaps2RowSpec mlkemEncaps2Fallback :=
  mlkemEncaps2Fallback_rowSpecAt mlkemHookStack

theorem mlkemDecapsFallback_rowSpecAt (stk : Nat) :
    MlkemDecapsRowSpecAt stk mlkemDecapsFallback :=
  rowTuple_of_fallback mlkemDecapsFallback_preserved
    (mlkemDecapsHook_at_keepsFs_ok mlkem768Incremental stk)

theorem mlkemDecapsFallback_rowSpec : MlkemDecapsRowSpec mlkemDecapsFallback :=
  mlkemDecapsFallback_rowSpecAt mlkemHookStack

theorem mlkemValidatePkFallback_rowSpecAt (stk : Nat) :
    MlkemValidatePkRowSpecAt stk mlkemValidatePkFallback :=
  rowTuple_of_fallback mlkemValidatePkFallback_preserved
    (mlkemValidatePkHook_at_keepsFs_ok mlkem768Incremental stk)

theorem mlkemValidatePkFallback_rowSpec : MlkemValidatePkRowSpec mlkemValidatePkFallback :=
  mlkemValidatePkFallback_rowSpecAt mlkemHookStack

end WithPlacement

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoMlKemRowSpecs
