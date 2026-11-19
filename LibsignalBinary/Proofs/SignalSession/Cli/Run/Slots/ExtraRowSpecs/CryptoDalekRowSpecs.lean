/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks -- proof-setup: allow-public-import
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.SpqrHooksPCommon

/-!
# Crypto & Curve25519/Edwards25519 Consumer `HookOk` Row Arms (`ExtraRowSpecs.CryptoDalekRowSpecs`)

Consumer-contract leaf module for the 9 linked cryptographic symbols in
`ExtraGhostSpecs.ExtraRowSpec`:
- 6 `dalekCliMultiLib` symbols (`lsScalarModSym`, `lsScalarWideSym`, `lsToEdwardsSym`,
  `lsCompressSym`, `lsTorsionFreeSym`, `lsDsmbSym`);
- `lsEdNegSym` (`EdNegRowSpec`, bridging `masterEdNegSpec` to `edwardsPointNegUnstackedSpec`,
  `pureByteFunctionSpec dalekEdNegVec`, `cryptoLeafStubSpec`, and `dalekEdNegExtSpec`);
- 2 ML-KEM-768 public-key projection symbols (`lsMlkemPk1Sym`, `lsMlkemPk2Sym`).
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (u8Vec vecU8)
open CryptoVerification.E2E.Pqxdh (mlkemPk1Hook_ok mlkemPk2Hook_ok)
open CryptoVerification.E2E.Pqxdh.Shared (bytesToBv8 cryptoLeafStubSpec)
open CryptoVerification.LibsignalSpqrV1 (mlkemPk1Spec mlkemPk2Spec)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC edNegHook_fsT mlkemPk1Hook_fsT mlkemPk2Hook_fsT)
open CryptoVerification.SignalSession.CliExt (pureByteFunctionSpec withStack)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.Fine (hookOk_withVmPreserved mlkemPk1Hook_vmPreserved mlkemPk2Hook_vmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (SpecSimulates)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.EdNegCode (
  edNegHook_masterEdNeg_ok edNegHook_vmPreserved
  hookOk_edNegCryptoLeafStub_of_master hookOk_edNegPureByteFunction_of_master
  hookOk_edNegUnstackedFalse_keepsFs_of_master hookOk_edNegUnstacked_keepsFs_of_master
  hookOk_edNegUnstacked_of_master masterEdNegSpec
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithAlloc
  (hookOk_withAlloc_of_withVmPreserved withAlloc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookOk_withLsRet specSimulates_withLsRet withLsRet withLsRet_withVmPreserved)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy
  (edNegHook mlkemPk1Hook mlkemPk2Hook)
open VerifiedLibraries.Common (edExtOfAffine edSmul fpInv recoverXEven)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.ConsumerBridges
  (dalekEdNegVec fe51Point4Bounded_mono specSimulates_keepsFs specSimulates_withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.CurveSpecs
  (edDoubleScalarMulBasepoint edExtOfBytes fe51Point4Bounded montToEdwards)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.DalekPureFallbacks (
  PureFallbackPreserved dalekCompressCore dalekCompressFallback dalekCompressFallback_ok
  dalekCompressFallback_preserved dalekCompressSpec dalekDsmbFallback dalekDsmbFallback_ok
  dalekDsmbFallback_preserved dalekDsmbSpec dalekHookStack dalekMontToEdFallback
  dalekMontToEdFallback_ok dalekMontToEdFallback_preserved dalekMontToEdSpec
  dalekOptionEdwardsAt dalekScalarModFallback dalekScalarModFallback_ok
  dalekScalarModFallback_preserved dalekScalarModSpec dalekScalarWideFallback
  dalekScalarWideFallback_ok dalekScalarWideFallback_preserved dalekScalarWideSpec
  dalekTorsionFreeBool dalekTorsionFreeCore dalekTorsionFreeFallback
  dalekTorsionFreeFallback_ok dalekTorsionFreeFallback_preserved dalekTorsionFreeSpec
)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block202
  (dalekMontToEdExtOutAt dalekMontToEdExtOutAt_none dalekMontToEdExtOutAt_some
   dalekMontToEdExtSpec dalekTorsionFreeExtSpec)
open LibsignalBinary.Proofs.HookDischarge.EdwardsPoint.Phase4Block204
  (dalekCompressExtSpec dalekDsmbExtSpec dalekEdNegExtSpec dalekScalarModExtSpec
   dalekScalarWideExtSpec edwardsPointNegUnstackedSpec
   specSimulates_dalekCompressExtSpec_mono specSimulates_dalekCompressExtSpec_of_vecSpec
   specSimulates_dalekDsmbExtSpec_mono specSimulates_dalekEdNegExtSpec_of_unstacked
   specSimulates_dalekScalarModExtSpec_mono specSimulates_dalekScalarModExtSpec_of_withStack
   specSimulates_dalekScalarWideExtSpec_mono specSimulates_dalekScalarWideExtSpec_of_withStack
   stackAt_split_low)

private theorem fe51Point4Bounded_len {bs : List (BitVec 8)} {b : Nat}
    (h : fe51Point4Bounded bs b) : bs.length = 160 := h.1

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff VmPreserved
  fpInv recoverXEven edSmul fe51Point4Bounded edExtOfBytes edDoubleScalarMulBasepoint montToEdwards dalekTorsionFreeBool

/-! ## 1. Acyclic `HookOk` Consequence Helpers & `SpecSimulates` Bridges -/

theorem hookOk_of_simulates {α β : Type} {f : State → State}
    {s₁ : Spec α} {s₂ : Spec β} (hsim : SpecSimulates s₁ s₂) (hok : HookOk f s₁) :
    HookOk f s₂ :=
  fun y R s0 hrun hpre hsp => by
    obtain ⟨x, R₁, hpre₁, hmap⟩ := hsim y R s0 hpre
    obtain ⟨hkf, hsym, hout₁⟩ := hok x R₁ s0 hrun hpre₁ hsp
    exact ⟨hkf, hsym, hmap (f s0) hout₁⟩

theorem hookOk_withLsRet_of_simulates [LibsignalPlacement] {α β : Type} {f : State → State}
    {s₁ : Spec α} {s₂ : Spec β} (hsim : SpecSimulates s₁ s₂)
    (hok : HookOk f (withLsRet s₁)) : HookOk f (withLsRet s₂) :=
  hookOk_of_simulates (specSimulates_withLsRet hsim) hok

private theorem satisfies_prepend_pure {m : Memory} {P : Prop} {Q : SepProp} (hP : P) (hQ : m ⊨ Q) :
    m ⊨ ⌜P⌝ ∗ Q := (satisfies_pure_sepConj P Q m).mpr ⟨hP, hQ⟩
private theorem satisfies_split_pure {m : Memory} {P : Prop} {Q R : SepProp} (h : m ⊨ (⌜P⌝ ∗ Q) ∗ R) :
    P ∧ (m ⊨ Q ∗ R) := by rw [sepConj_assoc, satisfies_pure_sepConj] at h; exact h
private theorem satisfies_pre1 {m : Memory} {P : Prop} {A S R : SepProp} (hP : P) (h : m ⊨ (A ∗ S) ∗ R) :
    m ⊨ ((⌜P⌝ ∗ A) ∗ S) ∗ R := by simp only [sepConj_assoc] at h ⊢; exact satisfies_prepend_pure hP h
private theorem satisfies_pre2 {m : Memory} {P : Prop} {A B S R : SepProp} (hP : P) (h : m ⊨ (A ∗ B ∗ S) ∗ R) :
    m ⊨ ((⌜P⌝ ∗ A ∗ B) ∗ S) ∗ R := by simp only [sepConj_assoc] at h ⊢; exact satisfies_prepend_pure hP h
private theorem satisfies_pre4 {m : Memory} {P : Prop} {A B C D S R : SepProp} (hP : P)
    (h : m ⊨ (A ∗ B ∗ C ∗ D ∗ S) ∗ R) : m ⊨ ((⌜P⌝ ∗ A ∗ B ∗ C ∗ D) ∗ S) ∗ R := by
  simp only [sepConj_assoc] at h ⊢; exact satisfies_prepend_pure hP h
private theorem satisfies_post1_fs {m : Memory} {F P₁ Q : Prop} {A S R : SepProp} (hq : F → P₁ → Q)
    (h : m ⊨ (⌜F⌝ ∗ ((⌜P₁⌝ ∗ A) ∗ S)) ∗ R) : m ⊨ (⌜Q⌝ ∗ A ∗ S) ∗ R := by
  simp only [sepConj_assoc] at h ⊢; rw [satisfies_pure_sepConj] at h
  obtain ⟨hf, h2⟩ := h; rw [satisfies_pure_sepConj] at h2; exact satisfies_prepend_pure (hq hf h2.1) h2.2
private theorem satisfies_post2_fs {m : Memory} {F T : Prop} {A B₁ B₂ S R : SepProp} (hB : B₁ = B₂)
    (h : m ⊨ (⌜F⌝ ∗ ((⌜T⌝ ∗ A ∗ B₁) ∗ S)) ∗ R) : m ⊨ (⌜F ∧ T⌝ ∗ A ∗ B₂ ∗ S) ∗ R := by
  subst hB; exact satisfies_post1_fs And.intro (by simpa only [sepConj_assoc] using h)
private theorem satisfies_post4 {m : Memory} {T : Prop} {A B C D₁ D₂ S R : SepProp} (hD : D₁ = D₂)
    (h : m ⊨ ((⌜T⌝ ∗ A ∗ B ∗ C ∗ D₁) ∗ S) ∗ R) : m ⊨ (⌜T⌝ ∗ A ∗ B ∗ C ∗ D₂ ∗ S) ∗ R := by
  subst hD; simpa only [sepConj_assoc] using h

private theorem specSimulates_drop_keepsFs {α : Type} (spec : Spec α) : SpecSimulates (keepsFs spec) spec :=
  fun x R _ hpre => ⟨x, R, hpre, fun _ hout => hout.imp_left fun ⟨hret, hcc, hp⟩ =>
    ⟨hret, hcc, (satisfies_split_pure hp).2⟩⟩

private theorem specSimulates_keepsFs_of_post_fs {α : Type} {spec : Spec α}
    (hfs : ∀ x (R : SepProp) (s0 sf : State), sf.mem ⊨ spec.post x s0 sf ∗ R → sf.fs = s0.fs)
    (hpan : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl) : SpecSimulates spec (keepsFs spec) :=
  SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun x R s0 hpre =>
    ⟨x, R, hpre, fun sf _ _ hq => by
      change sf.mem ⊨ (⌜sf.fs = s0.fs⌝ ∗ spec.post x s0 sf) ∗ R; rw [sepConj_assoc]
      exact satisfies_prepend_pure (hfs x R s0 sf hq) hq⟩

theorem specSimulates_dalekScalarModExtSpec (stk : Nat) :
    SpecSimulates (dalekScalarModSpec stk) (dalekScalarModExtSpec stk) :=
  specSimulates_dalekScalarModExtSpec_of_withStack stk

theorem specSimulates_keepsFs_dalekScalarModExtSpec (stk : Nat) :
    SpecSimulates (keepsFs (dalekScalarModSpec stk)) (keepsFs (dalekScalarModExtSpec stk)) :=
  specSimulates_keepsFs (specSimulates_dalekScalarModExtSpec stk)

theorem specSimulates_dalekScalarWideExtSpec (stk : Nat) :
    SpecSimulates (dalekScalarWideSpec stk) (dalekScalarWideExtSpec stk) :=
  specSimulates_dalekScalarWideExtSpec_of_withStack stk

theorem specSimulates_keepsFs_dalekScalarWideExtSpec (stk : Nat) :
    SpecSimulates (keepsFs (dalekScalarWideSpec stk)) (keepsFs (dalekScalarWideExtSpec stk)) :=
  specSimulates_keepsFs (specSimulates_dalekScalarWideExtSpec stk)

private theorem bv8_ofNat_signBit_mod2 (b : UInt8) :
    (BitVec.ofNat 8 b.toNat).toNat % 2 = (b &&& 1).toNat := by
  rcases b with ⟨bv⟩; revert bv; decide

private theorem dalekOptionEdwardsAt_eq_extOutAt (ret : BitVec 64) (u_bs : List (BitVec 8)) (sign : Nat) :
    dalekOptionEdwardsAt ret (montToEdwards u_bs sign) = dalekMontToEdExtOutAt ret u_bs sign := by
  rcases hmont : montToEdwards u_bs sign with _ | Apt
  · rw [dalekMontToEdExtOutAt_none ret u_bs sign hmont]; rfl
  · rw [dalekMontToEdExtOutAt_some ret u_bs sign Apt hmont]
    change (∃∗ pt_bs : List (BitVec 8), ⌜fe51Point4Bounded pt_bs (2 ^ 52) ∧
      edExtOfBytes pt_bs = edExtOfAffine Apt⌝ ∗ (ret ↦₆₄ 1#64) ∗ ((ret + 8#64) ↦ₛ pt_bs)) = _
    apply congrArg sepExists; funext pt_bs; congr 1; congr 1
    exact propext ⟨fun ⟨hfe, hed⟩ => ⟨fe51Point4Bounded_len hfe, hfe, hed⟩, fun ⟨_, hfe, hed⟩ => ⟨hfe, hed⟩⟩

theorem specSimulates_dalekMontToEdExtSpec_of_ghost (stk : Nat) :
    SpecSimulates (keepsFs (dalekMontToEdSpec stk)) (dalekMontToEdExtSpec stk) :=
  SpecSimulates.of_map fun g R _ hpre =>
    let ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩ := satisfies_split_pure hpre
    let u : List.Vector (BitVec 8) 32 := ⟨bytesToBv8 g.inBytes, by unfold bytesToBv8; simp [hlen]⟩
    ⟨(g.inPtr, u, BitVec.ofNat 8 g.signBit.toNat, g.outPtr), R, satisfies_pre2 ⟨hx0, hx1, hx8⟩ hmem,
      fun _ _ _ hpost => satisfies_post2_fs (show dalekOptionEdwardsAt g.outPtr
        (montToEdwards (bytesToBv8 g.inBytes) ((BitVec.ofNat 8 g.signBit.toNat).toNat % 2)) = _ by
        rw [bv8_ofNat_signBit_mod2, dalekOptionEdwardsAt_eq_extOutAt]) hpost⟩

theorem specSimulates_keepsFs_dalekMontToEdExtSpec_of_ghost (stk : Nat) :
    SpecSimulates (keepsFs (dalekMontToEdSpec stk)) (keepsFs (dalekMontToEdExtSpec stk)) :=
  (specSimulates_dalekMontToEdExtSpec_of_ghost stk).trans
    (specSimulates_keepsFs_of_post_fs fun _ _ _ _ hq => (satisfies_split_pure hq).1.1)

theorem specSimulates_dalekCompressExtSpec (stk : Nat) (bound : Nat := 2 ^ 53)
    (hb : 2 ^ 52 ≤ bound := by decide) :
    SpecSimulates (dalekCompressSpec stk false bound) (dalekCompressExtSpec stk) :=
  specSimulates_dalekCompressExtSpec_of_vecSpec stk bound hb

theorem specSimulates_keepsFs_dalekCompressExtSpec (stk : Nat) (bound : Nat := 2 ^ 53)
    (hb : 2 ^ 52 ≤ bound := by decide) :
    SpecSimulates (keepsFs (dalekCompressSpec stk false bound)) (keepsFs (dalekCompressExtSpec stk)) :=
  specSimulates_keepsFs (specSimulates_dalekCompressExtSpec stk bound hb)

theorem specSimulates_dalekTorsionFreeExtSpec_of_ghost (stk : Nat) :
    SpecSimulates (keepsFs (dalekTorsionFreeSpec stk (2 ^ 53))) (dalekTorsionFreeExtSpec stk) :=
  SpecSimulates.of_map fun g R _ hpre =>
    let ⟨⟨hx0, hlen, hfe, hval⟩, hmem⟩ := satisfies_split_pure hpre
    ⟨(g.inPtr, ⟨g.edBytes, hlen⟩), R, satisfies_pre1 ⟨hx0, fe51Point4Bounded_mono hfe (by decide)⟩ hmem,
      fun _ _ _ hpost => satisfies_post1_fs (fun hfs ⟨htr, _, himp⟩ => ⟨hfs, htr, himp hval⟩) hpost⟩

theorem specSimulates_keepsFs_dalekTorsionFreeExtSpec_of_ghost (stk : Nat) :
    SpecSimulates (keepsFs (dalekTorsionFreeSpec stk (2 ^ 53))) (keepsFs (dalekTorsionFreeExtSpec stk)) :=
  (specSimulates_dalekTorsionFreeExtSpec_of_ghost stk).trans
    (specSimulates_keepsFs_of_post_fs fun _ _ _ _ hq => (satisfies_split_pure hq).1.1)

theorem specSimulates_dalekDsmbExtSpec (stk : Nat) :
    SpecSimulates (dalekDsmbSpec stk) (dalekDsmbExtSpec stk) :=
  SpecSimulates.of_map fun g R _ hpre =>
    let ⟨⟨hx0, hx1, hx2, hx8, ha, hp, hfe, hb⟩, hmem⟩ := satisfies_split_pure hpre
    ⟨(g.aPtr, ⟨g.aBytes, ha⟩, g.pPtr, ⟨g.pBytes, hp⟩, g.bPtr, ⟨g.bBytes, hb⟩, g.outPtr), R,
      satisfies_pre4 ⟨hx0, hx1, hx2, hx8, hfe⟩ hmem, fun _ _ _ hpost => satisfies_post4 (by
        apply congrArg sepExists; funext res_bs; congr 1; congr 1
        exact propext ⟨fun ⟨h1, h2⟩ => ⟨fe51Point4Bounded_len h1, h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩) hpost⟩

theorem specSimulates_keepsFs_dalekDsmbExtSpec (stk : Nat) :
    SpecSimulates (keepsFs (dalekDsmbSpec stk)) (keepsFs (dalekDsmbExtSpec stk)) :=
  specSimulates_keepsFs (specSimulates_dalekDsmbExtSpec stk)

private theorem satisfies_stack_split1 {m : Memory} {A R : SepProp} {sp : BitVec 64} {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) : (m ⊨ (A ∗ stackAt sp s₂) ∗ R) ↔
      (m ⊨ (A ∗ stackAt sp s₁) ∗ (memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R)) := by
  rw [stackAt_split_low sp hle hb]; exact (congrArg (m ⊨ ·) (by sep_ac_rfl)).to_iff
private theorem satisfies_stack_split2 {m : Memory} {A B R : SepProp} {sp : BitVec 64} {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) : (m ⊨ (A ∗ B ∗ stackAt sp s₂) ∗ R) ↔
      (m ⊨ (A ∗ B ∗ stackAt sp s₁) ∗ (memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R)) := by
  rw [stackAt_split_low sp hle hb]; exact (congrArg (m ⊨ ·) (by sep_ac_rfl)).to_iff
private theorem satisfies_stack_split3 {m : Memory} {A B C R : SepProp} {sp : BitVec 64} {s₁ s₂ : Nat}
    (hle : s₁ ≤ s₂) (hb : s₂ ≤ 2 ^ 64) : (m ⊨ (A ∗ B ∗ C ∗ stackAt sp s₂) ∗ R) ↔
      (m ⊨ (A ∗ B ∗ C ∗ stackAt sp s₁) ∗ (memRegion (sp - BitVec.ofNat 64 s₂) (s₂ - s₁) ∗ R)) := by
  rw [stackAt_split_low sp hle hb]; exact (congrArg (m ⊨ ·) (by sep_ac_rfl)).to_iff

theorem specSimulates_dalekMontToEdExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekMontToEdExtSpec s₁) (dalekMontToEdExtSpec s₂) :=
  SpecSimulates.of_map fun g _ _ hpre => ⟨g, _, (satisfies_stack_split3 hle hbound).mp hpre,
    fun _ _ _ hq => (satisfies_stack_split3 hle hbound).mpr hq⟩

theorem specSimulates_dalekTorsionFreeExtSpec_mono {s₁ s₂ : Nat} (hle : s₁ ≤ s₂) (hbound : s₂ ≤ 2 ^ 64) :
    SpecSimulates (dalekTorsionFreeExtSpec s₁) (dalekTorsionFreeExtSpec s₂) :=
  SpecSimulates.of_map fun g _ _ hpre => ⟨g, _, (satisfies_stack_split2 hle hbound).mp hpre,
    fun _ _ _ hq => (satisfies_stack_split2 hle hbound).mpr hq⟩

private theorem specSimulates_withStack_mono_local {α : Type} (core : Spec α) {stk₀ stk : Nat}
    (hlo : stk₀ ≤ stk) (hhi : stk ≤ 2 ^ 64)
    (hpan : core.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (hex : core.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (hoom : core.onOom = fun _ _ _ => ⌜False⌝ := by rfl) :
    SpecSimulates (withStack core stk₀) (withStack core stk) :=
  SpecSimulates.of_map (hpan := hpan) (hex := hex) (hoom := hoom) fun x _ _ hpre =>
    ⟨x, _, (satisfies_stack_split1 hlo hhi).mp hpre, fun _ _ _ hq => (satisfies_stack_split1 hlo hhi).mpr hq⟩

/-! ## 2. `DalekLsRowTuple`, the 6 `Dalek*RowSpec` Arms, & Pure Fallback Instances -/

section WithPlacement

variable [LibsignalPlacement]

abbrev DalekLsRowTuple {α : Type} (f : State → State) (spec : Spec α) : Prop :=
  HookOk f (withLsRet spec) ∧ HookOk f (withLsRet (withVmPreserved spec)) ∧
  HookOk f (withLsRet (withVmPreserved (keepsFs spec))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withAlloc A lim (withLsRet spec))) ∧
  (∀ {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits),
    HookOk f (withLsRet (withAlloc A lim spec)))

theorem DalekLsRowTuple.plain {α : Type} {f : State → State} {spec : Spec α}
    (h : DalekLsRowTuple f spec) : HookOk f (withLsRet spec) := h.1
theorem DalekLsRowTuple.vm {α : Type} {f : State → State} {spec : Spec α}
    (h : DalekLsRowTuple f spec) : HookOk f (withLsRet (withVmPreserved spec)) := h.2.1
theorem DalekLsRowTuple.keepsFsVm {α : Type} {f : State → State} {spec : Spec α}
    (h : DalekLsRowTuple f spec) : HookOk f (withLsRet (withVmPreserved (keepsFs spec))) := h.2.2.1
theorem DalekLsRowTuple.alloc {α : Type} {f : State → State} {spec : Spec α}
    (h : DalekLsRowTuple f spec) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim (withLsRet spec)) := h.2.2.2.1 A lim
theorem DalekLsRowTuple.withLsRetAlloc {α : Type} {f : State → State} {spec : Spec α}
    (h : DalekLsRowTuple f spec) {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim spec)) := h.2.2.2.2 A lim

theorem withLsRet_withAlloc_eq {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (spec : Spec α) :
    withLsRet (withAlloc A lim spec) = withAlloc A lim (withLsRet spec) := by
  cases spec; dsimp only [withLsRet, withAlloc]; congr 1; funext ⟨x, st⟩ s; simp only [sepConj_assoc]

private theorem hookOk_plain_of_vm {α : Type} {f : State → State} {spec : Spec α}
    (hv : HookOk f (withLsRet (withVmPreserved spec))) : HookOk f (withLsRet spec) := by
  intro x R s0 hrun hpre hsp; rcases hv x R s0 hrun hpre hsp with ⟨hkf, hsym, ⟨hret, hcs, hq⟩ | hrest⟩
  · exact ⟨hkf, hsym, Or.inl ⟨hret, hcs, (satisfies_split_pure hq).2⟩⟩
  · exact ⟨hkf, hsym, Or.inr hrest⟩

theorem rowTuple_of_keepsFs_vm {α : Type} {f : State → State} {spec : Spec α}
    (hk : HookOk f (withLsRet (withVmPreserved (keepsFs spec)))) : DalekLsRowTuple f spec := by
  have hv : HookOk f (withLsRet (withVmPreserved spec)) :=
    hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved (specSimulates_drop_keepsFs spec)) hk
  have hv' : HookOk f (withVmPreserved (withLsRet spec)) := by rw [← withLsRet_withVmPreserved]; exact hv
  exact ⟨hookOk_plain_of_vm hv, hv, hk, fun A lim => hookOk_withAlloc_of_withVmPreserved A lim hv',
    fun A lim => by rw [withLsRet_withAlloc_eq]; exact hookOk_withAlloc_of_withVmPreserved A lim hv'⟩

@[expose] def DalekScalarModRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekScalarModExtSpec dalekHookStack)
@[expose] def DalekScalarWideRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekScalarWideExtSpec dalekHookStack)
@[expose] def DalekMontToEdRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekMontToEdExtSpec dalekHookStack)
@[expose] def DalekCompressRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekCompressExtSpec dalekHookStack)
@[expose] def DalekTorsionFreeRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekTorsionFreeExtSpec dalekHookStack)
@[expose] def DalekDsmbRowSpec (f : State → State) : Prop := DalekLsRowTuple f (dalekDsmbExtSpec dalekHookStack)

private theorem liftRow {α : Type} {f : State → State} {s₁ s₂ : Spec α}
    (hm : SpecSimulates s₁ s₂) (hk : HookOk f (withLsRet (withVmPreserved (keepsFs s₁)))) :
    DalekLsRowTuple f s₂ :=
  rowTuple_of_keepsFs_vm (hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved (specSimulates_keepsFs hm)) hk)

theorem DalekScalarModRowSpec.at_stk {f : State → State} (h : DalekScalarModRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekScalarModExtSpec stk) :=
  liftRow (specSimulates_dalekScalarModExtSpec_mono hlo hhi) h.2.2.1

theorem DalekScalarWideRowSpec.at_stk {f : State → State} (h : DalekScalarWideRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekScalarWideExtSpec stk) :=
  liftRow (specSimulates_dalekScalarWideExtSpec_mono hlo hhi) h.2.2.1

theorem DalekMontToEdRowSpec.at_stk {f : State → State} (h : DalekMontToEdRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekMontToEdExtSpec stk) :=
  liftRow (specSimulates_dalekMontToEdExtSpec_mono hlo hhi) h.2.2.1

theorem DalekCompressRowSpec.at_stk {f : State → State} (h : DalekCompressRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekCompressExtSpec stk) :=
  liftRow (specSimulates_dalekCompressExtSpec_mono hlo hhi) h.2.2.1

theorem DalekTorsionFreeRowSpec.at_stk {f : State → State} (h : DalekTorsionFreeRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekTorsionFreeExtSpec stk) :=
  liftRow (specSimulates_dalekTorsionFreeExtSpec_mono hlo hhi) h.2.2.1

theorem DalekDsmbRowSpec.at_stk {f : State → State} (h : DalekDsmbRowSpec f)
    (stk : Nat := dalekHookStack) (hlo : dalekHookStack ≤ stk := by decide)
    (hhi : stk ≤ 2 ^ 64 := by decide) : DalekLsRowTuple f (dalekDsmbExtSpec stk) :=
  liftRow (specSimulates_dalekDsmbExtSpec_mono hlo hhi) h.2.2.1

theorem ghostRow {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (hm : SpecSimulates (keepsFs s₁) (keepsFs s₂))
    (hk : HookOk f (withLsRet (withVmPreserved (keepsFs s₁)))) :
    DalekLsRowTuple f s₂ :=
  rowTuple_of_keepsFs_vm (hookOk_withLsRet_of_simulates (specSimulates_withVmPreserved hm) hk)

theorem fallback_rowTuple {α β : Type} {fb : State → State} {ghostSpec : Spec α} {extSpec : Spec β}
    (hfb : HookOk fb (keepsFs ghostSpec)) (hp : PureFallbackPreserved fb)
    (hsim : SpecSimulates (keepsFs ghostSpec) (keepsFs extSpec)) : DalekLsRowTuple fb extSpec :=
  rowTuple_of_keepsFs_vm (hookOk_withLsRet (hookOk_withVmPreserved (hookOk_of_simulates hsim hfb) (fun s => (hp s).1)))

theorem dalekScalarModFallback_ext_at_stk (stk : Nat := dalekHookStack) :
    DalekLsRowTuple dalekScalarModFallback (dalekScalarModExtSpec stk) :=
  fallback_rowTuple (dalekScalarModFallback_ok stk) dalekScalarModFallback_preserved
    (specSimulates_keepsFs_dalekScalarModExtSpec stk)

theorem dalekScalarWideFallback_ext_at_stk (stk : Nat := dalekHookStack) :
    DalekLsRowTuple dalekScalarWideFallback (dalekScalarWideExtSpec stk) :=
  fallback_rowTuple (dalekScalarWideFallback_ok stk) dalekScalarWideFallback_preserved
    (specSimulates_keepsFs_dalekScalarWideExtSpec stk)

theorem dalekMontToEdFallback_ext_at_stk (stk : Nat := dalekHookStack) :
    DalekLsRowTuple dalekMontToEdFallback (dalekMontToEdExtSpec stk) :=
  fallback_rowTuple (dalekMontToEdFallback_ok stk) dalekMontToEdFallback_preserved
    (specSimulates_keepsFs_dalekMontToEdExtSpec_of_ghost stk)

theorem dalekCompressFallback_ext_at_stk (stk : Nat := dalekHookStack)
    (hlo : 1552 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple dalekCompressFallback (dalekCompressExtSpec stk) :=
  fallback_rowTuple dalekCompressFallback_ok dalekCompressFallback_preserved
    ((specSimulates_keepsFs (specSimulates_withStack_mono_local (dalekCompressCore false (2 ^ 54)) hlo hhi)).trans
      (specSimulates_keepsFs_dalekCompressExtSpec stk (2 ^ 54) (by decide)))

theorem dalekTorsionFreeFallback_ext_at_stk (stk : Nat := dalekHookStack)
    (hlo : 4848 ≤ stk := by decide) (hhi : stk ≤ 2 ^ 64 := by decide) :
    DalekLsRowTuple dalekTorsionFreeFallback (dalekTorsionFreeExtSpec stk) :=
  fallback_rowTuple dalekTorsionFreeFallback_ok dalekTorsionFreeFallback_preserved
    ((specSimulates_keepsFs (specSimulates_withStack_mono_local (dalekTorsionFreeCore (2 ^ 53)) hlo hhi)).trans
      (specSimulates_keepsFs_dalekTorsionFreeExtSpec_of_ghost stk))

theorem dalekDsmbFallback_ext_at_stk (stk : Nat := dalekHookStack) :
    DalekLsRowTuple dalekDsmbFallback (dalekDsmbExtSpec stk) :=
  fallback_rowTuple (dalekDsmbFallback_ok stk) dalekDsmbFallback_preserved
    (specSimulates_keepsFs_dalekDsmbExtSpec stk)

theorem dalekScalarModFallback_rowSpec : DalekScalarModRowSpec dalekScalarModFallback := dalekScalarModFallback_ext_at_stk
theorem dalekScalarWideFallback_rowSpec : DalekScalarWideRowSpec dalekScalarWideFallback := dalekScalarWideFallback_ext_at_stk
theorem dalekMontToEdFallback_rowSpec : DalekMontToEdRowSpec dalekMontToEdFallback := dalekMontToEdFallback_ext_at_stk
theorem dalekCompressFallback_rowSpec : DalekCompressRowSpec dalekCompressFallback := dalekCompressFallback_ext_at_stk
theorem dalekTorsionFreeFallback_rowSpec : DalekTorsionFreeRowSpec dalekTorsionFreeFallback := dalekTorsionFreeFallback_ext_at_stk
theorem dalekDsmbFallback_rowSpec : DalekDsmbRowSpec dalekDsmbFallback := dalekDsmbFallback_ext_at_stk

/-! ## 3. `lsEdNegSym` (`EdNegRowSpec`) & ML-KEM-768 `pk1` / `pk2` (`MlkemPk1RowSpec`, `MlkemPk2RowSpec`) -/

/-- Consumer `HookOk` arm for `lsEdNegSym` (`<&EdwardsPoint as Neg>::neg`), holding for both
    pure fallback `edNegHook dalekEdNegVec` and linked `narrowEdNegGhostHook entryTarget`. -/
@[expose] def EdNegRowSpec (f : State → State) : Prop :=
  HookOk f masterEdNegSpec ∧ (∀ s : State, VmPreserved s (f s))

theorem EdNegRowSpec.master {f : State → State} (h : EdNegRowSpec f) : HookOk f masterEdNegSpec := h.1
theorem EdNegRowSpec.vmPreserved {f : State → State} (h : EdNegRowSpec f) (s : State) : VmPreserved s (f s) := h.2 s
theorem EdNegRowSpec.masterVm {f : State → State} (h : EdNegRowSpec f) :
    HookOk f (withVmPreserved masterEdNegSpec) := hookOk_withVmPreserved h.1 h.2
theorem EdNegRowSpec.unstacked {f : State → State} (h : EdNegRowSpec f) (byVal : Bool := false) :
    HookOk f (edwardsPointNegUnstackedSpec byVal) := hookOk_edNegUnstacked_of_master byVal h.1
theorem EdNegRowSpec.unstackedVm {f : State → State} (h : EdNegRowSpec f) (byVal : Bool := false) :
    HookOk f (withVmPreserved (edwardsPointNegUnstackedSpec byVal)) :=
  hookOk_withVmPreserved (h.unstacked byVal) h.2
theorem EdNegRowSpec.unstackedKeepsFs {f : State → State} (h : EdNegRowSpec f) (byVal : Bool := false) :
    HookOk f (keepsFs (edwardsPointNegUnstackedSpec byVal)) :=
  hookOk_edNegUnstacked_keepsFs_of_master byVal h.1
theorem EdNegRowSpec.pureByteFunction {f : State → State} (h : EdNegRowSpec f) (byVal : Bool := false) :
    HookOk f (pureByteFunctionSpec dalekEdNegVec byVal) := hookOk_edNegPureByteFunction_of_master byVal h.1
theorem EdNegRowSpec.pureByteFunctionVm {f : State → State} (h : EdNegRowSpec f) (byVal : Bool := false) :
    HookOk f (withVmPreserved (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  hookOk_withVmPreserved (h.pureByteFunction byVal) h.2
theorem EdNegRowSpec.pureByteFunctionAlloc {f : State → State} (h : EdNegRowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (byVal : Bool := false) :
    HookOk f (withAlloc A lim (pureByteFunctionSpec dalekEdNegVec byVal)) :=
  hookOk_withAlloc_of_withVmPreserved A lim (h.pureByteFunctionVm byVal)
theorem EdNegRowSpec.cryptoLeafStub {f : State → State} (h : EdNegRowSpec f) :
    HookOk f (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160) :=
  hookOk_edNegCryptoLeafStub_of_master h.1
theorem EdNegRowSpec.cryptoLeafStubVm {f : State → State} (h : EdNegRowSpec f) :
    HookOk f (withVmPreserved (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  hookOk_withVmPreserved h.cryptoLeafStub h.2
theorem EdNegRowSpec.cryptoLeafStubAlloc {f : State → State} (h : EdNegRowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim (cryptoLeafStubSpec (fun bs => vecU8 (dalekEdNegVec (u8Vec 160 bs))) 160 160)) :=
  hookOk_withAlloc_of_withVmPreserved A lim h.cryptoLeafStubVm
theorem EdNegRowSpec.at_stk {f : State → State} (h : EdNegRowSpec f) (stk : Nat := dalekHookStack) :
    DalekLsRowTuple f (dalekEdNegExtSpec stk) :=
  rowTuple_of_keepsFs_vm (hookOk_withLsRet (hookOk_withVmPreserved
    (hookOk_of_simulates (specSimulates_keepsFs (specSimulates_dalekEdNegExtSpec_of_unstacked stk))
      (hookOk_edNegUnstackedFalse_keepsFs_of_master h.1))
    h.2))

theorem edNegFallback_rowSpec : EdNegRowSpec (edNegHook dalekEdNegVec) :=
  ⟨edNegHook_masterEdNeg_ok, edNegHook_vmPreserved dalekEdNegVec⟩

theorem edNegFallback_fsT : HookFsTraced IsFsC (edNegHook dalekEdNegVec) :=
  edNegHook_fsT dalekEdNegVec

/-- Consumer `HookOk` arm for `lsMlkemPk1Sym` (`MlKemKeyPair::public_key`). -/
@[expose] def MlkemPk1RowSpec (f : State → State) : Prop :=
  HookOk f mlkemPk1Spec ∧ (∀ s : State, VmPreserved s (f s))

theorem MlkemPk1RowSpec.plain {f : State → State} (h : MlkemPk1RowSpec f) : HookOk f mlkemPk1Spec := h.1
theorem MlkemPk1RowSpec.vmPreserved {f : State → State} (h : MlkemPk1RowSpec f) (s : State) : VmPreserved s (f s) := h.2 s
theorem MlkemPk1RowSpec.vm {f : State → State} (h : MlkemPk1RowSpec f) :
    HookOk f (withVmPreserved mlkemPk1Spec) := hookOk_withVmPreserved h.1 h.2
theorem MlkemPk1RowSpec.alloc {f : State → State} (h : MlkemPk1RowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim mlkemPk1Spec) := hookOk_withAlloc_of_withVmPreserved A lim h.vm
theorem MlkemPk1RowSpec.ls {f : State → State} (h : MlkemPk1RowSpec f) :
    HookOk f (withLsRet mlkemPk1Spec) := hookOk_withLsRet h.1
theorem MlkemPk1RowSpec.lsVm {f : State → State} (h : MlkemPk1RowSpec f) :
    HookOk f (withLsRet (withVmPreserved mlkemPk1Spec)) := hookOk_withLsRet h.vm
theorem MlkemPk1RowSpec.lsAlloc {f : State → State} (h : MlkemPk1RowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim mlkemPk1Spec)) := hookOk_withLsRet (h.alloc A lim)

theorem mlkemPk1Hook_rowSpec : MlkemPk1RowSpec mlkemPk1Hook :=
  ⟨mlkemPk1Hook_ok, mlkemPk1Hook_vmPreserved⟩

theorem mlkemPk1Fallback_fsT : HookFsTraced IsFsC mlkemPk1Hook := mlkemPk1Hook_fsT

/-- Consumer `HookOk` arm for `lsMlkemPk2Sym` (`MlKemPublicKey::as_slice`). -/
@[expose] def MlkemPk2RowSpec (f : State → State) : Prop :=
  HookOk f mlkemPk2Spec ∧ (∀ s : State, VmPreserved s (f s))

theorem MlkemPk2RowSpec.plain {f : State → State} (h : MlkemPk2RowSpec f) : HookOk f mlkemPk2Spec := h.1
theorem MlkemPk2RowSpec.vmPreserved {f : State → State} (h : MlkemPk2RowSpec f) (s : State) : VmPreserved s (f s) := h.2 s
theorem MlkemPk2RowSpec.vm {f : State → State} (h : MlkemPk2RowSpec f) :
    HookOk f (withVmPreserved mlkemPk2Spec) := hookOk_withVmPreserved h.1 h.2
theorem MlkemPk2RowSpec.alloc {f : State → State} (h : MlkemPk2RowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withAlloc A lim mlkemPk2Spec) := hookOk_withAlloc_of_withVmPreserved A lim h.vm
theorem MlkemPk2RowSpec.ls {f : State → State} (h : MlkemPk2RowSpec f) :
    HookOk f (withLsRet mlkemPk2Spec) := hookOk_withLsRet h.1
theorem MlkemPk2RowSpec.lsVm {f : State → State} (h : MlkemPk2RowSpec f) :
    HookOk f (withLsRet (withVmPreserved mlkemPk2Spec)) := hookOk_withLsRet h.vm
theorem MlkemPk2RowSpec.lsAlloc {f : State → State} (h : MlkemPk2RowSpec f)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    HookOk f (withLsRet (withAlloc A lim mlkemPk2Spec)) := hookOk_withLsRet (h.alloc A lim)

theorem mlkemPk2Hook_rowSpec : MlkemPk2RowSpec mlkemPk2Hook :=
  ⟨mlkemPk2Hook_ok, mlkemPk2Hook_vmPreserved⟩

theorem mlkemPk2Fallback_fsT : HookFsTraced IsFsC mlkemPk2Hook := mlkemPk2Hook_fsT

end WithPlacement

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.CryptoDalekRowSpecs
