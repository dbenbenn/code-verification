/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Raw -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Steps
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Specifications.AsmConstants
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `promote_matching_session`: Raw Subroutine Helpers

`VmPreserved`-strengthened specifications, prologue/epilogue steppers, and constant-time loop raw
subroutine proofs for `Matched.M1Budget`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1BudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched hiding
  promoteMatchingSessionMatchSpec promoteMatchingSessionMatchSpecExt

attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## `VmPreserved`-strengthened specifications -/

@[expose] def promoteMatchingSessionRawBudgetSpec : Spec PromoteRawGhost :=
  withVmPreserved promoteMatchingSessionRawSpec

@[expose] def promoteMatchingSessionRawBudgetSpecExt32 : Spec PromoteRawGhost :=
  withVmPreserved promoteMatchingSessionRawSpecExt32

@[expose] def promoteMatchingSessionMatchBudgetSpec (A : RustAlloc) : Spec PromoteMatchGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.promoteMatchingSessionMatchSpec A)

abbrev promoteMatchingSessionMatchSpec (A : RustAlloc) : Spec PromoteMatchGhost :=
  promoteMatchingSessionMatchBudgetSpec A

@[expose] def promoteMatchingSessionMatchBudgetSpecExt (A : RustAlloc) : Spec PromoteMatchGhost :=
  withVmPreserved
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.promoteMatchingSessionMatchSpecExt A)

abbrev promoteMatchingSessionMatchSpecExt (A : RustAlloc) : Spec PromoteMatchGhost :=
  promoteMatchingSessionMatchBudgetSpecExt A

/-! ## Arithmetic, hook, prologue, and epilogue `VmPreserved` lemmas -/

private theorem cond_eq_adds_1_false {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

private theorem cond_ne_subs64_one {n : Nat} (hgt : 1 < n) (hlt : n < 2 ^ 64) :
    ConditionHolds CondCode.NE (subsPState64 (BitVec.ofNat 64 n) 1#64) = true := by
  rw [conditionHolds_ne_subsPState64, bne_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at hnat
  omega

private theorem ofNat64_succ_sub_one (n : Nat) :
    BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n := by
  bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_1184_align (sp : BitVec 64) :
    ((sp - 1184#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

private theorem sp_sub_1184_aligned {sp : BitVec 64}
    (h : (sp &&& 15#64 == 0#64) = true) :
    ((sp - 1184#64) &&& 15#64 == 0#64) = true := by
  rwa [sp_sub_1184_align]

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_sub_96_align (sp : BitVec 64) :
    ((sp - 96#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem sp_add_1088_align (sp : BitVec 64) :
    ((sp + 1088#64) &&& 15#64) = (sp &&& 15#64) := by
  bv_robdd

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs32_self (v : BitVec 32) :
    ConditionHolds CondCode.EQ (subsPState32 v v) = true := by
  rw [conditionHolds_eq_subsPState32, beq_self_eq_true]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs32_self (v : BitVec 32) :
    ConditionHolds CondCode.NE (subsPState32 v v) = false := by
  rw [conditionHolds_ne_subsPState32, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ne_subs64_self (v : BitVec 64) :
    ConditionHolds CondCode.NE (subsPState64 v v) = false := by
  rw [conditionHolds_ne_subsPState64, bne_self_eq_false]

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_setWidth32_byte (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).setWidth 32 = v.zeroExtend 32 := by
  bv_omega

@[local simp, local wp_norm, local arm64_norm]
private theorem zext64_extractLsb32_byte (v : BitVec 8) :
    (v.zeroExtend 64 : BitVec 64).extractLsb' 0 32 = v.zeroExtend 32 := by
  bv_slice

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_setWidth32 (sessVer : BitVec 32) :
    BitVec.setWidth 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem csel_ver_extractLsb32 (sessVer : BitVec 32) :
    BitVec.extractLsb' 0 32 (if ConditionHolds CondCode.EQ (subsPState32 sessVer 0#32)
      then 2#64 else BitVec.setWidth 64 sessVer) =
    if sessVer = 0#32 then 2#32 else sessVer := by
  rw [conditionHolds_eq_subsPState32]
  by_cases h : sessVer = 0#32
  · subst h; decide
  · simp only [beq_iff_eq, h, ↓reduceIte]
    bv_slice

@[local simp, local wp_norm, local arm64_norm]
private theorem byte_bne_zext32_self (a : BitVec 8) :
    (BitVec.setWidth 32 a != BitVec.setWidth 32 a) = false :=
  bne_self_eq_false _

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_ite_1_0 (c : Bool) :
    BitVec.setWidth 32 (if c = true then 1#64 else 0#64) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth8_ite_1_0 (c : Bool) :
    BitVec.setWidth 8 (if c = true then 1#64 else 0#64) = if c = true then 1#8 else 0#8 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_32 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#32 else 0#32) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth64_ite_1_0_8 (c : Bool) :
    BitVec.setWidth 64 (if c = true then 1#8 else 0#8) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#64 else 0#64) &&& (if c2 = true then 1#64 else 0#64)) =
      if (c1 && c2) = true then 1#64 else 0#64 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 1#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and64_mask32_ite_1_0 (c : Bool) :
    ((if c = true then 1#64 else 0#64) &&& 4294967297#64) = if c = true then 1#64 else 0#64 := by
  cases c <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_ite_1_0 (c1 c2 : Bool) :
    ((if c1 = true then 1#32 else 0#32) &&& (if c2 = true then 1#32 else 0#32)) =
      if (c1 && c2) = true then 1#32 else 0#32 := by
  cases c1 <;> cases c2 <;> rfl

@[local simp, local wp_norm, local arm64_norm]
private theorem and32_1_ite_1_0 (c : Bool) :
    ((if c = true then 1#32 else 0#32) &&& 1#32) = if c = true then 1#32 else 0#32 := by
  cases c <;> rfl

private theorem extractLsb32_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    v.extractLsb' 0 32 = 1#32 := by
  bv_slice

private theorem and64_mask8_of_setWidth32_eq_one {v : BitVec 64}
    (h : v.setWidth 32 = 1#32) :
    (v &&& 255#64) = 1#64 := by
  bv_slice

private theorem cells_96_12_eq (sp : BitVec 64) :
    cells (sp - 96#64) 12 =
      (∃∗ v0, (sp - 96#64) ↦₆₄ v0 ∗
      ∃∗ v1, (sp - 88#64) ↦₆₄ v1 ∗
      ∃∗ v2, (sp - 80#64) ↦₆₄ v2 ∗
      ∃∗ v3, (sp - 72#64) ↦₆₄ v3 ∗
      ∃∗ v4, (sp - 64#64) ↦₆₄ v4 ∗
      ∃∗ v5, (sp - 56#64) ↦₆₄ v5 ∗
      ∃∗ v6, (sp - 48#64) ↦₆₄ v6 ∗
      ∃∗ v7, (sp - 40#64) ↦₆₄ v7 ∗
      ∃∗ v8, (sp - 32#64) ↦₆₄ v8 ∗
      ∃∗ v9, (sp - 24#64) ↦₆₄ v9 ∗
      ∃∗ v10, (sp - 16#64) ↦₆₄ v10 ∗
      ∃∗ v11, (sp - 8#64) ↦₆₄ v11 ∗ emp) := by
  have hstep (k1 k2 : BitVec 64) (h : k1 - 8#64 = k2) : (sp - k1) + 8#64 = sp - k2 := by
    subst h; bv_omega
  dsimp only [cells]
  rw [hstep 96#64 88#64 rfl, hstep 88#64 80#64 rfl, hstep 80#64 72#64 rfl,
      hstep 72#64 64#64 rfl, hstep 64#64 56#64 rfl, hstep 56#64 48#64 rfl,
      hstep 48#64 40#64 rfl, hstep 40#64 32#64 rfl, hstep 32#64 24#64 rfl,
      hstep 24#64 16#64 rfl, hstep 16#64 8#64 rfl]

private theorem step_blackBox_ext32_vm {prog : Program} {target_pc entry_bb ret_pc : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop}
    (hbb : subroutine_ok prog entry_bb
      (withVmPreserved CryptoVerification.SignalSession.CliExt.blackBoxSpec))
    (hpc : s.pc = entry_bb)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      VmPreserved s sf →
      (sf.readReg64 .x0).setWidth 32 = 1#32 →
      sf.trace = s.trace →
      SepWP prog target_pc sf (stackAt sf.sp extHookStack ∗ F) post) :
    SepWP prog target_pc s (stackAt s.sp extHookStack ∗ F) post := by
  refine SepWP.call_subroutine_frame_auto (x := 1#64) (F := F) hbb hpc hrun hsp_align hlr
    (fun _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun sf hpcf hrunf hspf hcsf => ?_)
    (fun R hm => ?_)
  · dsimp only [withVmPreserved, CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    simp only [sepConj_assoc, ← hspf]
    refine SepWP.focus_pure (by sep_focus) fun hvm => ?_
    refine SepWP.focus_pure (by sep_focus) fun hpure => ?_
    exact hnext sf hpcf hrunf hspf hcsf hvm hpure.1 hpure.2
  · dsimp only [withVmPreserved, CryptoVerification.SignalSession.CliExt.blackBoxSpec,
      CryptoVerification.SignalSession.CliExt.withStack]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hx0, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1BudgetAux
