/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
public import Arm64.Trusted.Object.Labels
public import ProofLib.BV
public import ProofLib.BV.MaskLemmas
public import ProofLib.BV.PolyMul
public import ProofLib.GenPlacedFetches
public import ProofLib.Hoare.MultiCodeROHook
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.MallocngBridge
public import ProofLib.Placed
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage
public import ProofLib.Placed.LabelsInterned
public import ProofLib.Placed.SharedCode
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.LoopTactics
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
public import ProofLib.StdStartup.OutlineAtomics
public import ProofLib.StdStartup.Strlen
public import VerifiedLibraries.Mallocng.Spec
public import VerifiedLibraries.Mallocng.Spec.Cost
public import VerifiedLibraries.Musl.Spec.Top
public import VerifiedLibraries.RustStd.Spec
public import VerifiedLibraries.RustStd.Spec.AllocFormatInner
public import VerifiedLibraries.RustStd.Spec.AllocFormatInnerBudget
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Spec.CoreFmtDisplay
public import VerifiedLibraries.RustStd.Spec.CoreFmtWrite
public import VerifiedLibraries.RustStd.Spec.CoreFromUtf8
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import VerifiedLibraries.RustStd.Spec.FsRead
public import VerifiedLibraries.RustStd.Spec.FsWrite
public import VerifiedLibraries.RustStd.Spec.Stdio
public import VerifiedLibraries.RustStd.Spec.TimeAdd
public import VerifiedLibraries.RustStd.Spec.TimeDurationSince
import LibsignalBinary.Proofs.CodeLayout
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaFullProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedCallocProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocEntryProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedPosixMemalignProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded Stage P2 Matched-Session Basic Blocks: Part B

`VmPreserved` and pool-threaded `p2_matched_to_dealloc_*_wp` / `p2_matched_to_remote_ik_*_wp`
segments, plus the budget-threaded `<str as ToOwned>::to_owned` envelope `StrToOwnedEnv` and
contracts `strToOwnedLocal2Spec` / `strToOwnedLocal2SpecWithStack`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  strToOwnedLocal2Name strToOwnedLocal2Stack strToOwnedLocal2StackWith
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget VmPreserved rustAllocEvents
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  strToOwnedLocal2Name strToOwnedLocal2Stack strToOwnedLocal2StackWith
  stackAt_strToOwnedLocal2 stackAt_strToOwnedLocal2With memRegion24_cells3
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cond_eq_adds_1_false_m2_budget {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

private theorem sepWP_frame_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {target_pc : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q : State → Prop}
    (hwp : SepWP prog target_pc s Pre
      (fun s1 P_f => (P_f ⊢ Post) ∧ VmPreserved s s1 ∧ Q s1)) :
    SepWP prog target_pc s (Pre ∗ A.pool lim st s)
      (fun s1 P_f => (P_f ⊢ Post ∗ A.pool lim st s1) ∧ Q s1) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL
  rcases hout with ⟨hpc1, hrun1, P_f, hPf, hent, hvm, hQ⟩ | ⟨_, hoom⟩
  · refine ⟨s1, hsteps, Or.inl ⟨hpc1, hrun1, P_f ∗ A.pool lim st s, ?_, ?_, hQ⟩⟩
    · rwa [sepConj_assoc]
    · rw [A.pool_of_vmPreserved hvm]
      exact sepConj_mono_left hent
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Exact binary allocator event trace of `<str as alloc::borrow::ToOwned>::to_owned` on a
non-empty string slice (`0 < bs.length`): a single `__rust_alloc(bs.length, 1)` call. -/
abbrev strToOwnedEvents (bs : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents bs.length 1

/-- Exact singleton event envelope for `<str as alloc::borrow::ToOwned>::to_owned`
(`0 < bs.length`). -/
@[expose] def StrToOwnedEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  fun evs => evs = strToOwnedEvents bs

theorem fitsEnv_strToOwnedEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} :
    FitsEnv M lim st (StrToOwnedEnv bs) ↔ FitsEvents M lim st (strToOwnedEvents bs) :=
  ⟨fun h => h _ rfl, fun h _ heq => heq ▸ h⟩

/-- Stack-parametric budget-threaded contract of `<str as alloc::borrow::ToOwned>::to_owned`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEvents M lim st (strToOwnedEvents bs)`). -/
@[expose] def strToOwnedLocal2SpecWithStack (hookStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((outPtr, srcPtr, bs), st) s =>
    ⌜s.readReg64 .x0 = outPtr ∧
     s.readReg64 .x1 = srcPtr ∧
     s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
     0 < bs.length ∧
     bs.length < 2 ^ 63 ∧
     FitsEvents M lim st (strToOwnedEvents bs)⌝ ∗
    memRegion outPtr 24 ∗
    (srcPtr ↦ᵣ bs) ∗
    A.pool lim st s ∗
    stackAt s.sp (strToOwnedLocal2StackWith hookStack)
  post := fun ((outPtr, srcPtr, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A.repAlloc outPtr bs ∗
    (srcPtr ↦ᵣ bs) ∗
    A.pool lim (M.stepEvents (strToOwnedEvents bs) st) sf ∗
    stackAt s0.sp (strToOwnedLocal2StackWith hookStack)

/-- Budget-threaded contract of `<str as alloc::borrow::ToOwned>::to_owned` at `allocHookStack`
(`strToOwnedLocal2Stack = 48 + allocHookStack`). -/
abbrev strToOwnedLocal2Spec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) :=
  strToOwnedLocal2SpecWithStack allocHookStack A lim

theorem vecU8_of_exact_alloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (outPtr p : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp : p ≠ 0#64) :
    (outPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((outPtr + 8#64) ↦₆₄ p) ∗
    ((outPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live p bs.length 1 ∗
    (p ↦ₛ bs) ⊢
      vecU8 A.repAlloc outPtr bs :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.vecU8_of_exact_alloc
    A.repAlloc outPtr p bs hpos hlt hp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget
