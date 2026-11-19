/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5b -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Heap.IfaceBudgetBase
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5b: Arm 9 (`States.ct1Acknowledged`) Step Lemmas

Step lemmas for Arm 9 (`States.ct1Acknowledged`, tag `11`) threading `RustCliAllocBudget M`,
`BudgetLimits`, `FitsEvents`, `FreeOnlyEvs`, `VmPreserved`, and `AllocCallPreserved`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbPanic TraceCalleeSaved bv_add_add_lit' bv_sub_sub_lit' ct1AcknowledgedScratchCells epilogueStagingCells ofNat_beq_zero_false' ofNat_lt_2pow63_and_highBit_zero ofNat_lt_2pow63_lsr63_zero ofNat_lt_2pow63_msb_zero ofNat_ne_zero_true statesIntoPbJumpTableAt statesIntoPbJumpTableBytes statesIntoPbName vecU8CloneTail vecU8CloneTail_entails_dealloc vecU8Heap vecU8Heap_nil_intro vecU8Heap_of_exact_alloc)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents FreeOnlyEvs
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)

private theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

private theorem vmPreserved_prepend {s s1 s2 : State}
    (h2 : VmPreserved s1 s2) (h1 : VmPreserved s s1) :
    VmPreserved s s2 :=
  h1.trans h2

local elab "lift_fetches_withSvc" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let lctx ← Lean.MonadLCtx.getLCtx
    let mut hyps : Array Lean.Meta.Hypothesis := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let ty ← Lean.instantiateMVars decl.type
        if ty.isAppOfArity ``Eq 3 && (ty.getArg! 1).isAppOfArity ``Arm64.Program.fetch 2 then
          let progE := (ty.getArg! 1).getArg! 0
          if !progE.isAppOfArity ``Arm64.Program.withSvc 2 then
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

local macro "by_into_pb_vm_steps " "(" tac:tacticSeq ")" : tactic =>
  `(tactic| (
      apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved
      ($tac)))

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_pre {prog : Program} {target : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog target s P' post) :
    SepWP prog target s P post :=
  heq ▸ h

/-! ## 1. Re-Exports of `RustAlloc`-Parametric Representation & Scratch Helpers -/

abbrev words4 := @CryptoVerification.SpqrV1.States.IntoPb.Relocatable.words4
abbrev words4_polyDecoderAt :=
  @CryptoVerification.SpqrV1.States.IntoPb.Relocatable.words4_polyDecoderAt
abbrev unchunkedCt1Sent_expose_clone :=
  @CryptoVerification.SpqrV1.States.IntoPb.unchunkedCt1Sent_expose_clone
abbrev chunkedCt1Acknowledged_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedCt1Acknowledged_expose
abbrev stA_ct1Acknowledged_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_ct1Acknowledged_entails_928
abbrev memRegion_ct1Acknowledged_scratch_split :=
  @CryptoVerification.SpqrV1.States.IntoPb.memRegion_ct1Acknowledged_scratch_split
abbrev ct1AcknowledgedScratchCells_entails_memRegions :=
  @CryptoVerification.SpqrV1.States.IntoPb.ct1AcknowledgedScratchCells_entails_memRegions
abbrev outWords28_entails_ct1Acknowledged :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_ct1Acknowledged

/-! ## 2. Allocator Event Lists & Sequencing Helpers for Arm 9 -/

/-- Exact allocator event list emitted when cloning `ct1 : List (BitVec 8)` in Arm 9:
`[]` when `ct1` is empty, `rustAllocEvents ct1.length 1` otherwise. -/
@[expose] def ct1CloneEvents (ct1 : List (BitVec 8)) : List AllocEvent :=
  if ct1.length = 0 then [] else rustAllocEvents ct1.length 1

/-- Exact allocator event list emitted when dropping the old `(cap_ct1, ptr_ct1)` buffer in Arm 9:
`[]` when `cap_ct1 == 0#64`, `rustDeallocEvents cap_ct1.toNat 1` otherwise. -/
@[expose] def ct1DeallocEvents (cap_ct1 : BitVec 64) : List AllocEvent :=
  if cap_ct1 == 0#64 then [] else rustDeallocEvents cap_ct1.toNat 1

theorem freeOnlyEvs_ct1DeallocEvents (cap_ct1 : BitVec 64) :
    FreeOnlyEvs (ct1DeallocEvents cap_ct1) := by
  unfold ct1DeallocEvents
  by_cases hc : (cap_ct1 == 0#64) = true
  · simp only [hc, ↓reduceIte]
    exact FreeOnlyEvs.nil
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact FreeOnlyEvs.singleton 1 cap_ct1.toNat

private theorem allocCallPreserved_trans {s0 s1 s2 : State}
    (h1 : AllocCallPreserved s0 s1) (h2 : AllocCallPreserved s1 s2) :
    AllocCallPreserved s0 s2 := by
  rcases h1 with ⟨hfs1, htr1, hsig1, htp1, hbs1, hor1, hsym1⟩
  rcases h2 with ⟨hfs2, htr2, hsig2, htp2, hbs2, hor2, hsym2⟩
  exact ⟨hfs2.trans hfs1, htr2.trans htr1, hsig2.trans hsig1,
    htp2.trans htp1, hbs2.trans hbs1, hor2.trans hor1, hsym2.trans hsym1⟩

private theorem seq_vm_step {P : Program} {b : BitVec 64} {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State}
    {Pre P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP (P.rebase b Hk) mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP (P.rebase b Hk) target sm P_mid post) :
    SepWP (P.rebase b Hk) target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hvm, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hvm hQ)

/-! ## 3. Step Lemmas for Arm 9 (`States.ct1Acknowledged`) -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
