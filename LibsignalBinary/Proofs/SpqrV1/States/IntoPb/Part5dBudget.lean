/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5d: Arm 7 (`States.ct1Sampled`) Step Lemmas

Step lemmas for Arm 7 (`States.ct1Sampled`, `PolyEncoder` tag `0` or `1`, jump table index `7`,
`+60 -> +828 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544`) threading
`RustCliAllocBudget M`, `BudgetLimits`, `FitsEnv`/`FitsEvents`, `VmPreserved`, and
`AllocCallPreserved`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (
  PolyDecoder PolyEncoder States spqrAuthApi spqrPolyApi
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  none2Cap_add_two_beq_zero noneCap_add_two_beq_zero vecCapPtrDealloc
)
open CryptoVerification.SpqrV1.Poly (
  polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
  protoPolynomialDecoderSize protoPolynomialEncoderSize
)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbPanic TraceCalleeSaved bv_add_add_lit' bv_sub_sub_lit' ekReceivedScratchCells epilogueStagingCells ofNat_beq_zero_false' ofNat_lt_2pow63_and_highBit_zero ofNat_lt_2pow63_lsr63_zero ofNat_lt_2pow63_msb_zero ofNat_ne_zero_true protoPolynomialDecoderHeap protoPolynomialEncoderHeap sp_sub_1520_add_1424 sp_sub_480_add_200 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168 sp_sub_96_sub_176 sp_sub_96_sub_192 sp_sub_96_sub_208 statesIntoPbJumpTableAt statesIntoPbJumpTableBytes statesIntoPbName vecU8CloneTail vecU8CloneTail_entails_dealloc vecU8Heap vecU8Heap_nil_intro vecU8Heap_of_exact_alloc)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved rustAllocEvents rustCliAllocNoOomSpecBase
  rustCliDeallocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (
  DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (
  EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (
  ct1CloneEvents ct1DeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (align_pre allocCallPreserved_trans rebase_fnAddr_eq seq_vm_step vmPreserved_prepend withSvc_fetch_eq)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)

export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (
  Ct1CloneAllocEnv Ct1CloneAndDropEnv Ct1SampledEnv ct1SampledEnv_of_parts
  polyEncoderTag encoderStateTailAt polyEncoderTailAt polyEncoderAt_eq_tag_tail
  polyEncoderTag_eq_zero_or_one chunkedCt1Sampled_expose stA_ct1Sampled_entails_928
  ct1SampledScratchCells_entails_memRegions outWords28_entails_ct1Sampled
  statesIntoPbVariantSpecOfEnv statesIntoPbCt1SampledSpec
)

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
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_1520_add_1424
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168 sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

/-! ## Step Lemmas for Arm 7 (`+60 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544`) -/

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget
