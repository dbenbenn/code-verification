/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5e
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5e: Arm 7 (`States.ct1Sampled`)

Verifies Arm 7 (`States.ct1Sampled`, `PolyEncoder` tag `0` or `1`, jump table index `7`,
`+0 -> +60 -> +828 -> +1712 -> +2028 -> +2100 -> +2116 -> +2128 -> +1544 -> ret`) under
`RustCliAllocBudget M`, `BudgetLimits`, and `Ct1SampledEnv`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize
   vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb
  (TraceCalleeSaved authenticatorHeap bv_add_add_lit' bv_sub_sub_lit'
   ekReceivedScratchCells epilogueStagingCells memRegion_1424_split_epilogue
   memRegion_ekReceived_scratch_split outWords28 protoPolynomialDecoderHeap
   protoPolynomialEncoderHeap stackAt_encoderIntoPb_eq_allocHook
   statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
   statesIntoPbStack vecU8CloneTail vecU8Heap)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (DecoderIntoPbAllocEnv DecoderIntoPbEnv fitsEnv_decoderIntoPbAllocEnv_of_decoderIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbAllocEnv EncoderIntoPbEnv fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)

open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget
  (ct1CloneEvents ct1DeallocEvents)

open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1CloneAndDropEnv Ct1SampledEnv chunkedCt1Sampled_expose
   ct1CloneAndDropEnv_of_dealloc ct1SampledEnv_of_parts
   ct1SampledScratchCells_entails_memRegions fitsEvents_clone_of_ct1CloneAndDropEnv
   outWords28_entails_ct1Sampled polyEncoderAt_eq_tag_tail polyEncoderTag
   polyEncoderTailAt stA_ct1Sampled_entails_928)


export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux
  (Ct1SampledEnv ct1SampledEnv_of_parts)

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  bv_sub_sub_lit' bv_add_add_lit'
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5eBudget
