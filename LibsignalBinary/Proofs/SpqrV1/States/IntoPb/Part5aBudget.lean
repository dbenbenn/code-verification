/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5a
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# `<spqr::v1::chunked::states::States>::into_pb` — Part 5a: Arm 8 (`States.ekReceivedCt1Sampled`)

Verifies `states_into_pb_ekReceivedCt1Sampled` (Arm 8, tag `10`, jump table index `8` -> `+1644`)
under `RustCliAllocBudget M`, `BudgetLimits`, and `EkReceivedCt1SampledEnv`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (PolyEncoder States spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (EkReceivedCt1Sampled)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Drop (
  chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero noneCap_add_two_beq_zero
  optProtoInnerStateAt optProtoInnerStateSize
)
open CryptoVerification.SpqrV1.Poly (polyEncoderAt polyEncoderSize)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbStack)
open CryptoVerification.SpqrV1.States.IntoPb (
  authenticatorHeap ekReceivedScratchCells epilogueStagingCells
  memRegion_1424_split_epilogue memRegion_ekReceived_scratch_split outWords28
  protoPolynomialEncoderHeap stackAt_encoderIntoPb_eq_allocHook
  statesIntoPbJumpTableAt statesIntoPbName statesIntoPbSavedCells
  statesIntoPbStack vecU8CloneTail vecU8Heap
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbAllocEnv EncoderIntoPbEnv fitsEnv_encoderIntoPbAllocEnv_of_encoderIntoPbEnv)

open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5bBudget (
  ct1CloneEvents ct1DeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv chunkedEkReceivedCt1Sampled_expose ct1CloneAndDropEnv_of_dealloc ekReceivedCt1SampledEnv_of_parts ekReceivedScratchCells_entails_memRegions fitsEvents_clone_of_ct1CloneAndDropEnv outWords28_entails_ekReceivedCt1Sampled stA_ekReceivedCt1Sampled_entails_928 statesIntoPbEkReceivedCt1SampledSpec statesIntoPbVariantSpecOfEnv)


export LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5dBudgetAux (
  Ct1CloneAllocEnv Ct1CloneAndDropEnv EkReceivedCt1SampledEnv
  ekReceivedCt1SampledEnv_of_parts statesIntoPbVariantSpecOfEnv
  statesIntoPbEkReceivedCt1SampledSpec
)
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part5aBudget
