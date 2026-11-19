/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Mid
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedSegs
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public meta import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget
public meta import ProofLib.SepLogic.WP -- shake: keep
public meta import Lean -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import ProofLib.ProgramReflection.SortedFresh
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
meta import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Middle Segments

Re-exports `SendCt2StepsBudget`, `SendCt2MidBudgetAux`, and `SendCt2MidPlacedBudget`, and
proves fixed-base `RustCliAllocBudget`-threaded Segment 5a (`+676 → +836`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator libcruxHmacName spqrAuthApi
)
open CryptoVerification.SpqrV1.Auth (
  pointsTo64_rev64_eq_toBEBytes toBEBytes_8_length
)
open CryptoVerification.SpqrV1.ChainProofs (
  SliceConcat3Ghost bytesAt_false bytesAt_true sliceConcatName
)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost unchunkedCt1SentEkReceivedSendCt2Name)
open CryptoVerification.SpqrV1.Unchunked (bytes_rem_entails_memRegion_cap ctLabel_length exists_unpack64_of_length_128 fold_sp_144_24 fold_sp_272_24_24 macCtUnchecked_eq_hmacWith memRegion_128_cells memRegion_ct1_split_128_len memRegion_sp_272_split_48_80 pointsToBytes_append_ct1_ct2 stackAt_extHook_eq_allocHook)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec libcruxHmacSha256Events)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  SliceConcat3Env sliceConcat3Events sliceConcat3Spec
)

open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2StepsBudgetAux (SendCt2Reserve128Env UnchunkedSendCt2PreEnv fitsEnv_sliceConcat3_of_concatHmac fitsEvents_concatHmac_of_preEnv libcruxHmacSafeBudgetSpec sendCt2ConcatHmacEvents sendCt2Seg23Events sepWPp_call_noPanic sepWPp_exists_left_eq sepWPp_intro_state sepWPp_pure_left_eq sepWPp_rw_pre_eq)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudgetAux (call_rustDealloc_cs_wpp call_rustDealloc_cs_wppBase expose_concat3_md_sp_144 fitsEvents_hmac_of_concatHmac sendCt2Seg5aEvents sepWPp_pure_left_focus)

export LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidPlacedBudget (
  send_ct2_append_hmac_placed_wpp
  send_ct2_append_hmac_placed_preEnv_wpp
)

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.sp_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg64_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg32_setMem_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setPC_pre
  CryptoVerification.SpqrV1.Alloc.DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

local macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))

/-! ## Fixed-Base Segment 5a (`+676 → +836`) -/

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2MidBudget
