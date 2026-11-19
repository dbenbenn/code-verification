/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchet -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym433
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs

/-!
# Budget-Threaded Segment 9 (`apply_to_session_state`) Proofs

Re-exports the Segment 9 allocator event envelopes and block `130` (`159`) theorems from
`ApplyRatchetBudgetAux`, and proves the block `433` (`549`) theorems
(`applyRatchet_from_6d0_549_placed`, `applyRatchet_549_placed_ok`, and their `_x` `decFn`
variants) over `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto SessionState SignalProtocolError TripleRatchet
)
open CryptoVerification (
  LibsignalPlacement lsMemcpySym lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost decryptDraws okTagVec protocolAddressAt sessionStateAt signalMessageAt
  tapeAfter uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost extHookStack logOff
  sessionMemcpyRegionSpec trApplyStack trApplyStackX trAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  clearUpkStack clearUpkStackX
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_434 blkLib_eq_434 blkPl_434 logOff_tryDecryptPlacedImg
  tryDecryptCommonHeap tryDecryptPlacedImg tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt (
  Satisfies.mono_focus SepWP.setPC_setMem_ite_false
  SepWPp.elim_exists SepWPp.elim_exists_focus SepWPp.elim_memRegion8_focus
  SepWPp.elim_pure SepWPp.elim_pure_focus SepWPp.elim_vecU8_focus SepWPp.mono_focus
  allocHookStack_to_subStack applyRatchet_local_frame_entails_memRegion
  applyRatchet_ret_split applyRatchet_scr_split clearUpkStackX_to_subStack
  clearUpkStack_to_subStack decRel_of_trApplyRel decResultAt_ok_of_parts
  extHookStack_to_subStack extHookStack_to_trApplyStackX layoutOk_of_cap_ne_zero
  length_trStackBytes newPqr_dealloc_prep' newPqr_zero_prep noPanic_callee
  sepWPp_to_reaches_outcome stackAt_rootStack_of_parts stackAt_sub_split
  trApplyStackX_to_clearUpkStackX trApplyStack_to_clearUpkStack trAt_eq_stack_heap
  trAt_eq_withoutPq trAt_of_stack_heap trAt_of_withoutPq trAt_senderPad_len
  trHeapPart trStackBytes trWithoutPqAt tryDecryptSavedRegs_entails_memRegion
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.AuthDecryptFacts (
  spAligned_of_sp_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsRetAddr624_blockPlacement_base_add)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (
  clearUpkSpec clearUpkSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget (
  rustDeallocExternSpecWithStack withStack
)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget (
  TrApplyEnv trApplySpec trApplySpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  S9SeamPlaced S9SeamXPlaced tryDecryptFnRawSpecPlaced tryDecryptFnSpecPlaced
  tryDecryptRawSpecPlaced tryDecryptSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget (
  SepWPp.call_cro_frame_placed SepWPp.call_frame_placed SepWPp.of_sepWP_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (
  protocolAddressAt_atState sessionStateAt_atState signalMessageAt_atState
  trAt_atState vecResultAt_atState vecU8_atState
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

/-! ## 1. Re-Exports from `ApplyRatchetBudgetAux` -/

abbrev s9From6d0Env := ApplyRatchetBudgetAux.s9From6d0Env
abbrev s9Env := ApplyRatchetBudgetAux.s9Env
abbrev freeOnlyEvs_rustDeallocEvents := ApplyRatchetBudgetAux.freeOnlyEvs_rustDeallocEvents

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
