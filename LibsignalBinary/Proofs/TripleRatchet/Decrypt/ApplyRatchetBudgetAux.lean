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
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DecryptCodeSym130
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs

/-!
# Budget-Threaded Segment 9 (`apply_to_session_state`) Proofs — Block `130` (`159`)

Defines the Segment 9 allocator event envelopes (`s9From6d0Env`, `s9Env`) and proves the
relocatable `[LibsignalPlacement]` block `130` (`159`) Segment 9 theorems
(`applyRatchet_from_6d0_159_placed`, `applyRatchet_159_placed_ok`, and their `_x` `decFn`
variants) over `RustCliAllocBudget M`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624 lsRetAddr624_blockPlacement_base_add)

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto SessionState SignalMessage SignalProtocolError TripleRatchet
)
open CryptoVerification (
  LibsignalPlacement lsMemcpySym lsRustDeallocSym lsmpl lsρ
)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.LibsignalSessionRepr (RatchetGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost decryptDraws okTagVec
  protocolAddressAt sessionStateAt signalMessageAt tapeAfter uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TrGhost TryDecryptGhost extHookStack logOff
  sessionMemcpyRegionSpec trApplyStack trApplyStackX trAt withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  clearUpkStack clearUpkStackX
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkLib_eq_131 blkPl_131 logOff_tryDecryptPlacedImg
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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] BitVec.toNat_zero

private theorem sepWP_seg_130 [LibsignalPlacement] {H : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hseg : ∀ m_strip : Memory,
      SepWP ((blkPC_131).rebase (blkPl_131).base (hooksException H)) mid (s.setMem m_strip) Pre
        (fun sm' Pm => ∀ m_real : Memory, ProofLib.NonSyscallPreserved s (sm'.setMem m_real) →
          SepWP ((blkPC_131).rebase (blkPl_131).base H) target (sm'.setMem m_real) Pm post oom)) :
    SepWP ((blkPC_131).rebase (blkPl_131).base H) target s Pre post oom :=
  sepWP_seg_ls_vm (Q := (blkPC_131).rebase (blkPl_131).base (hooksException H)) blkLib_eq_131 (by rfl) hseg

local macro "wp_sync_130 " mid:term : tactic =>
  `(tactic| (
    apply sepWP_seg_130 (mid := $mid); intro _m_strip; wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool (_hnsp.toVmPreserved (by wp_norm_lhs)) (hnext := ?_)))

/-! ## 1. `atState` Normalization & Segment-9 Envelopes (`s9From6d0Env`, `s9Env`) -/

theorem vecU8_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 (A.atState lim st s) a bs = vecU8 A.repAlloc a bs := rfl

theorem vecResultAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (r : BitVec 64)
    (res : Except SignalProtocolError (List (BitVec 8))) :
    vecResultAt (A.atState lim st s) r res = vecResultAt A.repAlloc r res := rfl

theorem protocolAddressAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (g : AddrGhost) (a : BitVec 64) :
    protocolAddressAt (A.atState lim st s) g a = protocolAddressAt A.repAlloc g a := rfl

theorem signalMessageAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (g : SignalMessageGhost) (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt (A.atState lim st s) g a m = signalMessageAt A.repAlloc g a m := rfl

theorem sessionStateAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (ss : BitVec 64) (G : SessionGhost) (st1 : SessionState (List (BitVec 8))) :
    sessionStateAt (A.atState lim st s) ss G st1 = sessionStateAt A.repAlloc ss G st1 := rfl

theorem trAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trAt (A.atState lim st s) a G tr = trAt A.repAlloc a G tr := rfl

theorem trWithoutPqAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (a : BitVec 64) (G : RatchetGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trWithoutPqAt (A.atState lim st s) a G tr = trWithoutPqAt A.repAlloc a G tr := rfl

theorem trHeapPart_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State)
    (G : TrGhost) (tr : TripleRatchet (List (BitVec 8))) :
    trHeapPart (A.atState lim st s) G tr = trHeapPart A.repAlloc G tr := rfl

theorem freeOnlyEvs_rustDeallocEvents (sz al : Nat) :
    FreeOnlyEvs (rustDeallocEvents sz al) :=
  FreeOnlyEvs.singleton al sz

/-- Segment-9 tail envelope from `+0x6d0` (`+1744`): `apply_to_session_state` (`TrApplyEnv`)
    followed by `clear_unacknowledged_pre_key_message` (`FreeOnlyEvs`). -/
@[expose] def s9From6d0Env : List AllocEvent → Prop :=
  SeqEnv TrApplyEnv FreeOnlyEvs

/-- Full Segment-9 (`+0x6a4` / `+1700` → return) allocator event envelope: optional old-`pqrState`
    deallocation (`FreeOnlyEvs`) followed by `s9From6d0Env`. -/
@[expose] def s9Env (_x : TryDecryptGhost) (_trG : TrGhost) (_tr : TripleRatchet (List (BitVec 8)))
    (_st1 : SessionState (List (BitVec 8))) (_newPqrState : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs s9From6d0Env

/-! ## 2. Block `130` (`159`) Segment-9 Proofs (`S9SeamPlaced` & `S9SeamXPlaced`) -/

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux
