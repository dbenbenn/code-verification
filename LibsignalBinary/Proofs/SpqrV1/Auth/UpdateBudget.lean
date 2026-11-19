/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.SpqrV1.Auth.Update -- shake: keep -- proof-setup: allow-public-import
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded Fixed-Offset Proof of `<spqr::authenticator::Authenticator>::update`

Re-exports the envelopes, `RustCliAllocBudget` specifications, and `[LibsignalPlacement]` proofs
from `UpdateBudgetAux`, and proves the fixed-offset `.inImage img` contracts for
`<Authenticator>::update` (`0x58ac4`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState toBEBytes)
open CryptoVerification.LibsignalSpqrV1 (
  Authenticator HkdfFn hkdfToSliceUnchecked hkdfToVecUnchecked spqrHkdfWith
)
open CryptoVerification.LibsignalTripleRatchet.Keys (SepWPp.rw_pre memRegion_32_cells)
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp (
  readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre
)
open CryptoVerification.RustHeap (LayoutOk RustAlloc vecU8At)
open CryptoVerification.SpqrV1.Auth (
  AuthUpdateGhost AuthUpdatePinnedGhost AuthenticatorGhost
  SepWPp.pure_left_focus
  authUpdateName authUpdateStackExt authUpdateStackX
  authenticatorAt authenticatorAt_eq_exists_pinned authenticatorPinAt
  authenticatorPinAt_expose_entails dealloc_vecBuf_cases
  drop_32_take_32_eq_drop_32_of_length_64 hkdfToVecUnchecked_eq_hkdfToSliceUnchecked
  pointsTo64_rev64_eq_toBEBytes pointsToBytes_64_entails_memRegion
  pointsToBytes_replicate_64_entails_memRegion toBEBytes_8_length
  vecBufAt vecBufAt_fold vecBufAt_of_cap_ne_zero vecBufAt_of_cap_zero
  vecU8At_expose_entails
)
open CryptoVerification.SpqrV1.Auth.UpdateFacts (authenticatorAt_of_32_32 rejoin_stack_authUpdateX replicate_32_zero_length stackAt_authUpdateX_split updateLabel_length)
open CryptoVerification.SpqrV1.ChainProofs (
  HkdfToSliceGhost SliceConcat2Ghost
  bytesAt bytesAt_false bytesAt_true exists_unpack64_of_length_64_split
  hkdfToSliceName hkdfToSliceSpec hkdfToSliceSpecExt hkdfToSliceSpqrSpec
  hkdfToSliceStackExt sliceConcatName
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpecBase rustDeallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStackBase rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocBudgetExternSpecWithStackBase subroutine_ok_rustCliAllocBudget_withStackBase
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (
  SliceConcat2Env sliceConcat2Events sliceConcat2Spec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget (subroutine_ok_post_entails)

open LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget (rebase_trapHooks_fnAddr shimSpecWithStack)

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst := h

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length updateLabel_length replicate_32_zero_length
  List.length_append
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre

abbrev optCapDeallocEvents := @UpdateBudgetAux.optCapDeallocEvents
abbrev sliceConcat2DeallocEvents := @UpdateBudgetAux.sliceConcat2DeallocEvents
abbrev optCapDeallocEvents_ofNat := @UpdateBudgetAux.optCapDeallocEvents_ofNat
abbrev freeOnlyEvs_optCapDeallocEvents := @UpdateBudgetAux.freeOnlyEvs_optCapDeallocEvents
abbrev freeOnlyEvs_sliceConcat2DeallocEvents :=
  @UpdateBudgetAux.freeOnlyEvs_sliceConcat2DeallocEvents
abbrev authUpdatePinnedEvents := @UpdateBudgetAux.authUpdatePinnedEvents
abbrev AuthUpdatePinnedEnv := @UpdateBudgetAux.AuthUpdatePinnedEnv
abbrev fitsEnv_authUpdatePinned_iff := @UpdateBudgetAux.fitsEnv_authUpdatePinned_iff
abbrev AuthUpdatePreAlloc1Env := @UpdateBudgetAux.AuthUpdatePreAlloc1Env
abbrev AuthUpdateAlloc2Env := @UpdateBudgetAux.AuthUpdateAlloc2Env
abbrev AuthUpdateLenEnv := @UpdateBudgetAux.AuthUpdateLenEnv
abbrev AuthUpdateEnv := @UpdateBudgetAux.AuthUpdateEnv
abbrev authUpdatePinnedEvents_mem_authUpdateLenEnv :=
  @UpdateBudgetAux.authUpdatePinnedEvents_mem_authUpdateLenEnv
abbrev authUpdatePinnedEvents_mem_authUpdateEnv :=
  @UpdateBudgetAux.authUpdatePinnedEvents_mem_authUpdateEnv
abbrev fitsEvents_pinned_of_fitsEnv_authUpdateEnv :=
  @UpdateBudgetAux.fitsEvents_pinned_of_fitsEnv_authUpdateEnv
abbrev spqrBoundedEvs_of_authUpdateLenEnv := @UpdateBudgetAux.spqrBoundedEvs_of_authUpdateLenEnv
abbrev spqrBoundedEvs_of_authUpdateEnv := @UpdateBudgetAux.spqrBoundedEvs_of_authUpdateEnv
abbrev fitsEvents_authUpdatePinned_unpack := @UpdateBudgetAux.fitsEvents_authUpdatePinned_unpack
abbrev authUpdatePinnedSpecAt := @UpdateBudgetAux.authUpdatePinnedSpecAt
abbrev authUpdateSpecAt := @UpdateBudgetAux.authUpdateSpecAt
abbrev authUpdatePinnedSpec := @UpdateBudgetAux.authUpdatePinnedSpec
abbrev authUpdateSpec := @UpdateBudgetAux.authUpdateSpec
abbrev authUpdatePinnedSpecExt := @UpdateBudgetAux.authUpdatePinnedSpecExt
abbrev authUpdateSpecExt := @UpdateBudgetAux.authUpdateSpecExt
abbrev AuthUpdatePlacedOk := @UpdateBudgetAux.AuthUpdatePlacedOk
abbrev seq_frame_lsCallInv_pool := @UpdateBudgetAux.seq_frame_lsCallInv_pool
abbrev withStack_withVmPreserved_shim_of_rustAllocShimVm :=
  @UpdateBudgetAux.withStack_withVmPreserved_shim_of_rustAllocShimVm
abbrev withLsCallInv_withVmPreserved_of_withAllocVmPreserved :=
  @UpdateBudgetAux.withLsCallInv_withVmPreserved_of_withAllocVmPreserved
abbrev expose_info_vecU8At := @UpdateBudgetAux.expose_info_vecU8At
abbrev vecBufAt_fold_append := @UpdateBudgetAux.vecBufAt_fold_append
abbrev authUpdatePinned_placed_ok := @UpdateBudgetAux.authUpdatePinned_placed_ok
abbrev authUpdate_placed_ok := @UpdateBudgetAux.authUpdate_placed_ok
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
            let prf ← Lean.Meta.mkAppM ``withSvc_fetch_eq
              #[Lean.mkConst ``Arm64.noSyscalls, decl.toExpr]
            let newTy ← Lean.Meta.inferType prf
            hyps := hyps.push { userName := `this, type := newTy, value := prf }
    if !hyps.isEmpty then
      let g ← Lean.Elab.Tactic.getMainGoal
      let (_, g') ← g.assertHypotheses hyps
      Lean.Elab.Tactic.replaceMainGoal [g']

private def authHkdfVmSpecAt (stk : Nat) (hkdf : HkdfFn) : Spec HkdfToSliceGhost where
  pre x s := ⌜s.readReg64 .x0 = x.saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.salt.length ∧
    s.readReg64 .x2 = x.ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 x.ikm.length ∧
    s.readReg64 .x4 = x.infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 x.info.length ∧
    s.readReg64 .x6 = x.okmA ∧ s.readReg64 .x7 = BitVec.ofNat 64 x.okmLen ∧
    x.salt.length < 2 ^ 63 ∧ x.ikm.length < 2 ^ 63 ∧
    (¬x.saltRO ∨ x.salt.length ≤ 64) ∧ (¬x.ikmRO ∨ x.ikm.length < 64) ∧
    32 ≤ x.info.length ∧ x.info.length < 55 ∧
    (x.okmLen = 32 ∨ x.okmLen = 64 ∨ x.okmLen = 96)⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ memRegion x.okmA x.okmLen ∗ stackAt s.sp stk
  post x s0 sf :=
    ⌜VmPreserved s0 sf ∧ (hkdf x.salt x.ikm x.info x.okmLen).length = x.okmLen ∧
      sf.trace = s0.trace⌝ ∗
    bytesAt x.saltRO x.saltA x.salt ∗ bytesAt x.ikmRO x.ikmA x.ikm ∗
    bytesAt x.infoRO x.infoA x.info ∗ (x.okmA ↦ₛ hkdf x.salt x.ikm x.info x.okmLen) ∗
    stackAt s0.sp stk

attribute [local irreducible] FitsEvents

end LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
