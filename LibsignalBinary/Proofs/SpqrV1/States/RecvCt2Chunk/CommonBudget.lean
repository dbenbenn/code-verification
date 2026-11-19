/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.IsNonZero -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofXBudget
public import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux -- proof-setup: allow-public-import
public meta import Lean -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public meta import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudgetAux -- shake: keep -- proof-setup: allow-public-import
public meta import ProofLib.SepLogic.WP.ControlTactics -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.OptContractsBudget
public import VerifiedLibraries.Musl.Spec
import LibsignalBinary.Proofs.SpecLemmas.ReachesOutcome
import LibsignalBinary.Proofs.SpecLemmas.SymtabGhost
public import VerifiedLibraries.Musl.Proofs.CryptoHooks
public import VerifiedLibraries.Musl.Proofs.MemmoveProof
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExtBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.GF.GfCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.Defs
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVec
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<EkSentCt1Received>::recv_ct2_chunk`: Budget Callee Contracts & Framing Helpers

`VmPreserved` proofs for `spqr::util::is_non_zero` (`0x5e50c` / Block `380`), total-correctness
`libcruxHmacSafeBudgetSpec`, and fixed-offset budget callee contracts for `recv_ct2_chunk`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget

open CryptoVerification.LibsignalTripleRatchet (extHookStack)

open CryptoVerification (LibsignalPlacement blkPC_380 blkPl_380)

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.LibsignalSession (ShaCompress)
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 (
  Bytes HkdfFn LibcruxHmacCall MlKem NUM_POLYS isNonZero
  libcruxHmacName mlkemDecapsName mlkemDecapsSpec optKeyBytesAt spqrHkdfWith
)
open CryptoVerification.RustHeap (RustAlloc vecU8)
open CryptoVerification.SpqrV1.Alloc (doReserve7Name)
open CryptoVerification.SpqrV1.Auth (authUpdateName)

open CryptoVerification.SpqrV1.ChainProofs (
  hkdfToSliceSpecExt hkdfToSliceSpqrSpec sliceConcatName
)

open CryptoVerification.SpqrV1.Drop (
  DropGlueSortedSetPt16Ghost dropSortedSetPt16Name sub_ok_of_addr_eq
)
open CryptoVerification.SpqrV1.GF.IsNonZero (isNonZeroName isNonZeroSpec isNonZero_asm_eq readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre stackAt_16_merge_byte12 stackAt_16_split_byte12)
open CryptoVerification.SpqrV1.Kdf (hkdfToSliceName)
open CryptoVerification.SpqrV1.Poly (
  boolByte polyDecoderAt polyDecoderIsCompleteOff polyDecoderPadOff
  polyDecoderPadSize polyDecoderPtsNeededOff sortedSetPtListOf vecHeaderBytes
)
open CryptoVerification.SpqrV1.Poly.AddChunk (PolyDecoderStrictSorted addChunkName)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (
  DecodedMessageGhost decodedMessageName decodedMessageStack decodedMessageTotal
  decodedMessage_eq_ok optVecU8Of
)
open CryptoVerification.SpqrV1.States.RecvCt2Chunk (SplitBytes polyDecodedMessageName polyDecodedMessageStackX recvCt2ChunkName)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
  rustCliDeallocBudgetExternSpecWithStack
)
open LibsignalBinary.Heap.SpecBudget (
  LibcruxHmacEnv libcruxHmacBudgetSpec libcruxHmacSha256Events withVmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  sepWP_rebase_vmPreserved trapHooks
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (
  sliceConcat3Spec sliceConcat3SpecXA
)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget (doReserveSpecX)

open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec dropGlueSortedSetPt16SpecBase)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget (addChunkSpecX)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget (PolyDecodedMessageEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2MemcpyBudgetSpecX session2ShimBudgetSpecX)

open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec
)

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst := h

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm, local wp_norm] isNonZero_asm_eq
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

abbrev onPanic_false_entails_recvCt2 := @CommonBudgetAux.onPanic_false_entails_recvCt2
abbrev onPanic_pure_entails_recvCt2 := @CommonBudgetAux.onPanic_pure_entails_recvCt2
abbrev onPanic_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_budget_entails_recvCt2
abbrev onPanic_hmac_budget_entails_recvCt2 := @CommonBudgetAux.onPanic_hmac_budget_entails_recvCt2
abbrev allowPanic_isPanic_budget_recvCt2 := @CommonBudgetAux.allowPanic_isPanic_budget_recvCt2

abbrev recvCt2ChunkBudgetPostQp := @CommonBudgetAux.recvCt2ChunkBudgetPostQp

abbrev SplitBytes.memcpyVm_withStack_ok := @CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok
abbrev splitBytes_memcpyVm_withStack_ok := @CommonBudgetAux.SplitBytes.memcpyVm_withStack_ok

abbrev fitsEnv_seqEnv_left := @CommonBudgetAux.fitsEnv_seqEnv_left
abbrev fitsEnv_seqEnv_right := @CommonBudgetAux.fitsEnv_seqEnv_right
abbrev seqEnv_nonempty := @CommonBudgetAux.seqEnv_nonempty
abbrev authUpdateLenEnv_nonempty := @CommonBudgetAux.authUpdateLenEnv_nonempty
abbrev freeOnlyEvs_nonempty := @CommonBudgetAux.freeOnlyEvs_nonempty
abbrev freeOnlyEvs_rustDealloc1 := @CommonBudgetAux.freeOnlyEvs_rustDealloc1
abbrev freeOnlyEvs_macDealloc := @CommonBudgetAux.freeOnlyEvs_macDealloc

abbrev recvCt2ChunkEnv_of_epoch_ne := @CommonBudgetAux.recvCt2ChunkEnv_of_epoch_ne
abbrev recvCt2ChunkEnv_of_lt_128 := @CommonBudgetAux.recvCt2ChunkEnv_of_lt_128
abbrev recvCt2ChunkEnv_of_bad_kem_len := @CommonBudgetAux.recvCt2ChunkEnv_of_bad_kem_len
abbrev recvCt2ChunkEnv_of_postDecaps := @CommonBudgetAux.recvCt2ChunkEnv_of_postDecaps
abbrev recvCt2PostDecapsEnv_mk := @CommonBudgetAux.recvCt2PostDecapsEnv_mk

abbrev fitsEnv_addChunk_of_recvCt2 := @CommonBudgetAux.fitsEnv_addChunk_of_recvCt2
abbrev fitsEnv_decodedMessage_of_recvCt2 := @CommonBudgetAux.fitsEnv_decodedMessage_of_recvCt2
abbrev fitsEnv_tail_of_recvCt2 := @CommonBudgetAux.fitsEnv_tail_of_recvCt2
abbrev fitsEvents_macCt2Alloc_of_tail := @CommonBudgetAux.fitsEvents_macCt2Alloc_of_tail
abbrev fitsEnv_postDecaps_of_tail := @CommonBudgetAux.fitsEnv_postDecaps_of_tail
abbrev fitsEvents_preAuth_of_postDecaps := @CommonBudgetAux.fitsEvents_preAuth_of_postDecaps
abbrev fitsEnv_authUpdate_of_postDecaps := @CommonBudgetAux.fitsEnv_authUpdate_of_postDecaps
abbrev fitsEnv_reserveCt1_of_postDecaps := @CommonBudgetAux.fitsEnv_reserveCt1_of_postDecaps
abbrev fitsEnv_doReserve_of_reserveCt1 := @CommonBudgetAux.fitsEnv_doReserve_of_reserveCt1
abbrev fitsEvents_hmac_of_postDecaps := @CommonBudgetAux.fitsEvents_hmac_of_postDecaps
abbrev fitsEnv_libcruxHmacEnv_of_fitsEvents := @CommonBudgetAux.fitsEnv_libcruxHmacEnv_of_fitsEvents
abbrev fitsEnv_free1_of_postDecaps := @CommonBudgetAux.fitsEnv_free1_of_postDecaps
abbrev fitsEnv_optSecret32_of_postDecaps := @CommonBudgetAux.fitsEnv_optSecret32_of_postDecaps
abbrev fitsEnv_free2_of_postDecaps := @CommonBudgetAux.fitsEnv_free2_of_postDecaps

/-! ## `spqr::util::is_non_zero` (`0x5e5f0`, Block `380`) with `VmPreserved` -/

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

@[local arm64_norm, local wp_norm]
private theorem isNonZero_asm_eq' (v : BitVec 8) :
    BitVec.setWidth 64 (BitVec.truncate 8 ((0#32 - BitVec.zeroExtend 32 v) >>> 31)) =
    BitVec.zeroExtend 64 (isNonZero v) := by
  revert v
  decide +kernel

/-- Relocatable `spqr::util::is_non_zero` (Block `380`, 9 instructions) satisfies
`withVmPreserved isNonZeroSpec` under `[LibsignalPlacement]`. -/
theorem isNonZero_vm_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_380).rebase (blkPl_380).base H) (blkPl_380).base
      (withVmPreserved isNonZeroSpec) := by
  simp only [withVmPreserved, isNonZeroSpec]
  wp_init v s0
  wp_simp_pre [stackAt_16_split_byte12]
  wp_pull_exists
  refine SepWP.mono
    (post := fun sf P_f =>
      VmPreserved s0 sf ∧
      (P_f ⊢ stackAt s0.sp 0x10) ∧
      sf.readReg64 .x0 = BitVec.zeroExtend 64 (isNonZero v) ∧
      sf.trace = s0.trace ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf)
    ?_
    (fun sf P_f _ _ ⟨hvm, hstk, hx0_f, htr_f, hsp_f, hcs_f⟩ =>
      ⟨fun hm => by
        have hm' := Satisfies.mono (sepConj_mono_left hstk) hm
        simp only [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hvm, ⟨hx0_f, htr_f⟩, hm'⟩, hsp_f, hcs_f⟩)
  by_vm_steps (
    wp_steps
    apply SepWP.fold
      (stackAt_16_merge_byte12 s0.sp
        (BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (0#32 - BitVec.zeroExtend 32 v) >>> 31)))
      (by sep_focus)
    wp_done)

/-- Specialized budget `libcrux_hmac::hmac` contract when `key.length < 2 ^ 32`,
`data.length < 2 ^ 32`, and `FitsEvents M lim st libcruxHmacSha256Events` are already known at
the call site (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`, concrete `libcruxHmacSha256Events` step). -/
@[expose] def libcruxHmacSafeBudgetSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LibcruxHmacCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
      FitsEvents M lim st libcruxHmacSha256Events⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
      A.pool lim (M.stepEvents libcruxHmacSha256Events st) sf ∗ stackAt s0.sp extHookStack

theorem subroutine_ok_libcruxHmacSafeBudget_of_budget {prog : Program} {entry : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hhmac : subroutine_ok prog entry (libcruxHmacBudgetSpec F M A lim)) :
    subroutine_ok prog entry (libcruxHmacSafeBudgetSpec F M A lim) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hsp => ?_
  dsimp only [libcruxHmacSafeBudgetSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hk_lt, hd_lt, hfit⟩, hmem⟩
  have hfit_env : FitsEnv M lim st (LibcruxHmacEnv x) :=
    fitsEnv_libcruxHmacEnv_of_fitsEvents x hk_lt hd_lt hfit
  have hpre' : s0.mem ⊨ (libcruxHmacBudgetSpec F M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [libcruxHmacBudgetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hfit_env⟩, hmem⟩
  refine (hhmac.to_outcome (x, st) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [libcruxHmacBudgetSpec, libcruxHmacSafeBudgetSpec] at hpost ⊢
    rw [sepExists_sepConj_left, satisfies_sepExists] at hpost
    rcases hpost with ⟨evs, hpost⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨_, _, htr, hevs⟩, hmem'⟩
    unfold LibcruxHmacEnv at hevs
    simp only [hk_lt, hd_lt, and_self, ↓reduceIte] at hevs
    rw [hevs] at hmem'
    exact ⟨htr, hmem'⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [libcruxHmacBudgetSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨⟨hk_ge | hd_ge, _⟩, _⟩ <;> omega
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hpost⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hpost⟩))

private theorem optVecU8Of_eq_optKeyBytesAt (A : RustAlloc) (a : BitVec 64) (opt : Option Bytes) :
    optVecU8Of A a opt = optKeyBytesAt A a opt := by
  cases opt <;> rfl

abbrev authUpdateSpec := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.authUpdateSpec
abbrev authUpdateSpecExt := @LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget.authUpdateSpecExt

end LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.CommonBudget
