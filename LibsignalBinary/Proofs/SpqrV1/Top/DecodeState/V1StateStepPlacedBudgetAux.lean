/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Outer `skip_field` & `PqRatchetState::v1` `some` Helpers (Block `325`)

Proves budget-threaded `V1State::merge` call wrappers, outer `skip_field(depth=100)` (`+456`),
224-byte `PqRatchetState::v1` spatial helpers, and in-place Tag 3 `some (.v1 v1)` merge (`+476`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement lsmpl)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet (decodeErrorAtStackLen withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join sliceCursorAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge (OptInnerStatePolyBound V1StateMergeGhost codecWireTypeToProto mergeLoopBin optProtoInnerStateCapAt v1StateJumpTablesPlacedAt v1StateMergeStack)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost Quads28 TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg none2Cap none3Cap optChainPBCapOkAt optChainPBCapOkAt_entails_optChainPBAt optChainPBCapOkAt_mono optProtoInnerStateAt optProtoInnerStateCapOkAt optProtoInnerStateCapOkAt_entails_capAt optProtoInnerStateCapOkAt_entails_quads28 optProtoInnerStateCapOkHeap optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt optVersionNegotiationPBCapOkAt optVersionNegotiationPBCapOkAt_entails_optVersionNegotiationPBAt optVersionNegotiationPBCapOkAt_mono protoPqRatchetStateAt protoPqRatchetStateCapOkAt protoPqRatchetStateCapOkAt_mono proto_mergeMessage_suffix quads14At quads28At quads28_entails_head_and_memRegion_216 quads28_entails_optProtoInnerStateCapOkAt quads7At quads7At_split_head scratch_688_fold_48 scratch_688_split_48 sp_sub_1392_aligned memRegion_224_eq_quads28At)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (V1StateMergeEnv V1StateMergePostEnv v1StateMergePlacedSpec v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_calleeErr_proto_to_errFrame_placed loopCommon_calleeErr_to_errFrame_placed)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Budget-Threaded Call Wrappers for `V1State::merge` -/

/-- Envelope-parameterized call wrapper for `v1StateMergePlacedSpecOfEnv` (`lsmpl.base 298`). -/
theorem call_v1StateMerge_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {V1PreEnv V1PostEnv : V1StateMergeGhost → List AllocEvent → Prop}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)))
    (hcap : ∀ (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState),
      OptInnerStatePolyBound remLen opt →
      optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
        optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt)
    (hdrop : ∀ (a : BitVec 64) (opt : Option V1State.InnerState),
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
        optProtoInnerStateAt H_inner A.repAlloc a opt)
    (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 32)
    (hfits : OptInnerStatePolyBound bs.length msg.innerState →
      FitsEnv M lim st (V1PreEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr bs.length msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : V1State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption =
        some (m', rest) →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr rest.length m'.innerState ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : Option V1State.InnerState) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = none →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1PostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 4 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          optProtoInnerStateAt H_inner A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp := by
  intro hinv R' hm hL
  let x_v1 : V1StateMergeGhost := ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩
  rw [hP] at hm
  have hm_cap := Satisfies.mono (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left
    (optProtoInnerStateCapOkAt_entails_capAt H_inner A.repAlloc msgPtr bs.length msg.innerState)))) hm
  have hm_pb : s.mem ⊨ ⌜OptInnerStatePolyBound bs.length msg.innerState⌝ ∗
      ((optProtoInnerStateCapAt A.repAlloc msgPtr bs.length msg.innerState ∗
        v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
        sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
        stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F ∗ R') := by
    refine Satisfies.mono (Entails.of_eq ?_) hm_cap
    sep_ac_rfl
  rw [satisfies_pure_sepConj] at hm_pb
  rcases hm_pb with ⟨hpb, hm'⟩
  have hpre : s.mem ⊨
      (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv)).pre
        (x_v1, st) s ∗ (F ∗ R') := by
    dsimp only [withLsCodeRoLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hinv, ?_⟩
    dsimp only [v1StateMergePlacedSpecOfEnv, x_v1]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, by omega, hpb, hfits hpb⟩, ?_⟩
    refine Satisfies.mono (Entails.of_eq ?_) hm'
    sep_ac_rfl
  have halign : s.spAligned = true := by
    rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome (x_v1, st) (F ∗ R') s hpc hrun hpre halign hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · change sm.mem ⊨ (v1StateMergePlacedSpecOfEnv A lim V1PreEnv V1PostEnv).post (x_v1, st) s sm ∗
      (F ∗ R') at hpost
    dsimp only [v1StateMergePlacedSpecOfEnv, x_v1] at hpost
    rw [hsp] at hpost
    rcases hv1 : (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption with _ | ⟨m', rest⟩
    · simp only [hv1, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨m', n, evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜V1PostEnv x_v1 evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗ (⌜sm.readReg64 .x0 ≠ 0#64⌝ ∗ (⌜n ≤ 4⌝ ∗
            (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
              stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
              v1StateJumpTablesPlacedAt ∗
              decodeErrorAtStackLen A.repAlloc (sm.readReg64 .x0) n ∗
              CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc msgPtr m' ∗
              memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F) ∗ R'))) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj,
        satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, hx0_ne, hn, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_left (hdrop msgPtr m'))))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      obtain ⟨sf, hsteps', hout'⟩ :=
        herr sm n m' evs hv1 hpb hevs hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_ne hn
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
    · simp only [hv1, sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
      rcases hpost with ⟨evs, hpost⟩
      have hpost_pure : sm.mem ⊨ ⌜V1PostEnv x_v1 evs⌝ ∗
          (⌜sm.trace = s.trace⌝ ∗
            (⌜sm.readReg64 .x0 = 0#64 ∧ OptInnerStatePolyBound rest.length m'.innerState⌝ ∗
              (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sm ∗
                stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
                v1StateJumpTablesPlacedAt ∗
                optProtoInnerStateCapAt A.repAlloc msgPtr rest.length m'.innerState ∗
                sliceCursorAfter slot ptr bs rest) ∗ F) ∗ R')) := by
        refine Satisfies.mono (Entails.of_eq ?_) hpost
        sep_ac_rfl
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost_pure
      rcases hpost_pure with ⟨hevs, htrm, ⟨hx0_0, hpb'⟩, hpost1⟩
      have hpost2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (hcap msgPtr rest.length m'.innerState hpb')))))))) hpost1
      rw [hlr] at hpcm; rw [hsp] at hspm
      have ⟨hle, hsuf⟩ := proto_mergeMessage_suffix hv1
      obtain ⟨sf, hsteps', hout'⟩ :=
        hok sm m' rest evs hv1 hpb hevs hle hsuf hpcm hrunm hspm (htr.step htrm hcsm) hcsm hx0_0
          (hinv.of_keepsFrozen hsteps.keepsFrozen) R' hpost2 (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)
  · dsimp only [v1StateMergePlacedSpecOfEnv, withLsCodeRoLoaded] at hpost
    exact False.elim (not_satisfies_false_sepConj hpost)

theorem call_v1StateMerge [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {ret entry ret_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim)))
    (hcap : ∀ (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState),
      OptInnerStatePolyBound remLen opt →
      optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
        optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt)
    (hdrop : ∀ (a : BitVec 64) (opt : Option V1State.InnerState),
      CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
        optProtoInnerStateAt H_inner A.repAlloc a opt)
    (wt : WireType) (msgPtr : BitVec 64) (msg : V1State)
    (bufRef slot ptr : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1392#64)
    (hs0A : s0.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : TraceVRegs s s0)
    (hx0 : (s.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 wt.toNat)
    (hx1 : s.readReg64 .x1 = msgPtr)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hlen : bs.length < 2 ^ 32)
    (hfits : OptInnerStatePolyBound bs.length msg.innerState →
      FitsEnv M lim st (V1StateMergeEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩))
    (hP : P = (optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr bs.length msg.innerState ∗
      v1StateJumpTablesPlacedAt ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot ptr bs ∗ A.pool lim st s ∗
      stackAt (s0.sp - 1392#64) v1StateMergeStack) ∗ F)
    (hok : ∀ (sf : State) (m' : V1State) (rest : List (BitVec 8)) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption =
        some (m', rest) →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1StateMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      rest.length ≤ bs.length → IsDropSuffix bs rest →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 = 0#64 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          optProtoInnerStateCapOkAt H_inner A.repAlloc msgPtr rest.length m'.innerState ∗
          sliceCursorAfter slot ptr bs rest) ∗ F)
        Q Qp)
    (herr : ∀ (sf : State) (n : Nat) (m' : Option V1State.InnerState) (evs : List AllocEvent),
      (mergeMessage V1State.mergeField (codecWireTypeToProto wt) msg bs 100).toOption = none →
      OptInnerStatePolyBound bs.length msg.innerState →
      V1StateMergePostEnv ⟨wt, msgPtr, msg, bufRef, slot, ptr, bs⟩ evs →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s0.sp - 1392#64 → TraceVRegs sf s0 → CalleeSavedPreserved s sf →
      sf.readReg64 .x0 ≠ 0#64 → n ≤ 4 →
      SepWPpIPlaced prog ret sf
        (((bufRef ↦₆₄ slot) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt (s0.sp - 1392#64) v1StateMergeStack ∗
          v1StateJumpTablesPlacedAt ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) n ∗
          optProtoInnerStateAt H_inner A.repAlloc msgPtr m' ∗
          memRegion slot 16 ∗ (ptr ↦ₛ bs)) ∗ F)
        Q Qp) :
    SepWPpIPlaced prog ret s P Q Qp :=
  call_v1StateMerge_ofEnv hcall hcap hdrop wt msgPtr msg bufRef slot ptr bs st
    hpc hrun hsp hs0A hlr htr hx0 hx1 hx2 hlen hfits hP hok herr

/-! ## 2. Outer `skip_field(depth=100)` (`+456` -> `+1576` / `+1668`) -/

attribute [local irreducible] mergeMessage mergeLoopBin

theorem setWidth8_ofNat64_wt (iwt : WireType) :
    BitVec.setWidth 8 (BitVec.ofNat 64 iwt.toNat) = BitVec.ofNat 8 iwt.toNat := by
  cases iwt <;> rfl

/-! ## 3. Spatial & Framing Helpers for Outer Tag 3 (`PqRatchetState::v1`, `224`B) -/

theorem protoPqRatchetStateCapOkAt_v1_eq (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (sp : BitVec 64) (remLen : Nat) (optVn : Option VersionNegotiationPB)
    (optCh : Option ChainPB) (inner : Option PqRatchetState.Inner) :
    protoPqRatchetStateCapOkAt H_inner A (sp - 1040#64) remLen ⟨optVn, optCh, inner⟩ =
      optVersionNegotiationPBCapOkAt A (sp - 1040#64) remLen optVn ∗
      optChainPBCapOkAt A (sp - 992#64) remLen optCh ∗
      optProtoPqRatchetInnerCapOkAt H_inner A (sp - 912#64) remLen inner := by
  unfold protoPqRatchetStateCapOkAt
  dsimp only
  have ha1 : sp - 1040#64 + 48#64 = sp - 992#64 := by bv_omega
  have ha2 : sp - 1040#64 + 128#64 = sp - 912#64 := by bv_omega
  rw [ha1, ha2]

theorem optProtoInnerStateCapOkAt_expose_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (opt : Option V1State.InnerState) :
    optProtoInnerStateCapOkAt H_inner A a remLen opt ⊢
      ∃∗ q : Quads28,
        ⌜q.head ≠ none3Cap⌝ ∗
        (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) := by
  refine Entails.trans (optProtoInnerStateCapOkAt_entails_quads28 H_inner A a remLen opt) ?_
  apply Entails.sepExists_elim; intro q
  refine Entails.sepExists_right q ?_
  cases opt with
  | none =>
    unfold optProtoInnerStateCapOkHeap quads28At
    dsimp only
    rw [quads14At, quads7At_split_head a q.1.1]
    rw [sepConj_comm _ ⌜_⌝]
    apply Entails.pure_left; intro hrh
    have hne : q.head ≠ none3Cap := by rw [hrh.2]; decide
    apply Entails.pure_right hne
    have htrue : (⌜remLen < 2 ^ 56 ∧ q.head = none2Cap⌝ : SepProp) = emp := by
      simp only [hrh, and_self, pure_true]
    rw [htrue, sepConj_emp]
    unfold Quads28.head
    exact Entails.of_eq (by sep_ac_rfl)
  | some is =>
    unfold optProtoInnerStateCapOkHeap
    dsimp only
    rw [sepConj_comm (quads28At a q), sepConj_assoc]
    apply Entails.pure_left; intro hph
    apply Entails.pure_right hph.2
    have htrue : (⌜OptInnerStatePolyBound remLen (some is) ∧ q.head ≠ none3Cap⌝ : SepProp) = emp := by
      rw [eq_true hph, pure_true]
    rw [quads28At, quads14At, quads7At_split_head a q.1.1, htrue, emp_sepConj]
    unfold Quads28.head
    exact Entails.of_eq (by sep_ac_rfl)

theorem optProtoInnerStateCapOkAt_fold_head (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (q : Quads28) (remLen : Nat) (opt : Option V1State.InnerState) :
    (a ↦₆₄ q.head) ∗
      (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
       ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
       ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
       quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
       optProtoInnerStateCapOkHeap H_inner A remLen q opt) ⊢
    optProtoInnerStateCapOkAt H_inner A a remLen opt := by
  have hq :
      (a ↦₆₄ q.head) ∗
        (((a + 8#64) ↦₆₄ q.1.1.2.1) ∗ ((a + 16#64) ↦₆₄ q.1.1.2.2.1) ∗
         ((a + 24#64) ↦₆₄ q.1.1.2.2.2.1) ∗ ((a + 32#64) ↦₆₄ q.1.1.2.2.2.2.1) ∗
         ((a + 40#64) ↦₆₄ q.1.1.2.2.2.2.2.1) ∗ ((a + 48#64) ↦₆₄ q.1.1.2.2.2.2.2.2) ∗
         quads7At (a + 56#64) q.1.2 ∗ quads14At (a + 112#64) q.2 ∗
         optProtoInnerStateCapOkHeap H_inner A remLen q opt) =
      quads28At a q ∗ optProtoInnerStateCapOkHeap H_inner A remLen q opt := by
    unfold quads28At quads14At Quads28.head
    rw [quads7At_split_head a q.1.1]
    sep_ac_rfl
  rw [hq]
  exact quads28_entails_optProtoInnerStateCapOkAt H_inner A a remLen q opt

theorem head_ne_none3Cap_branch {w : BitVec 64} (hne : w ≠ none3Cap) :
    (w + 3#64 != 0#64) = true ∧ (w + 3#64 == 0#64) = false := by
  have h0 : w + 3#64 ≠ 0#64 := by
    intro h
    apply hne
    change w = -3#64
    bv_omega
  exact ⟨bne_iff_ne.mpr h0, beq_eq_false_iff_ne.mpr h0⟩

theorem memRegion_224_split_head (a : BitVec 64) :
    memRegion a 224 ⊢
      memRegion (a + 8#64) 216 ∗ (∃∗ w : BitVec 64, a ↦₆₄ w) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a]
  exact Entails.of_eq (by sep_ac_rfl)

theorem optProtoInnerStateCapOkAt_default_init (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (a : BitVec 64) (remLen : Nat) (hrem : remLen < 2 ^ 56) :
    (a ↦₆₄ (-2#64)) ∗ memRegion (a + 8#64) 216 ⊢
      optProtoInnerStateCapOkAt H_inner A a remLen (default : V1State).innerState := by
  have hd : (default : V1State).innerState = none := rfl
  rw [hd]
  unfold optProtoInnerStateCapOkAt none2Cap
  exact Entails.pure_right hrem (Entails.refl _)

theorem scratch_688_split_quads28_and_3a0 (sp w0 : BitVec 64) :
    ((sp - 688#64) ↦₆₄ w0) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ⊢
      memRegion (sp - 456#64) 120 ∗
      (∃∗ w_3a0 : BitVec 64, ∃∗ q_dst : Quads28,
        quads28At (sp - 688#64) q_dst ∗ ((sp - 464#64) ↦₆₄ w_3a0)) := by
  refine Entails.trans (scratch_688_fold_48 sp w0) ?_
  rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
      (b' := sp - 464#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
      (b' := sp - 456#64) rfl (by bv_omega) (by decide),
    memRegion_224_eq_quads28At (sp - 688#64),
    ProofLib.memRegion_eight (sp - 464#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  exact Entails.of_eq (by sep_ac_rfl)

theorem scratch_688_restore_from_quads28 (sp w_3a0 : BitVec 64) (q : Quads28) :
    quads28At (sp - 688#64) q ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      ((sp - 688#64) ↦₆₄ q.head) ∗ memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
  have h1 := quads28_entails_head_and_memRegion_216 (sp - 688#64) q
  have h2 : ((sp - 464#64) ↦₆₄ w_3a0) ⊢ memRegion (sp - 464#64) 8 :=
    ProofLib.pointsTo64_entails_memRegion _ _
  refine Entails.trans (sepConj_mono h1 (sepConj_mono_left h2)) ?_
  have ha680 : sp - 688#64 + 8#64 = sp - 680#64 := by bv_omega
  rw [ha680]
  have h344 : memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120 =
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 := by
    rw [← ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide),
      ← ProofLib.memRegion_split' (b := sp - 680#64) (n := 216) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 680#64) (n := 40) (k := 304)
        (b' := sp - 640#64) rfl (by bv_omega) (by decide)]
  have hassoc :
      ((sp - 688#64) ↦₆₄ q.head ∗ memRegion (sp - 680#64) 216) ∗
        (memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) =
      (sp - 688#64) ↦₆₄ q.head ∗
        (memRegion (sp - 680#64) 216 ∗ memRegion (sp - 464#64) 8 ∗ memRegion (sp - 456#64) 120) := by
    sep_ac_rfl
  rw [hassoc, h344]
  exact Entails.refl _

theorem scratch_688_dropped_split_48 (sp w_3a0 : BitVec 64) :
    memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 680#64) 40 ∗ memRegion (sp - 640#64) 304 ∗
      (∃∗ w0' : BitVec 64, (sp - 688#64) ↦₆₄ w0') := by
  have h352 : memRegion (sp - 688#64) 224 ∗ ((sp - 464#64) ↦₆₄ w_3a0) ∗ memRegion (sp - 456#64) 120 ⊢
      memRegion (sp - 688#64) 352 := by
    rw [ProofLib.memRegion_split' (b := sp - 688#64) (n := 224) (k := 128)
        (b' := sp - 464#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 464#64) (n := 8) (k := 120)
        (b' := sp - 456#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _))
  exact Entails.trans h352 (scratch_688_split_48 sp)

/-! ## 4. Outer Tag 3 `some (.v1 v1)` In-Place Merge (`+476..+492`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
