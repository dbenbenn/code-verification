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
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.MessageMergePart2CodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Outer `PqRatchetState::v1` (Tag 3) Entry & `none` Path (Block `325`)

Proves 224-byte Q-register stack copies (`+340`, `+1484`), the budget-threaded relocatable outer
Tag 3 `none` merge path (`+324`), and Tag 3 entry (`+312`), re-exporting `skip_field` and `some`
helpers from `V1StateStepPlacedBudgetAux`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPl_325)
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalProtoCodec (WireType)
open CryptoVerification.LibsignalTripleRatchet.Prost (IsDropSuffix sliceCursorAfter sliceCursorAfter_eq_split sliceCursorAfter_join)
open CryptoVerification.SpqrV1.Prost.MessageMerge (OptInnerStatePolyBound V1StateMergeGhost codecWireTypeToProto mergeLoopBin v1StateJumpTablesPlacedAt)
open CryptoVerification.LibsignalSpqrV1 (ChainPB PqRatchetState V1State VersionNegotiationPB spqrDecodeState)
open CryptoVerification.LibsignalSpqrV1.Proto (mergeMessage)
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost DropOptProtoInnerStateGhost Quads28 TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg dropOptProtoInnerStateStack memRegion_224_eq_quads28At none3Cap optChainPBCapOkAt_mono optProtoInnerStateAt_entails_quads28 optProtoInnerStateCapOkAt_entails_quads28 optProtoPqRatchetInnerAt optProtoPqRatchetInnerCapOkAt optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt optVersionNegotiationPBCapOkAt_mono pqRatchetState_mergeField_tag3 protoPqRatchetStateCapOkAt quads14At quads28At quads28At_entails_memRegion_224 quads28_entails_optProtoInnerStateAt quads28_entails_optProtoInnerStateCapOkAt quads7At sp_sub_1392_aligned stackAt_of_callee stackAt_to_callee)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget (V1StateMergeEnv V1StateMergePostEnv v1StateMergePlacedSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced DecodeStateCalleeContractsPlacedX dropOptProtoInnerStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.LoopCommonPlacedBudget (SepWPpIPlaced decodeStateLoopCommonPlaced loopCommon_calleeErr_to_errFrame_placed)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux (head_ne_none3Cap_branch memRegion_224_split_head optProtoInnerStateCapOkAt_default_init optProtoInnerStateCapOkAt_expose_head optProtoInnerStateCapOkAt_fold_head protoPqRatchetStateCapOkAt_v1_eq scratch_688_dropped_split_48 scratch_688_restore_from_quads28 scratch_688_split_quads28_and_3a0 setWidth8_ofNat64_wt)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudgetAux (call_v1StateMerge_ofEnv call_v1StateMerge)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup v1StateJumpTablesPlacedAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local irreducible] mergeMessage mergeLoopBin

@[simp] private theorem decodeState_codecWireTypeToProto_eq (wt : WireType) :
    CryptoVerification.SpqrV1.Top.DecodeState.codecWireTypeToProto wt = codecWireTypeToProto wt := by
  cases wt <;> rfl

/-! ## 1. 224-Byte Q-Register Copies & Outer Tag 3 `none` Path (`+324..+452`, `+1484..+1572`) -/

private theorem optProtoPqRatchetInnerCapOkAt_none_entails_quads28
    (H_inner : V1InnerHeapPred) (A : RustAlloc) (a : BitVec 64) (remLen : Nat) :
    optProtoPqRatchetInnerCapOkAt H_inner A a remLen none ⊢ ∃∗ q_dst : Quads28, quads28At a q_dst := by
  refine Entails.trans (optProtoPqRatchetInnerCapOkAt_entails_optProtoPqRatchetInnerAt H_inner A a remLen none) ?_
  unfold optProtoPqRatchetInnerAt
  rw [← memRegion_224_eq_quads28At a,
      ProofLib.memRegion_split' (b := a) (n := 8) (k := 216) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)

/-- Budget-threaded 224-byte Q-register copy (`+340..+428`, 22 instructions) from
`x29 - 0xe8` (`s0.sp - 328#64`) to `sp + 0x2c0` (`s0.sp - 688#64`), also storing
`x24` (`s0.sp - 912#64`) at `sp + 0x3a0` (`s0.sp - 464#64`). -/
theorem decodeState_v1_copy_to_scratch_535f0_placed [LibsignalPlacement]
    {M : AllocCostModel} {target_pc v0 v20 v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (w_3a0 : BitVec 64)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 340#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = v0)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 688#64) q_dst ∗
      ((s0.sp - 464#64) ↦₆₄ w_3a0) ∗
      A.pool lim st s) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 428#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 (Reg.gpr 0#5) = v0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = v20 →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 688#64) q_src ∗
        ((s0.sp - 464#64) ↦₆₄ (s0.sp - 912#64)) ∗
        A.pool lim st sf) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps_sync_pool ((blkPl_325).base + 428#64)
  try simp only [State.setMem_setMem]
  exact hnext _ _
    (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx19])
    (by simp only [wp_norm, arm64_norm, hx20]) (by simp only [wp_norm, arm64_norm, hx21])
    (by simp only [wp_norm, arm64_norm, hx22]) (by simp only [wp_norm, arm64_norm, hx23])
    (by simp only [wp_norm, arm64_norm, hx24]) (by simp only [wp_norm, arm64_norm, hx25])
    (by simp only [wp_norm, arm64_norm, hx26]) (by simp only [wp_norm, arm64_norm, hx27])
    (by simp only [wp_norm, arm64_norm, hx28]) (by simp only [wp_norm, arm64_norm, hx29])
    (by sep_ac_rfl)

/-- Budget-threaded 224-byte Q-register copy (`+1484..+1576`, 23 instructions) from
`x29 - 0xe8` (`s0.sp - 328#64`) to `x24` (`s0.sp - 912#64`), followed by `cbnz x0, 0x53bc0`
(not taken since `x0 = 0#64`) and `ldr x20, [sp, #0x158]`. -/
theorem decodeState_v1_copy_to_state_53a68_placed [LibsignalPlacement]
    {M : AllocCostModel} {target_pc v27 : BitVec 64}
    {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (outPtr : BitVec 64) (q_src q_dst : Quads28) (remLen : Nat)
    (s0 s : State) (P R_frame : SepProp) (post : State → SepProp → Prop)
    (hs0A : s0.spAligned = true)
    (hpc : s.pc = decodeStatePlacedEntry + 1484#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 1392#64)
    (htr : TraceVRegs s s0)
    (hx0 : s.readReg64 (Reg.gpr 0#5) = 0#64)
    (hx19 : s.readReg64 .x19 = outPtr)
    (hx21 : s.readReg64 .x21 = 0x8000000000000006#64)
    (hx22 : s.readReg64 .x22 = s0.sp - 1040#64)
    (hx23 : s.readReg64 .x23 = -1#64)
    (hx24 : s.readReg64 .x24 = s0.sp - 912#64)
    (hx25 : s.readReg64 .x25 = s0.sp - 688#64)
    (hx26 : s.readReg64 .x26 = -2#64)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 1#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P = (quads28At (s0.sp - 328#64) q_src ∗
      quads28At (s0.sp - 912#64) q_dst ∗
      ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen) ∗
      A.pool lim st s) ∗
      R_frame)
    (hnext : ∀ (sf : State) (P' : SepProp),
      sf.pc = decodeStatePlacedEntry + 1576#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1392#64 →
      TraceVRegs sf s0 →
      sf.readReg64 .x19 = outPtr →
      sf.readReg64 .x20 = BitVec.ofNat 64 remLen →
      sf.readReg64 .x21 = 0x8000000000000006#64 →
      sf.readReg64 .x22 = s0.sp - 1040#64 →
      sf.readReg64 .x23 = -1#64 →
      sf.readReg64 .x24 = s0.sp - 912#64 →
      sf.readReg64 .x25 = s0.sp - 688#64 →
      sf.readReg64 .x26 = -2#64 →
      sf.readReg64 .x27 = v27 →
      sf.readReg64 .x28 = 1#64 →
      sf.readReg64 .x29 = s0.sp - 96#64 →
      P' = (quads28At (s0.sp - 328#64) q_src ∗
        quads28At (s0.sp - 912#64) q_src ∗
        ((s0.sp - 1048#64) ↦₆₄ BitVec.ofNat 64 remLen) ∗
        A.pool lim st sf) ∗
        R_frame →
      SepWP (decodeStatePlacedProg ext) target_pc sf P' post) :
    SepWP (decodeStatePlacedProg ext) target_pc s P post := by
  have hspA : s.spAligned = true := by rw [State.spAligned, hsp]; exact sp_sub_1392_aligned s0 hs0A
  have hbne0 : (s.readReg64 (Reg.gpr 0#5) != 0#64) = false := by rw [hx0]; rfl
  have hbeq0 : (s.readReg64 (Reg.gpr 0#5) == 0#64) = true := by rw [hx0]; rfl
  subst hP
  rcases q_src with ⟨⟨⟨s00, s01, s02, s03, s04, s05, s06⟩, ⟨s10, s11, s12, s13, s14, s15, s16⟩⟩,
                     ⟨⟨s20, s21, s22, s23, s24, s25, s26⟩, ⟨s30, s31, s32, s33, s34, s35, s36⟩⟩⟩
  rcases q_dst with ⟨⟨⟨d00, d01, d02, d03, d04, d05, d06⟩, ⟨d10, d11, d12, d13, d14, d15, d16⟩⟩,
                     ⟨⟨d20, d21, d22, d23, d24, d25, d26⟩, ⟨d30, d31, d32, d33, d34, d35, d36⟩⟩⟩
  dsimp only [decodeStatePlacedProg, decodeStatePlacedEntry, quads28At, quads14At, quads7At] at hpc hnext ⊢
  wp_steps_sync_pool ((blkPl_325).base + 1576#64)
  try simp only [State.setMem_setMem]
  exact hnext _ _
    (by simp only [wp_norm, arm64_norm, hx0])
    (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
    (by simp only [wp_norm, arm64_norm, htr])
    (by simp only [wp_norm, arm64_norm, hx19]) (by simp only [wp_norm, arm64_norm])
    (by simp only [wp_norm, arm64_norm, hx21]) (by simp only [wp_norm, arm64_norm, hx22])
    (by simp only [wp_norm, arm64_norm, hx23]) (by simp only [wp_norm, arm64_norm, hx24])
    (by simp only [wp_norm, arm64_norm, hx25]) (by simp only [wp_norm, arm64_norm, hx26])
    (by simp only [wp_norm, arm64_norm, hx27]) (by simp only [wp_norm, arm64_norm, hx28])
    (by simp only [wp_norm, arm64_norm, hx29])
    (by sep_ac_rfl)

/-! ## 2. Outer Tag 3 Entry (`+312`) -/

/-- Message value passed to `V1State::merge` in outer tag 3 (`PqRatchetState::v1`). -/
@[expose] def pqRatchetStateV1OrDefault (curSt : PqRatchetState) : V1State :=
  match curSt.inner with
  | none => default
  | some (.v1 v1) => v1

/-- Stack pointer passed as `x1` (`msgPtr`) to `V1State::merge` in outer tag 3:
`sp - 328#64` (`x29 - 0xe8`) when `curSt.inner = none`, and `sp - 912#64` (`x24`) when
`curSt.inner = some (.v1 _)`. -/
@[expose] def pqRatchetStateV1MsgPtr (sp : BitVec 64) (curSt : PqRatchetState) : BitVec 64 :=
  match curSt.inner with
  | none => sp - 328#64
  | some (.v1 _) => sp - 912#64

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.V1StateStepPlacedBudget
