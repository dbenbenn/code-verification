/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
meta import LibsignalBinary.Proofs.CodeLayout -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import

/-!
# Budget-Threaded `<States>::into_pb` — Part 1: Prologue, Epilogue, Arm 0 (`keysUnsampled`), and Call Helpers

Fixed-offset `RustCliAllocBudget M` prologue/epilogue lemmas, Arm 0 (`States.keysUnsampled`, tag `2`,
`evs = []`) contracts under `KeysUnsampledEnv`, and budget-threaded call helpers for
`<PolyEncoder>::into_pb` and `<PolyDecoder>::into_pb`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget

open CryptoVerification.SpqrV1.States.IntoPb (chunkedKeysUnsampled_expose fnAddr_fwd_eq outWords28_entails_keysUnsampled protoPolynomialDecoderHeap protoPolynomialDecoder_expose protoPolynomialEncoderHeap protoPolynomialEncoder_expose sp_sub_1520_add_1424 sp_sub_480_add_200 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160 sp_sub_96_sub_168 sp_sub_96_sub_176 sp_sub_96_sub_192 sp_sub_96_sub_208 stA_words8_and_864_entails_928 statesIntoPbJumpTableAt statesIntoPbStack)

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (PolyDecoder PolyEncoder States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (KeysUnsampled)
open CryptoVerification.SpqrV1.Drop
  (chunkedStatesAt chunkedStatesSize none2Cap_add_two_beq_zero
   noneCap_add_two_beq_zero optProtoInnerStateAt optProtoInnerStateSize)
open CryptoVerification.SpqrV1.Poly
  (polyDecoderAt polyDecoderSize polyEncoderAt polyEncoderSize
   protoPolynomialDecoderAt protoPolynomialDecoderSize
   protoPolynomialEncoderAt protoPolynomialEncoderSize)
open CryptoVerification.SpqrV1.Poly.DecoderPb (decoderIntoPbName decoderIntoPbStack)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (encoderIntoPbName encoderIntoPbStack)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv
   RustCliAllocBudget VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (trapHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsBudget
  (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

private theorem rebase_fnAddr_eq (P : Program) (b : BitVec 64)
    (H₁ H₂ : String → Option (State → State)) :
    (P.rebase b H₁).fnAddr = (P.rebase b H₂).fnAddr :=
  rfl

private theorem withSvc_fetch_eq {prog : Program} (svc : State → State) {pc : BitVec 64}
    {inst : Instr} (h : prog.fetch pc = some inst) :
    (prog.withSvc svc).fetch pc = some inst :=
  h

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

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_1424 sp_sub_96_sub_160
  sp_sub_1520_add_1424
  sp_sub_96_sub_208 sp_sub_96_sub_192 sp_sub_96_sub_176 sp_sub_96_sub_168
  sp_sub_480_add_200
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero noneCap_add_two_beq_zero

private theorem align_entails_vm {prog : Program} {target : BitVec 64} {s0 s : State}
    {P P_mid : SepProp} {Q : State → Prop}
    (h : P ⊢ P_mid)
    (hwp : SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ (Pm ⊢ P_mid) ∧ Q sm) :=
  SepWP.mono hwp fun _ _ _ _ ⟨htp, hp, hq⟩ => ⟨htp, Entails.trans hp h, hq⟩

private theorem seq_clean_wp {prog : Program} {mid target : BitVec 64} {s : State}
    {Pre : SepProp} {P_mid : State → SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s Pre (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s Pre post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 sm hpc hrun hQ)

/-! ## 1. Re-Exports of `RustAlloc`-Generic `Part1` Helpers -/

abbrev vecU8Payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Payload
abbrev vecU8At_eq_header_payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8At_eq_header_payload
abbrev vecU8_of_header_payload :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_of_header_payload
abbrev authenticatorHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorHeap
abbrev authenticatorAt_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorAt_expose
abbrev authenticatorAt_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.authenticatorAt_of_words_heap
abbrev vecU8Heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8Heap
abbrev vecU8_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_expose
abbrev vecU8_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.vecU8_of_words_heap
abbrev protoPolynomialEncoderHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoderHeap
abbrev protoPolynomialEncoder_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoder_expose
abbrev protoPolynomialEncoder_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialEncoder_of_words_heap
abbrev protoPolynomialDecoderHeap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoderHeap
abbrev protoPolynomialDecoder_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoder_expose
abbrev protoPolynomialDecoder_of_words_heap :=
  @CryptoVerification.SpqrV1.States.IntoPb.protoPolynomialDecoder_of_words_heap
abbrev chunkedKeysUnsampled_expose :=
  @CryptoVerification.SpqrV1.States.IntoPb.chunkedKeysUnsampled_expose
abbrev stA_words8_and_864_entails_928 :=
  @CryptoVerification.SpqrV1.States.IntoPb.stA_words8_and_864_entails_928
abbrev outWords28_entails_keysUnsampled :=
  @CryptoVerification.SpqrV1.States.IntoPb.outWords28_entails_keysUnsampled
abbrev fnAddr_fwd_eq :=
  @CryptoVerification.SpqrV1.States.IntoPb.fnAddr_fwd_eq
abbrev statesIntoPb_seq_sepWP :=
  @CryptoVerification.SpqrV1.States.IntoPb.statesIntoPb_seq_sepWP

/-! ## 2. Pool-Synchronized Fixed-Offset Prologue, Extended Prologue, Epilogue, and Exit Bridges -/

/-- Envelope-parametric return postcondition of `<States>::into_pb` for `SepWPp`. -/
@[expose] def StatesIntoPbPostOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {F : ShaCompress} (b : BitVec 64) (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F))
    (Env : List AllocEvent → Prop) : State → SepProp → Prop :=
  fun sf Pf =>
    (∃ evs : List AllocEvent, Env evs ∧
      (Pf ⊢
        optProtoInnerStateAt A.repAlloc out stateVal.into_pb.innerState ∗
        memRegion stA chunkedStatesSize ∗
        statesIntoPbJumpTableAt b ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp statesIntoPbStack)) ∧
    sf.sp = s0.sp ∧
    CalleeSavedPreserved s0 sf ∧
    sf.trace = s0.trace

/-- Default-envelope return postcondition of `<States>::into_pb` for `SepWPp`. -/
abbrev StatesIntoPbPost {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    {F : ShaCompress} (b : BitVec 64) (st : M.σ) (s0 : State) (out stA : BitVec 64)
    (stateVal : States spqrPolyApi (spqrAuthApi F)) : State → SepProp → Prop :=
  StatesIntoPbPostOfEnv A lim b st s0 out stA stateVal
    (SpqrBoundedEvs 64 (2 * (V1State.encodeRaw stateVal.into_pb).length + 1024))

/-- Non-panicking (`onPanic = ⌜False⌝`) panic postcondition of budget `<States>::into_pb` for `SepWPp`. -/
@[expose] def StatesIntoPbNoPanic (R : SepProp) : State → SepProp → Prop :=
  fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)

/-- Exact allocator event envelope of `<States>::into_pb` on Arm 0 (`States.keysUnsampled`):
    zero heap allocations or deallocations (`evs = []`). -/
@[expose] def KeysUnsampledEnv (evs : List AllocEvent) : Prop :=
  evs = []

theorem sub_ok_of_addr_eq {α : Type} {P : Program} {a1 a2 : BitVec 64} {S : Spec α}
    (heq : a1 = a2) (h : subroutine_ok P a1 S) : subroutine_ok P a2 S :=
  heq ▸ h

end LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1Budget
