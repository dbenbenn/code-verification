/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSub
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Budget-Threaded Relocatable Outer Loop & Initial `ChainPB` Error Exits for `spqr::decode_state` (Block `325`)

Proves budget-threaded relocatable error exits for `v1::State::merge` (`+1828`), outer
`decode_key` and `skip_field` (`+1628..+1672`), and the shared `ChainPB` `DecodeError::push`
blocks (`+2048..+2088`, `+2600..+2656`, `+2800..+2832`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux

open Arm64 Arm64.Obj ProofLib SepProp
open scoped LibsignalBinary.Proofs.Placed.BudgetPoolSync
open scoped CryptoVerification.SpqrV1.Top.DecodeState.Placed
open CryptoVerification.SpqrV1.Top.DecodeState (DecodeStateGhost TraceVRegs V1InnerHeapPred decodeStatePlacedEntry decodeStatePlacedProg decodeStateSavedAt protoPqRatchetStateAt scratch_688_fold_48 sp_sub_1392_aligned)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (DecodeErrorFromEnv DecodeErrorPushEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget (DecodeStateEnv DecodeStateIterEnv DecodeStateLoopEnv FitsEnv.decodeStateLoop_head FitsEnv.decodeStateLoop_tail)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (DecodeStateCalleeContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (bv_sub_688_add_8 decodeStateErrFramePlaced scratch_680_fold_1_1 scratch_680_fold_8 scratch_680_split_1_1 scratch_680_split_8)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitPlacedBudget (decodeStatePanicPostPlaced decodeStatePanicPostPlacedOfEnv decodeStatePostPlaced decodeStatePostPlacedOfEnv)

export LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubBudget (decodeStateErrFramePlaced)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff Program.fnAddr Obj.lookup
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `SepWPp` Spatial Helpers & `DecodeStateLoopEnv` Error-Exit Discharge Lemmas -/

theorem SepWPp.fold {prog : Program} {ret : BitVec 64} {s : State} {P T T' F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hent : T ⊢ T') (hf : P = T ∗ F)
    (h : SepWPp prog ret s (T' ∗ F) Q Qp oom) : SepWPp prog ret s P Q Qp oom := fun R hm hL => by
  rw [hf] at hm
  exact h R (Satisfies.mono (sepConj_mono_left (sepConj_mono_left hent)) hm) hL

theorem SepWPp.exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a : α, P a) Q Qp oom := fun R hm hL => by
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem decodeStateIterEnv_of_decodeErrorFrom {maxLen polyCapBound : Nat} {evs : List AllocEvent}
    (h : DecodeErrorFromEnv evs) :
    DecodeStateIterEnv maxLen polyCapBound evs := by
  dsimp only [DecodeErrorFromEnv] at h
  subst h
  exact .fromErr

theorem fitsEnv_decodeErrorFrom_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound : Nat} (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st DecodeErrorFromEnv :=
  FitsEnv.decodeStateLoop_head (fuel := rem - 1)
    (fun _ h => decodeStateIterEnv_of_decodeErrorFrom h)
    (fun evs hevs => hFit evs (hevs.mono_fuel (by omega)))

theorem fitsEnv_decodeErrorPush_of_loop {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {rem maxLen polyCapBound n : Nat} (hn : n ≤ 4) (hrem : 1 ≤ rem)
    (hFit : FitsEnv M lim st (DecodeStateLoopEnv rem maxLen polyCapBound)) :
    FitsEnv M lim st (DecodeErrorPushEnv n) :=
  FitsEnv.decodeStateLoop_head (fuel := rem - 1)
    (fun _ h => .pushErr hn h)
    (fun evs hevs => hFit evs (hevs.mono_fuel (by omega)))

theorem decodeStateEnv_of_loop_from_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 2 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_fr evs_f, DecodeErrorFromEnv evs_fr → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 = M.stepEvents evs_f (M.stepEvents evs_fr st) := by
  intro evs_fr evs_f hfr hfree
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_fr :=
    DecodeStateLoopEnv.single (fuel := 0) (decodeStateIterEnv_of_decodeErrorFrom hfr)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨(evs_acc ++ evs_fr) ++ evs_f, ((hloop.append h1).append h2).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_push2_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f n : Nat} {evs_acc : List AllocEvent}
    (hn : n + 1 ≤ 4)
    (hf : f + 3 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_p1 evs_p2 evs_f,
      DecodeErrorPushEnv n evs_p1 → DecodeErrorPushEnv (n + 1) evs_p2 → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 st)) := by
  intro evs_p1 evs_p2 evs_f hp1 hp2 hfree
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p1 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by omega) hp1)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p2 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr hn hp2)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨((evs_acc ++ evs_p1) ++ evs_p2) ++ evs_f,
    (((hloop.append h1).append h2).append h3).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_from_push_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 3 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_fr evs_p evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p → FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p (M.stepEvents evs_fr st)) := by
  intro evs_fr evs_p evs_f hfr hp hfree
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_fr :=
    DecodeStateLoopEnv.single (fuel := 0) (decodeStateIterEnv_of_decodeErrorFrom hfr)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨((evs_acc ++ evs_fr) ++ evs_p) ++ evs_f,
    (((hloop.append h1).append h2).append h3).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst]

theorem decodeStateEnv_of_loop_from_push2_free {M : AllocCostModel} {x : DecodeStateGhost}
    {st0 st : M.σ} {f : Nat} {evs_acc : List AllocEvent}
    (hf : f + 4 ≤ 16 * x.st.bytes.length + 32)
    (hloop : DecodeStateLoopEnv f x.st.bytes.length (2 * x.st.bytes.length + 16) evs_acc)
    (hst : M.stepEvents evs_acc st0 = st) :
    ∀ evs_fr evs_p1 evs_p2 evs_f,
      DecodeErrorFromEnv evs_fr → DecodeErrorPushEnv 0 evs_p1 → DecodeErrorPushEnv 1 evs_p2 →
      FreeOnlyEvs evs_f →
      ∃ evs, DecodeStateEnv x evs ∧
        M.stepEvents evs st0 =
          M.stepEvents evs_f (M.stepEvents evs_p2 (M.stepEvents evs_p1 (M.stepEvents evs_fr st))) := by
  intro evs_fr evs_p1 evs_p2 evs_f hfr hp1 hp2 hfree
  have h1 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_fr :=
    DecodeStateLoopEnv.single (fuel := 0) (decodeStateIterEnv_of_decodeErrorFrom hfr)
  have h2 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p1 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp1)
  have h3 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_p2 :=
    DecodeStateLoopEnv.single (fuel := 0) (.pushErr (by decide) hp2)
  have h4 : DecodeStateLoopEnv 1 x.st.bytes.length (2 * x.st.bytes.length + 16) evs_f :=
    DecodeStateLoopEnv.single (fuel := 0) (.deallocs hfree)
  refine ⟨(((evs_acc ++ evs_fr) ++ evs_p1) ++ evs_p2) ++ evs_f,
    ((((hloop.append h1).append h2).append h3).append h4).mono_fuel hf, ?_⟩
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, M.stepEvents_append, hst]

/-! ## 2. `v1::State::merge` Error Push (`0x53bc0`) -/

/-! ## 3. Outer Loop `decode_key` & `skip_field` Error Exits (`0x53af8..0x53b24`) -/

/-! ## 4. `ChainPB` Shared Error Push `0x53cbc` & First Group (`0x53c9c`, `0x53ec4..0x53fac`) -/

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.ErrorExitSubPlacedBudgetAux
