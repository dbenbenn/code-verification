/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon -- proof-setup: allow-public-import
import ProofLib
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: `SendEk` Shared Writeback Helpers under `AllocContractsX`

**Checked by Lean.** `AllocContractsX` (`extHookStack = 16384` B) `Relocatable` `memcpy` rule
and shared `Ok(V1Recv)` writeback epilogue (`0x59e88..0x59ff0`).
-/

public section

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv BitVec.sub_add_cancel BitVec.toNat_zero
  Leaves.extractLsb'_0_64_append Leaves.extractLsb'_64_64_append
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv sp_sub_48_add_8_recv
  sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv

/-! ## Shared AC-Framing & `.inImage img` Combinators -/

open Lean Meta Elab Tactic in
elab "sep_ac_rfl_recv_ext" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let some (_, lhs, rhs) := ty.eq?
      | throwError "sep_ac_rfl_recv_ext: expected equality"
    if lhs == rhs then
      g.assign (← mkEqRefl lhs)
      replaceMainGoal []
    else if let some (tbl, tA, tB) := ProofLib.SepSolver.synReifyPermTbl? lhs rhs then
      g.assign (← ProofLib.SepSolver.eqACOfTbl lhs rhs tbl tA tB)
      replaceMainGoal []
    else
      evalTactic (← `(tactic| sep_frame))

theorem sepWP_weaken_mono_recv_ext {prog : Program} {target_pc : BitVec 64} {s : State}
    {P P' : SepProp} {post post' : State → SepProp → Prop}
    (h : SepWP prog target_pc s P' post')
    (hpost : ∀ sf Pf, sf.pc = target_pc → sf.status = .Running → post' sf Pf → post sf Pf)
    (hP : P = P' := by sep_ac_rfl_recv_ext) :
    SepWP prog target_pc s P post :=
  hP ▸ SepWP.mono h hpost

abbrev sessionMemcpyRegionSpecExt : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  withStack sessionMemcpyRegionSpec extHookStack

/-- `abbrev` definitionally equal (`rfl`) to `DispatchExt.growToCalleeExt`, growing any callee
    `Spec α` at stack budget `oldStack ≤ statesRecvCalleeStackXExt` up to `statesRecvCalleeStackXExt`
    (`35936` B) without importing `DispatchExt`. -/
abbrev growToCalleeExtSendEk {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α :=
  { pre := fun x s =>
      spec.pre x s ∗
        memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - oldStack)
    post := fun x s0 sf =>
      spec.post x s0 sf ∗
        memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
          (statesRecvCalleeStackXExt - oldStack)
    onPanic := spec.onPanic }

theorem stackAt_statesRecvCalleeExt_split (sp_call : BitVec 64) (oldStack : Nat)
    (hle : oldStack ≤ statesRecvCalleeStackXExt := by decide) :
    stackAt sp_call statesRecvCalleeStackXExt =
      memRegion (sp_call - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack) ∗
      stackAt sp_call oldStack := by
  have hadd : oldStack + (statesRecvCalleeStackXExt - oldStack) = statesRecvCalleeStackXExt :=
    Nat.add_sub_of_le hle
  have hbound : oldStack + (statesRecvCalleeStackXExt - oldStack) ≤ 2 ^ 64 := by
    rw [hadd]; decide
  simpa [hadd] using
    ProofLib.stackAt_split_bottom sp_call oldStack (statesRecvCalleeStackXExt - oldStack) hbound

end CryptoVerification.SpqrV1.States.Recv
