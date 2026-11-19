/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.Defs
import ProofLib
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Dispatch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv`: Prologue, Dispatch, and Epilogues under `AllocContractsX`

Lifts the prologue, jump-table dispatch, tail-call dealloc/drop epilogues, and shared `Ok(V1Recv)`
store epilogue of `<States>::recv` to `AllocContractsX` / `DeallocOkExt` (`40,176`-byte stack budget).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.States.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local wp_norm] private theorem symtab_writeReg64_ax
    (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[local wp_norm] private theorem symtab_setPC_ax
    (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[local wp_norm] private theorem symtab_setPState_ax
    (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

@[local wp_norm] private theorem exists_two_pow_zero_ax : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

@[local wp_norm] private theorem exists_two_pow_one_ax : (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

theorem stackAt_split_callee_ax (sp : BitVec 64) (nSmall nBig : Nat)
    (hle : nSmall ≤ nBig := by decide) (hbd : nBig ≤ 131072 := by decide) :
    stackAt sp nBig =
      memRegion (sp - BitVec.ofNat 64 nBig) (nBig - nSmall) ∗ stackAt sp nSmall := by
  have hbd' : nSmall + (nBig - nSmall) ≤ 2 ^ 64 := by omega
  have h := ProofLib.stackAt_split_bottom sp nSmall (nBig - nSmall) hbd'
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_statesRecvCalleeExt_eq_extHook_ax (fsp : BitVec 64) :
    stackAt fsp statesRecvCalleeStackXExt =
      memRegion (fsp - 35936#64) 19552 ∗ stackAt fsp extHookStack :=
  ProofLib.stackAt_split_bottom fsp extHookStack 19552 (by decide)

theorem stackAt_statesRecvStackXExt_eq_extHook_ax (sp : BitVec 64) :
    stackAt sp statesRecvStackXExt =
      memRegion (sp - 40176#64) 23792 ∗ stackAt sp extHookStack :=
  ProofLib.stackAt_split_bottom sp extHookStack 23792 (by decide)

abbrev sessionMemcpyRegionSpecAx : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  session2MemcpySpecX

/-- Grow any callee `Spec α` whose internal `stackAt` budget is `oldStack ≤ statesRecvCalleeStackXExt`
    up to the full `statesRecvCalleeStackXExt` (`35936` B) callee stack budget of `States::recv`. -/
@[expose] def growToCalleeExt {α : Type} (oldStack : Nat) (spec : Spec α) : Spec α where
  pre := fun x s =>
    spec.pre x s ∗
      memRegion (s.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  post := fun x s0 sf =>
    spec.post x s0 sf ∗
      memRegion (s0.sp - BitVec.ofNat 64 statesRecvCalleeStackXExt)
        (statesRecvCalleeStackXExt - oldStack)
  onPanic := spec.onPanic

end CryptoVerification.SpqrV1.States.Recv
