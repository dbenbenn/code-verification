/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.GrowOne -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.SigTryFrom.PushCore
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeErrorPush
open BS31

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre_x sp_setMem_setPC_pre_x
  readReg64_setPC_pre_x readReg64_setMem_setPC_pre_x
  readReg32_setPC_pre_x readReg32_setMem_setPC_pre_x
  readReg_setPC_pre_x readReg_setMem_setPC_pre_x

theorem pre_inImage_merge {P Q : Prop} {S : SepProp} :
    ⌜P⌝ ∗ (⌜Q⌝ ∗ S) = ⌜P ∧ Q⌝ ∗ S := by
  rw [← sepConj_assoc, pure_sepConj_pure]

@[expose] def growAmortizedSpecX (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, gsp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.readReg64 .x1 = cap ∧ s.sp = gsp ∧
      cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
    stackAt (gsp - 96#64) extHookStack
  post := fun (v, cap, ptr, gsp) s0 sf =>
    ∃∗ res : BitVec 64, ∃∗ p' : BitVec 64,
      (if res = 0xffffffffffffffff#64 then
        ⌜sf.readReg64 .x0 = 0xffffffffffffffff#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32)
       else
        ⌜res = 8#64 ∧ sf.readReg64 .x0 = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32))) ∗
      A.pool ∗ cells (gsp - 64#64) 8 ∗ cells (gsp - 96#64) 4 ∗
      stackAt (gsp - 96#64) extHookStack

@[expose] def growOneStrPairSpecX (A : RustAlloc) : Spec GrowAmortizedGhost where
  pre := fun (v, cap, ptr, osp) s =>
    ⌜s.readReg64 .x0 = v ∧ s.sp = osp ∧ cap.toNat < 2 ^ 32 ∧ ptr ≠ 0#64⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)) ∗
    A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
    stackAt (osp - 112#64) extHookStack
  post := fun (v, cap, _ptr, osp) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (v ↦₆₄ newCap cap) ∗ ((v + 8#64) ↦₆₄ p') ∗
      A.live p' ((newCap cap).toNat * 32) 8 ∗ memRegion p' ((newCap cap).toNat * 32) ∗
      A.pool ∗ cells (osp - 16#64) 2 ∗ cells (osp - 80#64) 8 ∗ cells (osp - 112#64) 4 ∗
      stackAt (osp - 112#64) extHookStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
