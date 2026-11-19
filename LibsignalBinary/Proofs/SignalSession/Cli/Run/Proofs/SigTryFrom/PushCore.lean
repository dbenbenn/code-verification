/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Core -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

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
@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_x (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_x (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_x (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_x (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_x (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[expose] def rustReallocUninitSpecX (A : RustAlloc) : Spec (BitVec 64 × Nat × Nat × Nat) where
  pre := fun (p, old, align, new) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ LayoutOk old align ∧ LayoutOk new align⌝ ∗
      A.pool ∗ A.live p old align ∗ memRegion p old ∗ stackAt s.sp extHookStack
  post := fun (p, old, align, new) s0 sf =>
    A.pool ∗ stackAt s0.sp extHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live p old align ∗ memRegion p old
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ memRegion (sf.readReg64 .x0) new)

@[expose] def finishGrow7ZeroSpecX (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap = 0#64 ∧
      0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack
  post := fun (out, _cap, _ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

@[expose] def finishGrow7NeSpecX (A : RustAlloc) : Spec FinishGrow7Ghost where
  pre := fun (out, cap, ptr, new, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.sp = fsp ∧ cap ≠ 0#64 ∧
      cap.toNat * 32 < 2 ^ 63 ∧ 0 < new.toNat ∧ new.toNat * 32 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool ∗ A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32) ∗
    cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack
  post := fun (out, cap, ptr, new, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜p' = 8#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.live ptr (cap.toNat * 32) 8 ∗ memRegion ptr (cap.toNat * 32)
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
        A.live p' (new.toNat * 32) 8 ∗ memRegion p' (new.toNat * 32)) ∗
      A.pool ∗ cells (fsp - 32#64) 4 ∗ stackAt (fsp - 32#64) extHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

end CryptoVerification.SignalSession.Cli.RunProofs.SigTryFromHelpers
