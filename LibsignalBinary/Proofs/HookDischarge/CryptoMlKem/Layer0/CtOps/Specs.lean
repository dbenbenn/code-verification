/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.CommonBase

/-!
# Constant-Time Helper Contracts (`B12`–`B18`)

Placement-independent `Spec` contracts for `B15` (`inz`), `B12` (`is_non_zero`),
`B17` (`compare`), `B13` (`compare_ciphertexts_in_constant_time`), `B18` (`select_ct`),
`B14` (`select_shared_secret_in_constant_time`), and `B16`
(`compare_ciphertexts_select_shared_secret_in_constant_time`, including RO, all-RW, and
RO-`lhsCt` + RW-stack specializations for `B04` and `B06`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs

open Arm64 ProofLib

/-- Zero-stack `B15` (`libcrux_ml_kem::constant_time_ops::inz`) contract. -/
@[expose] def mlkemInzSpec : Spec (BitVec 8) where
  pre := fun b s0 =>
    ⌜(s0.readReg32 .x0).truncate 8 = b⌝
  post := fun b s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.readReg32 .x0 = (if b == 0#8 then 0#32 else 1#32)⌝
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `32`-byte-stack `B12` (`libcrux_ml_kem::constant_time_ops::is_non_zero`) contract. -/
@[expose] def mlkemIsNonZeroSpec : Spec (BitVec 8) where
  pre := fun b s0 =>
    ⌜(s0.readReg32 .x0).truncate 8 = b⌝ ∗
      stackAt s0.sp 32
  post := fun b s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.readReg32 .x0 = (if b == 0#8 then 0#32 else 1#32)⌝ ∗
      stackAt s0.sp 32
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Read-only constant-time slice comparison contract (`stkBytes = 32` for `B17`,
    `stkBytes = 64` for `B13`). -/
@[expose] def mlkemCtCompareROSpec (stkBytes : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × List (BitVec 8)) where
  pre := fun (lhsPtr, rhsPtr, lhs, rhs) s0 =>
    ⌜s0.readReg64 .x0 = lhsPtr ∧
      (s0.readReg64 .x1).toNat = lhs.length ∧
      s0.readReg64 .x2 = rhsPtr ∧
      (s0.readReg64 .x3).toNat = rhs.length ∧
      1 ≤ lhs.length ∧
      rhs.length = lhs.length ∧
      lhs.length < 2 ^ 64⌝ ∗
      (lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ stackAt s0.sp stkBytes
  post := fun (lhsPtr, rhsPtr, lhs, rhs) s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf ∧
      sf.readReg32 .x0 = (if lhs == rhs then 0#32 else 1#32)⌝ ∗
      (lhsPtr ↦ᵣ lhs) ∗ (rhsPtr ↦ᵣ rhs) ∗ stackAt s0.sp stkBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Arguments to `B18` (`select_ct`) and `B14` (`select_shared_secret_in_constant_time`). -/
structure CtSelectArgs where
  outPtr : BitVec 64
  lhsPtr : BitVec 64
  rhsPtr : BitVec 64
  lhs    : List (BitVec 8)
  rhs    : List (BitVec 8)
  sel    : BitVec 8

/-- Read-only `32`-byte constant-time selection contract (`stkBytes = 80` for `B18`,
    `stkBytes = 112` for `B14`). -/
@[expose] def mlkemSelectCtROSpec (stkBytes : Nat) : Spec CtSelectArgs where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.outPtr ∧
      s0.readReg64 .x1 = a.lhsPtr ∧
      s0.readReg64 .x2 = 32#64 ∧
      s0.readReg64 .x3 = a.rhsPtr ∧
      (s0.readReg32 .x4).truncate 8 = a.sel ∧
      a.lhs.length = 32 ∧
      a.rhs.length = 32⌝ ∗
      memRegion a.outPtr 32 ∗ (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗
      stackAt s0.sp stkBytes
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      (a.outPtr ↦ₛ (if a.sel == 0#8 then a.lhs else a.rhs)) ∗
      (a.lhsPtr ↦ᵣ a.lhs) ∗ (a.rhsPtr ↦ᵣ a.rhs) ∗ stackAt s0.sp stkBytes
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- Arguments to `B16` (`compare_ciphertexts_select_shared_secret_in_constant_time`). -/
structure CtCompareSelectArgs where
  outPtr   : BitVec 64
  lhsCtPtr : BitVec 64
  rhsCtPtr : BitVec 64
  lhsSsPtr : BitVec 64
  rhsSsPtr : BitVec 64
  lhsCt    : List (BitVec 8)
  rhsCt    : List (BitVec 8)
  lhsSs    : List (BitVec 8)
  rhsSs    : List (BitVec 8)

/-- Pure register/length precondition shared by `B16` contracts. -/
@[expose] def CtCompareSelectPurePre (a : CtCompareSelectArgs) (s0 : State) : Prop :=
  s0.readReg64 .x0 = a.outPtr ∧
  s0.readReg64 .x1 = a.lhsCtPtr ∧
  (s0.readReg64 .x2).toNat = a.lhsCt.length ∧
  s0.readReg64 .x3 = a.rhsCtPtr ∧
  (s0.readReg64 .x4).toNat = a.rhsCt.length ∧
  s0.readReg64 .x5 = a.lhsSsPtr ∧
  s0.readReg64 .x6 = a.rhsSsPtr ∧
  1 ≤ a.lhsCt.length ∧
  a.rhsCt.length = a.lhsCt.length ∧
  a.lhsCt.length < 2 ^ 64 ∧
  a.lhsSs.length = 32 ∧
  a.rhsSs.length = 32

/-- `B16` read-only input specification (`112`-byte stack frame). -/
@[expose] def mlkemCompareSelectROSpec : Spec CtCompareSelectArgs where
  pre := fun a s0 =>
    ⌜CtCompareSelectPurePre a s0⌝ ∗
      memRegion a.outPtr 32 ∗
      (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
      (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗
      stackAt s0.sp 112
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      (a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ᵣ a.rhsCt) ∗
      (a.lhsSsPtr ↦ᵣ a.lhsSs) ∗ (a.rhsSsPtr ↦ᵣ a.rhsSs) ∗
      stackAt s0.sp 112
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B16` all-RW input specialization (matches `B04`, where both ciphertexts and both
    shared-secret candidates reside in the caller's writable stack frame). -/
@[expose] def mlkemCompareSelectRWSpec : Spec CtCompareSelectArgs where
  pre := fun a s0 =>
    ⌜CtCompareSelectPurePre a s0⌝ ∗
      memRegion a.outPtr 32 ∗
      (a.lhsCtPtr ↦ₛ a.lhsCt) ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
      (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs) ∗
      stackAt s0.sp 112
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      (a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      (a.lhsCtPtr ↦ₛ a.lhsCt) ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
      (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs) ∗
      stackAt s0.sp 112
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

/-- `B16` RO-`lhsCt` + RW-`rhsCt`/`lhsSs`/`rhsSs` specialization (matches `B06`, where `lhsCt` is
    the read-only caller ciphertext slice and `rhsCt`, `lhsSs`, `rhsSs` reside on the stack). -/
@[expose] def mlkemCompareSelectRO1RW3Spec : Spec CtCompareSelectArgs where
  pre := fun a s0 =>
    ⌜CtCompareSelectPurePre a s0⌝ ∗
      memRegion a.outPtr 32 ∗
      (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
      (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs) ∗
      stackAt s0.sp 112
  post := fun a s0 sf =>
    ⌜ProofLib.NonSyscallPreserved s0 sf⌝ ∗
      (a.outPtr ↦ₛ (if a.lhsCt == a.rhsCt then a.lhsSs else a.rhsSs)) ∗
      (a.lhsCtPtr ↦ᵣ a.lhsCt) ∗ (a.rhsCtPtr ↦ₛ a.rhsCt) ∗
      (a.lhsSsPtr ↦ₛ a.lhsSs) ∗ (a.rhsSsPtr ↦ₛ a.rhsSs) ∗
      stackAt s0.sp 112
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Layer0.CtOps.Specs
