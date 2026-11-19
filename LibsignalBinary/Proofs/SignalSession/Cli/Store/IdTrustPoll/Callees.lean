/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoGames.LibsignalSessionApi CryptoVerification.RecordCodecs
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## Callee cell-friendly wrappers at `calleeStk` -/

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def dirGetCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, nameA, name, fsp) s =>
    ⌜s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nameA ∧
      (s.readReg64 .x3).toNat = name.length ∧ s.sp = fsp ∧
      name.length < 2 ^ 32 ∧ dir.path.length < 2 ^ 32 ∧ pathOk (pathOf dir.path name)⌝ ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗ memRegion ret 48 ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, nameA, name, fsp) s0 sf =>
    (∃∗ r : Except Unit (List (BitVec 8)),
      ⌜r = dir.get rd s0.fs.files name ∧ sf.trace = s0.trace⌝ ∗
        getResultAt A ret r) ∗
      dirAt A self dir ∗ (nameA ↦ₛ name) ∗ stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev IkDecodeCellsGhost :=
  BitVec 64 × List (BitVec 8) × BitVec 64 × IdentityKey × BitVec 64

abbrev DeallocVecBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def deallocVecBufSpec (A : RustAlloc) (calleeStk : Nat) : Spec DeallocVecBufGhost where
  pre := fun (bPtr, bCap, bs, fsp) s =>
    ⌜s.readReg64 .x0 = bPtr ∧ s.readReg64 .x1 = bCap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp ∧ bs.length ≤ bCap.toNat ∧ bCap.toNat < 2 ^ 63 ∧ bCap ≠ 0#64⌝ ∗
      (bPtr ↦ₛ bs) ∗ vecU8BufRest A bCap bPtr bs.length ∗ A.pool ∗ stackAt fsp calleeStk
  post := fun (_bPtr, _bCap, _bs, fsp) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev PkEqCellsGhost := BitVec 64 × IdentityKey × BitVec 64 × IdentityKey × BitVec 64

@[expose] def pkEqCellsSpec (calleeStk : Nat) : Spec PkEqCellsGhost where
  pre := fun (p1, ik1, p2, ik2, fsp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = fsp⌝ ∗
      (p1 ↦ₛ ik1.publicKey.bytes.toList) ∗ (p2 ↦ₛ ik2.publicKey.bytes.toList) ∗
      stackAt fsp calleeStk
  post := fun (p1, ik1, p2, ik2, fsp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if decide (ik1 = ik2) then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ ik1.publicKey.bytes.toList) ∗ (p2 ↦ₛ ik2.publicKey.bytes.toList) ∗
      stackAt fsp calleeStk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.Store.IdTrustPoll.Helpers
