/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs

/-!
# `message::merge<Chain> [local#5]`: MessageKeys Shared Definitions

Defines the preserved register bundle `Chain3MkRegs` and the four sub-step statements decomposing
the tag-4 (`message_keys`) slice (`Chain3MessageKeysStmt`) around the 104-byte scratch `MessageKey`
at `sp0 - 0xe8`: `Chain3MkHeadStmt`, `Chain3MkCntStmt`, `Chain3MkSeedStmt`, and `Chain3MkPushStmt`
(plus `A : RustAlloc`-parameterized `*Ext` variants).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

/-! ## 1. Register bookkeeping -/

/-- The registers the tag-4 path keeps: `x19..x24`, `x26..x29` and `calleeSavedVRegs`
(`x25` holds the inner limit, then the `Vec` length; it is not in `Chain3LoopAtW`). -/
@[expose] def Chain3MkRegs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧
  s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧
  s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧
  s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧
  s1.readReg64 .x28 = s0.readReg64 .x28 ∧
  s1.readReg64 .x29 = s0.readReg64 .x29 ∧
  calleeSavedVRegs s1 = calleeSavedVRegs s0

theorem Chain3MkRegs.refl (s : State) : Chain3MkRegs s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Chain3MkRegs.trans {s0 s1 s2 : State}
    (h01 : Chain3MkRegs s0 s1) (h12 : Chain3MkRegs s1 s2) : Chain3MkRegs s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1, h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.2.2.2.2.trans h01.2.2.2.2.2.2.2.2.2.2⟩

theorem Chain3MkRegs.of_calleeSaved {s0 s1 : State}
    (h : CalleeSavedPreserved s0 s1) : Chain3MkRegs s0 s1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-! ## 2. Step 4d + 4e: the push (`+0x244 → +0x0a8`) -/

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3
