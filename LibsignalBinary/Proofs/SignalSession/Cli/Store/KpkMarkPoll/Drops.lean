/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

theorem cs_x19 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x19 = s.readReg64 .x19 := h.1
theorem cs_x20 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x20 = s.readReg64 .x20 := h.2.1
theorem cs_x21 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x21 = s.readReg64 .x21 := h.2.2.1
theorem cs_x22 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x22 = s.readReg64 .x22 := h.2.2.2.1
theorem cs_x23 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.1
theorem cs_x24 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.1
theorem cs_x25 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.1
theorem cs_x26 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x27 = s.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
theorem cs_x29 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x29 = s.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s sm : State} (h : CalleeSavedPreserved s sm) : calleeSavedVRegs sm = calleeSavedVRegs s := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## Shared `Dir::put::<String>` Tail (`+184 .. +192` → `kpk_epilogue_330`) & Dual-`Vec` Drops -/

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
