/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import Aesop.BuiltinRules
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import Mathlib.Tactic.Attr.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.SepLogic.WPp
import VCVio.Prelude.Core
public import ProofLib.GenDecodes
public import ProofLib.VCGen

/-!
# `HookSessionStore::store_session` Shim (`0x42e5c`)

Verifies `<HookSessionStore as SessionStore>::store_session(self = x0, address = x1, record = x2)`
(24 instructions): allocates a 32-byte 8-aligned box holding `[self, address, record, 0#8]` and
returns `(x0 = box, x1 = b + 0x4db00)`.
-/

public section

namespace CryptoVerification.LibsignalPublicApi.StoreSession

open Arm64 ProofLib CryptoVerification.RustHeap

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The `store_session` shim (`0x42e5c`). -/
abbrev storeSessionShimName : String :=
  "<libsignal_session_stores::HookSessionStore as libsignal_protocol::storage::traits::SessionStore>::store_session"

/-- Stack of the shim: its 48-byte frame (`0x42e5c: stp x29, x30, [sp, #-0x30]!`) and the
allocator hook's. -/
abbrev storeSessionShimStack : Nat := allocHookStack + 48

/-- Ghost of a shim call: `self` (`x0`, the store's data pointer), the address (`x1`) and the
record (`x2`) pointers. -/
structure StoreShimCall where
  self : BitVec 64
  addrA : BitVec 64
  recA : BitVec 64

private theorem stackAt_storeSessionShim (sp : BitVec 64) :
    stackAt sp storeSessionShimStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

private theorem memRegion_32_box (p : BitVec 64) :
    memRegion p 32 =
      (∃∗ b0 : BitVec 8, ∃∗ u2 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₆₄ u2) ∗ ((p + 24#64) ↦₈ b0) ∗
        memRegion (p + 25#64) 7) := by
  rw [memRegion_split p 8 24 (by decide),
    memRegion_split (p + 8#64) 8 16 (by decide),
    memRegion_split (p + 8#64 + 8#64) 8 8 (by decide),
    memRegion_split (p + 8#64 + 8#64 + 8#64) 1 7 (by decide),
    memRegion_one, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

private theorem sepWPp_pure_mid {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) Q Qp) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) Q Qp := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

end CryptoVerification.LibsignalPublicApi.StoreSession
