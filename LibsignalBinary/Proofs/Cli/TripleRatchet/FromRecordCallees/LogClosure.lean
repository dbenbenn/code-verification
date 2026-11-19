/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

/-!
# `try_decrypt_from_record::{closure#0}` Verification

Proves that `try_decrypt_from_record::<Coins>::{closure#0}` meets `logClosureSpec` on the log-off
path in the CLI image.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_closure (sp : BitVec 64) :
    stackAt sp closureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) ∗
      stackAt (sp - 64#64) 296 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
  have h1 := stackAt_split_cells sp 320 8 (by decide)
  have h2 := stackAt_split_bottom (sp - 64#64) 296 24 (by decide)
  have hsub : (sp - 64#64) - BitVec.ofNat 64 (296 + 24) = sp - 384#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (24 : Nat) = 8 * 3 by rfl, memRegion_cells (sp - 384#64) 3 (by decide)] at h2
  change stackAt sp closureStack = stackAt (sp - 64#64) 320 ∗ cells (sp - 64#64) 8 at h1
  have hc3 : cells (sp - 384#64) 3 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) := by
    cells_unfold
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
    cells_unfold
  rw [h1, h2, hc3, hc8, sepConj_assoc]

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
