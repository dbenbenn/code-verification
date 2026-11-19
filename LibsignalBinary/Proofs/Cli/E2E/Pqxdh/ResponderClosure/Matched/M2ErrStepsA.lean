/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1DropSS3A -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.LoadHelpers
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P2 Matched-Session Shared Error Unwind: Part A

`tripleRatchetProgAtExt b ext` basic blocks `+0x1698 → +0x1898 → +0x3588 → dropSessionStructure3`
preserving `s1.vregs = s.vregs`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem coro_268_split32_std3 (coroPtr w : BitVec 64) :
    (coroPtr + 0x268#64) ↦₆₄ w =
    ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32, BitVec.add_assoc]; rfl

private theorem coro_268_pair32_std3 (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi) =
    (coroPtr + 0x268#64) ↦₆₄ (hi ++ lo) := by
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
  rw [coro_268_split32_std3 coroPtr (hi ++ lo), hlo, hhi]

private theorem realign_40_at_a98_std3 (sp w0 w1 w2 w3 w4 : BitVec 64) :
    (((sp + 0xa98#64) ↦₆₄ w0) ∗ ((sp + 0xaa0#64) ↦₆₄ w1) ∗ ((sp + 0xaa8#64) ↦₆₄ w2) ∗
     ((sp + 0xab0#64) ↦₆₄ w3) ∗ ((sp + 0xab8#64) ↦₆₄ w4)) =
    (((sp + 0xa98#64) ↦₃₂ w0.extractLsb' 0 32) ∗
     ((sp + 0xa9c#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
     ((sp + 0xaa4#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
     ((sp + 0xaac#64) ↦₆₄ (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)) ∗
     ((sp + 0xab4#64) ↦₆₄ (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)) ∗
     ((sp + 0xabc#64) ↦₃₂ w4.extractLsb' 32 32)) := by
  have h := realign_40 (sp + 0xa98#64) w0 w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  exact h

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
