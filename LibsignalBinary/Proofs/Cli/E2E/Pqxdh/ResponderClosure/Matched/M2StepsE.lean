/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import ProofLib.SepLogic.WP
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
# Stage P2 Matched-Session Mismatch Funnel Blocks

`tripleRatchetProgAtExt b ext` basic blocks `+0x1310 → drop_process_prekey_impl_state1` and
`+0x1698 → +0x3588` specialized to `InvalidMessage(.preKey)` (`errTag = 0x8000000000000018#64`).
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

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_cap_lo32_lsr8 (cap : BitVec 64) :
    ((cap.extractLsb' 0 32).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_setWidth32_lsr8 (cap : BitVec 64) :
    ((BitVec.setWidth 32 cap).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_hi_lo_append (w : BitVec 64) :
    BitVec.setWidth 32 (w >>> 32) ++ BitVec.setWidth 32 w = w := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_3_zero :
    ((3#64 : BitVec 64) &&& 255#64 |||
      ((0#64 : BitVec 64) &&& 72057594037927935#64) <<< 8) = 3#64 := by
  decide

private theorem coro_268_split32_m2e (coroPtr w : BitVec 64) :
    (coroPtr + 0x268#64) ↦₆₄ w =
    ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32, BitVec.add_assoc]; rfl

private theorem coro_268_pair32_m2e (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi) =
    (coroPtr + 0x268#64) ↦₆₄ (hi ++ lo) := by
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
  rw [coro_268_split32_m2e coroPtr (hi ++ lo), hlo, hhi]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
