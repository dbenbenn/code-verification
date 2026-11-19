/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Placed.PlacedCallSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ParseServiceId
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.ProtocolAddressDisplay

/-!
# Trap-at-RNG and Cross-Block Call-Site Lemmas for In-Image Callees

Call-site transport lemmas on `trTrapProgAt` for `ServiceId::parse_from_service_id_string`
and `<ProtocolAddress as Display>::fmt`, plus generic `[LibsignalPlacement]` cross-block lifting.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr

/-- Relocatable cross-block lift from block `j` to caller block `i`. -/
theorem inImage_placed_ok_at [LibsignalPlacement] {α : Type} {prog calleeProg : Program}
    {i j : Nat} {H : String → Option (State → State)} {spec : Spec α}
    [IsLsBlockProg prog i H] [IsLsBlockProg calleeProg j H]
    (h : subroutine_ok calleeProg (lsmpl.base j) (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (_hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide)
    (hj : j < 619 := by decide) (hunmut_j : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsmpl.base j) (withLsCodeLoaded lsmpl spec) :=
  ls_subroutine_ok_of_block (callerProg := prog) h hi hj hunmut_j

end CryptoVerification.LibsignalTripleRatchet
