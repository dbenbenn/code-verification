/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From

/-!
# Root Theorems `otrFrom_run` and `otrApply_run`

Bridges `otrFrom_ok` and `otrApply_ok` from `tripleRatchetProgAt` to the root statements
`OtrFromRunStmt` and `OtrApplyRunStmt`, and re-exports their `[LibsignalPlacement]` counterparts.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

theorem otrFrom_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hremIk : subroutine_ok ((blkPC_29).rebase (blkPl_29).base H)
      (blkPl_29).base (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (hdropSpe : subroutine_ok ((blkPC_5).rebase (blkPl_5).base H)
      (blkPl_5).base (withLsRoLoaded lsmpl (dropSpeSpec A))) :
    subroutine_ok ((blkPC_19).rebase (blkPl_19).base H) (blkPl_19).base
      (otrFromPlacedSpec A) :=
  otrFrom_placed_ok h_dealloc hremIk hdropSpe

theorem otrApply_run_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (h_shim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (h_alloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (h_dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (h_panic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_20).rebase (blkPl_20).base H) (blkPl_20).base
      (otrApplyPlacedSpec A) :=
  otrApply_placed_ok h_shim h_alloc h_dealloc h_panic

end CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
