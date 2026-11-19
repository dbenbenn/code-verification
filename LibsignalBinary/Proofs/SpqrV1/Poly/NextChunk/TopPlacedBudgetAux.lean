/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangeComplete.Proof

/-!
# `VmPreserved`-Strengthened Placed Contract for `lagrange_interpolate_complete`

Thin wrapper re-exporting `CryptoVerification.SpqrV1.Poly.LagrangeComplete.lagrangeComplete_vm_placed_ok`
under the `TopPlacedBudgetAux` namespace.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudgetAux

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkPC_373 blkPl_373 lsmpl withLsCodeLoaded)
open CryptoVerification.SpqrV1.GF.Mul2U16 (OnceCallHookOk addVmPreserved)
open CryptoVerification.SpqrV1.Poly.LagrangeComplete (lagrangeCompletePlacedSpec)

/-- Relocatable `<spqr::encoding::polynomial::Poly>::lagrange_interpolate_complete` (Block `373`)
    satisfies `withLsCodeLoaded lsmpl (addVmPreserved lagrangeCompletePlacedSpec)` under
    `[LibsignalPlacement]` and `OnceCallHookOk`. -/
theorem lagrangeComplete_vm_placed_ok [LibsignalPlacement] (ext : String → Option (State → State))
    (hOnce : OnceCallHookOk (Rust.withPanics ext)) :
    subroutine_ok ((blkPC_373).rebase (blkPl_373).base (Rust.withPanics ext))
      (blkPl_373).base (withLsCodeLoaded lsmpl (addVmPreserved lagrangeCompletePlacedSpec)) :=
  CryptoVerification.SpqrV1.Poly.LagrangeComplete.lagrangeComplete_vm_placed_ok ext hOnce

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudgetAux
