/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Stack

/-!
# Frame Carving and Stack Splitting for Panicking/OOM Callees

Provides `subroutine_ok_carve_frame` (frame preservation across normal return, panic, exit, and OOM
outcomes) and `stackAt_split_of_le` (splitting `stackAt sp m` into a lower `m - n` region and top
`stackAt sp n` frame) to lift fixed-stack callee contracts to arbitrary `stk ≥ need`.
-/

public section

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib

/-- Splits `stackAt sp m` into `memRegion (sp - m) (m - n) ∗ stackAt sp n` when `n ≤ m ≤ sp.toNat`. -/
theorem stackAt_split_of_le (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hbound : m ≤ sp.toNat) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  unfold stackAt
  have hsum : (m - n) + n = m := by omega
  have hsp : sp.toNat < 2 ^ 64 := sp.isLt
  refine memRegion_split'
    (b := sp - BitVec.ofNat 64 m)
    (b' := sp - BitVec.ofNat 64 n)
    (n := m - n) (k := n)
    hsum.symm ?_ (by omega)
  bv_omega

end CryptoVerification.SignalSession.Cli.Slots
