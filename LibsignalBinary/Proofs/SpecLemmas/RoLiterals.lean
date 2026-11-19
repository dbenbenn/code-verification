/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic

public section

set_option autoImplicit false

/-!
# Read-only literal assertions (`roLits`)

**Checked by Lean.**

Separating conjunction `roLits base ls` of read-only byte assertions `(base + off) ↦ᵣ bs` for a
list of `(offset, bytes)` pairs.
-/

namespace Arm64.Obj

open Arm64 ProofLib

/-- The read-only points-to facts of the literals `ls` (`(offset, bytes)`, base-relative) based at
`base`. -/
@[expose] def roLits (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) : SepProp :=
  ls.foldr (fun l P => ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ P) emp

@[simp] theorem roLits_nil (base : BitVec 64) : roLits base [] = emp := rfl

@[simp] theorem roLits_cons (base : BitVec 64) (l : Nat × List (BitVec 8))
    (ls : List (Nat × List (BitVec 8))) :
    roLits base (l :: ls) = ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ roLits base ls := rfl

/-- Read-only literals duplicate. -/
@[simp] theorem roLits_dup (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) :
    (roLits base ls ∗ roLits base ls) = roLits base ls := by
  induction ls with
  | nil => rw [roLits_nil, emp_sepConj]
  | cons l ls ih =>
    rw [roLits_cons, sepConj_assoc, sepConj_left_comm (roLits base ls), ← sepConj_assoc,
      pointsToBytesRO_dup, ih]

end Arm64.Obj
