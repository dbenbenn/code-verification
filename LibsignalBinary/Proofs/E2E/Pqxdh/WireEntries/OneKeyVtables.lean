/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.CodeLayout
public import Mathlib.Tactic.ToDual
public import ProofLib.SepLogic.Bytes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import ProofLib.GenDecodes
public import ProofLib.VCGen

public section

namespace CryptoVerification.E2E.Pqxdh.WireEntries

set_option warningAsError false
set_option maxRecDepth 200000

open Arm64 ProofLib
open ProofLib.ProgramReflection

/-! ## `.data.rel.ro` Vtable Predicates (`0x87a30..0x87d40`) -/

/-- `.data.rel.ro` future vtable (32 B): `(drop, size, align, poll)`. -/
@[expose] def futVtableAtP (vtAddr dropAddr size align pollAddr : BitVec 64) : SepProp :=
  (vtAddr ↦₆₄ᵣ dropAddr) ∗
  ((vtAddr + 0x08#64) ↦₆₄ᵣ size) ∗
  ((vtAddr + 0x10#64) ↦₆₄ᵣ align) ∗
  ((vtAddr + 0x18#64) ↦₆₄ᵣ pollAddr)

end CryptoVerification.E2E.Pqxdh.WireEntries
