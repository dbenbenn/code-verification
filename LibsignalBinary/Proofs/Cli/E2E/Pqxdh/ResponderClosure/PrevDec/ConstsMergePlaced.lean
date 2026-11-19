/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ConstsMerge
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.BridgePlaced
public meta import Lean
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
public import Arm64.Trusted.Surface.IncludeBytes
public import ProofLib
public import ProofLib.GenPlacedFetches
public import ProofLib.Placed.Multi
public import ProofLib.ProgramReflection.SortedFresh
public import ProofLib.ProgramReflection.Variant.TrapTransfer
public import ProofLib.SepLogic.WPp

/-!
# Relocatable `SessionStructure::merge_field` Constants Re-exports

Re-exports byte-offset constants, prost tag constants, and arithmetic helpers from
`PrevDec.ConstsMerge` alongside `PrevDec.BridgePlaced`.
-/

public section

set_option autoImplicit false
