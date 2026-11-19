/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliLabels -- proof-setup: allow-public-import
public import ProofLib.Placed.LabelsInterned
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Interned `MultiPlacedLib` Equality Check

**Checked by Lean.** Proves `cliLabelsLfo_lib_eq` over `libsignalSessionLib` against the interned
`IdxTree` certificate in `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextLibEq

open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (libsignalSessionLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_iLib cliLabelsLfo_namesTree)

theorem cliLabelsLfo_lib_eq :
    (libsignalSessionLib : Arm64.Obj.MultiPlacedLib) =
      cliLabelsLfo_iLib.toMultiPlacedLib cliLabelsLfo_namesTree := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextLibEq
