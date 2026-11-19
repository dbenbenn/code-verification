/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.LabelsInterned
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Code-Slice Relocation Certificate Check

**Checked by Lean.** Proves `cliLabelsLfo_brelocs_ok` against the interned `IdxTree` certificate in
`CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextRelocs

open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_N cliLabelsLfo_bOTree cliLabelsLfo_dOTree cliLabelsLfo_iLib cliLabelsLfo_objsTree
   cliLabelsLfo_rawSummary cliLabelsLfo_symRole)

theorem cliLabelsLfo_brelocs_ok :
    Arm64.Obj.LabelsInterned.checkAllBlockRelocsB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib cliLabelsLfo_bOTree cliLabelsLfo_dOTree cliLabelsLfo_symRole
      cliLabelsLfo_rawSummary = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextRelocs
