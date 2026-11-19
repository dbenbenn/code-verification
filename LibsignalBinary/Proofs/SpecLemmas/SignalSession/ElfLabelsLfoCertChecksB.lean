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
# Interned `LabelsFromObjects` Disjointness, Export, and Extern Checks

**Checked by Lean.** Discharges slice-group disjointness, export validity, and extern validity
checks over `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoCertChecksB

open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_B cliLabelsLfo_D cliLabelsLfo_N cliLabelsLfo_bOTree cliLabelsLfo_branchCalled
   cliLabelsLfo_commonExtSet cliLabelsLfo_dOTree cliLabelsLfo_dataGroups cliLabelsLfo_dataToGroup
   cliLabelsLfo_iLib cliLabelsLfo_objsTree cliLabelsLfo_rawSummary cliLabelsLfo_symRole
   cliLabelsLfo_textGroups cliLabelsLfo_textToGroup)

theorem cliLabelsLfo_bdisj_ok :
    Arm64.Obj.LabelsInterned.checkGroupsDisjointB cliLabelsLfo_B cliLabelsLfo_bOTree
      cliLabelsLfo_textGroups cliLabelsLfo_textToGroup = true := by
  rfl_kernel

theorem cliLabelsLfo_ddisj_ok :
    Arm64.Obj.LabelsInterned.checkGroupsDisjointB cliLabelsLfo_D cliLabelsLfo_dOTree
      cliLabelsLfo_dataGroups cliLabelsLfo_dataToGroup = true := by
  rfl_kernel

theorem cliLabelsLfo_exports_ok :
    Arm64.Obj.LabelsInterned.checkIExportsB cliLabelsLfo_N cliLabelsLfo_objsTree cliLabelsLfo_iLib
      cliLabelsLfo_bOTree cliLabelsLfo_symRole cliLabelsLfo_rawSummary = true := by
  rfl_kernel

theorem cliLabelsLfo_externs_ok :
    Arm64.Obj.LabelsInterned.checkIExternsB cliLabelsLfo_N cliLabelsLfo_iLib cliLabelsLfo_symRole
      cliLabelsLfo_rawSummary cliLabelsLfo_branchCalled cliLabelsLfo_commonExtSet = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoCertChecksB
