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
# Interned `LabelsFromObjects` Table and Role Certificate Checks

**Checked by Lean.** Discharges the symbol-table size, character nodup, slice count, role, and
empty COMDAT group checks over `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoCertChecksA

open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (checkIObjsGroupsEmptyB cliLabelsLfo_B cliLabelsLfo_D cliLabelsLfo_N cliLabelsLfo_charsTree
   cliLabelsLfo_iLib cliLabelsLfo_namesTree cliLabelsLfo_objsTree cliLabelsLfo_symRole)

theorem cliLabelsLfo_names_sz : cliLabelsLfo_namesTree.size? = some cliLabelsLfo_N := by
  rfl_kernel

theorem cliLabelsLfo_chars_sz : cliLabelsLfo_charsTree.size? = some cliLabelsLfo_N := by
  rfl_kernel

theorem cliLabelsLfo_names_eq :
    cliLabelsLfo_namesTree.toList = cliLabelsLfo_charsTree.toList.map String.ofList := by
  rfl_kernel

theorem cliLabelsLfo_names_nodup :
    Arm64.Obj.Interned.namesNodup cliLabelsLfo_charsTree.toList = true := by
  rfl_kernel

theorem cliLabelsLfo_names_zero : cliLabelsLfo_namesTree.get? 0 = some "" := by
  rfl_kernel

theorem cliLabelsLfo_blocks_sz : cliLabelsLfo_iLib.blocks.size? = some cliLabelsLfo_B := by
  rfl_kernel

theorem cliLabelsLfo_data_sz : cliLabelsLfo_iLib.data.size? = some cliLabelsLfo_D := by
  rfl_kernel

theorem cliLabelsLfo_roles_ok :
    Arm64.Obj.LabelsInterned.checkSymRolesB cliLabelsLfo_N cliLabelsLfo_iLib cliLabelsLfo_symRole =
      true := by
  rfl_kernel

theorem cliLabelsLfo_groups_ok : checkIObjsGroupsEmptyB cliLabelsLfo_objsTree = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoCertChecksA
