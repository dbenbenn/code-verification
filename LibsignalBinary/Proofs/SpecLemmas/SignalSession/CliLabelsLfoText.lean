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
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextLibEq -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextBytes -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextRelocs -- proof-setup: allow-public-import
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

public section

set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Code-Slice Byte, Metadata, and Relocation Certificate Checks

**Checked by Lean.** Re-exports the parallel `cliLabelsLfo_lib_eq`, `cliLabelsLfo_tbytes_ok`, and
`cliLabelsLfo_brelocs_ok` shards and proves `cliLabelsLfo_tmeta_ok` against `CliLabelsLfoCert`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoText

open ProofLib.ProgramReflection
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoCert
  (cliLabelsLfo_N cliLabelsLfo_bOTree cliLabelsLfo_iLib cliLabelsLfo_objsTree
   cliLabelsLfo_rawClaimed)

export LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextLibEq (cliLabelsLfo_lib_eq)
export LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextBytes (cliLabelsLfo_tbytes_ok)
export LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfLabelsLfoTextRelocs (cliLabelsLfo_brelocs_ok)

theorem cliLabelsLfo_tmeta_ok :
    Arm64.Obj.LabelsInterned.checkTextSlicesMetaB cliLabelsLfo_N cliLabelsLfo_objsTree
      cliLabelsLfo_iLib.blocks cliLabelsLfo_bOTree cliLabelsLfo_rawClaimed = true := by
  rfl_kernel

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfoText
