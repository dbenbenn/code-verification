/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
public import LibsignalBinary.Specifications.SignalSession.CliElf
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlainPlaced
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced -- proof-setup: allow-public-import
public import VerifiedLibraries.Mallocng.Spec

/-!
# Relocatable Plain-Memory Progress for `cliElfBytes` from `H2KGhostArms`

**Checked by Lean.**

Instantiates `cliElfProgressPlainPanPlaced_of_strictG` at `cliElfBytes` from `H2KGhostArms`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf

open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage cliElf_parse libsignalSessionLib)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
  (H2KGhostArmsType cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms
   h2kg_hinitSem_cliElfG
   h2kg_hmain_cliElfG
   h2kg_hoverD3_cliElfG
   h2kg_hpathB_cliElfG
   h2kg_huntyped_cliElfG
   h2kg_hvalidMatch_cliElfG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)
open Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced (CliElfProgressPlainPanPlaced)
open Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressElfPlainPlaced
  (cliElfProgressPlainPanPlaced_of_strictG)

/-- Relocatable two-placement plain-memory progress for `cliElfBytes` from `H2KGhostArms`. -/
theorem cliElfProgressPlaced_cliElfK (hG : H2KGhostArms) :
    ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
        CliElfProgressPlainPanPlaced mpl elf := by
  intro mpl mmpl hLs hMm elf hparse
  have helf : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hparse)
  subst helf
  let hG' : H2KGhostArmsType := fun mpl' mmpl' hLs' hMm' =>
    letI : LibsignalPlacement :=
      libsignalPlacementOf mpl' (hole2_hblk mpl' hLs') (hole2_hext_nodup mpl' hLs')
    let ha := hG mpl' mmpl' hLs' hMm'
    ⟨ha.hmain, ha.hoverD3, ha.huntyped, ha.hpathB, ha.hvalidMatch, ha.hinitSem⟩
  exact cliElfProgressPlainPanPlaced_of_strictG
    (cliElf_f3B2NeedLocksAssumptionsG hLs hMm)
    (h2kg_hmain_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hoverD3_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_huntyped_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hpathB_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hvalidMatch_cliElfG hG mpl mmpl hLs hMm)
    (h2kg_hinitSem_cliElfG hG mpl mmpl hLs hMm)
    (cliRunPlacedSig_eq_none_of_v2F3StuckDomain_cliElfK hG' mpl mmpl hLs hMm)

end Symbolic.Proofs.TopLevelHelpers.Composed.Cli.ProgressPlacedKElf
