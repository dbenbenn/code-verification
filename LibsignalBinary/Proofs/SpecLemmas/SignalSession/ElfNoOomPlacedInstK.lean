/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliElfProof -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliPlainPanPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliElf
public import VerifiedLibraries.Mallocng.Spec
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer
import LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst

/-!
# Ghost-Arm Pointwise `¬ CliReachesOOMPlainPanPlaced1` Instantiation for `cliElfImage`

**Checked by Lean.** Plain-memory counterpart of `ElfNoOomPlacedInst` parameterized by
`(hG : H2KGhostArms)` via `h2kg_hmain_cliElfG` and `h2kg_hoverD3_cliElfG`.
-/

public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK

open Arm64
open Arm64.Process (ElfImage)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs cliElfBytes
    cliElfImage cliElf_parse libsignalSessionLib realCrypto realPEParams realPqxdhPrims)
open LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
  (CliPqxdhElfCorrectPlainPanPlaced CliReachesOOMPlainPanPlaced1
   CliReachesSampleNttStuckPlainPanPlaced cliReachesOOMPlainPanPlaced_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3BinaryOomProofF3G
  (mainOkCliF3OverG_of_mainOkOverD3F3G)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlainPlacedComposer
  (cliPqxdhElfCorrectPlainPanPlaced_of_f3B2NeedLocksG'
   not_cliReachesOOMPlainPanPlaced_of_f3B2NeedLocksG_notStuck)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.B2MainFrameComposeBudget (libsignalPlacementOf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSampleNttStuckDiverge
  (H2KGhostArmsType cliRunPlacedSig_eq_none_of_cliPqxdhInputs_cliElfK
   not_cliReachesOOMPlaced_of_cliPqxdhInputs_cliElfK)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KGhostArms
  (H2KGhostArms h2kg_hmain_cliElfG h2kg_hoverD3_cliElfG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG
  (cliElf_f3B2NeedLocksAssumptionsG)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst
  (hole2_hblk hole2_hext_nodup)

/-- Under `H2KGhostArms`, proves both `CliPqxdhElfCorrectPlainPanPlaced` and
`¬ CliReachesOOMPlainPanPlaced1 mpl cliElfImage i` across `CliPqxdhInputs realPEParams` for any
`LinkedAt cliElfBytes` placements `(mpl, mmpl)`. -/
theorem cliElf_noOOMK (hG : H2KGhostArms) :
    ∀ (mpl mmpl : Obj.MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliPqxdhElfCorrectPlainPanPlaced mpl mmpl cliElfImage ∧
      ∀ i : Inputs, CliPqxdhInputs realPEParams i →
        ¬ CliReachesOOMPlainPanPlaced1 mpl cliElfImage i :=
  fun mpl mmpl hLs hMm =>
    let hG' : H2KGhostArmsType := fun mpl' mmpl' hLs' hMm' =>
      letI : LibsignalPlacement :=
        libsignalPlacementOf mpl' (hole2_hblk mpl' hLs') (hole2_hext_nodup mpl' hLs')
      let ha := hG mpl' mmpl' hLs' hMm'
      ⟨ha.hmain, ha.hoverD3, ha.huntyped, ha.hpathB, ha.hvalidMatch, ha.hinitSem⟩
    let H := cliElf_f3B2NeedLocksAssumptionsG hLs hMm
    let hmain := h2kg_hmain_cliElfG hG mpl mmpl hLs hMm
    let hover := mainOkCliF3OverG_of_mainOkOverD3F3G (h2kg_hoverD3_cliElfG hG mpl mmpl hLs hMm)
    ⟨cliPqxdhElfCorrectPlainPanPlaced_of_f3B2NeedLocksG' H hmain hover
        (cliRunPlacedSig_eq_none_of_cliPqxdhInputs_cliElfK hG' mpl mmpl hLs hMm),
      fun i hi => by
        let W : CliHooks := ⟨realCrypto, realPqxdhPrims⟩
        rw [← cliReachesOOMPlainPanPlaced_eq mpl mmpl cliElfImage W]
        by_cases hStuck : CliReachesSampleNttStuckPlainPanPlaced mpl mmpl cliElfImage W i
        · exact not_cliReachesOOMPlaced_of_cliPqxdhInputs_cliElfK
            hG' mpl mmpl hLs hMm W rfl rfl rfl rfl rfl rfl rfl rfl rfl i hi hStuck
        · exact not_cliReachesOOMPlainPanPlaced_of_f3B2NeedLocksG_notStuck
            H hmain hover W rfl rfl rfl rfl rfl rfl rfl rfl rfl hi hStuck⟩

/-- `ElfImage.parse` form of `cliElf_noOOMK`. -/
theorem cliElf_noOOM_of_parseK (hG : H2KGhostArms) :
    ∀ (mpl mmpl : Obj.MultiPlacement), libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
      CliPqxdhElfCorrectPlainPanPlaced mpl mmpl elf ∧
      ∀ (i : Inputs), CliPqxdhInputs realPEParams i →
        ¬ CliReachesOOMPlainPanPlaced1 mpl elf i := by
  intro mpl mmpl hLs hMm elf hParse
  have h : cliElfImage = elf := Except.ok.inj (cliElf_parse.symm.trans hParse)
  subst h
  exact cliElf_noOOMK hG mpl mmpl hLs hMm

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfNoOomPlacedInstK
