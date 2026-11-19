/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedG -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlacedInst -- rooting-only, no decl used
public import LibsignalBinary.Specifications.SignalSession.CliElf
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
import Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlaced -- proof-setup: allow-public-import
public import Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfMemsetEntryGuard
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Asm
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2Branch2
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2ExecFrozenWire
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KAssembly
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KBridges
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KHooks
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KFdAll
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMainEntryFitsSat -- rooting-only, no decl used
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemcpy
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KMemset
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KNarrowR1
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KWitness
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2StepsLiftR2
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.AesDecErrRoGhost -- rooting-only, no decl used
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512 -- rooting-only, no decl used
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.MlKemSampleNttHelpers -- rooting-only, no decl used
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.T4Witness -- rooting-only, no decl used
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.X25519Row -- rooting-only, no decl used
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.RefinementKElf
import Symbolic.Proofs.TopLevelHelpers.Composed.Cli.AsmLevelSecurityKElf
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MlKemSampleNttDiverge -- rooting-only, no decl used

/-!
# Relocatable Whole-Protocol CLI Refinement for `cliElfBytes`

Instantiates `compRefinesCliBinaryPlaced_of_v2OomF3Bytes` and `comp_refines_cli_model_b2` at
`cliElfBytes`, and discharges the ghost-arm obligation via `h2k_ghostArms_closed` to conclude
`CompRefinesCliBinaryPlaced cliElfBytes`.
-/

public section

set_option autoImplicit false

namespace Symbolic.Proofs.TopLevelHelpers.Composed.Cli

open Arm64 (Memory)
open Arm64.Obj (MultiPlacement)
open Arm64.Process (ElfImage)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)
open CryptoVerification.SignalSession (cliElfBytes libsignalSessionLib)
open DY.Libsignal.Composed.Refinement.Cli (CompRefinesCliBinaryPlaced comp_refines_cli_model_b2)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3MatchingPathBF3 (MainOkPathBD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3NonCanonF3
  (MainOkOverD3F3 MainOkValidMatchD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (MainOkUntypedD3F3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.CliStrictPlaced2
  (CliElfF3B2NeedLocksAssumptions MainOkCliF3PqB2NeedLocksPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Parity.F3.BundleInitElfF3 (MainInitSemF3)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomPlaced
  (CliPqBinaryV2OomF3BytesPlaced
   cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2KM1
  (h2k_ghostArms_closed)
open Symbolic.Proofs.Refinement.Composed.Cli.ElfToModelV2BridgeF3Placed
  (compRefinesCliBinaryPlaced_of_v2OomF3Bytes)

/-- Relocatable `cliElfBytes` whole-protocol CLI refinement from
`hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes`. -/
theorem comp_refines_cli_placed_of_v2
    (hv2 : CliPqBinaryV2OomF3BytesPlaced cliElfBytes)
    (hprog : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf' : ElfImage, ElfImage.parse cliElfBytes = .ok elf' →
        DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl elf') :
    CompRefinesCliBinaryPlaced cliElfBytes :=
  compRefinesCliBinaryPlaced_of_v2OomF3Bytes
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_mallocng_linkedIn
    (fun _ hLs _ hparse =>
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_trustedCodeMatchesPlaced_of_parse
        hLs hparse)
    hv2 hprog comp_refines_cli_model_b2

/-- Composes `cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main` with `comp_refines_cli_placed_of_v2`
to derive `CompRefinesCliBinaryPlaced cliElfBytes` from the `main`-level witnesses. -/
theorem comp_refines_cli_placed_of_main
    {elf : ElfImage} {exitStk : Nat} {stk : Nat}
    {CodeOk : MultiPlacement → MultiPlacement → Memory → Prop}
    (hparse : ElfImage.parse cliElfBytes = .ok elf)
    (hAssump : ∀ (mpl mmpl : MultiPlacement),
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      CliElfF3B2NeedLocksAssumptions mpl mmpl exitStk
        (mallocngAddrsOfPlacement mmpl).libc stk (CodeOk mpl mmpl) elf)
    (hmain : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkCliF3PqB2NeedLocksPlacedAt mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hoverD3 : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkOverD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (huntyped : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkUntypedD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hpathB : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkPathBD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hvalidMatch : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainOkValidMatchD3F3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hinitSem : ∀ mpl mmpl, libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      MainInitSemF3 mpl mmpl (CodeOk mpl mmpl)
        (mallocngAddrsOfPlacement mmpl).libc elf.brkStart stk)
    (hprog : ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf' : ElfImage, ElfImage.parse cliElfBytes = .ok elf' →
        DY.Libsignal.Composed.Refinement.Cli.CliElfProgressPlaced mpl elf') :
    CompRefinesCliBinaryPlaced cliElfBytes :=
  comp_refines_cli_placed_of_v2
    (cliPqBinaryV2OomF3BytesPlaced_cliElf_of_main
      hparse hAssump hmain hoverD3 huntyped hpathB hvalidMatch hinitSem)
    hprog

/-- Plain-memory placed progress for `cliElfBytes`. -/
theorem cliElfProgressPlaced_cliElf :
    ∀ mpl mmpl : MultiPlacement,
      libsignalSessionLib.LinkedAt cliElfBytes mpl →
      VerifiedLibraries.mallocngLib.LinkedAt cliElfBytes mmpl →
      ∀ elf : ElfImage, ElfImage.parse cliElfBytes = .ok elf →
        Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced.CliElfProgressPlainPanPlaced mpl elf :=
  RefinementKElf.cliElfProgressPlaced_cliElfK h2k_ghostArms_closed

/-- Relocatable plain-memory whole-protocol CLI refinement for `cliElfBytes`. -/
theorem comp_refines_cli_placed_proof :
    Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced.CompRefinesCliBinaryPlainPanPlaced
      cliElfBytes :=
  RefinementKElf.comp_refines_cli_placed_proofK h2k_ghostArms_closed

/-- ELF-direct whole-protocol CLI refinement and progress for `cliElfBytes`. -/
theorem comp_refines_cli_proof :
    DY.Libsignal.Composed.Refinement.Cli.CompRefinesCliBinary cliElfBytes := by
  have hAt := comp_refines_cli_placed_proof
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElfMultiPlacement
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElf_linkedAt
  rcases hAt with ⟨elf, hparse, _, hprog, href⟩
  have helf : elf = CryptoVerification.SignalSession.cliElfImage := by
    rw [CryptoVerification.SignalSession.cliElf_parse] at hparse
    exact Except.ok.inj hparse.symm
  subst helf
  have hrel :
      DY.Libsignal.Composed.Refinement.Cli.elfRel
        CryptoVerification.SignalSession.cliElfImage
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliElfAddrsVal =
      Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced.elfRelPlainPanPlaced
        LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElfMultiPlacement
        CryptoVerification.SignalSession.cliElfImage := by
    funext interp W i o
    simp only [DY.Libsignal.Composed.Refinement.Cli.elfRel,
      Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced.elfRelPlainPanPlaced,
      LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliRunElf_eq]
  refine ⟨CryptoVerification.SignalSession.cliElfImage,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliElfAddrsVal,
    CryptoVerification.SignalSession.cliElf_parse,
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliElf_resolveAddrs,
    ?_, ?_⟩
  · intro interp hInt W hW r hr t ht c i hc hi hAgree
    have ht' : DY.Libsignal.Composed.Refinement.Cli.CliReachable
        (Symbolic.Proofs.SpecLemmas.ElfBindingPlainPanPlaced.elfRelPlainPanPlaced
          LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced.cliElfMultiPlacement
          CryptoVerification.SignalSession.cliElfImage interp W)
        interp r
        (DY.Libsignal.Composed.Refinement.Cli.CliTurn.init
          (DY.Libsignal.Composed.Refinement.Cli.initDirs interp r)) t := by
      simpa [hrel] using ht
    rcases hprog interp hInt W hW r hr t ht' c i hc hi hAgree with hne | hstuck
    · exact Or.inl (by
        rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliRunElf_eq]
        exact hne)
    · exact Or.inr
        ((LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfDirectBridge.cliReachesSampleNttStuckElf_iff i).mpr
          hstuck)
  · simpa [hrel] using href

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refines_cli_placed_of_v2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_refines_cli_placed_of_v2

/--
info: 'Symbolic.Proofs.TopLevelHelpers.Composed.Cli.comp_refines_cli_placed_of_main' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms comp_refines_cli_placed_of_main


end Symbolic.Proofs.TopLevelHelpers.Composed.Cli
