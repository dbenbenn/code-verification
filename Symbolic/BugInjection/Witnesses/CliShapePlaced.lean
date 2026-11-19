/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.Specifications.Security.Binary
public import Symbolic.Proofs.SpecLemmas.SecurityBinaryPlaced
public import VerifiedLibraries.Mallocng.Spec

/-!
# Placed CLI Refinement Shape and Disproof Lemmas

Defines `cliCompShapePlaced`, equipping `cliCompShape` with `elfRelPlaced mpl mmpl elf` traces while
reusing `cliCompShape.SpecHalf`. Proves `not_signalSessionSecureFor_placed_of_witness` and
`not_signalSessionSecurePlaced_of_witness` to refute `SignalSessionSecurePlaced bytes` directly on
the security relation at linked placements.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement.Cli
  (CliTraces CliTurn CoinsFresh ExternContractsHoldCli HooksMatchPlaced InvertsGuarded elfRelPlaced
   initDirs)

/-- Variant of `cliCompShape` whose `contracts` require `HooksMatchPlaced` and whose `traces`
relation uses `elfRelPlaced mpl elf`. -/
def cliCompShapePlaced (mpl _mmpl : Arm64.Obj.MultiPlacement) : RefinementShape :=
  { cliCompShape with
    contracts := fun iw _ => ExternContractsHoldCli iw.1 ∧ HooksMatchPlaced iw.1 iw.2
    traces := fun elf iw r evs =>
      CliTraces (elfRelPlaced mpl elf iw.1 iw.2) iw.1 r (CliTurn.init (initDirs iw.1 r)) evs ∧
        InvertsGuarded iw.1 r evs }

/-- Refutes `SignalSessionSecureFor` at `elfRelPlaced mpl elf` for any ELF parsed from `bytes`
given `SpecHalf`, placed `ImplHalf`, and `CoinsFresh`. -/
theorem not_signalSessionSecureFor_placed_of_witness
    {fits : cliCompShape.Interp → cliCompShape.Rec → Prop} {τ : List CliEvent}
    {bytes : List (BitVec 8)} {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hs : cliCompShape.SpecHalf fits τ)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf fits elf τ)
    (hcf : ∀ iw r, fits iw r → CoinsFresh r τ) :
    ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      ¬ DY.Libsignal.Composed.Security.SignalSessionSecureFor
          HooksMatchPlaced (elfRelPlaced mpl elf) := by
  intro elf hparse hsec
  obtain ⟨⟨interp, W⟩, r, hfit, ⟨hc, hW⟩, htr, hg⟩ := hi elf hparse
  obtain ⟨hwf, hne⟩ := hs (interp, W) r hfit
  obtain ⟨S, hall⟩ := hsec interp hc W hW r hwf
  refine hne S trivial ?_
  rcases hall τ htr hg (hcf (interp, W) r hfit) with
    ⟨hex, _⟩ | ⟨evs₁, ev, evs₂, heq, ⟨g, ss, vis, hE, hN⟩, _⟩
  · exact Or.inl hex
  · exact Or.inr ⟨evs₁, ev, evs₂, g, ss, vis, heq, hE, hN⟩

/-- Refutes `SignalSessionSecurePlaced bytes` from a placed witness at a linked
`libsignalSessionLib` placement `mpl` (the `_hmg` argument is retained for existing disproof
callers). -/
theorem not_signalSessionSecurePlaced_of_witness
    {fits : cliCompShape.Interp → cliCompShape.Rec → Prop} {τ : List CliEvent}
    {bytes : List (BitVec 8)} {mpl mmpl : Arm64.Obj.MultiPlacement}
    (hls : CryptoVerification.SignalSession.libsignalSessionLib.LinkedAt bytes mpl)
    (_hmg : VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl)
    (hs : cliCompShape.SpecHalf fits τ)
    (hi : ∀ elf : Arm64.Process.ElfImage, Arm64.Process.ElfImage.parse bytes = .ok elf →
      (cliCompShapePlaced mpl mmpl).ImplHalf fits elf τ)
    (hcf : ∀ iw r, fits iw r → CoinsFresh r τ) :
    ¬ DY.Libsignal.Composed.Security.SignalSessionSecurePlaced bytes := by
  rintro h
  obtain ⟨elf, hparse, _hcode, _hprog, hsec⟩ := h mpl hls
  exact not_signalSessionSecureFor_placed_of_witness hs hi hcf elf hparse hsec

end Symbolic.BugInjection
