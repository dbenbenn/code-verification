/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliLabels -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo -- proof-setup: allow-public-import
public import ProofLib.Placed.LabelsCheck
public import ProofLib.Placed.LabelsCoverage

public section

set_option autoImplicit false

/-!
# SPQR CPU-Probe Data Label Anchoring (`CliProbeLabelsAnchored`)

**Checked by Lean.** Certifies `CliProbeLabelsAnchored` via `CoveredDataSpec` witnesses
(`tokenStorageSpec`, `tokenSpec`) for SPQR's `STORAGE.0` and `TOKEN` statics, and derives the
symbol-resolution (`libsignalSessionLib.resolve = mpl.ρ`) and relocation-provenance lemmas consumed
by `cliTokenPatchPlaced`.
-/

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProbeLabels

open Arm64
open CryptoVerification.LibsignalSpqrV1 (tokenStorageName tokenName)
open CryptoVerification.SignalSession (
  cliLinkObjs libsignalSessionLib CliProbeLabelsAnchored
)
open CryptoVerification.SignalSession.Placed (cliTokenPatchPlaced)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliLabelsLfo (
  cliLabelsLfo_dOTree cliLabelsLfo_bO cliLabelsLfo_dO cliLabelsLfo_spec
)

/-- `CoveredDataSpec` for `spqr::encoding::gf::check_accelerated::use_accelerated::STORAGE.0`
(1-byte `AtomicU8` at `libsignalSessionLib.data[818]`, sharing section `(oi := 6, si := 650)` with
`TOKEN`). -/
def tokenStorageSpec : Obj.CoveredDataSpec :=
  { di := 818
    sym := tokenStorageName
    origin := { oi := 6, si := 650, start := 0, len := 1 }
    rawName :=
      "_RNvNtNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated15use_accelerated7STORAGE.0"
    demangledName := tokenStorageName
    expectedReadOnly := some false
    expectedZeroTail := some 0
    soleInSection := false }

/-- `CoveredDataSpec` for `spqr::encoding::gf::check_accelerated::TOKEN` (16-byte
`LazyLock<InitToken>` at `libsignalSessionLib.data[819]`, sharing section `(oi := 6, si := 650)`
with `STORAGE.0`). -/
def tokenSpec : Obj.CoveredDataSpec :=
  { di := 819
    sym := tokenName
    origin := { oi := 6, si := 650, start := 8, len := 16 }
    rawName :=
      "_RNvNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated5TOKEN"
    demangledName := tokenName
    expectedReadOnly := some false
    expectedZeroTail := some 0
    soleInSection := false }

/-- Boolean checker anchoring both SPQR CPU-probe statics (`tokenStorageName`, `tokenName`) against
`cliLinkObjs` and `libsignalSessionLib` at slice-origin map `dO`. -/
def checkCliProbeLabelsB (dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin) : Bool :=
  Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenStorageSpec &&
    Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenSpec

/-- Projects `Obj.DataLabelAnchored` to the `.o` `STT_OBJECT` witness required by
`CliProbeLabelsAnchored` when `spec.sym = n` and `spec.demangledName = n`. -/
theorem dataLabelAnchored_probe_witness
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {dO : Fin lib.data.length → Obj.SliceOrigin} {spec : Obj.CoveredDataSpec} {n : String}
    (hd : Obj.DataLabelAnchored objs lib dO spec)
    (hsym : spec.sym = n)
    (hdem : spec.demangledName = n) :
    ∃ dj : Fin lib.data.length, lib.data[dj].sym = n ∧
      ∃ obj, objs[(dO dj).oi]? = some obj ∧ ∃ sy ∈ obj.symbols,
        Obj.CoversDataSlice (dO dj) sy ∧ sy.name = n := by
  refine ⟨⟨spec.di, hd.in_bounds⟩, by simpa using hd.sym_eq.trans hsym, ?_⟩
  obtain ⟨obj, _sec, sy, hobj, _hsec, hsy_mem, hcov, _hraw, hsy_name, _hder, _hro⟩ :=
    hd.obj_witness
  have horig : dO ⟨spec.di, hd.in_bounds⟩ = spec.origin := hd.origin_eq
  rw [horig]
  exact ⟨obj, hobj, sy, hsy_mem, hcov, hsy_name.trans hdem⟩

/-- Any slice-origin map `dO` satisfying `checkCliProbeLabelsB dO = true` satisfies
`CliProbeLabelsAnchored dO`. -/
theorem cliProbeLabelsAnchored_of_check
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (h : checkCliProbeLabelsB dO = true) :
    CliProbeLabelsAnchored dO := by
  unfold checkCliProbeLabelsB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hs, ht⟩ := h
  intro n hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · exact dataLabelAnchored_probe_witness (Obj.dataLabelAnchored_of_check hs) rfl rfl
  · exact dataLabelAnchored_probe_witness (Obj.dataLabelAnchored_of_check ht) rfl rfl

/-- When `spec.soleInSection = false`, `Obj.checkCoveredDataSpecB` depends on `dO` only at
`spec.di`. -/
theorem checkCoveredDataSpecB_congr_of_sole_false
    {objs : List Obj.ExtractedObj} {lib : Obj.MultiPlacedLib}
    {dO₁ dO₂ : Fin lib.data.length → Obj.SliceOrigin} {spec : Obj.CoveredDataSpec}
    (hsole : spec.soleInSection = false)
    (heq : ∀ hdi : spec.di < lib.data.length, dO₁ ⟨spec.di, hdi⟩ = dO₂ ⟨spec.di, hdi⟩) :
    Obj.checkCoveredDataSpecB objs lib dO₁ spec =
      Obj.checkCoveredDataSpecB objs lib dO₂ spec := by
  unfold Obj.checkCoveredDataSpecB
  split
  case isFalse => rfl
  case isTrue hdi =>
    simp only [hsole, Bool.false_eq_true, ↓reduceIte, heq hdi]

/-- Standalone slice-origin map matching `tokenStorageSpec.origin` at `818` and `tokenSpec.origin`
at `819`. -/
def probePreviewDO (dj : Fin libsignalSessionLib.data.length) : Obj.SliceOrigin :=
  if dj.val == 818 then tokenStorageSpec.origin else tokenSpec.origin

theorem checkCliProbeLabelsB_preview : checkCliProbeLabelsB probePreviewDO = true := by
  decide +kernel

/-- Transfers `checkCliProbeLabelsB` from `probePreviewDO` to any `dO` agreeing at indices `818`
and `819` without re-evaluating `cliLinkObjs`. -/
theorem checkCliProbeLabelsB_of_origins
    {dO : Fin libsignalSessionLib.data.length → Obj.SliceOrigin}
    (hs : ∀ hdi : 818 < libsignalSessionLib.data.length,
      dO ⟨818, hdi⟩ = tokenStorageSpec.origin)
    (ht : ∀ hdi : 819 < libsignalSessionLib.data.length,
      dO ⟨819, hdi⟩ = tokenSpec.origin) :
    checkCliProbeLabelsB dO = true := by
  have h1 : Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenStorageSpec =
      Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib probePreviewDO tokenStorageSpec :=
    checkCoveredDataSpecB_congr_of_sole_false rfl fun hdi => hs hdi
  have h2 : Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib dO tokenSpec =
      Obj.checkCoveredDataSpecB cliLinkObjs libsignalSessionLib probePreviewDO tokenSpec :=
    checkCoveredDataSpecB_congr_of_sole_false rfl fun hdi => ht hdi
  unfold checkCliProbeLabelsB
  rw [h1, h2]
  exact checkCliProbeLabelsB_preview

/-! ## Instantiation at `cliLabelsLfo_dO` -/

private theorem cliLabelsLfo_dOTree_818 :
    (cliLabelsLfo_dOTree.get? 818).getD { oi := 0, si := 0, start := 0, len := 0 } =
      tokenStorageSpec.origin :=
  rfl

private theorem cliLabelsLfo_dOTree_819 :
    (cliLabelsLfo_dOTree.get? 819).getD { oi := 0, si := 0, start := 0, len := 0 } =
      tokenSpec.origin :=
  rfl

theorem cliLabelsLfo_dO_818 (hdi : 818 < libsignalSessionLib.data.length) :
    cliLabelsLfo_dO ⟨818, hdi⟩ = tokenStorageSpec.origin :=
  cliLabelsLfo_dOTree_818

theorem cliLabelsLfo_dO_819 (hdi : 819 < libsignalSessionLib.data.length) :
    cliLabelsLfo_dO ⟨819, hdi⟩ = tokenSpec.origin :=
  cliLabelsLfo_dOTree_819

theorem checkCliProbeLabelsB_lfo : checkCliProbeLabelsB cliLabelsLfo_dO = true :=
  checkCliProbeLabelsB_of_origins cliLabelsLfo_dO_818 cliLabelsLfo_dO_819

/-- Concrete SPQR CPU-probe data label anchoring at `cliLabelsLfo_dO`. -/
theorem cliProbeLabelsAnchored : CliProbeLabelsAnchored cliLabelsLfo_dO :=
  cliProbeLabelsAnchored_of_check checkCliProbeLabelsB_lfo

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliProbeLabels
