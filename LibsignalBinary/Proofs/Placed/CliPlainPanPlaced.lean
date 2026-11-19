/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge

/-!
# Plain-Memory Panic-Intercepted Placed Run Definitions

Intermediate run definitions starting from plain `elf.loadState (cliProcessInputs i)` (without
`cliTokenPatchPlaced`) under `cliProgPlacedSig` (`18` crate panic entry points intercepted as
`SIGABRT`). Bridges the entry-guarded `main` proofs (`CliStrictPlaced2G`, `D3BinaryOomProofF3G`,
`ProgressElfPlacedG`) to the plain `Program.pureMem` run (`cliRunElf`) via `PanicBridge`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Placed.CliPlainPanPlaced

open Arm64 Arm64.Process ProofLib
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession
  (CliHooks CliRun CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhOrExcusedAbort Inputs
   MlKemSampleNttStuckAt Outcome OutcomeMatchesProcess cliProcessInputs
   libsignalSessionLib outcomeObserved_unique processTerminatedOutcome_unique
   realCrypto realPEParams realPqxdhPrims)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliElfCodeMatchesPlaced cliProgPlacedSig cliProgPlacedSig_eq)

/-- Single-placement plain-memory `CliRunsTo` under `cliProgPlacedSig mpl` (no `.data` token patch). -/
@[expose] def CliRunsToPlainPanPlaced1 (mpl : Obj.MultiPlacement) (elf : ElfImage) (i : Inputs)
    (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo
      (CryptoVerification.SignalSession.Placed.cliProgPlacedSig mpl) s0
      (OutcomeMatchesProcess o)

open Classical in
/-- Single-placement plain-memory `CliRun` under `cliProgPlacedSig mpl`. -/
@[expose] noncomputable def cliRunPlainPanPlaced1 (mpl : Obj.MultiPlacement) (elf : ElfImage) :
    CliRun := fun i =>
  if h : ∃ o, CliRunsToPlainPanPlaced1 mpl elf i o then some (Classical.choose h) else none

/-- Single-placement plain-memory OOM reachability under `cliProgPlacedSig mpl`. -/
@[expose] def CliReachesOOMPlainPanPlaced1 (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (CryptoVerification.SignalSession.Placed.cliProgPlacedSig mpl) s0 s ∧
    s.status = .OutOfMemory

/-- Single-placement plain-memory `SampleNTT` non-terminating entry reachability. -/
@[expose] def CliReachesSampleNttStuckPlainPanPlaced1 (mpl : Obj.MultiPlacement) (elf : ElfImage)
    (i : Inputs) : Prop :=
  ∃ s0 u, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (CryptoVerification.SignalSession.Placed.cliProgPlacedSig mpl) s0 u ∧
    u.status = .Running ∧ MlKemSampleNttStuckAt mpl u

/-- Two-placement `(mpl, mmpl)` plain-memory `CliRunsTo`. -/
@[expose] def CliRunsToPlainPanPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgPlacedSig mpl mmpl W) s0
      (OutcomeMatchesProcess o)

open Classical in
/-- Two-placement `(mpl, mmpl)` plain-memory `CliRun`. -/
@[expose] noncomputable def cliRunPlainPanPlacedSig (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) : CliRun := fun i =>
  if h : ∃ o, CliRunsToPlainPanPlaced mpl mmpl elf W i o then some (Classical.choose h) else none

/-- Two-placement `(mpl, mmpl)` plain-memory OOM reachability. -/
@[expose] def CliReachesOOMPlainPanPlaced (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 s, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgPlacedSig mpl mmpl W) s0 s ∧
    s.status = .OutOfMemory

/-- Two-placement `(mpl, mmpl)` plain-memory `SampleNTT` non-terminating entry reachability. -/
@[expose] def CliReachesSampleNttStuckPlainPanPlaced (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) : Prop :=
  ∃ s0 u, elf.loadState (cliProcessInputs i) = .ok s0 ∧
    Steps (cliProgPlacedSig mpl mmpl W) s0 u ∧
    u.status = .Running ∧ MlKemSampleNttStuckAt mpl u

theorem cliRunsToPlainPanPlaced_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    CliRunsToPlainPanPlaced mpl mmpl elf W = CliRunsToPlainPanPlaced1 mpl elf := by
  funext i o
  unfold CliRunsToPlainPanPlaced CliRunsToPlainPanPlaced1 cliProgPlacedSig
  rw [cliProgPlacedSig_eq]

theorem cliRunPlainPanPlacedSig_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    cliRunPlainPanPlacedSig mpl mmpl elf W = cliRunPlainPanPlaced1 mpl elf := by
  funext i
  unfold cliRunPlainPanPlacedSig cliRunPlainPanPlaced1
  rw [cliRunsToPlainPanPlaced_eq]

theorem cliReachesOOMPlainPanPlaced_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    CliReachesOOMPlainPanPlaced mpl mmpl elf W = CliReachesOOMPlainPanPlaced1 mpl elf := by
  funext i
  unfold CliReachesOOMPlainPanPlaced CliReachesOOMPlainPanPlaced1 cliProgPlacedSig
  rw [cliProgPlacedSig_eq]

theorem cliReachesSampleNttStuckPlainPanPlaced_eq (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) :
    CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf W =
      CliReachesSampleNttStuckPlainPanPlaced1 mpl elf := by
  funext i
  unfold CliReachesSampleNttStuckPlainPanPlaced CliReachesSampleNttStuckPlainPanPlaced1
    cliProgPlacedSig
  rw [cliProgPlacedSig_eq]

private theorem processTerminatedOutcome_not_running {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

theorem cliRunsToPlainPanPlaced_unique {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i : Inputs} {o₁ o₂ : Outcome}
    (h₁ : CliRunsToPlainPanPlaced mpl mmpl elf W i o₁)
    (h₂ : CliRunsToPlainPanPlaced mpl mmpl elf W i o₂) : o₁ = o₂ := by
  rcases h₁ with ⟨s0, hLoad₁, ⟨out₁, ⟨sf, hSteps, hTerm₁⟩, hObs₁⟩ | ⟨_, _, _, hOom₁⟩, _⟩
  · rcases h₂ with ⟨s0', hLoad₂, _, hSafe₂⟩
    rw [hLoad₁] at hLoad₂
    cases hLoad₂
    rcases hSafe₂ sf hSteps with ⟨out₂, hTerm₂, hObs₂⟩ | ⟨_, hOom⟩ | ⟨hRun, _⟩
    · cases processTerminatedOutcome_unique hTerm₁ hTerm₂
      exact outcomeObserved_unique hObs₁ hObs₂
    · exact False.elim hOom
    · exact absurd hRun (processTerminatedOutcome_not_running hTerm₁)
  · exact False.elim hOom₁

theorem cliRunPlainPanPlacedSig_eq_some {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : CliRunsToPlainPanPlaced mpl mmpl elf W i o) :
    cliRunPlainPanPlacedSig mpl mmpl elf W i = some o := by
  unfold cliRunPlainPanPlacedSig
  split
  · next hex =>
    exact congrArg some (cliRunsToPlainPanPlaced_unique (Classical.choose_spec hex) h)
  · next hne => exact absurd ⟨o, h⟩ hne

theorem cliRunsToPlainPanPlaced_of_eq_some {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : cliRunPlainPanPlacedSig mpl mmpl elf W i = some o) :
    CliRunsToPlainPanPlaced mpl mmpl elf W i o := by
  unfold cliRunPlainPanPlacedSig at h
  split at h
  · next hex =>
    injection h with hEq
    rw [← hEq]
    exact Classical.choose_spec hex
  · cases h

theorem cliRunsToPlainPanPlaced1_unique {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {i : Inputs} {o₁ o₂ : Outcome}
    (h₁ : CliRunsToPlainPanPlaced1 mpl elf i o₁)
    (h₂ : CliRunsToPlainPanPlaced1 mpl elf i o₂) : o₁ = o₂ := by
  rw [← congrFun (congrFun (cliRunsToPlainPanPlaced_eq mpl mpl elf ⟨realCrypto, realPqxdhPrims⟩) i) o₁] at h₁
  rw [← congrFun (congrFun (cliRunsToPlainPanPlaced_eq mpl mpl elf ⟨realCrypto, realPqxdhPrims⟩) i) o₂] at h₂
  exact cliRunsToPlainPanPlaced_unique h₁ h₂

theorem cliRunPlainPanPlaced1_eq_some {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {i : Inputs} {o : Outcome}
    (h : CliRunsToPlainPanPlaced1 mpl elf i o) :
    cliRunPlainPanPlaced1 mpl elf i = some o := by
  rw [← cliRunPlainPanPlacedSig_eq mpl mpl elf ⟨realCrypto, realPqxdhPrims⟩]
  apply cliRunPlainPanPlacedSig_eq_some
  rwa [cliRunsToPlainPanPlaced_eq]

theorem cliRunsToPlainPanPlaced1_of_eq_some {mpl : Obj.MultiPlacement} {elf : ElfImage}
    {i : Inputs} {o : Outcome}
    (h : cliRunPlainPanPlaced1 mpl elf i = some o) :
    CliRunsToPlainPanPlaced1 mpl elf i o := by
  rw [← cliRunPlainPanPlacedSig_eq mpl mpl elf ⟨realCrypto, realPqxdhPrims⟩] at h
  have h2 := cliRunsToPlainPanPlaced_of_eq_some h
  rwa [cliRunsToPlainPanPlaced_eq] at h2

/-- Two-placement `(mpl, mmpl)` plain-memory `CliPqxdhElfCorrect`. -/
@[expose] def CliPqxdhElfCorrectPlainPanPlaced (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort
      (fun i => CliReachesOOMPlainPanPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i ∨
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i)
      (cliRunPlainPanPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams ∧
    CliSpecPqxdhNoMatchOrExcusedAbort
      (fun i => CliReachesOOMPlainPanPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i ∨
        CliReachesSampleNttStuckPlainPanPlaced mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩ i)
      (cliRunPlainPanPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams

/-- Single-placement plain-memory `CliPqxdhElfCorrect`. -/
@[expose] def CliPqxdhElfCorrectPlainPanPlaced1 (mpl : Obj.MultiPlacement)
    (elf : ElfImage) : Prop :=
  CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf ∧
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdhOrExcusedAbort
      (fun i => CliReachesOOMPlainPanPlaced1 mpl elf i ∨
        CliReachesSampleNttStuckPlainPanPlaced1 mpl elf i)
      (cliRunPlainPanPlaced1 mpl elf) X realPEParams ∧
    CliSpecPqxdhNoMatchOrExcusedAbort
      (fun i => CliReachesOOMPlainPanPlaced1 mpl elf i ∨
        CliReachesSampleNttStuckPlainPanPlaced1 mpl elf i)
      (cliRunPlainPanPlaced1 mpl elf) X realPEParams

theorem cliPqxdhElfCorrectPlainPanPlaced_to_1 {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hcm : CryptoVerification.SignalSession.Placed.CliElfCodeMatchesPlaced mpl elf)
    (h : CliPqxdhElfCorrectPlainPanPlaced mpl mmpl elf) :
    CliPqxdhElfCorrectPlainPanPlaced1 mpl elf := by
  refine ⟨hcm, fun X => ?_⟩
  have hX := h.2 X
  rw [cliReachesOOMPlainPanPlaced_eq, cliReachesSampleNttStuckPlainPanPlaced_eq,
      cliRunPlainPanPlacedSig_eq] at hX
  exact hX

@[expose] def CliPqxdhBinaryCorrectPlainPanPlacedAt (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectPlainPanPlaced mpl mmpl elf

@[expose] def CliPqxdhBinaryCorrectPlainPanPlaced (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectPlainPanPlacedAt mpl mmpl bytes

end LibsignalBinary.Proofs.Placed.CliPlainPanPlaced
