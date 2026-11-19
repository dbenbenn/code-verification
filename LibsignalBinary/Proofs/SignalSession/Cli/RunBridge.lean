/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.SmDirProofDefs

public section

set_option autoImplicit false

/-!
# Process-to-`Outcome` Determinism Bridge

**Checked by Lean.** Proves uniqueness of `ProcessTerminatedOutcome` and observed CLI `Outcome`.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-- A single machine state `sf` admits at most one `ProcessTerminatedOutcome`. -/
theorem processTerminatedOutcome_unique {sf : State} {out₁ out₂ : ProcessOutcome}
    (h₁ : ProcessTerminatedOutcome sf out₁) (h₂ : ProcessTerminatedOutcome sf out₂) :
    out₁ = out₂ := by
  rcases h₁ with ⟨code₁, hst₁, rfl⟩ | ⟨sig₁, hst₁, rfl⟩ <;>
    rcases h₂ with ⟨code₂, hst₂, rfl⟩ | ⟨sig₂, hst₂, rfl⟩ <;>
    rw [hst₁] at hst₂ <;> cases hst₂ <;> rfl

/-- A single `ProcessOutcome` observes at most one CLI `Outcome`. -/
theorem outcomeObserved_unique {o₁ o₂ : Outcome} {out : ProcessOutcome}
    (h₁ : OutcomeMatchesProcess o₁ out) (h₂ : OutcomeMatchesProcess o₂ out) : o₁ = o₂ := by
  cases o₁ <;> cases o₂
  · rcases h₁ with ⟨_, rfl, rfl, rfl⟩
    rcases h₂ with ⟨_, rfl, rfl, rfl⟩
    rfl
  · rcases h₁ with ⟨hs₁, _⟩
    rcases h₂ with ⟨hs₂, _⟩
    rw [hs₁] at hs₂
    cases hs₂
  · rcases h₁ with ⟨hs₁, _⟩
    rcases h₂ with ⟨hs₂, _⟩
    rw [hs₁] at hs₂
    cases hs₂
  · rfl

end CryptoVerification.SignalSession
