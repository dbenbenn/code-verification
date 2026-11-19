/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
import LibsignalBinary.Proofs.SignalSession.PqModelRun

/-!
# Patching Excused Aborts of a CLI Run with the Model's Outcomes

**Checked by Lean.** `patchRun exc run X W` answers every excused input on the PQXDH-mode domain
(`CliPqxdhExcusedAbort exc run W`) with the pure model run's outcome (`pqModelRun`,
`PqModelRun.lean`) and coincides with `run` elsewhere.
- `cliSpecPq_patchRun`: if `run` satisfies `CliSpecPqxdhOrExcusedAbort exc`, `patchRun` satisfies
  strict `CliSpecPqxdh`.
- `patchRun_eq_of_not`: outside `CliPqxdhExcusedAbort exc run W`, `patchRun` equals `run`.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.Oom.PatchRun

open CryptoVerification.E2E (CliPqxdhExcusedAbort PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.SignalSession (CliPqxdhInputs CliRun CliSpecPqxdh
  CliSpecPqxdhOrExcusedAbort Inputs Outcome OutcomeOrExcusedAbort cliSpecPq_pqModelRun pqModelRun)

open Classical in
/-- **The run with its excused aborts replaced by the model's outcomes.** -/
noncomputable def patchRun (exc : Inputs → Prop) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) : CliRun := fun i =>
  if CliPqxdhExcusedAbort exc run W i then pqModelRun X W i else run i

private theorem patchRun_apply_of_outcomeUpTo {exc : Inputs → Prop} {run : CliRun}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {i : Inputs} {e : Outcome}
    (hi : CliPqxdhInputs W i) (hu : OutcomeOrExcusedAbort exc run i (· = e))
    (hm : pqModelRun X W i = some e) :
    patchRun exc run X W i = some e := by
  unfold patchRun
  by_cases hc : CliPqxdhExcusedAbort exc run W i
  · simp only [hc, ↓reduceIte]
    exact hm
  · simp only [hc, ↓reduceIte]
    rcases hu with ⟨_, hrun, rfl⟩ | ⟨hab, hexc⟩
    · exact hrun
    · exact False.elim (hc ⟨hi, hexc, Or.inl hab⟩)

/-- **The patched run meets `CliSpecPqxdh`.** On each clause input, `run` either produces the
clause's outcome or has no outcome on an excused input (`run i = none ∧ exc i`), which `patchRun`
replaces with `pqModelRun`'s outcome (`cliSpecPq_pqModelRun`). -/
theorem cliSpecPq_patchRun {exc : Inputs → Prop} {run : CliRun}
    {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (h : CliSpecPqxdhOrExcusedAbort exc run X W) :
    CliSpecPqxdh (patchRun exc run X W) X W := by
  intro st hwf
  obtain ⟨hInit, hSend, hWhisper, hPrekey, hOther⟩ := h st hwf
  obtain ⟨mInit, mSend, mWhisper, mPrekey, mOther⟩ := cliSpecPq_pqModelRun X W st hwf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hsess
    exact patchRun_apply_of_outcomeUpTo
      ⟨st, hwf, Or.inl ⟨hsess, b, t, rfl⟩⟩
      (hInit b t hsess)
      (mInit b t hsess)
  · intro m r hm
    have hp := patchRun_apply_of_outcomeUpTo
      ⟨st, hwf, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩
      (hSend m r hm)
      (by rw [mSend m r hm]; split_ifs <;> rfl)
    rw [hp]; split_ifs <;> rfl
  · intro c rc hc
    have hp := patchRun_apply_of_outcomeUpTo
      ⟨st, hwf, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩
      (hWhisper c rc hc)
      (by rw [mWhisper c rc hc]; split_ifs <;> rfl)
    rw [hp]; split_ifs <;> rfl
  · intro m rc hm hmatch
    have hp := patchRun_apply_of_outcomeUpTo
      ⟨st, hwf, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩
      (hPrekey m rc hm hmatch)
      (by rw [mPrekey m rc hm hmatch]; split_ifs <;> rfl)
    rw [hp]; split_ifs <;> rfl
  · intro c rc hc hnw hnp
    have hp := patchRun_apply_of_outcomeUpTo
      ⟨st, hwf, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, hnw, hnp, rfl⟩)))⟩
      (hOther c rc hc hnw hnp)
      (by rw [mOther c rc hc hnw hnp]; split_ifs <;> rfl)
    rw [hp]; split_ifs <;> rfl

/-- **Off the excused aborts the patched run is `run`.** -/
theorem patchRun_eq_of_not {exc : Inputs → Prop} {run : CliRun}
    {X : UnreachedPqxdhPrimitives} {W : PEParams} {i : Inputs}
    (hi : ¬ CliPqxdhExcusedAbort exc run W i) :
    patchRun exc run X W i = run i := by
  simp only [patchRun, hi, ↓reduceIte]

end Computational.Proofs.LibsignalCli.Oom.PatchRun
