/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.SignalSession.PqDirNoMatch

public section

set_option autoImplicit false

/-!
# PQXDH-Mode OOM-Excuse Equivalences

**Checked by Lean.** Equivalence and elimination lemmas relating the OOM-excused PQXDH
specifications (`OutcomeOrExcusedAbort`, `CliSpecPqxdhOrExcusedAbort`,
`CliSpecPqxdhNoMatchOrExcusedAbort`) to unconditional `CliSpecPqxdh` and `CliSpecPqxdhNoMatch`
when `CliReachesOOMPlaced` is excluded.
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-- Reaching `.OutOfMemory` (`CliReachesOOMPlaced mpl elf i`) precludes `CliRunsToPlaced`
and forces `Placed.cliRunPlacedSig mpl elf i = none`. -/
theorem cliRunPlacedSig_eq_none_of_reachesOOM
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {i : Inputs}
    (hOOM : CliReachesOOMPlaced mpl elf i) :
    Placed.cliRunPlacedSig mpl elf i = none := by
  rcases hOOM with ⟨s0, s, hload, hsteps, hoom⟩
  dsimp only [Placed.cliRunPlacedSig]
  split_ifs with h
  · exfalso
    rcases h with ⟨o, s0', hload', _, hsafe⟩
    cases hload.symm.trans hload'
    rcases hsafe s hsteps with ⟨_, (⟨_, hex, _⟩ | ⟨_, hsig, _⟩), _⟩ | ⟨_, hf⟩ | ⟨hrun, _⟩
    · cases hoom.symm.trans hex
    · cases hoom.symm.trans hsig
    · exact hf
    · cases hoom.symm.trans hrun
  · rfl

private theorem outcomeOrExcusedAbort_eq_of_not_exc {exc : Inputs → Prop} {run : CliRun}
    {i : Inputs} {e : Outcome} (h : OutcomeOrExcusedAbort exc run i (· = e)) (hn : ¬ exc i) :
    run i = some e := by
  rcases h with ⟨_, hr, rfl⟩ | ⟨_, hexc⟩
  · exact hr
  · exact (hn hexc).elim

private theorem outcomeOrExcusedAbort_false_eq_iff {run : CliRun} {i : Inputs} {e : Outcome} :
    OutcomeOrExcusedAbort (fun _ => False) run i (· = e) ↔ run i = some e := by
  unfold OutcomeOrExcusedAbort
  constructor
  · rintro (⟨_, hr, rfl⟩ | ⟨_, hf⟩)
    · exact hr
    · exact hf.elim
  · exact fun hr => .inl ⟨e, hr, rfl⟩

/-- At `exc := fun _ => False`, `CliSpecPqxdhOrExcusedAbort` is equivalent to `CliSpecPqxdh`. -/
theorem cliSpecPqxdhOrExcusedAbort_false_iff
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdh run X W := by
  unfold CliSpecPqxdhOrExcusedAbort CliSpecPqxdh
  refine forall_congr' fun st => imp_congr_right fun _ => ?_
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact forall_congr' fun b => forall_congr' fun t => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff
  · exact forall_congr' fun m => forall_congr' fun r => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun c => forall_congr' fun rc => imp_congr_right fun _ =>
      outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun m => forall_congr' fun rc => imp_congr_right fun _ =>
      imp_congr_right fun _ =>
        outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)
  · exact forall_congr' fun c => forall_congr' fun rc => imp_congr_right fun _ =>
      imp_congr_right fun _ => imp_congr_right fun _ =>
        outcomeOrExcusedAbort_false_eq_iff.trans (by split_ifs <;> rfl)

/-- At `exc := fun _ => False`, `CliSpecPqxdhNoMatchOrExcusedAbort` is equivalent to
`CliSpecPqxdhNoMatch`. -/
theorem cliSpecPqxdhNoMatchOrExcusedAbort_false_iff
    (run : CliRun) (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdhNoMatchOrExcusedAbort (fun _ => False) run X W ↔ CliSpecPqxdhNoMatch run X W := by
  unfold CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhNoMatch OutcomeOrExcusedAbort
  refine forall_congr' fun st => imp_congr_right fun _ => ?_
  refine forall_congr' fun x => forall_congr' fun g => imp_congr_right fun _ => ?_
  refine forall_congr' fun m => forall_congr' fun rc => imp_congr_right fun _ => ?_
  refine imp_congr_right fun _ => ?_
  by_cases hg : (wirePrekey :: m.bytes).length > stdinCapBytes
  · simp only [hg, ↓reduceIte, and_false, or_false]
    exact ⟨fun ⟨_, hr, he⟩ => he ▸ hr, fun hr => ⟨_, hr, rfl⟩⟩
  · simp only [hg, ↓reduceIte, and_false, or_false]

/-- Excluding `CliReachesOOMPlaced` and `CliReachesSampleNttStuckPlaced` across `CliPqxdhInputs`
recovers `CliSpecPqxdh` from `CliPqxdhElfCorrectPlaced`. -/
theorem cliSpecPqxdh_of_elfCorrectPlaced_and_noOOM
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs realPEParams i → ¬ CliReachesOOMPlaced mpl elf i)
    (hNoStuck : ∀ i : Inputs, CliPqxdhInputs realPEParams i →
      ¬ CliReachesSampleNttStuckPlaced mpl elf i) :
    CliSpecPqxdh (Placed.cliRunPlacedSig mpl elf) X realPEParams := by
  have hNoExc : ∀ i : Inputs, CliPqxdhInputs realPEParams i →
      ¬ (CliReachesOOMPlaced mpl elf i ∨ CliReachesSampleNttStuckPlaced mpl elf i) :=
    fun i hi h => h.elim (hNoOOM i hi) (hNoStuck i hi)
  intro st hdom
  rcases (hL4.2 X).1 st hdom with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoExc _ ⟨st, hdom, .inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hlen
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hlen)
      (hNoExc _ ⟨st, hdom, .inr (.inl ⟨m, r, hlen, rfl⟩)⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro c rc hlen
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hlen)
      (hNoExc _ ⟨st, hdom, .inr (.inr (.inl ⟨c, rc, hlen, rfl⟩))⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro m rc hlen hmatch
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hlen hmatch)
      (hNoExc _ ⟨st, hdom, .inr (.inr (.inr (.inl ⟨m, rc, hlen, rfl⟩)))⟩)
    split_ifs at hr ⊢ <;> exact hr
  · intro c rc hlen hw hp
    have hr := outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hlen hw hp)
      (hNoExc _ ⟨st, hdom, .inr (.inr (.inr (.inr ⟨c, rc, hlen, hw, hp, rfl⟩)))⟩)
    split_ifs at hr ⊢ <;> exact hr

/-- Excluding `CliReachesOOMPlaced` and `CliReachesSampleNttStuckPlaced` across `CliPqxdhInputs`
recovers `CliSpecPqxdhNoMatch` from `CliPqxdhElfCorrectPlaced`. -/
theorem cliSpecPqxdhNoMatch_of_elfCorrectPlaced_and_noOOM
    {mpl : Obj.MultiPlacement} {elf : ElfImage} {X : UnreachedPqxdhPrimitives}
    (hL4 : CliPqxdhElfCorrectPlaced mpl elf)
    (hNoOOM : ∀ i : Inputs, CliPqxdhInputs realPEParams i → ¬ CliReachesOOMPlaced mpl elf i)
    (hNoStuck : ∀ i : Inputs, CliPqxdhInputs realPEParams i →
      ¬ CliReachesSampleNttStuckPlaced mpl elf i) :
    CliSpecPqxdhNoMatch (Placed.cliRunPlacedSig mpl elf) X realPEParams := by
  intro st hdom x g hsess m rc hlen hnomatch
  have h := (hL4.2 X).2 st hdom x g hsess m rc hlen hnomatch
  have hi : CliPqxdhInputs realPEParams (pqRecvInputs realPEParams st (wirePrekey :: m.bytes) rc) :=
    ⟨st, hdom, .inr (.inr (.inr (.inl ⟨m, rc, hlen, rfl⟩)))⟩
  rcases h with ⟨o, hr, ho⟩ | ⟨_, hoom | hstuck⟩
  · by_cases hg : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hg, ↓reduceIte] at ho ⊢
      exact ho ▸ hr
    · simp only [hg, ↓reduceIte] at ho ⊢
      exact ⟨o, hr, ho⟩
  · exact (hNoOOM _ hi hoom).elim
  · exact (hNoStuck _ hi hstuck).elim

end CryptoVerification.SignalSession
