/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced -- proof-setup: allow-public-import

/-!
# Two-Placement Shape-H ↔ Strict Recovery Corollaries

Two-placement `(mpl, mmpl)` strict ELF and binary correctness predicates
(`CliPqxdhElfCorrectStrictPlaced2`, `CliPqxdhBinaryCorrectStrictPlacedAt2`,
`CliPqxdhBinaryCorrectStrictPlaced2`) alongside weakening and `¬ CliReachesOOMPlaced` recovery
corollaries for the placed Shape-H ("total except `.OutOfMemory`", `DEV-CLI15`) predicates of
`CliBinaryPq`.
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2

open Arm64 Arm64.Obj Arm64.Process
open CryptoGames.HMAC (ShaState)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.SignalSession
  (CliHooks
   CliPqxdhInputs CliRun CliSpecPqxdh
   CliSpecPqxdhNoMatch CliSpecPqxdhNoMatchOrExcusedAbort CliSpecPqxdhOrExcusedAbort Inputs Outcome
   OutcomeOrExcusedAbort libsignalSessionLib realCrypto realPqxdhPrims realPEParams)
open LibsignalBinary.Proofs.Placed.CliBinaryPqPlaced
  (CliElfCodeMatchesPlaced CliPqxdhBinaryCorrectPlaced CliPqxdhBinaryCorrectPlacedAt
   CliPqxdhElfCorrectPlaced CliReachesOOMPlaced CliReachesSampleNttStuckPlaced cliRunPlacedSig)
open VerifiedLibraries (mallocngLib)

/-! ## Strict Two-Placement ELF and Binary Correctness Predicates -/

/-- Untrusted `F`-parameterized Shape-H ELF correctness abbreviation (`rfl`-equal to
`CliPqxdhElfCorrectPlaced` at `F = sha256Compress`). -/
abbrev CliPqxdhElfCorrectPlacedWith
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.F = F →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdhOrExcusedAbort
        (fun i => CliReachesOOMPlaced mpl mmpl elf W i ∨
          CliReachesSampleNttStuckPlaced mpl mmpl elf W i)
        (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatchOrExcusedAbort
        (fun i => CliReachesOOMPlaced mpl mmpl elf W i ∨
          CliReachesSampleNttStuckPlaced mpl mmpl elf W i)
        (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Strict relocatable `CliPqxdhElfCorrect` at a fixed SHA-256 compression function `F` and real
AES-256 under `libsignalSessionLib` placement `mpl` and `VerifiedLibraries.mallocngLib` placement
`mmpl`. -/
@[expose] def CliPqxdhElfCorrectStrictPlaced2With
    (F : ShaState → List (BitVec 8) → ShaState)
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.F = F →
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Closed-primitive strict relocatable `CliPqxdhElfCorrect` matching
`CliPqxdhElfCorrectPlaced`. -/
def CliPqxdhElfCorrectStrictPlaced2Exists (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams ∧
    CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf ⟨realCrypto, realPqxdhPrims⟩) X realPEParams

/-- Existentially-bound-`F` strict relocatable `CliPqxdhBinaryCorrect` at fixed `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlacedAt2Exists (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectStrictPlaced2Exists mpl mmpl elf

/-- Existentially-bound-`F` strict relocatable `CliPqxdhBinaryCorrect` across all `LinkedAt`
placements `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlaced2Exists (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectStrictPlacedAt2Exists mpl mmpl bytes

/-- Strict relocatable `CliPqxdhElfCorrect` under `libsignalSessionLib` placement `mpl` and
`VerifiedLibraries.mallocngLib` placement `mmpl` with no `OrExcusedAbort` relaxation: `elf` matches
`libsignalSessionLib` and `mallocngLib` under `(mpl, mmpl)` (`CliElfCodeMatchesPlaced`) and
for every `W` and `X`, `cliRunPlacedSig mpl mmpl elf W` satisfies `CliSpecPqxdh` and
`CliSpecPqxdhNoMatch` directly. -/
@[expose] def CliPqxdhElfCorrectStrictPlaced2 (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks, ∀ X : UnreachedPqxdhPrimitives,
    CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
    CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Strict relocatable `CliPqxdhBinaryCorrect` at fixed placements `(mpl, mmpl)`. -/
@[expose] def CliPqxdhBinaryCorrectStrictPlacedAt2 (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf

/-- Strict relocatable `CliPqxdhBinaryCorrect` universally quantified over every pair of placements
`mpl` linked at `bytes` (`libsignalSessionLib.LinkedAt bytes mpl`) and `mmpl` linked at `bytes`
(`VerifiedLibraries.mallocngLib.LinkedAt bytes mmpl`). -/
@[expose] def CliPqxdhBinaryCorrectStrictPlaced2 (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectStrictPlacedAt2 mpl mmpl bytes

/-- Real-AES-guarded strict relocatable `CliPqxdhElfCorrect` matching `CliPqxdhElfCorrectPlaced`
(`W.C.E = CryptoGames.AES256.aes256Enc` and `W.C.D = CryptoGames.AES256.aes256Dec`). -/
@[expose] def CliPqxdhElfCorrectStrictPlaced2Aes (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) : Prop :=
  CliElfCodeMatchesPlaced mpl mmpl elf ∧
  ∀ W : CliHooks,
    W.C.E = CryptoGames.AES256.aes256Enc →
    W.C.D = CryptoGames.AES256.aes256Dec →
    W.C.X = CryptoGames.RFC7748.x25519Ref →
    W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
    W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
    W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
    W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
    W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
    ∀ X : UnreachedPqxdhPrimitives,
      CliSpecPqxdh (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩ ∧
      CliSpecPqxdhNoMatch (cliRunPlacedSig mpl mmpl elf W) X ⟨W.C, W.Q⟩

/-- Real-AES-guarded strict relocatable `CliPqxdhBinaryCorrect` at fixed `(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlacedAt2Aes (mpl mmpl : Obj.MultiPlacement)
    (bytes : List (BitVec 8)) : Prop :=
  ∃ elf, ElfImage.parse bytes = .ok elf ∧ CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf

/-- Real-AES-guarded strict relocatable `CliPqxdhBinaryCorrect` across all `LinkedAt` placements
`(mpl, mmpl)`. -/
def CliPqxdhBinaryCorrectStrictPlaced2Aes (bytes : List (BitVec 8)) : Prop :=
  ∀ mpl mmpl : Obj.MultiPlacement,
    libsignalSessionLib.LinkedAt bytes mpl →
    mallocngLib.LinkedAt bytes mmpl →
    CliPqxdhBinaryCorrectStrictPlacedAt2Aes mpl mmpl bytes

/-! ## `OutcomeOrExcusedAbort` Elimination and Introduction Helpers -/

/-- Eliminate the excused-abort disjunct of `OutcomeOrExcusedAbort` when `¬ exc i`. -/
theorem outcomeOrExcusedAbort_of_not_exc
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {P : Outcome → Prop}
    (h : OutcomeOrExcusedAbort exc run i P) (hne : ¬ exc i) :
    ∃ o, run i = some o ∧ P o := by
  rcases h with ho | ⟨_, hexc⟩
  · exact ho
  · exact (hne hexc).elim

theorem outcomeOrExcusedAbort_eq_of_not_exc
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {expected : Outcome}
    (h : OutcomeOrExcusedAbort exc run i (· = expected)) (hne : ¬ exc i) :
    run i = some expected := by
  obtain ⟨o, hrun, rfl⟩ := outcomeOrExcusedAbort_of_not_exc h hne
  exact hrun

/-- Lift a concrete outcome witness `run i = some expected` into `OutcomeOrExcusedAbort`. -/
theorem outcomeOrExcusedAbort_of_eq
    {exc : Inputs → Prop} {run : CliRun} {i : Inputs} {expected : Outcome}
    (h : run i = some expected) :
    OutcomeOrExcusedAbort exc run i (· = expected) :=
  Or.inl ⟨expected, h, rfl⟩

private theorem some_ite {α : Type} {c : Prop} [Decidable c] {a b : α} :
    some (if c then a else b) = (if c then some a else some b) := by
  by_cases hc : c <;> simp only [hc, ↓reduceIte]

private theorem some_ite2 {α : Type} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    {a b d : α} :
    some (if c₁ then a else if c₂ then b else d) =
      (if c₁ then some a else if c₂ then some b else some d) := by
  by_cases hc₁ : c₁
  · simp only [hc₁, ↓reduceIte]
  · simp only [hc₁, ↓reduceIte]
    exact some_ite

private theorem exists_some_ite_eq {α : Type} {x : Option α} {c : Prop} [Decidable c]
    {a : α} {P : α → Prop}
    (h : ∃ o, x = some o ∧ (if c then o = a else P o)) :
    if c then x = some a else ∃ o, x = some o ∧ P o := by
  obtain ⟨o, hx, hP⟩ := h
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at hP ⊢
    exact hx.trans (congrArg some hP)
  · simp only [hc, ↓reduceIte] at hP ⊢
    exact ⟨o, hx, hP⟩

private theorem exists_some_ite_eq_inv {α : Type} {x : Option α} {c : Prop} [Decidable c]
    {a : α} {P : α → Prop}
    (h : if c then x = some a else ∃ o, x = some o ∧ P o) :
    ∃ o, x = some o ∧ (if c then o = a else P o) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h
    exact ⟨a, h, by simp only [hc, ↓reduceIte]⟩
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨o, hx, hP⟩ := h
    exact ⟨o, hx, by simp only [hc, ↓reduceIte]; exact hP⟩

/-! ## Strict ⇒ Shape-H (`OrExcusedAbort`) Weakening -/

/-- Strict `CliSpecPqxdh` implies `CliSpecPqxdhOrExcusedAbort` for any `exc`. -/
theorem cliSpecPqxdhOrExcusedAbort_of_strict
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (h : CliSpecPqxdh run X W) :
    CliSpecPqxdhOrExcusedAbort exc run X W := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := h st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun b t hnone => outcomeOrExcusedAbort_of_eq (h1 b t hnone)
  · exact fun m r hm => outcomeOrExcusedAbort_of_eq ((h2 m r hm).trans some_ite2.symm)
  · exact fun c rc hc => outcomeOrExcusedAbort_of_eq ((h3 c rc hc).trans some_ite.symm)
  · exact fun m rc hm hmatch => outcomeOrExcusedAbort_of_eq ((h4 m rc hm hmatch).trans some_ite.symm)
  · exact fun c rc hc h2ne h3ne =>
      outcomeOrExcusedAbort_of_eq ((h5 c rc hc h2ne h3ne).trans some_ite.symm)

theorem cliSpecPqxdhNoMatchOrExcusedAbort_of_strict
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (h : CliSpecPqxdhNoMatch run X W) :
    CliSpecPqxdhNoMatchOrExcusedAbort exc run X W :=
  fun st hst x g hsess m rc hm hnm =>
    Or.inl (exists_some_ite_eq_inv (h st hst x g hsess m rc hm hnm))

theorem cliPqxdhElfCorrectPlacedWith_of_strict2With
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf) :
    CliPqxdhElfCorrectPlacedWith F mpl mmpl elf :=
  ⟨h.1, fun W hF hE hD hX hPub hF512 hEnc hDec hK X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict (h.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict (h.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).2⟩⟩

theorem cliPqxdhElfCorrectPlaced_of_placedWith
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectPlacedWith sha256Compress mpl mmpl elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  ⟨h.1, fun X => h.2 ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl rfl X⟩

theorem cliPqxdhElfCorrectPlaced_of_strict2Aes
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlaced2Aes mpl mmpl elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  ⟨h.1, fun X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict
      (h.2 ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict
      (h.2 ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl X).2⟩⟩

theorem cliPqxdhBinaryCorrectPlacedAt_of_strict2Aes
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlacedAt2Aes mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes := by
  obtain ⟨elf, hparse, hStrict⟩ := h
  exact ⟨elf, hparse, cliPqxdhElfCorrectPlaced_of_strict2Aes hStrict⟩

theorem cliPqxdhBinaryCorrectPlaced_of_strict2Aes
    {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlaced2Aes bytes) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  fun mpl mmpl hLs hMal => cliPqxdhBinaryCorrectPlacedAt_of_strict2Aes (h mpl mmpl hLs hMal)

theorem cliPqxdhElfCorrectPlaced_of_strict2
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (h : CliPqxdhElfCorrectStrictPlaced2 mpl mmpl elf) :
    CliPqxdhElfCorrectPlaced mpl mmpl elf :=
  ⟨h.1, fun X =>
    ⟨cliSpecPqxdhOrExcusedAbort_of_strict (h.2 ⟨realCrypto, realPqxdhPrims⟩ X).1,
     cliSpecPqxdhNoMatchOrExcusedAbort_of_strict (h.2 ⟨realCrypto, realPqxdhPrims⟩ X).2⟩⟩

theorem cliPqxdhBinaryCorrectPlacedAt_of_strict2
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlacedAt2 mpl mmpl bytes) :
    CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes := by
  obtain ⟨elf, hparse, hStrict⟩ := h
  exact ⟨elf, hparse, cliPqxdhElfCorrectPlaced_of_strict2 hStrict⟩

theorem cliPqxdhBinaryCorrectPlaced_of_strict2
    {bytes : List (BitVec 8)}
    (h : CliPqxdhBinaryCorrectStrictPlaced2 bytes) :
    CliPqxdhBinaryCorrectPlaced bytes :=
  fun mpl mmpl hLs hMal => cliPqxdhBinaryCorrectPlacedAt_of_strict2 (h mpl mmpl hLs hMal)

/-! ## Shape-H + `¬ CliReachesOOMPlaced` ⇒ Strict Recovery -/

private theorem cliSpecPqxdh_of_orExcusedAbort_exc
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhOrExcusedAbort exc run X W)
    (hNoExc : ∀ i, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdh run X W := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOr st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoExc _ ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hm
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hm)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩)).trans some_ite2
  · intro c rc hc
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hc)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩)).trans some_ite
  · intro m rc hm hmatch
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hm hmatch)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)).trans some_ite
  · intro c rc hc h2ne h3ne
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hc h2ne h3ne)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩)).trans some_ite

private theorem cliSpecPqxdhNoMatch_of_orExcusedAbort_exc
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhNoMatchOrExcusedAbort exc run X W)
    (hNoExc : ∀ i, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdhNoMatch run X W := by
  intro st hst x g hsess m rc hm hnm
  refine exists_some_ite_eq ?_
  exact outcomeOrExcusedAbort_of_not_exc (hOr st hst x g hsess m rc hm hnm)
    (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)

/-- Recover strict `CliSpecPqxdh` from `CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)`
and pointwise `¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
theorem cliSpecPqxdh_of_orExcusedAbort_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {run : CliRun} {X : UnreachedPqxdhPrimitives}
    (hOr : CliSpecPqxdhOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W) run X ⟨W.C, W.Q⟩)
    (hNoOOM : ∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdh run X ⟨W.C, W.Q⟩ :=
  cliSpecPqxdh_of_orExcusedAbort_exc hOr hNoOOM

/-- Recover strict `CliSpecPqxdhNoMatch` from
`CliSpecPqxdhNoMatchOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W)` and pointwise
`¬ CliReachesOOMPlaced mpl mmpl elf W i` across `CliPqxdhInputs ⟨W.C, W.Q⟩`. -/
theorem cliSpecPqxdhNoMatch_of_orExcusedAbort_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage} {W : CliHooks}
    {run : CliRun} {X : UnreachedPqxdhPrimitives}
    (hOr : CliSpecPqxdhNoMatchOrExcusedAbort (CliReachesOOMPlaced mpl mmpl elf W) run X ⟨W.C, W.Q⟩)
    (hNoOOM : ∀ i, CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i) :
    CliSpecPqxdhNoMatch run X ⟨W.C, W.Q⟩ :=
  cliSpecPqxdhNoMatch_of_orExcusedAbort_exc hOr hNoOOM

/-- Shape-H `CliPqxdhElfCorrectPlacedWith F mpl mmpl elf` together with pointwise
`¬ CliReachesOOMPlaced mpl mmpl elf W i` and `¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i`
across `CliPqxdhInputs ⟨W.C, W.Q⟩` implies `CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf`. -/
theorem cliPqxdhElfCorrectStrictPlaced2With_of_noOOM
    {F : ShaState → List (BitVec 8) → ShaState}
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hElf : CliPqxdhElfCorrectPlacedWith F mpl mmpl elf)
    (hNoOOM : ∀ (W : CliHooks),
      W.C.F = F →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (hNoStuck : ∀ (W : CliHooks),
      W.C.F = F →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2With F mpl mmpl elf :=
  ⟨hElf.1, fun W hF hE hD hX hPub hF512 hEnc hDec hK X =>
    ⟨cliSpecPqxdh_of_orExcusedAbort_exc
       (hElf.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).1
       (fun i hi h => h.elim
         (hNoOOM W hF hE hD hX hPub hF512 hEnc hDec hK i hi)
         (hNoStuck W hF hE hD hX hPub hF512 hEnc hDec hK i hi)),
     cliSpecPqxdhNoMatch_of_orExcusedAbort_exc
       (hElf.2 W hF hE hD hX hPub hF512 hEnc hDec hK X).2
       (fun i hi h => h.elim
         (hNoOOM W hF hE hD hX hPub hF512 hEnc hDec hK i hi)
         (hNoStuck W hF hE hD hX hPub hF512 hEnc hDec hK i hi))⟩⟩

theorem cliSpecPqxdh_of_orExcusedAbort_gen
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhOrExcusedAbort exc run X W)
    (hNoExc : ∀ i, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdh run X W := by
  intro st hst
  obtain ⟨h1, h2, h3, h4, h5⟩ := hOr st hst
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b t hnone
    exact outcomeOrExcusedAbort_eq_of_not_exc (h1 b t hnone)
      (hNoExc _ ⟨st, hst, Or.inl ⟨hnone, b, t, rfl⟩⟩)
  · intro m r hm
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h2 m r hm)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inl ⟨m, r, hm, rfl⟩)⟩)).trans some_ite2
  · intro c rc hc
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h3 c rc hc)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inl ⟨c, rc, hc, rfl⟩))⟩)).trans some_ite
  · intro m rc hm hmatch
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h4 m rc hm hmatch)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)).trans some_ite
  · intro c rc hc h2ne h3ne
    exact (outcomeOrExcusedAbort_eq_of_not_exc (h5 c rc hc h2ne h3ne)
      (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr ⟨c, rc, hc, h2ne, h3ne, rfl⟩)))⟩)).trans some_ite

theorem cliSpecPqxdhNoMatch_of_orExcusedAbort_gen
    {exc : Inputs → Prop} {run : CliRun} {X : UnreachedPqxdhPrimitives} {W : PEParams}
    (hOr : CliSpecPqxdhNoMatchOrExcusedAbort exc run X W)
    (hNoExc : ∀ i, CliPqxdhInputs W i → ¬ exc i) :
    CliSpecPqxdhNoMatch run X W := by
  intro st hst x g hsess m rc hm hnm
  refine exists_some_ite_eq ?_
  exact outcomeOrExcusedAbort_of_not_exc (hOr st hst x g hsess m rc hm hnm)
    (hNoExc _ ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rc, hm, rfl⟩)))⟩)

/-- Shape-H `CliPqxdhElfCorrectPlaced mpl mmpl elf` together with pointwise
`¬ CliReachesOOMPlaced mpl mmpl elf W i` and `¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i`
across `CliPqxdhInputs ⟨W.C, W.Q⟩` implies `CliPqxdhElfCorrectStrictPlaced2Exists mpl mmpl elf`. -/
theorem cliPqxdhElfCorrectStrictPlaced2_of_noOOM
    {mpl mmpl : Obj.MultiPlacement} {elf : ElfImage}
    (hElf : CliPqxdhElfCorrectPlaced mpl mmpl elf)
    (hNoOOM : ∀ (W : CliHooks),
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i → ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (hNoStuck : ∀ (W : CliHooks),
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      ∀ (i : Inputs), CliPqxdhInputs ⟨W.C, W.Q⟩ i →
        ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhElfCorrectStrictPlaced2Exists mpl mmpl elf :=
  ⟨hElf.1, fun X =>
    ⟨cliSpecPqxdh_of_orExcusedAbort_gen (hElf.2 X).1 (fun i hi h =>
        h.elim (hNoOOM ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl i hi)
          (hNoStuck ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl i hi)),
     cliSpecPqxdhNoMatch_of_orExcusedAbort_gen (hElf.2 X).2 (fun i hi h =>
        h.elim (hNoOOM ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl i hi)
          (hNoStuck ⟨realCrypto, realPqxdhPrims⟩ rfl rfl rfl rfl rfl rfl rfl rfl i hi))⟩⟩

theorem cliPqxdhBinaryCorrectStrictPlacedAt2_of_noOOM
    {mpl mmpl : Obj.MultiPlacement} {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlacedAt mpl mmpl bytes)
    (hNoOOM : ∀ (elf : ElfImage) (W : CliHooks) (i : Inputs),
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (hNoStuck : ∀ (elf : ElfImage) (W : CliHooks) (i : Inputs),
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlacedAt2Exists mpl mmpl bytes := by
  obtain ⟨elf, hparse, hElf⟩ := hBin
  exact ⟨elf, hparse,
    cliPqxdhElfCorrectStrictPlaced2_of_noOOM hElf
      (fun W hE hD hX hPub hF512 hEnc hDec hK i hi =>
        hNoOOM elf W i hparse hElf.1 hE hD hX hPub hF512 hEnc hDec hK hi)
      (fun W hE hD hX hPub hF512 hEnc hDec hK i hi =>
        hNoStuck elf W i hparse hElf.1 hE hD hX hPub hF512 hEnc hDec hK hi)⟩

theorem cliPqxdhBinaryCorrectStrictPlaced2_of_noOOM
    {bytes : List (BitVec 8)}
    (hBin : CliPqxdhBinaryCorrectPlaced bytes)
    (hNoOOM : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs),
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesOOMPlaced mpl mmpl elf W i)
    (hNoStuck : ∀ (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs),
      libsignalSessionLib.LinkedAt bytes mpl →
      mallocngLib.LinkedAt bytes mmpl →
      ElfImage.parse bytes = .ok elf →
      CliElfCodeMatchesPlaced mpl mmpl elf →
      W.C.E = CryptoGames.AES256.aes256Enc →
      W.C.D = CryptoGames.AES256.aes256Dec →
      W.C.X = CryptoGames.RFC7748.x25519Ref →
      W.C.pubKey = CryptoGames.RFC7748.x25519PubFromSecretRef →
      W.Q.F512 = CryptoGames.SHA512.sha512CompressState →
      W.Q.encaps = CryptoGames.MLKEM.kyber1024EncapsVec →
      W.Q.decaps = CryptoGames.MLKEM.kyber1024DecapsVec →
      W.Q.K = CryptoGames.MLKEM.mlkem768Incremental →
      CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      ¬ CliReachesSampleNttStuckPlaced mpl mmpl elf W i) :
    CliPqxdhBinaryCorrectStrictPlaced2Exists bytes :=
  fun mpl mmpl hLs hMal =>
    cliPqxdhBinaryCorrectStrictPlacedAt2_of_noOOM (hBin mpl mmpl hLs hMal)
      (fun elf W i hparse hCode hE hD hX hPub hF512 hEnc hDec hK hi =>
        hNoOOM mpl mmpl elf W i hLs hMal hparse hCode hE hD hX hPub hF512 hEnc hDec hK hi)
      (fun elf W i hparse hCode hE hD hX hPub hF512 hEnc hDec hK hi =>
        hNoStuck mpl mmpl elf W i hLs hMal hparse hCode hE hD hX hPub hF512 hEnc hDec hK hi)

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.PlacedOomRecovery2
