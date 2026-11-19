/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.LibsignalCli.StatementPqElf
public import Computational.Proofs.SpecLemmas.Game.StatementBinaryHarnessCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.MlKemCorrectFacts -- proof-setup: allow-public-import

/-!
# Headline and Non-Vacuity Witnesses for `W.Q` ML-KEM Equations

Helper bridges for `RealMlKemEquations` pinning `Q : PqxdhPrims` to the `libcrux_ml_kem`
specifications (`Q.encaps = kyber1024EncapsVec`, `Q.decaps = kyber1024DecapsVec`,
`Q.K = mlkem768Incremental`):

1. Override combinators (`withRealMlKemPrims`, `withRealMlKemPE`, `withRealMlKem`) that preserve
   `W.C` and `W.Q.F512`.
2. Discharges of `Encaps1Total K` and `MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds K` from
   `K = mlkem768Incremental` (discharging the `_hK_tot` premise of `CliPqxdhSecurityFor`).
3. Non-vacuity `δ = 1` witnesses (`mlkem768Incremental_correctWith_one`, `kemDeltaCorrect_one`),
   monotonicity (`kemDeltaCorrect_mono`), and equation-transport lemmas for `KemDeltaCorrect`
   and `modelPrims`.
-/

set_option autoImplicit false

public section

namespace Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses

open scoped ENNReal
open OracleComp OracleSpec
open CryptoVerification.E2E (
  MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds PEParams PqxdhPrims UnreachedPqxdhPrimitives
  modelPrims
)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.MlKemCorrectProofs (
  kyber1024DecapsVec kyber1024EncapsVec mlkem768Incremental_encaps1SucceedsOn64ByteHeaderAndSeeds
  mlkem768Incremental_encaps1Total
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Spec (mlkem768Incremental)
open SignalPqxdh (
  CryptoWellFormedDh CryptoWellFormedKemδ CryptoWellFormedPrimitivesδ KemDeltaCorrect Primitives
  WellFormedPrimitivesδ kemHonestExchangeFails
)

attribute [local irreducible] kyber1024EncapsVec kyber1024DecapsVec mlkem768Incremental

/-! ## 1. `W.Q` Equation Predicate and Override Combinators -/

/-- The 3 equations pinning `Q : PqxdhPrims` to the `libcrux_ml_kem` specifications
    (`kyber1024EncapsVec`, `kyber1024DecapsVec`, `mlkem768Incremental`). -/
@[expose] def RealMlKemEquations (Q : PqxdhPrims) : Prop :=
  Q.encaps = kyber1024EncapsVec ∧
  Q.decaps = kyber1024DecapsVec ∧
  Q.K = mlkem768Incremental

/-- Override `Q.encaps`, `Q.decaps`, and `Q.K` with the real `libcrux_ml_kem` primitives, keeping
    `Q.F512` unchanged. -/
@[expose] noncomputable def withRealMlKemPrims (Q : PqxdhPrims) : PqxdhPrims :=
  { Q with
    encaps := kyber1024EncapsVec
    decaps := kyber1024DecapsVec
    K := mlkem768Incremental }

/-- Override `W.Q` in `PEParams` with `withRealMlKemPrims W.Q`, keeping `W.C` and `W.Q.F512`
    unchanged. -/
@[expose] noncomputable def withRealMlKemPE (W : PEParams) : PEParams :=
  { W with Q := withRealMlKemPrims W.Q }

/-- Override `W.Q` in `CliHooks` with `withRealMlKemPrims W.Q`, keeping `W.C` and `W.Q.F512`
    unchanged. -/
@[expose] noncomputable def withRealMlKem (W : CliHooks) : CliHooks :=
  { W with Q := withRealMlKemPrims W.Q }

theorem withRealMlKemPrims_realEquations (Q : PqxdhPrims) :
    RealMlKemEquations (withRealMlKemPrims Q) := by
  unfold RealMlKemEquations withRealMlKemPrims; exact ⟨rfl, rfl, rfl⟩

theorem withRealMlKemPE_realEquations (W : PEParams) :
    RealMlKemEquations (withRealMlKemPE W).Q := by
  unfold withRealMlKemPE; exact withRealMlKemPrims_realEquations W.Q

theorem withRealMlKem_realEquations (W : CliHooks) :
    RealMlKemEquations (withRealMlKem W).Q := by
  unfold withRealMlKem; exact withRealMlKemPrims_realEquations W.Q

theorem withRealMlKem_C (W : CliHooks) : (withRealMlKem W).C = W.C := by
  unfold withRealMlKem; rfl

theorem withRealMlKem_F512 (W : CliHooks) : (withRealMlKem W).Q.F512 = W.Q.F512 := by
  unfold withRealMlKem withRealMlKemPrims; rfl

theorem withRealMlKemPE_C (W : PEParams) : (withRealMlKemPE W).C = W.C := by
  unfold withRealMlKemPE; rfl

theorem withRealMlKemPE_F512 (W : PEParams) : (withRealMlKemPE W).Q.F512 = W.Q.F512 := by
  unfold withRealMlKemPE withRealMlKemPrims; rfl

/-! ## 2. Discharging `Encaps1Total` & `MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds` -/

/-- `Encaps1Total K` holds whenever `K = mlkem768Incremental`. -/
theorem encaps1Total_of_eq_mlkem768Incremental {K : MlKem} (hK : K = mlkem768Incremental) :
    Encaps1Total K :=
  hK ▸ mlkem768Incremental_encaps1Total

/-- `MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds K` holds whenever `K = mlkem768Incremental`,
    discharging `_hK_tot` in `CliPqxdhSecurityFor`. -/
theorem encaps1SucceedsOn64ByteHeaderAndSeeds_of_eq_mlkem768Incremental {K : MlKem}
    (hK : K = mlkem768Incremental) :
    MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds K :=
  hK ▸ mlkem768Incremental_encaps1SucceedsOn64ByteHeaderAndSeeds

theorem encaps1SucceedsOn64ByteHeaderAndSeeds_of_realEquations {Q : PqxdhPrims}
    (hQ : RealMlKemEquations Q) :
    MlKemEncaps1SucceedsOn64ByteHeaderAndSeeds Q.K :=
  encaps1SucceedsOn64ByteHeaderAndSeeds_of_eq_mlkem768Incremental hQ.2.2

/-! ## 3. `CorrectWith 1`, `KemDeltaCorrect P 1`, Monotonicity, & `modelPrims` Equation Transport -/

/-- Non-vacuity `δ = 1` witness for `mlkem768Incremental.CorrectWith`. -/
theorem mlkem768Incremental_correctWith_one : mlkem768Incremental.CorrectWith 1 :=
  MlKem.correctWith_one mlkem768Incremental

theorem correctWith_one_of_eq_mlkem768Incremental {K : MlKem} (hK : K = mlkem768Incremental) :
    K.CorrectWith 1 :=
  hK ▸ mlkem768Incremental_correctWith_one

/-- Every PQXDH primitive suite `P` is `KemDeltaCorrect P 1` (since sub-probability
    distributions assign mass at most `1` to `{true}`), giving a non-vacuity witness for
    `δ_kem = 1`. -/
theorem kemDeltaCorrect_one (P : Primitives) : KemDeltaCorrect P 1 := by
  unfold KemDeltaCorrect
  exact ((evalDist _).mono (Set.subset_univ {true})).trans (EvalDistSemantics.apply_univ_le_one _)

/-- Monotonicity of `KemDeltaCorrect P` in the failure bound `δ`. -/
theorem kemDeltaCorrect_mono {P : Primitives} {δ₁ δ₂ : ENNReal}
    (h : KemDeltaCorrect P δ₁) (hle : δ₁ ≤ δ₂) : KemDeltaCorrect P δ₂ :=
  le_trans h hle

/-- Transport `KemDeltaCorrect` across two `Primitives` records sharing `kemKeyGen`, `kemEncaps`,
    and `kemDecaps`. -/
theorem kemDeltaCorrect_of_kem_eq {P₁ P₂ : Primitives} {δ : ENNReal}
    (hkg : P₁.kemKeyGen = P₂.kemKeyGen)
    (henc : P₁.kemEncaps = P₂.kemEncaps)
    (hdec : P₁.kemDecaps = P₂.kemDecaps)
    (h : KemDeltaCorrect P₁ δ) : KemDeltaCorrect P₂ δ := by
  have hex : kemHonestExchangeFails P₂ = kemHonestExchangeFails P₁ := by
    funext seed r
    unfold kemHonestExchangeFails
    rw [hkg, henc, hdec]
  unfold KemDeltaCorrect at h ⊢
  rwa [hex]

/-- `modelPrims X Wp` depends on `Wp.Q` only through `Wp.Q.F512`, `Wp.Q.encaps`, and `Wp.Q.decaps`
    (independent of `Wp.Q.K`). -/
theorem modelPrims_eq_of_C_F512_kem_eq (X : UnreachedPqxdhPrimitives) {W₁ W₂ : PEParams}
    (hC : W₁.C = W₂.C) (hF512 : W₁.Q.F512 = W₂.Q.F512)
    (henc : W₁.Q.encaps = W₂.Q.encaps) (hdec : W₁.Q.decaps = W₂.Q.decaps) :
    modelPrims X W₁ = modelPrims X W₂ := by
  rcases W₁ with ⟨C₁, ⟨F1, enc1, dec1, K1⟩⟩
  rcases W₂ with ⟨C₂, ⟨F2, enc2, dec2, K2⟩⟩
  dsimp only at hC hF512 henc hdec
  subst hC hF512 henc hdec
  rfl

/-- Replacing `Wp.Q.K` with `mlkem768Incremental` leaves `modelPrims X Wp` definitionally equal,
    so `CryptoWellFormedPrimitivesδ (modelPrims X Wp)` and `KemDeltaCorrect (modelPrims X Wp)`
    are unaffected by `Wp.Q.K = mlkem768Incremental`. -/
theorem modelPrims_withRealMlKemK_eq (X : UnreachedPqxdhPrimitives) (Wp : PEParams) :
    modelPrims X { Wp with Q := { Wp.Q with K := mlkem768Incremental } } = modelPrims X Wp :=
  modelPrims_eq_of_C_F512_kem_eq X rfl rfl rfl rfl

end Computational.Proofs.LibsignalCli.MlKemHeadlineWitnesses
