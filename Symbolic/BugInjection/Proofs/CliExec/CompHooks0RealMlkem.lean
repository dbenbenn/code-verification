/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.KEM.MlKem
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs -- proof-setup: allow-public-import
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits -- proof-setup: allow-public-import
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat0A
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat0B
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1A
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1B
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat2A
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat2B
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow0
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow1
import Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow2

/-!
# Certified `compHooks0` ML-KEM-768 Rows and Hybrid `mlkem768Incremental` Wrapper

Combines the parallel `rfl_kernel` certificates in `CompHooks0RealMlkemMat{0,1,2}{A,B}` and
`CompHooks0RealMlkemRow{0,1,2}` and exports `mlkem768Hybrid : MlKem` with
`mlkem768Hybrid_eq : mlkem768Hybrid = mlkem768Incremental`.
-/

namespace Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkem

open CryptoGames.MLKEM (mlkem768Incremental mlkem768ValidPk)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemDefs (
  mlkem768ValidPkFast mlkem768ValidPkFast_eq mlkemRowGivenMat_sound
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemLits (
  mlkemDk0 mlkemDk0_length mlkemDk1 mlkemDk1_length mlkemDk2 mlkemDk2_length
  mlkemSeed0 mlkemSeed0_length mlkemSeed1 mlkemSeed1_length mlkemSeed2 mlkemSeed2_length
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat0A (mlkem_mat0_01_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat0B (mlkem_mat0_2_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1A (mlkem_mat1_01_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat1B (mlkem_mat1_2_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat2A (mlkem_mat2_01_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemMat2B (mlkem_mat2_2_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow0 (mlkem_row0_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow1 (mlkem_row1_ok)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkemRow2 (mlkem_row2_ok)

public section
set_option autoImplicit false

private theorem mlkem_rows_unpacked :
    ((mlkem768Incremental.keyPair ⟨mlkemSeed0, mlkemSeed0_length⟩).toList = mlkemDk0 ∧
     mlkem768ValidPk ((mlkemDk0.drop 2304).take 64) ((mlkemDk0.drop 1152).take 1152) = true) ∧
    ((mlkem768Incremental.keyPair ⟨mlkemSeed1, mlkemSeed1_length⟩).toList = mlkemDk1 ∧
     mlkem768ValidPk ((mlkemDk1.drop 2304).take 64) ((mlkemDk1.drop 1152).take 1152) = true) ∧
    ((mlkem768Incremental.keyPair ⟨mlkemSeed2, mlkemSeed2_length⟩).toList = mlkemDk2 ∧
     mlkem768ValidPk ((mlkemDk2.drop 2304).take 64) ((mlkemDk2.drop 1152).take 1152) = true) :=
  ⟨mlkemRowGivenMat_sound ⟨mlkemSeed0, mlkemSeed0_length⟩ mlkemDk0_length mlkem_mat0_01_ok mlkem_mat0_2_ok mlkem_row0_ok,
   mlkemRowGivenMat_sound ⟨mlkemSeed1, mlkemSeed1_length⟩ mlkemDk1_length mlkem_mat1_01_ok mlkem_mat1_2_ok mlkem_row1_ok,
   mlkemRowGivenMat_sound ⟨mlkemSeed2, mlkemSeed2_length⟩ mlkemDk2_length mlkem_mat2_01_ok mlkem_mat2_2_ok mlkem_row2_ok⟩

@[expose] noncomputable def mlkem768Hybrid : MlKem where
  keyPair seed :=
    let s := seed.toList
    if s == mlkemSeed0 then
      ⟨mlkemDk0, mlkemDk0_length⟩
    else if s == mlkemSeed1 then
      ⟨mlkemDk1, mlkemDk1_length⟩
    else if s == mlkemSeed2 then
      ⟨mlkemDk2, mlkemDk2_length⟩
    else
      mlkem768Incremental.keyPair seed
  encaps1 := mlkem768Incremental.encaps1
  encaps2 := mlkem768Incremental.encaps2
  decaps := mlkem768Incremental.decaps
  validPk hdr ek :=
    if (hdr == (mlkemDk0.drop 2304).take 64 && ek == (mlkemDk0.drop 1152).take 1152) ||
       (hdr == (mlkemDk1.drop 2304).take 64 && ek == (mlkemDk1.drop 1152).take 1152) ||
       (hdr == (mlkemDk2.drop 2304).take 64 && ek == (mlkemDk2.drop 1152).take 1152) then
      true
    else
      mlkem768ValidPkFast hdr ek

private theorem vec_mk_toList {α : Type} {n : Nat} (xs : List α) (h : xs.length = n) :
    List.Vector.toList ⟨xs, h⟩ = xs := rfl

theorem mlkem768Hybrid_eq : mlkem768Hybrid = mlkem768Incremental := by
  rcases mlkem_rows_unpacked with ⟨⟨hkp0, hv0⟩, ⟨hkp1, hv1⟩, ⟨hkp2, hv2⟩⟩
  have hkp : mlkem768Hybrid.keyPair = mlkem768Incremental.keyPair := by
    funext seed
    unfold mlkem768Hybrid
    dsimp only
    by_cases hs0 : (seed.toList == mlkemSeed0) = true
    · simp only [hs0, ↓reduceIte]
      apply List.Vector.eq
      have hveq : seed = ⟨mlkemSeed0, mlkemSeed0_length⟩ :=
        List.Vector.eq seed _ (beq_iff_eq.mp hs0)
      rw [vec_mk_toList, hveq, hkp0]
    · simp only [Bool.not_eq_true] at hs0
      simp only [hs0, Bool.false_eq_true, ↓reduceIte]
      by_cases hs1 : (seed.toList == mlkemSeed1) = true
      · simp only [hs1, ↓reduceIte]
        apply List.Vector.eq
        have hveq : seed = ⟨mlkemSeed1, mlkemSeed1_length⟩ :=
          List.Vector.eq seed _ (beq_iff_eq.mp hs1)
        rw [vec_mk_toList, hveq, hkp1]
      · simp only [Bool.not_eq_true] at hs1
        simp only [hs1, Bool.false_eq_true, ↓reduceIte]
        by_cases hs2 : (seed.toList == mlkemSeed2) = true
        · simp only [hs2, ↓reduceIte]
          apply List.Vector.eq
          have hveq : seed = ⟨mlkemSeed2, mlkemSeed2_length⟩ :=
            List.Vector.eq seed _ (beq_iff_eq.mp hs2)
          rw [vec_mk_toList, hveq, hkp2]
        · simp only [Bool.not_eq_true] at hs2
          simp only [hs2, Bool.false_eq_true, ↓reduceIte]
  have hvp : mlkem768Hybrid.validPk = mlkem768Incremental.validPk := by
    funext hdr ek
    unfold mlkem768Hybrid
    dsimp only
    by_cases h : ((hdr == (mlkemDk0.drop 2304).take 64 && ek == (mlkemDk0.drop 1152).take 1152) ||
        (hdr == (mlkemDk1.drop 2304).take 64 && ek == (mlkemDk1.drop 1152).take 1152) ||
        (hdr == (mlkemDk2.drop 2304).take 64 && ek == (mlkemDk2.drop 1152).take 1152)) = true
    · simp only [h, ↓reduceIte]
      have hv_eq : mlkem768Incremental.validPk = mlkem768ValidPk := rfl
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      rcases h with (⟨hh0, he0⟩ | ⟨hh1, he1⟩) | ⟨hh2, he2⟩
      · rw [hv_eq, hh0, he0, hv0]
      · rw [hv_eq, hh1, he1, hv1]
      · rw [hv_eq, hh2, he2, hv2]
    · simp only [Bool.not_eq_true] at h
      simp only [h, Bool.false_eq_true, ↓reduceIte]
      exact mlkem768ValidPkFast_eq hdr ek
  cases hml : mlkem768Incremental with
  | mk kp e1 e2 dec vp =>
    have h1 : mlkem768Hybrid =
        { keyPair := mlkem768Hybrid.keyPair
          encaps1 := e1
          encaps2 := e2
          decaps := dec
          validPk := mlkem768Hybrid.validPk } := by
      unfold mlkem768Hybrid
      rw [hml]
    rw [h1, hkp, hvp, hml]

end

end Symbolic.BugInjection.Proofs.CliExec.CompHooks0RealMlkem
